"""E2 distance-duality local-global gluing test."""

from __future__ import annotations

import argparse
import csv
import json
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
import yaml
from dynesty import NestedSampler
from dynesty import utils as dyfunc
from scipy import stats

import sbt_cosmo
from sbt_cosmo.io.checksums import sha256_file
from sbt_cosmo.io.datasets import load_desi_dr2_bao, load_pantheon_plus
from sbt_cosmo.likelihoods.cmb_compressed import load_planck2018_compressed
from sbt_cosmo.theory.background_compressed import evaluate_background, omega_m_approx
from sbt_cosmo.xi.kernels import corrected_bao_observables, corrected_luminosity_distance

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class FitResult:
    model: str
    sampled_parameters: list[str]
    bestfit: dict[str, float]
    posterior: dict[str, dict[str, float]]
    block_chi2: dict[str, float]
    chi2: float
    logz: float
    logz_err: float
    neff: float
    ncall: int
    niter: int
    wall_clock_seconds: float
    chain_path: Path


class E2Likelihood:
    """Compressed CMB + DESI BAO + Pantheon+ likelihood for E2 models."""

    def __init__(self, model: str) -> None:
        self.model = model
        self.planck = load_planck2018_compressed()
        self.bao = load_desi_dr2_bao()
        self.sn = load_pantheon_plus()
        self.planck_inv = self.planck["inv_covariance_array"]
        self.bao_inv = np.linalg.inv(self.bao.covariance)
        self.sn_inv = np.linalg.inv(self.sn.covariance)

    def __call__(self, theta: np.ndarray, names: list[str], fixed: dict[str, float]) -> float:
        point = {**fixed, **{name: float(value) for name, value in zip(names, theta)}}
        try:
            blocks = self.block_chi2(point)
        except Exception:
            return -np.inf
        chi2 = float(sum(blocks.values()))
        return -0.5 * chi2 if np.isfinite(chi2) else -np.inf

    def block_chi2(self, point: dict[str, float]) -> dict[str, float]:
        return {"CMB": self._cmb(point), "BAO": self._bao(point), "SN": self._sn(point)}

    def _cmb(self, point: dict[str, float]) -> float:
        bg = evaluate_background(
            omega_b=point["omega_b"],
            omega_cdm=point["omega_cdm"],
            H0=point["H0"],
            w0_fld=point.get("w0_fld", -1.0),
            wa_fld=point.get("wa_fld", 0.0),
        )
        vector = np.asarray([bg.R, bg.l_A, 100.0 * point["omega_b"]], dtype=float)
        delta = vector - self.planck["mean_array"]
        return float(delta @ self.planck_inv @ delta)

    def _bao(self, point: dict[str, float]) -> float:
        z = np.asarray(self.bao.bins["z"], dtype=float)
        observables = list(self.bao.bins["observable"])
        if self.model in {"M2", "M_mix"}:
            prediction, _ = corrected_bao_observables(
                z=z,
                observables=observables,
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                parameters=point,
                w0_fld=point.get("w0_fld", -1.0),
                wa_fld=point.get("wa_fld", 0.0),
            )
        else:
            bg = evaluate_background(
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                w0_fld=point.get("w0_fld", -1.0),
                wa_fld=point.get("wa_fld", 0.0),
                z=tuple(z.tolist()),
            )
            prediction = np.empty_like(self.bao.data_vector)
            for index, obs in enumerate(observables):
                if obs == "DM_over_rs":
                    prediction[index] = bg.D_M[index] / bg.r_drag
                elif obs == "DH_over_rs":
                    prediction[index] = bg.D_H[index] / bg.r_drag
                elif obs == "DV_over_rs":
                    prediction[index] = bg.D_V[index] / bg.r_drag
                else:
                    raise ValueError(f"unsupported BAO observable: {obs}")
        residual = self.bao.data_vector - prediction
        return float(residual @ self.bao_inv @ residual)

    def _sn(self, point: dict[str, float]) -> float:
        z = np.asarray(self.sn.bins["z_cmb"], dtype=float)
        if self.model in {"M2", "M_mix"}:
            d_l, _ = corrected_luminosity_distance(
                z=z,
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                parameters=point,
                w0_fld=point.get("w0_fld", -1.0),
                wa_fld=point.get("wa_fld", 0.0),
            )
            if np.any(d_l <= 0):
                raise ValueError("Xi-corrected luminosity distance became non-positive")
            mu = 5.0 * np.log10(d_l) + 25.0
        else:
            bg = evaluate_background(
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                w0_fld=point.get("w0_fld", -1.0),
                wa_fld=point.get("wa_fld", 0.0),
                z=tuple(z.tolist()),
            )
            mu = bg.mu
            if self.model == "M_AM":
                eta = 1.0 + float(point["epsilon0"]) * z
                if np.any(eta <= 0):
                    raise ValueError("eta(z)=1+epsilon0*z became non-positive")
                mu = mu + 5.0 * np.log10(eta)
        residual = self.sn.data_vector - (mu + float(point["sn_M"]))
        return float(residual @ self.sn_inv @ residual)


def reconstruct_eta(config: dict[str, Any]) -> dict[str, Any]:
    """Reconstruct eta(z)/eta0 shape on the SN/BAO overlap grid."""
    sn = load_pantheon_plus()
    bao = load_desi_dr2_bao()
    cfg = config["eta_reconstruction"]
    z_grid = np.round(np.arange(float(cfg["z_min"]), float(cfg["z_max"]) + 0.5 * float(cfg["dz"]), float(cfg["dz"])), 6)

    sn_z = np.asarray(sn.bins["z_cmb"], dtype=float)
    width = float(cfg["sn_kernel_width"])
    w_sn = np.exp(-0.5 * ((z_grid[:, None] - sn_z[None, :]) / width) ** 2)
    w_sn = w_sn / np.sum(w_sn, axis=1)[:, None]
    mu_hat = w_sn @ sn.data_vector
    cov_ln_dl = (np.log(10.0) / 5.0) ** 2 * (w_sn @ sn.covariance @ w_sn.T)

    obs = np.asarray(bao.bins["observable"], dtype=object)
    dm_mask = obs == "DM_over_rs"
    z_dm = np.asarray(bao.bins["z"], dtype=float)[dm_mask]
    dm = bao.data_vector[dm_mask]
    cov_dm_native = bao.covariance[np.ix_(np.where(dm_mask)[0], np.where(dm_mask)[0])]
    order = np.argsort(z_dm)
    z_dm = z_dm[order]
    dm = dm[order]
    cov_dm_native = cov_dm_native[np.ix_(order, order)]
    interp = _interp_matrix(z_grid, z_dm)
    dm_hat = interp @ dm
    cov_dm = interp @ cov_dm_native @ interp.T
    cov_ln_dm = cov_dm / np.outer(dm_hat, dm_hat)

    log_eta = (np.log(10.0) / 5.0) * (mu_hat - 25.0) - np.log1p(z_grid) - np.log(dm_hat)
    cov = cov_ln_dl + cov_ln_dm
    inv = np.linalg.pinv(cov)
    flat = _linear_fit(log_eta, cov, np.ones((z_grid.size, 1)))
    residual = log_eta - flat["model"]
    eta_norm = np.exp(residual)
    fit_z = _linear_fit(log_eta, cov, np.column_stack((np.ones(z_grid.size), z_grid)))
    fit_log = _linear_fit(log_eta, cov, np.column_stack((np.ones(z_grid.size), np.log1p(z_grid))))
    spearman = stats.spearmanr(z_grid, eta_norm - 1.0)
    return {
        "z": z_grid.tolist(),
        "eta_norm": eta_norm.tolist(),
        "sigma_log_eta": np.sqrt(np.diag(cov)).tolist(),
        "flat_chi2": float(flat["chi2"]),
        "flat_dof": int(z_grid.size - 1),
        "flat_chi2_dof": float(flat["chi2"] / max(z_grid.size - 1, 1)),
        "epsilon_z": float(fit_z["beta"][1]),
        "epsilon_z_sigma": float(np.sqrt(fit_z["cov_beta"][1, 1])),
        "epsilon_z_significance": float(abs(fit_z["beta"][1]) / np.sqrt(fit_z["cov_beta"][1, 1])),
        "epsilon_log1p": float(fit_log["beta"][1]),
        "epsilon_log1p_sigma": float(np.sqrt(fit_log["cov_beta"][1, 1])),
        "epsilon_log1p_significance": float(abs(fit_log["beta"][1]) / np.sqrt(fit_log["cov_beta"][1, 1])),
        "spearman_r": float(spearman.statistic),
        "spearman_p": float(spearman.pvalue),
    }


def run_model(config: dict[str, Any], model: str, outdir: Path, *, nlive: int, dlogz: float, pool_size: int) -> FitResult:
    started = time.monotonic()
    model_cfg = config["models"][model]
    names = list(model_cfg["sampled"])
    fixed = {key: float(value) for key, value in model_cfg.get("fixed", {}).items()}
    transforms = [_uniform_transform(config["priors"][name]["prior"]) for name in names]
    likelihood = E2Likelihood(model)
    prior_transform = _PriorTransform(tuple(transforms))
    loglike = _LogLike(likelihood, tuple(names), fixed)
    rng = np.random.default_rng(int(config["seeds"]["dynesty"]) + _model_offset(model))
    kwargs = dict(ndim=len(names), nlive=int(nlive), bound=config["dynesty"]["bound"], sample=config["dynesty"]["sample"], rstate=rng)
    if pool_size > 1:
        import dynesty.pool as dypool

        with dypool.Pool(int(pool_size), loglike, prior_transform) as pool:
            sampler = NestedSampler(pool.loglike, pool.prior_transform, pool=pool, queue_size=int(pool_size), **kwargs)
            sampler.run_nested(dlogz=float(dlogz), print_progress=False)
            results = sampler.results
    else:
        sampler = NestedSampler(loglike, prior_transform, **kwargs)
        sampler.run_nested(dlogz=float(dlogz), print_progress=False)
        results = sampler.results
    samples = np.asarray(results.samples, dtype=float)
    logl = np.asarray(results.logl, dtype=float)
    logz = float(results.logz[-1])
    log_weights = np.asarray(results.logwt, dtype=float)
    weights = np.exp(log_weights - logz)
    weights = weights / np.sum(weights)
    best = int(np.argmax(logl))
    bestfit = {**fixed, **{name: float(value) for name, value in zip(names, samples[best])}}
    bestfit["Omega_m"] = omega_m_approx(omega_b=bestfit["omega_b"], omega_cdm=bestfit["omega_cdm"], H0=bestfit["H0"])
    blocks = likelihood.block_chi2(bestfit)
    chain_path = outdir / model / "chains" / f"{model}_dyn.1.txt"
    _write_chain(chain_path, names, fixed, samples, logl, weights, rng, int(config["dynesty"]["max_equal_samples"]))
    return FitResult(
        model=model,
        sampled_parameters=names,
        bestfit=bestfit,
        posterior=_posterior(names, samples, weights),
        block_chi2=blocks,
        chi2=float(sum(blocks.values())),
        logz=logz,
        logz_err=float(results.logzerr[-1]),
        neff=float(dyfunc.get_neff_from_logwt(log_weights)),
        ncall=int(np.sum(results.ncall)),
        niter=int(results.niter),
        wall_clock_seconds=float(time.monotonic() - started),
        chain_path=chain_path,
    )


def profile_likelihood(iterations: int) -> dict[str, float]:
    config = yaml.safe_load((ROOT / "configs" / "experiments" / "E2_compressed.yaml").read_text(encoding="utf-8"))
    model = "M2"
    names = list(config["models"][model]["sampled"])
    fixed = {key: float(value) for key, value in config["models"][model]["fixed"].items()}
    theta = np.asarray([0.02236, 0.12, 67.4, -0.02, -0.03, -0.13], dtype=float)
    loglike = _LogLike(E2Likelihood(model), tuple(names), fixed)
    loglike(theta)
    started = time.perf_counter()
    for _ in range(int(iterations)):
        loglike(theta)
    return {"iterations": int(iterations), "seconds_per_eval": float((time.perf_counter() - started) / int(iterations))}


def build_outputs(config_path: Path, config: dict[str, Any], outdir: Path, results_dir: Path, fits: dict[str, FitResult], eta: dict[str, Any], profile: dict[str, float]) -> dict[str, Any]:
    results_dir.mkdir(parents=True, exist_ok=True)
    _write_eta(results_dir, eta)
    comparison = _comparison_rows(fits)
    _write_model_comparison(results_dir / "model_comparison.csv", comparison)
    collapse = _collapse(fits)
    f4 = _f4_status(eta, comparison, collapse)
    (results_dir / "w_a_collapse.json").write_text(json.dumps(collapse, indent=2, sort_keys=True), encoding="utf-8")
    (results_dir / "f4_status.json").write_text(json.dumps(f4, indent=2, sort_keys=True), encoding="utf-8")
    summary = {
        "schema_version": 1,
        "experiment": "E2_distance_duality",
        "run_id": "E2_CDDR_C3",
        "terminal_state": f4["decision_verdict"],
        "package_version": sbt_cosmo.__version__,
        "thread_env": {key: os.environ.get(key) for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS")},
        "profile": profile,
        "eta_reconstruction": eta,
        "models": {name: _fit_payload(fit) for name, fit in fits.items()},
        "model_comparison": comparison,
        "w_a_collapse": collapse,
        "f4_status": f4,
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    _write_manifest(config_path, outdir, summary)
    _append_coherence(fits["M2"], f4)
    return summary


def _comparison_rows(fits: dict[str, FitResult]) -> dict[str, dict[str, Any]]:
    n_data = 3 + load_desi_dr2_bao().data_vector.size + load_pantheon_plus().data_vector.size
    rows = {}
    for name, fit in fits.items():
        k = len(fit.sampled_parameters)
        dof = n_data - k
        rows[name] = {
            "chi2": fit.chi2,
            "dof": dof,
            "chi2_dof": fit.chi2 / dof,
            "k_params": k,
            "AIC": fit.chi2 + 2 * k,
            "BIC": fit.chi2 + k * np.log(n_data),
            "logZ": fit.logz,
            "logZ_err": fit.logz_err,
            "CMB": fit.block_chi2["CMB"],
            "BAO": fit.block_chi2["BAO"],
            "SN": fit.block_chi2["SN"],
            "key_params": {key: fit.posterior[key] for key in fit.posterior if key in {"w0_fld", "wa_fld", "a0", "a2", "epsilon0"}},
        }
    bic_m1 = rows["M1"]["BIC"]
    for row in rows.values():
        row["delta_BIC_vs_M1"] = row["BIC"] - bic_m1
    return rows


def _collapse(fits: dict[str, FitResult]) -> dict[str, Any]:
    wa1 = fits["M1"].posterior["wa_fld"]
    wam = fits["M_mix"].posterior["wa_fld"]
    collapse = 1.0 - abs(wam["mean"]) / max(abs(wa1["mean"]), 1e-12)
    d_m = -np.sign(wam["mean"]) / max(abs(wa1["mean"]), 1e-12)
    d_1 = abs(wam["mean"]) * np.sign(wa1["mean"]) / max(abs(wa1["mean"]), 1e-12) ** 2
    sigma = float(np.sqrt((d_m * wam["sigma"]) ** 2 + (d_1 * wa1["sigma"]) ** 2))
    return {
        "wa_M1": wa1,
        "wa_M_mix": wam,
        "F_collapse": float(collapse),
        "F_collapse_sigma_delta": sigma,
        "abs_wa_reduction": float(abs(wa1["mean"]) - abs(wam["mean"])),
    }


def _f4_status(eta: dict[str, Any], comparison: dict[str, dict[str, Any]], collapse: dict[str, Any]) -> dict[str, Any]:
    z_sig = float(eta["epsilon_z_significance"])
    log_sig = float(eta["epsilon_log1p_significance"])
    comp_holds = z_sig < 2.0 and log_sig < 2.0
    overlap_inconsistent = z_sig > 2.0 and log_sig > 2.0
    best_flrw = min(comparison["M0"]["chi2_dof"], comparison["M1"]["chi2_dof"])
    image_member = best_flrw <= 1.05
    if overlap_inconsistent:
        status = "OverlapInconsistent"
    elif comp_holds and image_member:
        status = "GloballyExact"
    elif comp_holds:
        status = "CompatibleNonGlobal"
    else:
        status = "GloballyAmbiguous"
    fc = float(collapse["F_collapse"])
    mix_beats = comparison["M_mix"]["BIC"] + 5.0 < min(comparison["M0"]["BIC"], comparison["M1"]["BIC"], comparison["M2"]["BIC"])
    if fc > 0.5 and status in {"OverlapInconsistent", "CompatibleNonGlobal"}:
        decision = "Gluing residual"
        controversy = "Afroz-Mukherjee direction"
    elif fc < 0.2 and status in {"GloballyExact", "CompatibleNonGlobal"}:
        decision = "Rewrite residual"
        controversy = "Crossing-Statistics consistency direction"
    elif 0.2 <= fc <= 0.5 or mix_beats:
        decision = "Mixture"
        controversy = "mixed"
    else:
        decision = "Mixture"
        controversy = "mixed/ambiguous"
    return {
        "F4_status": status,
        "decision_verdict": decision,
        "controversy_leg_supported": controversy,
        "Comp_eta_flat": bool(comp_holds),
        "OverlapInconsistent_eta_shape": bool(overlap_inconsistent),
        "image_member_FLRW": bool(image_member),
        "best_FLRW_chi2_dof": float(best_flrw),
        "fiber_unique_proxy": bool(image_member),
        "thresholds": {
            "OverlapInconsistent": "epsilon_z and epsilon_log1p both >2 sigma",
            "Comp_holds": "epsilon_z and epsilon_log1p both <2 sigma",
            "GloballyExact": "Comp holds and M0 or M1 chi2/dof <=1.05",
            "Gluing": "F_collapse >0.5 and F4 OverlapInconsistent/CompatibleNonGlobal",
            "Rewrite": "F_collapse <0.2 and F4 GloballyExact/CompatibleNonGlobal",
            "Mixture": "0.2 <= F_collapse <=0.5 or M_mix beats alternatives by DeltaBIC>5",
        },
    }


def _kernel_amplitudes(point: dict[str, float]) -> dict[str, float]:
    sn = load_pantheon_plus()
    bao = load_desi_dr2_bao()
    _, k_l = corrected_luminosity_distance(
        z=np.asarray(sn.bins["z_cmb"], dtype=float),
        omega_b=point["omega_b"],
        omega_cdm=point["omega_cdm"],
        H0=point["H0"],
        parameters=point,
        w0_fld=point.get("w0_fld", -1.0),
        wa_fld=point.get("wa_fld", 0.0),
    )
    _, terms = corrected_bao_observables(
        z=np.asarray(bao.bins["z"], dtype=float),
        observables=list(bao.bins["observable"]),
        omega_b=point["omega_b"],
        omega_cdm=point["omega_cdm"],
        H0=point["H0"],
        parameters=point,
        w0_fld=point.get("w0_fld", -1.0),
        wa_fld=point.get("wa_fld", 0.0),
    )
    return {
        "K_L_max_abs_mpc": float(np.max(np.abs(k_l))),
        "K_M_max_abs_ratio": float(np.max(np.abs(terms["K_M"]))),
        "K_H_max_abs_ratio": float(np.max(np.abs(terms["K_H"]))),
    }


def _append_coherence(fit: FitResult, f4: dict[str, Any]) -> None:
    path = ROOT / "results" / "xi_cosmo_coherence.csv"
    amps = _kernel_amplitudes(fit.bestfit)
    e1_a2 = None
    rows: list[dict[str, str]] = []
    if path.exists():
        with path.open("r", encoding="utf-8", newline="") as handle:
            for row in csv.DictReader(handle):
                if row.get("experiment") == "E1B":
                    e1_a2 = float(row["a2"])
                if row.get("experiment") != "E2":
                    rows.append(row)
    fields = [
        "experiment",
        "run_id",
        "model",
        "a0",
        "a0_sigma",
        "a1",
        "a1_sigma",
        "a2",
        "a2_sigma",
        "K_L_max_abs_mpc",
        "K_M_max_abs_ratio",
        "K_H_max_abs_ratio",
        "aor_status",
    ]
    a2 = fit.posterior["a2"]["mean"]
    ratio = abs(a2) / abs(e1_a2) if e1_a2 not in {None, 0.0} else float("nan")
    coherent = bool(e1_a2 is not None and np.sign(a2) == np.sign(e1_a2) and ratio <= 10.0)
    rows.append(
        {
            "experiment": "E2",
            "run_id": "E2_CDDR_C3",
            "model": "M2",
            "a0": fit.posterior["a0"]["mean"],
            "a0_sigma": fit.posterior["a0"]["sigma"],
            "a1": 0.0,
            "a1_sigma": 0.0,
            "a2": a2,
            "a2_sigma": fit.posterior["a2"]["sigma"],
            "K_L_max_abs_mpc": amps["K_L_max_abs_mpc"],
            "K_M_max_abs_ratio": amps["K_M_max_abs_ratio"],
            "K_H_max_abs_ratio": amps["K_H_max_abs_ratio"],
            "aor_status": "bridged" if coherent else "budgeted",
        }
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    ledger = {
        "experiment": "E2",
        "F4_status": f4["F4_status"],
        "decision_verdict": f4["decision_verdict"],
        "a2_E2": a2,
        "a2_E1B": e1_a2,
        "abs_ratio_E2_to_E1B": ratio,
        "consistent_sign": None if e1_a2 is None else bool(np.sign(a2) == np.sign(e1_a2)),
        "coherent_within_10x": coherent,
    }
    ledger_path = ROOT / "results" / "coherence_ledger" / "E2.json"
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    ledger_path.write_text(json.dumps(ledger, indent=2, sort_keys=True), encoding="utf-8")


def _fit_payload(fit: FitResult) -> dict[str, Any]:
    payload = {
        "sampled_parameters": fit.sampled_parameters,
        "bestfit": fit.bestfit,
        "posterior": fit.posterior,
        "block_chi2": fit.block_chi2,
        "chi2": fit.chi2,
        "logZ": fit.logz,
        "logZ_err": fit.logz_err,
        "neff": fit.neff,
        "ncall": fit.ncall,
        "niter": fit.niter,
        "wall_clock_seconds": fit.wall_clock_seconds,
        "chain_file": str(fit.chain_path),
    }
    if fit.model in {"M2", "M_mix"}:
        payload["kernel_amplitudes"] = _kernel_amplitudes(fit.bestfit)
    return payload


def _write_eta(results_dir: Path, eta: dict[str, Any]) -> None:
    with (results_dir / "eta_reconstruction.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["z", "eta_norm", "sigma_log_eta"])
        writer.writeheader()
        for z, value, sigma in zip(eta["z"], eta["eta_norm"], eta["sigma_log_eta"]):
            writer.writerow({"z": z, "eta_norm": value, "sigma_log_eta": sigma})
    (results_dir / "eta_audit.json").write_text(json.dumps(eta, indent=2, sort_keys=True), encoding="utf-8")


def _write_model_comparison(path: Path, rows: dict[str, dict[str, Any]]) -> None:
    fields = ["model", "chi2", "dof", "chi2_dof", "k_params", "AIC", "BIC", "delta_BIC_vs_M1", "logZ", "logZ_err", "CMB", "BAO", "SN", "key_params"]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for model, row in rows.items():
            writer.writerow({**{key: row[key] for key in fields if key not in {"model", "key_params"}}, "model": model, "key_params": json.dumps(row["key_params"], sort_keys=True)})


def _interp_matrix(x: np.ndarray, xp: np.ndarray) -> np.ndarray:
    matrix = np.zeros((x.size, xp.size), dtype=float)
    for i, value in enumerate(x):
        right = int(np.searchsorted(xp, value, side="right"))
        if right <= 0:
            matrix[i, 0] = 1.0
        elif right >= xp.size:
            matrix[i, -1] = 1.0
        else:
            left = right - 1
            frac = (value - xp[left]) / (xp[right] - xp[left])
            matrix[i, left] = 1.0 - frac
            matrix[i, right] = frac
    return matrix


def _linear_fit(y: np.ndarray, cov: np.ndarray, design: np.ndarray) -> dict[str, Any]:
    inv = np.linalg.pinv(cov)
    cov_beta = np.linalg.pinv(design.T @ inv @ design)
    beta = cov_beta @ design.T @ inv @ y
    model = design @ beta
    residual = y - model
    return {"beta": beta, "cov_beta": cov_beta, "model": model, "chi2": float(residual @ inv @ residual)}


def _uniform_transform(prior: dict[str, float]) -> Any:
    return _Uniform(float(prior["min"]), float(prior["max"]) - float(prior["min"]))


class _Uniform:
    def __init__(self, lower: float, width: float) -> None:
        self.lower = lower
        self.width = width

    def __call__(self, unit: float) -> float:
        return self.lower + self.width * unit


class _PriorTransform:
    def __init__(self, transforms: tuple[Any, ...]) -> None:
        self.transforms = transforms

    def __call__(self, unit: np.ndarray) -> np.ndarray:
        return np.asarray([transform(float(value)) for transform, value in zip(self.transforms, unit)], dtype=float)


class _LogLike:
    def __init__(self, likelihood: E2Likelihood, names: tuple[str, ...], fixed: dict[str, float]) -> None:
        self.likelihood = likelihood
        self.names = list(names)
        self.fixed = dict(fixed)

    def __call__(self, theta: np.ndarray) -> float:
        return self.likelihood(theta, self.names, self.fixed)


def _posterior(names: list[str], samples: np.ndarray, weights: np.ndarray) -> dict[str, dict[str, float]]:
    output = {}
    for idx, name in enumerate(names):
        values = samples[:, idx]
        mean = float(np.sum(weights * values))
        sigma = float(np.sqrt(max(np.sum(weights * (values - mean) ** 2), 0.0)))
        output[name] = {"mean": mean, "sigma": sigma}
    return output


def _write_chain(path: Path, names: list[str], fixed: dict[str, float], samples: np.ndarray, logl: np.ndarray, weights: np.ndarray, rng: np.random.Generator, max_samples: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    n_equal = min(int(max_samples), max(1000, samples.shape[0]))
    indices = rng.choice(samples.shape[0], size=n_equal, replace=True, p=weights)
    columns = ["weight", "minuslogpost", *names, "Omega_m", "chi2"]
    lines = ["# " + " ".join(columns)]
    for idx in indices:
        point = {**fixed, **{name: float(value) for name, value in zip(names, samples[idx])}}
        row = [
            1.0,
            float(-logl[idx]),
            *[point[name] for name in names],
            omega_m_approx(omega_b=point["omega_b"], omega_cdm=point["omega_cdm"], H0=point["H0"]),
            float(-2.0 * logl[idx]),
        ]
        lines.append(" ".join(f"{item:.10e}" for item in row))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _model_offset(model: str) -> int:
    return {"M0": 100, "M1": 200, "M2": 300, "M_mix": 400, "M_AM": 500}[model]


def _write_manifest(config_path: Path, outdir: Path, summary: dict[str, Any]) -> None:
    artifacts = {str(path.relative_to(outdir)): sha256_file(path) for path in sorted(outdir.rglob("*")) if path.is_file() and path.name != "manifest.json"}
    manifest = {
        "schema_version": 1,
        "experiment": "E2_distance_duality",
        "run_id": summary["run_id"],
        "package_version": sbt_cosmo.__version__,
        "config_sha256": sha256_file(config_path),
        "artifact_checksums_sha256": artifacts,
        "terminal_state": summary["terminal_state"],
    }
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("configs/experiments/E2_compressed.yaml"))
    parser.add_argument("--outdir", type=Path, default=Path("runs/E2/E2_CDDR_C3"))
    parser.add_argument("--results-dir", type=Path, default=Path("results/E2"))
    parser.add_argument("--nlive", type=int)
    parser.add_argument("--dlogz", type=float)
    parser.add_argument("--pool", type=int, default=1)
    parser.add_argument("--models", nargs="*", default=["M0", "M1", "M2", "M_mix", "M_AM"])
    args = parser.parse_args()
    config = yaml.safe_load(args.config.read_text(encoding="utf-8"))
    args.outdir.mkdir(parents=True, exist_ok=True)
    profile = profile_likelihood(100)
    eta = reconstruct_eta(config)
    fits = {
        model: run_model(
            config,
            model,
            args.outdir,
            nlive=int(args.nlive or config["dynesty"]["nlive"]),
            dlogz=float(args.dlogz or config["dynesty"]["dlogz"]),
            pool_size=int(args.pool),
        )
        for model in args.models
    }
    summary = build_outputs(args.config, config, args.outdir, args.results_dir, fits, eta, profile)
    print(json.dumps({"summary": str(args.outdir / "summary.json"), "verdict": summary["f4_status"]["decision_verdict"], "F4": summary["f4_status"]["F4_status"]}, indent=2))


if __name__ == "__main__":
    main()
