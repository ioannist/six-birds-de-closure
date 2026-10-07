"""Dynesty runner for the E1-B compressed Xi_cosmo geometry fit."""

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

import sbt_cosmo
from sbt_cosmo.io.checksums import sha256_file
from sbt_cosmo.io.datasets import ProbeData, load_desi_dr2_bao, load_pantheon_plus
from sbt_cosmo.likelihoods.cmb_compressed import load_planck2018_compressed
from sbt_cosmo.theory.background_compressed import evaluate_background, omega_m_approx
from sbt_cosmo.xi.kernels import corrected_bao_observables, corrected_luminosity_distance

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class FitResult:
    """Result bundle for one dynesty geometry fit."""

    model: str
    sampled_parameters: list[str]
    bestfit: dict[str, float]
    block_chi2: dict[str, float]
    chi2: float
    logz: float
    logz_err: float
    neff: float
    ncall: int
    niter: int
    wall_clock_seconds: float
    posterior: dict[str, dict[str, float]]
    chain_path: Path


class GeometryLikelihood:
    """Compressed CMB + DESI BAO + Pantheon+ likelihood with optional Xi kernels."""

    def __init__(self, *, model: str, sn_indices: np.ndarray | None = None) -> None:
        self.model = model.lower()
        self.planck = load_planck2018_compressed()
        self.bao = load_desi_dr2_bao()
        self.sn = load_pantheon_plus()
        if sn_indices is None:
            self.sn_indices = np.arange(self.sn.data_vector.size, dtype=int)
        else:
            self.sn_indices = np.asarray(sn_indices, dtype=int)
        self.planck_inv = self.planck["inv_covariance_array"]
        self.bao_inv = np.linalg.inv(self.bao.covariance)
        self.sn_cov = self.sn.covariance[np.ix_(self.sn_indices, self.sn_indices)]
        self.sn_inv = np.linalg.inv(self.sn_cov)

    def __call__(self, theta: np.ndarray, names: list[str], fixed: dict[str, float]) -> float:
        point = {**fixed, **{name: float(value) for name, value in zip(names, theta)}}
        try:
            blocks = self.block_chi2(point)
        except Exception:
            return -np.inf
        chi2 = float(sum(blocks.values()))
        return -0.5 * chi2 if np.isfinite(chi2) else -np.inf

    def block_chi2(self, point: dict[str, float]) -> dict[str, float]:
        return {
            "CMB": self._cmb_chi2(point),
            "BAO": self._bao_chi2(point),
            "SN": self._sn_chi2(point, self.sn_indices),
        }

    def sn_oos_metrics(self, point: dict[str, float], holdout: np.ndarray) -> dict[str, float]:
        indices = np.asarray(holdout, dtype=int)
        prediction = self._sn_prediction(point, indices)
        residual = self.sn.data_vector[indices] - prediction
        covariance = self.sn.covariance[np.ix_(indices, indices)]
        chi2 = float(residual @ np.linalg.inv(covariance) @ residual)
        return {"chi2": chi2, "rms": float(np.sqrt(np.mean(residual * residual))), "n": int(indices.size)}

    def _cmb_chi2(self, point: dict[str, float]) -> float:
        background = evaluate_background(
            omega_b=point["omega_b"],
            omega_cdm=point["omega_cdm"],
            H0=point["H0"],
            w0_fld=point.get("w0_fld", -1.0),
            wa_fld=point.get("wa_fld", 0.0),
        )
        vector = np.asarray([background.R, background.l_A, 100.0 * point["omega_b"]], dtype=float)
        delta = vector - self.planck["mean_array"]
        return float(delta @ self.planck_inv @ delta)

    def _bao_chi2(self, point: dict[str, float]) -> float:
        z = np.asarray(self.bao.bins["z"], dtype=float)
        observables = list(self.bao.bins["observable"])
        if self.model == "sbt":
            prediction, _ = corrected_bao_observables(
                z=z,
                observables=observables,
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                parameters=point,
            )
        else:
            background = evaluate_background(
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                w0_fld=point.get("w0_fld", -1.0),
                wa_fld=point.get("wa_fld", 0.0),
                z=tuple(z.tolist()),
            )
            prediction = np.empty_like(self.bao.data_vector, dtype=float)
            for index, observable in enumerate(observables):
                if observable == "DM_over_rs":
                    prediction[index] = background.D_M[index] / background.r_drag
                elif observable == "DH_over_rs":
                    prediction[index] = background.D_H[index] / background.r_drag
                elif observable == "DV_over_rs":
                    prediction[index] = background.D_V[index] / background.r_drag
                else:
                    raise ValueError(f"unsupported BAO observable: {observable}")
        residual = self.bao.data_vector - prediction
        return float(residual @ self.bao_inv @ residual)

    def _sn_chi2(self, point: dict[str, float], indices: np.ndarray) -> float:
        residual = self.sn.data_vector[indices] - self._sn_prediction(point, indices)
        return float(residual @ self.sn_inv @ residual)

    def _sn_prediction(self, point: dict[str, float], indices: np.ndarray) -> np.ndarray:
        z_all = np.asarray(self.sn.bins["z_cmb"], dtype=float)
        z = z_all[np.asarray(indices, dtype=int)]
        if self.model == "sbt":
            d_l, _ = corrected_luminosity_distance(
                z=z,
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                parameters=point,
            )
            if np.any(d_l <= 0.0):
                raise ValueError("Xi-corrected luminosity distance became non-positive")
            mu = 5.0 * np.log10(d_l) + 25.0
        else:
            background = evaluate_background(
                omega_b=point["omega_b"],
                omega_cdm=point["omega_cdm"],
                H0=point["H0"],
                w0_fld=point.get("w0_fld", -1.0),
                wa_fld=point.get("wa_fld", 0.0),
                z=tuple(z.tolist()),
            )
            mu = background.mu
        return mu + float(point["sn_M"])


def run_fit(
    *,
    config: dict[str, Any],
    model: str,
    outdir: Path,
    run_label: str,
    nlive: int,
    dlogz: float,
    pool_size: int,
    seed: int,
    sn_indices: np.ndarray | None = None,
) -> FitResult:
    """Run a dynesty fit for lcdm, w0wa, or sbt."""
    started = time.monotonic()
    names, fixed = _model_parameters(model)
    transforms = [_uniform_transform(config["priors"][name]["prior"]) for name in names]
    likelihood = GeometryLikelihood(model=model, sn_indices=sn_indices)
    prior_transform = _PriorTransform(tuple(transforms))
    loglike = _LogLike(likelihood, tuple(names), fixed)
    rng = np.random.default_rng(int(seed))

    sampler_kwargs = dict(ndim=len(names), nlive=int(nlive), bound="multi", sample="rwalk", rstate=rng)
    if pool_size > 1:
        import dynesty.pool as dypool

        with dypool.Pool(int(pool_size), loglike, prior_transform) as pool:
            sampler = NestedSampler(pool.loglike, pool.prior_transform, pool=pool, queue_size=int(pool_size), **sampler_kwargs)
            sampler.run_nested(dlogz=float(dlogz), print_progress=False)
            results = sampler.results
    else:
        sampler = NestedSampler(loglike, prior_transform, **sampler_kwargs)
        sampler.run_nested(dlogz=float(dlogz), print_progress=False)
        results = sampler.results

    samples = np.asarray(results.samples, dtype=float)
    logl = np.asarray(results.logl, dtype=float)
    logz = float(results.logz[-1])
    logz_err = float(results.logzerr[-1])
    log_weights = np.asarray(results.logwt, dtype=float)
    weights = np.exp(log_weights - logz)
    weights = weights / np.sum(weights)
    best_index = int(np.argmax(logl))
    bestfit = {**fixed, **{name: float(value) for name, value in zip(names, samples[best_index])}}
    bestfit["Omega_m"] = omega_m_approx(omega_b=bestfit["omega_b"], omega_cdm=bestfit["omega_cdm"], H0=bestfit["H0"])
    blocks = likelihood.block_chi2(bestfit)
    chi2 = float(sum(blocks.values()))
    posterior = _posterior_summary(names, samples, weights)
    neff = float(dyfunc.get_neff_from_logwt(log_weights))
    chain_path = outdir / "chains" / f"{run_label}.1.txt"
    _write_equal_weight_chain(chain_path, names, fixed, samples, logl, weights, rng, max_samples=int(config["dynesty"]["max_equal_samples"]))
    return FitResult(
        model=model,
        sampled_parameters=names,
        bestfit=bestfit,
        block_chi2=blocks,
        chi2=chi2,
        logz=logz,
        logz_err=logz_err,
        neff=neff,
        ncall=int(np.sum(results.ncall)),
        niter=int(results.niter),
        wall_clock_seconds=float(time.monotonic() - started),
        posterior=posterior,
        chain_path=chain_path,
    )


def profile_likelihood(iterations: int = 200) -> dict[str, float]:
    """Return seconds per full C3 SBT likelihood evaluation."""
    likelihood = GeometryLikelihood(model="sbt")
    names, fixed = _model_parameters("sbt")
    theta = np.asarray([0.0225, 0.1181, 68.3, 0.0, 0.0, 0.0, -0.15], dtype=float)
    loglike = _LogLike(likelihood, tuple(names), fixed)
    loglike(theta)
    started = time.perf_counter()
    for _ in range(int(iterations)):
        loglike(theta)
    elapsed = time.perf_counter() - started
    return {"iterations": int(iterations), "seconds_per_eval": float(elapsed / int(iterations))}


def build_summary(
    *,
    config_path: Path,
    outdir: Path,
    run_id: str,
    main: FitResult,
    oos: dict[str, Any],
    profile: dict[str, float],
) -> dict[str, Any]:
    """Build and write the E1-B summary."""
    n_data = _n_data()
    baseline = _baseline_table(main)
    gates = _gate_table(baseline, oos)
    summary = {
        "schema_version": 1,
        "experiment": "E1B_sbt_geometry",
        "run_id": run_id,
        "mode": "production",
        "terminal_state": "PASS" if all(gate["pass"] for gate in gates.values()) else "FAIL",
        "package_version": sbt_cosmo.__version__,
        "config": str(config_path),
        "datasets": ["PLANCK_2018_COMPRESSED", "DESI_DR2_BAO", "PANTHEON_PLUS"],
        "sampler": "dynesty",
        "background_backend": "scipy",
        "thread_env": {key: os.environ.get(key) for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS")},
        "profile": profile,
        "n_data": n_data,
        "fit": _fit_payload(main),
        "baselines": baseline,
        "oos_sn": oos,
        "gates": gates,
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    _write_manifest(config_path, outdir, summary)
    return summary


def run_oos(
    *,
    config: dict[str, Any],
    outdir: Path,
    nlive: int,
    dlogz: float,
    pool_size: int,
) -> dict[str, Any]:
    """Fit SBT and w0wa on an 80% SN train split and score held-out Pantheon+."""
    sn = load_pantheon_plus()
    rng = np.random.default_rng(int(config["oos"]["seed"]))
    indices = np.arange(sn.data_vector.size, dtype=int)
    holdout_size = int(round(float(config["oos"]["holdout_fraction"]) * indices.size))
    holdout = np.sort(rng.choice(indices, size=holdout_size, replace=False))
    train = np.setdiff1d(indices, holdout, assume_unique=True)
    oos_dir = outdir / "oos"
    oos_dir.mkdir(exist_ok=True)
    (oos_dir / "chains").mkdir(exist_ok=True)
    sbt = run_fit(
        config=config,
        model="sbt",
        outdir=oos_dir,
        run_label="C3_sbt_oos_train_dyn",
        nlive=nlive,
        dlogz=dlogz,
        pool_size=pool_size,
        seed=int(config["seeds"]["dynesty"]) + 101,
        sn_indices=train,
    )
    w0wa = run_fit(
        config=config,
        model="w0wa",
        outdir=oos_dir,
        run_label="C3_w0wa_oos_train_dyn",
        nlive=nlive,
        dlogz=dlogz,
        pool_size=pool_size,
        seed=int(config["seeds"]["dynesty"]) + 202,
        sn_indices=train,
    )
    sbt_metrics = GeometryLikelihood(model="sbt").sn_oos_metrics(sbt.bestfit, holdout)
    w0wa_metrics = GeometryLikelihood(model="w0wa").sn_oos_metrics(w0wa.bestfit, holdout)
    return {
        "holdout_seed": int(config["oos"]["seed"]),
        "holdout_fraction": float(config["oos"]["holdout_fraction"]),
        "n_train": int(train.size),
        "n_holdout": int(holdout.size),
        "sbt": {"fit": _fit_payload(sbt), "holdout": sbt_metrics},
        "w0wa": {"fit": _fit_payload(w0wa), "holdout": w0wa_metrics},
        "sbt_to_w0wa_chi2_ratio": float(sbt_metrics["chi2"] / w0wa_metrics["chi2"]),
        "sbt_to_w0wa_rms_ratio": float(sbt_metrics["rms"] / w0wa_metrics["rms"]),
    }


def write_coherence_csv(path: Path, summary: dict[str, Any]) -> None:
    """Write the E1-B coherence handoff row."""
    fit = summary["fit"]
    row = {
        "experiment": "E1B",
        "run_id": summary["run_id"],
        "model": "sbt",
        "a0": fit["posterior"]["a0"]["mean"],
        "a0_sigma": fit["posterior"]["a0"]["sigma"],
        "a1": fit["posterior"]["a1"]["mean"],
        "a1_sigma": fit["posterior"]["a1"]["sigma"],
        "a2": fit["posterior"]["a2"]["mean"],
        "a2_sigma": fit["posterior"]["a2"]["sigma"],
        "K_L_max_abs_mpc": fit["kernel_amplitudes"]["K_L_max_abs_mpc"],
        "K_M_max_abs_ratio": fit["kernel_amplitudes"]["K_M_max_abs_ratio"],
        "K_H_max_abs_ratio": fit["kernel_amplitudes"]["K_H_max_abs_ratio"],
        "aor_status": "bridged" if summary["gates"]["G-E1-SBT-COHERENCE"]["pass"] else "budgeted",
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(row))
        writer.writeheader()
        writer.writerow(row)


def _baseline_table(main: FitResult) -> dict[str, Any]:
    n_data = _n_data()
    rows: dict[str, Any] = {}
    for model, path in {
        "lcdm": ROOT / "runs" / "E1" / "E1C_C3_lcdm_dyn" / "summary.json",
        "w0wa": ROOT / "runs" / "E1" / "E1C_C3_w0wa_dyn" / "summary.json",
    }.items():
        payload = json.loads(path.read_text(encoding="utf-8"))
        bestfit = {key: float(value) for key, value in payload["minimize"]["bestfit"].items()}
        likelihood = GeometryLikelihood(model=model)
        blocks = likelihood.block_chi2(bestfit)
        chi2 = float(sum(blocks.values()))
        k = len(_model_parameters(model)[0])
        rows[model] = _criterion_row(chi2, blocks, n_data=n_data, k_params=k, source=str(path))
    rows["sbt"] = _criterion_row(main.chi2, main.block_chi2, n_data=n_data, k_params=len(main.sampled_parameters), source="runs/E1B")
    return rows


def _criterion_row(chi2: float, blocks: dict[str, float], *, n_data: int, k_params: int, source: str) -> dict[str, Any]:
    dof = n_data - int(k_params)
    return {
        "source": source,
        "k_params": int(k_params),
        "n_data": int(n_data),
        "dof": int(dof),
        "chi2": float(chi2),
        "chi2_dof": float(chi2 / dof),
        "block_chi2": {key: float(value) for key, value in blocks.items()},
        "AIC": float(chi2 + 2 * k_params),
        "BIC": float(chi2 + k_params * np.log(n_data)),
    }


def _gate_table(baseline: dict[str, Any], oos: dict[str, Any]) -> dict[str, Any]:
    lcdm = baseline["lcdm"]
    w0wa = baseline["w0wa"]
    sbt = baseline["sbt"]
    improves_sn = sbt["block_chi2"]["SN"] < lcdm["block_chi2"]["SN"]
    improves_bao = sbt["block_chi2"]["BAO"] < lcdm["block_chi2"]["BAO"]
    oos_worse_ratio = oos["sbt_to_w0wa_chi2_ratio"]
    return {
        "G-E1-SBT-IMPROVE": {
            "pass": bool(sbt["chi2_dof"] <= 0.99 * w0wa["chi2_dof"]),
            "sbt_chi2_dof": sbt["chi2_dof"],
            "w0wa_chi2_dof": w0wa["chi2_dof"],
            "delta_chi2_sbt_minus_w0wa": float(sbt["chi2"] - w0wa["chi2"]),
        },
        "G-E1-SBT-COHERENCE": {
            "pass": bool(improves_sn and improves_bao),
            "sbt_improves_sn_vs_lcdm": bool(improves_sn),
            "sbt_improves_bao_vs_lcdm": bool(improves_bao),
        },
        "G-E1-SBT-OOS-SN": {
            "pass": bool(oos_worse_ratio <= 1.15),
            "sbt_to_w0wa_chi2_ratio": float(oos_worse_ratio),
            "sbt_to_w0wa_rms_ratio": float(oos["sbt_to_w0wa_rms_ratio"]),
        },
    }


def _fit_payload(result: FitResult) -> dict[str, Any]:
    payload = {
        "model": result.model,
        "sampled_parameters": result.sampled_parameters,
        "bestfit": result.bestfit,
        "posterior": result.posterior,
        "block_chi2": result.block_chi2,
        "chi2": result.chi2,
        "logZ": result.logz,
        "logZ_err": result.logz_err,
        "neff": result.neff,
        "ncall": result.ncall,
        "niter": result.niter,
        "wall_clock_seconds": result.wall_clock_seconds,
        "chain_file": str(result.chain_path),
    }
    if result.model == "sbt":
        payload["kernel_amplitudes"] = _kernel_amplitudes(result.bestfit)
    return payload


def _kernel_amplitudes(point: dict[str, float]) -> dict[str, float]:
    sn = load_pantheon_plus()
    bao = load_desi_dr2_bao()
    z_sn = np.asarray(sn.bins["z_cmb"], dtype=float)
    _, k_l = corrected_luminosity_distance(
        z=z_sn,
        omega_b=point["omega_b"],
        omega_cdm=point["omega_cdm"],
        H0=point["H0"],
        parameters=point,
    )
    _, bao_terms = corrected_bao_observables(
        z=np.asarray(bao.bins["z"], dtype=float),
        observables=list(bao.bins["observable"]),
        omega_b=point["omega_b"],
        omega_cdm=point["omega_cdm"],
        H0=point["H0"],
        parameters=point,
    )
    return {
        "K_L_max_abs_mpc": float(np.max(np.abs(k_l))),
        "K_L_rms_mpc": float(np.sqrt(np.mean(k_l * k_l))),
        "K_M_max_abs_ratio": float(np.max(np.abs(bao_terms["K_M"]))),
        "K_H_max_abs_ratio": float(np.max(np.abs(bao_terms["K_H"]))),
    }


def _model_parameters(model: str) -> tuple[list[str], dict[str, float]]:
    key = model.lower()
    if key == "sbt":
        return ["omega_b", "omega_cdm", "H0", "a0", "a1", "a2", "sn_M"], {"w0_fld": -1.0, "wa_fld": 0.0}
    if key == "lcdm":
        return ["omega_b", "omega_cdm", "H0", "sn_M"], {"w0_fld": -1.0, "wa_fld": 0.0}
    if key == "w0wa":
        return ["omega_b", "omega_cdm", "H0", "w0_fld", "wa_fld", "sn_M"], {}
    raise ValueError(f"unsupported model: {model}")


def _uniform_transform(prior: dict[str, float]) -> Any:
    lower = float(prior["min"])
    width = float(prior["max"]) - lower
    return _UniformTransform(lower, width)


class _UniformTransform:
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
    def __init__(self, likelihood: GeometryLikelihood, names: tuple[str, ...], fixed: dict[str, float]) -> None:
        self.likelihood = likelihood
        self.names = list(names)
        self.fixed = dict(fixed)

    def __call__(self, theta: np.ndarray) -> float:
        return self.likelihood(theta, self.names, self.fixed)


def _posterior_summary(names: list[str], samples: np.ndarray, weights: np.ndarray) -> dict[str, dict[str, float]]:
    output: dict[str, dict[str, float]] = {}
    for index, name in enumerate(names):
        values = samples[:, index]
        mean = float(np.sum(weights * values))
        variance = float(np.sum(weights * (values - mean) ** 2))
        output[name] = {"mean": mean, "sigma": float(np.sqrt(max(variance, 0.0)))}
    return output


def _write_equal_weight_chain(
    path: Path,
    names: list[str],
    fixed: dict[str, float],
    samples: np.ndarray,
    logl: np.ndarray,
    weights: np.ndarray,
    rng: np.random.Generator,
    *,
    max_samples: int,
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    n_equal = min(int(max_samples), max(1000, samples.shape[0]))
    indices = rng.choice(samples.shape[0], size=n_equal, replace=True, p=weights)
    columns = ["weight", "minuslogpost", *names, "Omega_m", "chi2"]
    lines = ["# " + " ".join(columns)]
    for index in indices:
        point = {**fixed, **{name: float(value) for name, value in zip(names, samples[index])}}
        omega_m = omega_m_approx(omega_b=point["omega_b"], omega_cdm=point["omega_cdm"], H0=point["H0"])
        chi2 = float(-2.0 * logl[index])
        row = [1.0, float(-logl[index]), *[point[name] for name in names], omega_m, chi2]
        lines.append(" ".join(f"{item:.10e}" for item in row))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _n_data() -> int:
    return 3 + load_desi_dr2_bao().data_vector.size + load_pantheon_plus().data_vector.size


def _write_manifest(config_path: Path, outdir: Path, summary: dict[str, Any]) -> None:
    artifacts = {
        str(path.relative_to(outdir)): sha256_file(path)
        for path in sorted(outdir.rglob("*"))
        if path.is_file() and path.name != "manifest.json"
    }
    manifest = {
        "schema_version": 1,
        "experiment": "E1B_sbt_geometry",
        "run_id": summary["run_id"],
        "sampler": "dynesty",
        "package_version": sbt_cosmo.__version__,
        "config_sha256": sha256_file(config_path),
        "artifact_checksums_sha256": artifacts,
        "terminal_state": summary["terminal_state"],
    }
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("configs/experiments/E1B_compressed.yaml"))
    parser.add_argument("--outdir", type=Path, default=Path("runs/E1B/E1B_C3_sbt"))
    parser.add_argument("--run-id", default="E1B_C3_sbt")
    parser.add_argument("--nlive", type=int)
    parser.add_argument("--dlogz", type=float)
    parser.add_argument("--pool", type=int, default=1)
    parser.add_argument("--oos-nlive", type=int, default=300)
    parser.add_argument("--oos-dlogz", type=float, default=0.2)
    parser.add_argument("--skip-oos", action="store_true")
    args = parser.parse_args()

    config = yaml.safe_load(args.config.read_text(encoding="utf-8"))
    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "chains").mkdir(exist_ok=True)
    profile = profile_likelihood()
    main_result = run_fit(
        config=config,
        model="sbt",
        outdir=outdir,
        run_label="C3_sbt_dyn",
        nlive=int(args.nlive or config["dynesty"]["nlive"]),
        dlogz=float(args.dlogz or config["dynesty"]["dlogz"]),
        pool_size=int(args.pool),
        seed=int(config["seeds"]["dynesty"]),
    )
    if args.skip_oos:
        oos = {"skipped": True}
    else:
        oos = run_oos(
            config=config,
            outdir=outdir,
            nlive=int(args.oos_nlive),
            dlogz=float(args.oos_dlogz),
            pool_size=int(args.pool),
        )
    summary = build_summary(config_path=args.config, outdir=outdir, run_id=args.run_id, main=main_result, oos=oos, profile=profile)
    write_coherence_csv(ROOT / "results" / "xi_cosmo_coherence.csv", summary)
    print(json.dumps({"summary": str(outdir / "summary.json"), "terminal_state": summary["terminal_state"], "chi2": summary["fit"]["chi2"]}, indent=2))


if __name__ == "__main__":
    main()
