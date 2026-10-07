#!/usr/bin/env python3
"""Run the DE rewrite-vs-Lambda audit battery on existing E1 geometry data."""

from __future__ import annotations

import csv
import json
import math
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
os.environ.setdefault("MPLCONFIGDIR", str(ROOT / ".cache" / "matplotlib"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy import linalg, optimize

from sbt_cosmo.audits.calibration import RANK_METADATA_FIELDS, rank_calibration
from sbt_cosmo.io.datasets import ProbeData, load_desi_dr2_bao, load_pantheon_plus
from sbt_cosmo.likelihoods.cmb_compressed import load_planck2018_compressed
from sbt_cosmo.theory import background_compressed as bg


RESULTS = ROOT / "results" / "DE_audit"
SEED = 20260612
SN_SPLIT_Z = 0.35
NULL_REALIZATIONS = 20
INJECT_REALIZATIONS = 20
INJECTION_AMPLITUDES = (0.70, 1.40, 2.80, 5.60)


def cap_threads() -> None:
    for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
        os.environ.setdefault(key, "1")


@dataclass(frozen=True)
class GaussianBlock:
    name: str
    data: np.ndarray
    covariance: np.ndarray
    inv_covariance: np.ndarray
    bins: dict[str, object]
    one_vector: np.ndarray | None = None


@dataclass(frozen=True)
class FitResult:
    model: str
    split: str
    params: dict[str, float]
    chi2: float
    n_data: int
    k: int
    success: bool
    message: str
    m_sigma: float | None = None
    diagnostics: dict[str, float | bool | str] | None = None


def _inverse(covariance: np.ndarray) -> np.ndarray:
    return linalg.cho_solve(linalg.cho_factor(covariance, lower=True, check_finite=False), np.eye(covariance.shape[0]))


def load_blocks() -> tuple[GaussianBlock, GaussianBlock, GaussianBlock]:
    bao = load_desi_dr2_bao()
    sn = load_pantheon_plus()
    planck = load_planck2018_compressed()
    return (
        GaussianBlock(
            name="planck2018_compressed",
            data=planck["mean_array"],
            covariance=planck["covariance_array"],
            inv_covariance=planck["inv_covariance_array"],
            bins={"parameters": planck["vector"]["parameters"]},
        ),
        _probe_block("desi_dr2_bao", bao),
        _probe_block("pantheon_plus", sn, include_intercept=True),
    )


def _probe_block(name: str, probe: ProbeData, *, include_intercept: bool = False) -> GaussianBlock:
    inv = _inverse(probe.covariance)
    return GaussianBlock(
        name=name,
        data=np.asarray(probe.data_vector, dtype=float),
        covariance=np.asarray(probe.covariance, dtype=float),
        inv_covariance=inv,
        bins=probe.bins,
        one_vector=np.ones(probe.data_vector.shape[0], dtype=float) if include_intercept else None,
    )


def slice_sn(block: GaussianBlock, mask: np.ndarray, name: str) -> GaussianBlock:
    cov = block.covariance[np.ix_(mask, mask)]
    bins = {}
    for key, value in block.bins.items():
        if isinstance(value, list) and len(value) == len(mask):
            bins[key] = np.asarray(value, dtype=object)[mask].tolist()
        else:
            bins[key] = value
    return GaussianBlock(
        name=name,
        data=block.data[mask],
        covariance=cov,
        inv_covariance=_inverse(cov),
        bins=bins,
        one_vector=np.ones(int(mask.sum()), dtype=float),
    )


def compress_sn_for_audit(block: GaussianBlock) -> GaussianBlock:
    """Compress Pantheon+ to fixed redshift-bin summaries for DEA staging."""
    z = np.asarray(block.bins["z_cmb"], dtype=float)
    edges = np.asarray([0.01, 0.10, 0.20, 0.35, 0.60, 1.00, 2.50], dtype=float)
    rows = []
    z_eff = []
    diag = np.diag(block.covariance)
    inv_diag = np.where(diag > 0.0, 1.0 / diag, 0.0)
    for lo, hi in zip(edges[:-1], edges[1:]):
        mask = (z >= lo) & (z < hi)
        if not np.any(mask):
            continue
        w = np.zeros_like(z)
        local = inv_diag[mask]
        if float(np.sum(local)) <= 0.0:
            local = np.ones(int(mask.sum()), dtype=float)
        local = local / float(np.sum(local))
        w[mask] = local
        rows.append(w)
        z_eff.append(float(np.sum(local * z[mask])))
    W = np.vstack(rows)
    data = W @ block.data
    covariance = W @ block.covariance @ W.T
    return GaussianBlock(
        name="pantheon_plus_binned_audit",
        data=np.asarray(data, dtype=float),
        covariance=np.asarray(covariance, dtype=float),
        inv_covariance=_inverse(covariance),
        bins={"z_cmb": z_eff, "z": z_eff, "compression": "six_redshift_bins"},
        one_vector=np.ones(len(z_eff), dtype=float),
    )


def omega_values(omega_b: float, omega_cdm: float, H0: float) -> tuple[float, float, float, float]:
    h = H0 / 100.0
    omega_m_phys = omega_b + omega_cdm + bg.OMEGA_NU_MASSIVE_H2
    omega_m = omega_m_phys / (h * h)
    omega_r = bg.OMEGA_R_H2 / (h * h)
    return h, omega_m_phys, omega_m, omega_r


def e2_rewrite(z: np.ndarray, omega_b: float, omega_cdm: float, H0: float, A: float, m: float) -> np.ndarray:
    _, _, omega_m, omega_r = omega_values(omega_b, omega_cdm, H0)
    z = np.asarray(z, dtype=float)
    e2 = omega_m * (1.0 + z) ** 3 + omega_r * (1.0 + z) ** 4 + A * (1.0 + z) ** m
    if np.any(e2 <= 0.0) or not np.all(np.isfinite(e2)):
        raise ValueError("invalid rewrite expansion")
    return e2


def comoving_rewrite(z: Iterable[float], omega_b: float, omega_cdm: float, H0: float, A: float, m: float) -> np.ndarray:
    z_eval = np.asarray(tuple(float(v) for v in z), dtype=float)
    if z_eval.size == 0:
        return np.asarray([], dtype=float)
    if float(np.max(z_eval)) > 20.0:
        from scipy import integrate

        def integrand(z: float) -> float:
            return 1.0 / (H0 * math.sqrt(float(e2_rewrite(np.asarray([z]), omega_b, omega_cdm, H0, A, m)[0])))

        values = []
        for z_value in z_eval:
            value, _ = integrate.quad(integrand, 0.0, float(z_value), epsabs=1.0e-7, epsrel=1.0e-7, limit=300)
            values.append(bg.LIGHT_SPEED_KM_S * value)
        return np.asarray(values, dtype=float)
    zmax = max(float(np.max(z_eval)), 1.0e-8)
    # DEA is an audit battery, not a precision-distance backend. A bounded
    # cumulative grid keeps the synthetic calibration tractable while retaining
    # sub-percent smooth-distance accuracy over the Pantheon redshift range.
    grid_n = min(2048, max(512, 4 * z_eval.size))
    grid = np.unique(np.concatenate(([0.0], z_eval, np.linspace(0.0, zmax, grid_n))))
    inv_h = 1.0 / (H0 * np.sqrt(e2_rewrite(grid, omega_b, omega_cdm, H0, A, m)))
    integ = np.zeros_like(grid)
    integ[1:] = np.cumsum(0.5 * (inv_h[1:] + inv_h[:-1]) * np.diff(grid))
    return bg.LIGHT_SPEED_KM_S * np.interp(z_eval, grid, integ)


def sound_horizon_rewrite(
    z_start: float, omega_b: float, omega_cdm: float, H0: float, A: float, m: float
) -> float:
    h, _, _, _ = omega_values(omega_b, omega_cdm, H0)

    def integrand(z: float) -> float:
        r_b = 31500.0 * omega_b * (bg.T_CMB_K / 2.7) ** (-4) / (1.0 + z)
        cs = bg.LIGHT_SPEED_KM_S / math.sqrt(3.0 * (1.0 + r_b))
        return cs / (H0 * math.sqrt(float(e2_rewrite(np.asarray([z]), omega_b, omega_cdm, H0, A, m)[0])))

    from scipy import integrate

    value, _ = integrate.quad(integrand, z_start, np.inf, epsabs=1.0e-5, epsrel=1.0e-5, limit=200)
    return float(value)


def rewrite_observables(
    z: Iterable[float], omega_b: float, omega_cdm: float, H0: float, A: float, m: float
) -> dict[str, np.ndarray | float]:
    z_array = np.asarray(tuple(float(v) for v in z), dtype=float)
    h, omega_m_phys, omega_m, _ = omega_values(omega_b, omega_cdm, H0)
    if omega_m <= 0.0 or omega_m >= 1.5 or A < 0.0:
        raise ValueError("invalid rewrite density")
    r_drag = bg.R_DRAG_CLASS_CORRECTION * 55.154 * np.exp(-72.3 * (bg.OMEGA_NU_MASSIVE_H2 + 0.0006) ** 2) / (
        omega_m_phys**0.25351 * omega_b**0.12807
    )
    if z_array.size:
        distances = comoving_rewrite(z_array, omega_b, omega_cdm, H0, A, m)
        d_m = distances
        z_star = math.nan
        rs_rec = math.nan
        shift_r = math.nan
        acoustic_l = math.nan
    else:
        z_star = bg.Z_STAR_CLASS_CORRECTION * bg._hu_sugiyama_z_star(omega_b=omega_b, omega_m_phys=omega_m_phys)
        rs_rec = bg.RS_REC_CLASS_CORRECTION * _sound_horizon_numeric(z_star, omega_b, omega_cdm, H0, A, m)
        distances = comoving_rewrite([z_star], omega_b, omega_cdm, H0, A, m)
        d_m = np.asarray([], dtype=float)
        d_star = float(distances[-1])
        shift_r = float(bg.SHIFT_R_CLASS_CORRECTION * math.sqrt(omega_m) * (H0 / bg.LIGHT_SPEED_KM_S) * d_star)
        acoustic_l = float(math.pi * d_star / rs_rec)
    e = np.sqrt(e2_rewrite(z_array, omega_b, omega_cdm, H0, A, m)) if z_array.size else np.asarray([])
    h_z = H0 * e
    d_h = bg.LIGHT_SPEED_KM_S / h_z if z_array.size else np.asarray([])
    d_v = np.cbrt(np.maximum(z_array * d_m * d_m * d_h, 0.0)) if z_array.size else np.asarray([])
    d_l = (1.0 + z_array) * d_m
    mu = np.full_like(d_l, -np.inf)
    mask = d_l > 0.0
    mu[mask] = 5.0 * np.log10(d_l[mask]) + 25.0
    return {
        "D_M": d_m,
        "D_H": d_h,
        "D_V": d_v,
        "D_L": d_l,
        "mu": mu,
        "r_drag": float(r_drag),
        "R": shift_r,
        "l_A": acoustic_l,
        "omega_m": float(omega_m),
        "z_star": float(z_star),
        "rs_rec": float(rs_rec),
    }


def _sound_horizon_numeric(z_start: float, omega_b: float, omega_cdm: float, H0: float, A: float, m: float) -> float:
    from scipy import integrate

    def integrand(z: float) -> float:
        r_b = 31500.0 * omega_b * (bg.T_CMB_K / 2.7) ** (-4) / (1.0 + z)
        cs = bg.LIGHT_SPEED_KM_S / math.sqrt(3.0 * (1.0 + r_b))
        return cs / (H0 * math.sqrt(float(e2_rewrite(np.asarray([z]), omega_b, omega_cdm, H0, A, m)[0])))

    value, _ = integrate.quad(integrand, z_start, np.inf, epsabs=1.0e-5, epsrel=1.0e-5, limit=200)
    return float(value)


def model_vector(model: str, params: dict[str, float], block: GaussianBlock) -> np.ndarray:
    if block.name == "planck2018_compressed":
        if model == "rewrite_power":
            obs = rewrite_observables([], **_rewrite_args(params))
            return np.asarray([obs["R"], obs["l_A"], 100.0 * params["omega_b"]], dtype=float)
        w0, wa = _w_params(model, params)
        back = bg.evaluate_background(
            omega_b=params["omega_b"], omega_cdm=params["omega_cdm"], H0=params["H0"], w0_fld=w0, wa_fld=wa
        )
        return np.asarray([back.R, back.l_A, 100.0 * params["omega_b"]], dtype=float)

    if block.name.startswith("desi_dr2_bao"):
        z = np.asarray(block.bins["z"], dtype=float)
        obs = list(block.bins["observable"])
        if model == "rewrite_power":
            back = rewrite_observables(z, **_rewrite_args(params))
            r_drag = float(back["r_drag"])
            values = {"DM_over_rs": np.asarray(back["D_M"]) / r_drag, "DH_over_rs": np.asarray(back["D_H"]) / r_drag, "DV_over_rs": np.asarray(back["D_V"]) / r_drag}
        else:
            w0, wa = _w_params(model, params)
            back = bg.evaluate_background(
                omega_b=params["omega_b"], omega_cdm=params["omega_cdm"], H0=params["H0"], w0_fld=w0, wa_fld=wa, z=z
            )
            values = {"DM_over_rs": back.D_M / back.r_drag, "DH_over_rs": back.D_H / back.r_drag, "DV_over_rs": back.D_V / back.r_drag}
        return np.asarray([values[name][i] for i, name in enumerate(obs)], dtype=float)

    if block.name.startswith("pantheon_plus"):
        z = np.asarray(block.bins.get("z_cmb", block.bins.get("z")), dtype=float)
        if model == "rewrite_power":
            return np.asarray(rewrite_observables(z, **_rewrite_args(params))["mu"], dtype=float)
        w0, wa = _w_params(model, params)
        return bg.evaluate_background(
            omega_b=params["omega_b"], omega_cdm=params["omega_cdm"], H0=params["H0"], w0_fld=w0, wa_fld=wa, z=z
        ).mu
    raise ValueError(f"unsupported block {block.name}")


def _w_params(model: str, params: dict[str, float]) -> tuple[float, float]:
    if model == "w0wa":
        return params["w0_fld"], params["wa_fld"]
    return -1.0, 0.0


def _rewrite_args(params: dict[str, float]) -> dict[str, float]:
    return {
        "omega_b": params["omega_b"],
        "omega_cdm": params["omega_cdm"],
        "H0": params["H0"],
        "A": params["A"],
        "m": params["m"],
    }


def block_chi2(model: str, params: dict[str, float], block: GaussianBlock) -> tuple[float, dict[str, float]]:
    pred = model_vector(model, params, block)
    residual = pred - block.data
    extra: dict[str, float] = {}
    if block.one_vector is not None:
        one = block.one_vector
        numerator = float(one @ block.inv_covariance @ residual)
        denominator = float(one @ block.inv_covariance @ one)
        intercept = -numerator / denominator
        residual = residual + intercept * one
        extra["sn_M_profiled"] = float(intercept)
    chi2 = float(residual @ block.inv_covariance @ residual)
    if not np.isfinite(chi2):
        raise ValueError("non-finite chi2")
    return chi2, extra


def total_chi2(model: str, x: np.ndarray, names: list[str], blocks: list[GaussianBlock]) -> tuple[float, dict[str, float]]:
    params = dict(zip(names, (float(v) for v in x)))
    total = 0.0
    extras: dict[str, float] = {}
    for block in blocks:
        chi2, extra = block_chi2(model, params, block)
        total += chi2
        extras.update(extra)
    return total, extras


def fit_model(model: str, split: str, blocks: list[GaussianBlock], start: dict[str, float] | None = None) -> FitResult:
    names, bounds, initial = model_spec(model)
    if start:
        for i, name in enumerate(names):
            if name in start:
                lo, hi = bounds[i]
                initial[i] = min(max(float(start[name]), lo + 1.0e-9), hi - 1.0e-9)

    def objective(x: np.ndarray) -> float:
        try:
            return total_chi2(model, x, names, blocks)[0]
        except Exception:
            return 1.0e100

    starts = [np.asarray(initial, dtype=float)]
    if model == "rewrite_power":
        for m0 in (-1.0, 0.0, 1.0):
            candidate = np.asarray(initial, dtype=float)
            candidate[names.index("m")] = m0
            starts.append(candidate)
    if model == "w0wa":
        for w0, wa in [(-1.0, 0.0), (-0.8, -0.7), (-0.5, -1.5)]:
            candidate = np.asarray(initial, dtype=float)
            candidate[names.index("w0_fld")] = w0
            candidate[names.index("wa_fld")] = wa
            starts.append(candidate)

    best = None
    for x0 in starts:
        result = optimize.minimize(objective, x0, method="Nelder-Mead", options={"maxiter": 1800, "xatol": 1.0e-5, "fatol": 1.0e-4})
        clipped = np.asarray([min(max(v, bounds[i][0]), bounds[i][1]) for i, v in enumerate(result.x)], dtype=float)
        result2 = optimize.minimize(objective, clipped, method="L-BFGS-B", bounds=bounds, options={"maxiter": 1200, "ftol": 1.0e-8})
        if best is None or float(result2.fun) < float(best.fun):
            best = result2
    assert best is not None
    chi2, extras = total_chi2(model, np.asarray(best.x, dtype=float), names, blocks)
    params = dict(zip(names, (float(v) for v in best.x)))
    params.update(extras)
    m_sigma = estimate_m_sigma(model, np.asarray(best.x, dtype=float), names, blocks) if model == "rewrite_power" else None
    return FitResult(
        model=model,
        split=split,
        params=params,
        chi2=float(chi2),
        n_data=sum(block.data.size for block in blocks),
        k=len(names) + (1 if any(block.one_vector is not None for block in blocks) else 0),
        success=bool(best.success or np.isfinite(chi2)),
        message=str(best.message),
        m_sigma=m_sigma,
    )


def model_spec(model: str) -> tuple[list[str], list[tuple[float, float]], list[float]]:
    if model == "lcdm":
        return ["omega_b", "omega_cdm", "H0"], [(0.018, 0.027), (0.08, 0.17), (55.0, 80.0)], [0.0225, 0.118, 68.3]
    if model == "w0wa":
        return (
            ["omega_b", "omega_cdm", "H0", "w0_fld", "wa_fld"],
            [(0.018, 0.027), (0.08, 0.17), (55.0, 80.0), (-2.8, 0.2), (-3.0, 1.5)],
            [0.0224, 0.119, 67.0, -0.8, -0.7],
        )
    if model == "rewrite_power":
        return (
            ["omega_b", "omega_cdm", "H0", "A", "m"],
            [(0.018, 0.027), (0.08, 0.17), (55.0, 80.0), (1.0e-4, 2.5), (-6.0, 3.0)],
            [0.0225, 0.118, 68.3, 0.70, 0.0],
        )
    raise ValueError(model)


def estimate_m_sigma(model: str, x: np.ndarray, names: list[str], blocks: list[GaussianBlock]) -> float | None:
    if model != "rewrite_power" or "m" not in names:
        return None
    idx = names.index("m")
    x0 = x.copy()
    h = 0.03

    def obj_at(m_value: float) -> float:
        xp = x0.copy()
        xp[idx] = m_value
        return total_chi2(model, xp, names, blocks)[0]

    try:
        f0 = obj_at(x0[idx])
        fp = obj_at(x0[idx] + h)
        fm = obj_at(x0[idx] - h)
        curvature = (fp - 2.0 * f0 + fm) / (h * h)
        if curvature <= 0 or not np.isfinite(curvature):
            return None
        return float(math.sqrt(2.0 / curvature))
    except Exception:
        return None


def aic(chi2: float, k: int) -> float:
    return float(chi2 + 2 * k)


def bic(chi2: float, k: int, n: int) -> float:
    return float(chi2 + k * math.log(max(n, 1)))


def omega_m_from_params(params: dict[str, float]) -> float:
    return omega_values(params["omega_b"], params["omega_cdm"], params["H0"])[2]


def write_csv(path: Path, rows: list[dict[str, object]], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def fit_main_models(planck: GaussianBlock, bao: GaussianBlock, sn: GaussianBlock, *, full_e1_n_data: int) -> dict[str, FitResult]:
    blocks = [planck, bao, sn]
    results: dict[str, FitResult] = {
        "lcdm": fit_from_e1_summary("lcdm", full_e1_n_data),
        "w0wa": fit_from_e1_summary("w0wa", full_e1_n_data),
    }
    results["rewrite_power"] = fit_rewrite_same_likelihood_dynesty(blocks)
    return results


def fit_rewrite_same_likelihood_dynesty(blocks: list[GaussianBlock]) -> FitResult:
    """Fit rewrite_power on the same C3 compressed likelihood via dynesty."""
    import dynesty
    from dynesty import utils as dyfunc

    names, bounds, _ = model_spec("rewrite_power")
    bounds_arr = np.asarray(bounds, dtype=float)

    def prior_transform(unit: np.ndarray) -> np.ndarray:
        return bounds_arr[:, 0] + unit * (bounds_arr[:, 1] - bounds_arr[:, 0])

    def loglike(x: np.ndarray) -> float:
        try:
            chi2, _ = total_chi2("rewrite_power", np.asarray(x, dtype=float), names, blocks)
        except Exception:
            return -1.0e100
        return -0.5 * chi2 if np.isfinite(chi2) else -1.0e100

    nlive = int(os.environ.get("DEA_REWRITE_NLIVE", "100"))
    dlogz = float(os.environ.get("DEA_REWRITE_DLOGZ", "1.0"))
    maxiter = int(os.environ.get("DEA_REWRITE_MAXITER", "8000"))
    sampler = dynesty.NestedSampler(
        loglike,
        prior_transform,
        ndim=len(names),
        nlive=nlive,
        bound="multi",
        sample="rwalk",
        rstate=np.random.default_rng(SEED + 91),
    )
    sampler.run_nested(dlogz=dlogz, maxiter=maxiter, print_progress=False)
    res = sampler.results
    weights = np.exp(res.logwt - res.logz[-1])
    equal = dyfunc.resample_equal(res.samples, weights, rstate=np.random.default_rng(SEED + 92))
    logl = np.asarray(res.logl, dtype=float)
    best_idx = int(np.argmax(logl))
    best_x = np.asarray(res.samples[best_idx], dtype=float)
    chi2, extras = total_chi2("rewrite_power", best_x, names, blocks)
    params = dict(zip(names, (float(v) for v in best_x)))
    params.update(extras)
    m_values = equal[:, names.index("m")]
    a_values = equal[:, names.index("A")]
    m_q16, m_med, m_q84 = np.quantile(m_values, [0.16, 0.5, 0.84])
    a_q16, a_med, a_q84 = np.quantile(a_values, [0.16, 0.5, 0.84])
    diagnostics: dict[str, float | bool | str] = {
        "sampler": "dynesty",
        "nlive": nlive,
        "dlogz_target": dlogz,
        "maxiter": maxiter,
        "logz": float(res.logz[-1]),
        "logz_err": float(res.logzerr[-1]),
        "ncall": int(np.sum(res.ncall)),
        "m_median": float(m_med),
        "m_q16": float(m_q16),
        "m_q84": float(m_q84),
        "A_median": float(a_med),
        "A_q16": float(a_q16),
        "A_q84": float(a_q84),
        "m_lower_hit": bool(abs(params["m"] - bounds_arr[names.index("m"), 0]) < 1.0e-3),
        "m_upper_hit": bool(abs(params["m"] - bounds_arr[names.index("m"), 1]) < 1.0e-3),
        "A_lower_hit": bool(abs(params["A"] - bounds_arr[names.index("A"), 0]) < 1.0e-5),
        "A_upper_hit": bool(abs(params["A"] - bounds_arr[names.index("A"), 1]) < 1.0e-3),
    }
    (RESULTS / "rewrite_dynesty_summary.json").write_text(
        json.dumps({"params_best": params, "diagnostics": diagnostics, "chi2": chi2}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return FitResult(
        model="rewrite_power",
        split="joint",
        params=params,
        chi2=float(chi2),
        n_data=sum(block.data.size for block in blocks),
        k=len(names) + 1,
        success=True,
        message="dynesty same-likelihood rewrite fit",
        m_sigma=float(0.5 * (m_q84 - m_q16)),
        diagnostics=diagnostics,
    )


def fit_from_e1_summary(model: str, n_data: int) -> FitResult:
    path = ROOT / "runs" / "E1" / f"E1C_C3_{model}_dyn" / "summary.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    best = payload["minimize"]["bestfit"]
    params = {
        "omega_b": float(best["omega_b"]),
        "omega_cdm": float(best["omega_cdm"]),
        "H0": float(best["H0"]),
        "sn_M_profiled": float(best.get("sn_M", math.nan)),
    }
    if model == "w0wa":
        params.update({"w0_fld": float(best["w0_fld"]), "wa_fld": float(best["wa_fld"])})
    return FitResult(
        model=model,
        split="joint",
        params=params,
        chi2=float(payload["minimize"]["chi2"]),
        n_data=n_data,
        k=4 if model == "lcdm" else 6,
        success=True,
        message=f"read from {path}",
    )


def model_table_rows(fits: dict[str, FitResult]) -> list[dict[str, object]]:
    rows = []
    base_aic = aic(fits["lcdm"].chi2, fits["lcdm"].k)
    base_bic = bic(fits["lcdm"].chi2, fits["lcdm"].k, fits["lcdm"].n_data)
    for name, fit in fits.items():
        same_likelihood = name in ("lcdm", "w0wa", "rewrite_power")
        row = {
            "model": name,
            "split": fit.split,
            "chi2": fit.chi2,
            "n_data": fit.n_data,
            "k": fit.k,
            "AIC": aic(fit.chi2, fit.k),
            "BIC": bic(fit.chi2, fit.k, fit.n_data),
            "delta_AIC_vs_lcdm": aic(fit.chi2, fit.k) - base_aic if same_likelihood else math.nan,
            "delta_BIC_vs_lcdm": bic(fit.chi2, fit.k, fit.n_data) - base_bic if same_likelihood else math.nan,
            "omega_m": omega_m_from_params(fit.params),
            "H0": fit.params.get("H0", math.nan),
            "w0_fld": fit.params.get("w0_fld", math.nan),
            "wa_fld": fit.params.get("wa_fld", math.nan),
            "A": fit.params.get("A", math.nan),
            "m": fit.params.get("m", math.nan),
            "m_sigma": fit.m_sigma if fit.m_sigma is not None else math.nan,
            "m_median": (fit.diagnostics or {}).get("m_median", math.nan),
            "m_q16": (fit.diagnostics or {}).get("m_q16", math.nan),
            "m_q84": (fit.diagnostics or {}).get("m_q84", math.nan),
            "A_median": (fit.diagnostics or {}).get("A_median", math.nan),
            "A_q16": (fit.diagnostics or {}).get("A_q16", math.nan),
            "A_q84": (fit.diagnostics or {}).get("A_q84", math.nan),
            "A_lower_hit": (fit.diagnostics or {}).get("A_lower_hit", False),
            "A_upper_hit": (fit.diagnostics or {}).get("A_upper_hit", False),
            "m_lower_hit": (fit.diagnostics or {}).get("m_lower_hit", False),
            "m_upper_hit": (fit.diagnostics or {}).get("m_upper_hit", False),
            "sn_M_profiled": fit.params.get("sn_M_profiled", math.nan),
            "fit_mode": "E1C_dynesty_summary" if name in ("lcdm", "w0wa") else "same_likelihood_dynesty",
            "same_likelihood_as_lcdm": same_likelihood,
            "success": fit.success,
        }
        rows.append(row)
    return rows


def b1b_chart(fit: FitResult) -> dict[str, object]:
    params = fit.params
    z = np.linspace(0.0, 2.5, 251)
    w = params["w0_fld"] + params["wa_fld"] * z / (1.0 + z)
    _, _, omega_m, omega_r = omega_values(params["omega_b"], params["omega_cdm"], params["H0"])
    e2_w = bg._e_z(z, omega_m=omega_m, omega_r=omega_r, omega_de=1.0 - omega_m - omega_r, w0_fld=params["w0_fld"], wa_fld=params["wa_fld"]) ** 2
    delta_h = e2_w - omega_m * (1.0 + z) ** 3 - omega_r * (1.0 + z) ** 4
    signs = np.sign(w + 1.0)
    crossing_z = math.nan
    for i in range(len(z) - 1):
        if signs[i] == 0:
            crossing_z = float(z[i])
            break
        if signs[i] * signs[i + 1] < 0:
            frac = abs(w[i] + 1.0) / (abs(w[i] + 1.0) + abs(w[i + 1] + 1.0))
            crossing_z = float(z[i] + frac * (z[i + 1] - z[i]))
            break
    rows = [
        {"z": float(zi), "w_fluid": float(wi), "Delta_H_additive": float(di), "finite": bool(np.isfinite(di))}
        for zi, wi, di in zip(z, w, delta_h)
    ]
    write_csv(RESULTS / "B1b_chart_comparison.csv", rows, ["z", "w_fluid", "Delta_H_additive", "finite"])
    fig, ax1 = plt.subplots(figsize=(7, 4.2))
    ax1.plot(z, w, label="w(z) fluid chart", color="#005f73")
    ax1.axhline(-1.0, color="black", lw=0.8, ls="--")
    ax1.set_xlabel("z")
    ax1.set_ylabel("w(z)")
    ax2 = ax1.twinx()
    ax2.plot(z, delta_h, label="Delta_H additive chart", color="#9b2226")
    ax2.set_ylabel("Delta_H(z)")
    if np.isfinite(crossing_z):
        ax1.axvline(crossing_z, color="#ca6702", lw=0.8, ls=":")
    fig.tight_layout()
    fig.savefig(RESULTS / "B1b_chart_comparison.png", dpi=160)
    plt.close(fig)
    jumps = np.abs(np.diff(delta_h))
    return {
        "crossing_z": crossing_z,
        "delta_h_finite": bool(np.all(np.isfinite(delta_h))),
        "delta_h_min": float(np.min(delta_h)),
        "delta_h_max": float(np.max(delta_h)),
        "delta_h_max_grid_jump": float(np.max(jumps)),
    }


def load_frozen_b1b_or_generate(fit: FitResult) -> dict[str, object]:
    verdict_path = RESULTS / "verdict.json"
    chart_csv = RESULTS / "B1b_chart_comparison.csv"
    chart_png = RESULTS / "B1b_chart_comparison.png"
    if verdict_path.exists() and chart_csv.exists() and chart_png.exists():
        try:
            payload = json.loads(verdict_path.read_text(encoding="utf-8"))
            if isinstance(payload.get("b1b"), dict):
                return payload["b1b"]
        except Exception:
            pass
    return b1b_chart(fit)


def make_mock_block(block: GaussianBlock, model: str, params: dict[str, float], rng: np.random.Generator, name: str) -> GaussianBlock:
    pred = model_vector(model, params, block)
    if block.one_vector is not None:
        _, extra = block_chi2(model, params, block)
        pred = pred + extra.get("sn_M_profiled", 0.0)
    draw = rng.multivariate_normal(pred, block.covariance)
    return GaussianBlock(name=name, data=draw, covariance=block.covariance, inv_covariance=block.inv_covariance, bins=block.bins, one_vector=block.one_vector)


def split_blocks(planck: GaussianBlock, bao: GaussianBlock, sn: GaussianBlock) -> dict[str, list[GaussianBlock]]:
    z = np.asarray(sn.bins["z_cmb"], dtype=float)
    low = z < SN_SPLIT_Z
    high = ~low
    return {
        "joint": [bao, sn],
        "bao_only": [bao],
        "sn_only": [sn],
        "sn_low_z": [slice_sn(sn, low, "pantheon_plus_low_z")],
        "sn_high_z": [slice_sn(sn, high, "pantheon_plus_high_z")],
    }


def staging_score(fits: dict[str, FitResult]) -> float:
    joint = fits["joint"]
    joint_m = joint.params["m"]
    joint_sig = joint.m_sigma or 1.0
    scores = []
    for split, fit in fits.items():
        if split == "joint":
            continue
        sig = fit.m_sigma or 1.0
        scores.append(abs(fit.params["m"] - joint_m) / math.sqrt(sig * sig + joint_sig * joint_sig + 0.05**2))
    return float(max(scores)) if scores else 0.0


def fit_rewrite_splits(splits: dict[str, list[GaussianBlock]], start: dict[str, float]) -> dict[str, FitResult]:
    return {name: fit_rewrite_shape_fixed_anchor(name, blocks, start) for name, blocks in splits.items()}


def fit_rewrite_shape_fixed_anchor(split: str, blocks: list[GaussianBlock], anchor: dict[str, float]) -> FitResult:
    """Fit the declared rewrite shape parameters with the C3 physical anchor fixed.

    The B2 staging audit concerns split-to-joint movement in ``(A,m)``. Holding
    ``omega_b, omega_cdm, H0`` fixed to the B1 C3 anchor keeps the synthetic
    calibration from spending almost all runtime on geometry directions that are
    not part of the staging statistic.
    """
    fixed = {
        "omega_b": float(anchor["omega_b"]),
        "omega_cdm": float(anchor["omega_cdm"]),
        "H0": float(anchor["H0"]),
    }

    def objective(y: np.ndarray) -> float:
        params = {**fixed, "A": float(y[0]), "m": float(y[1])}
        try:
            return sum(block_chi2("rewrite_power", params, block)[0] for block in blocks)
        except Exception:
            return 1.0e100

    best = None
    bounds = [(1.0e-4, 8.0), (-6.0, 3.0)]
    for y0 in (np.asarray([anchor.get("A", 0.7), anchor.get("m", 0.0)], dtype=float), np.asarray([0.7, -1.0]), np.asarray([1.4, 1.0])):
        result = optimize.minimize(objective, y0, method="L-BFGS-B", bounds=bounds, options={"maxiter": 500})
        if best is None or float(result.fun) < float(best.fun):
            best = result
    assert best is not None
    params = {**fixed, "A": float(best.x[0]), "m": float(best.x[1])}
    chi2 = float(objective(np.asarray(best.x, dtype=float)))
    m_sigma = estimate_shape_m_sigma(fixed, float(best.x[0]), float(best.x[1]), blocks)
    return FitResult(
        model="rewrite_power",
        split=split,
        params=params,
        chi2=chi2,
        n_data=sum(block.data.size for block in blocks),
        k=2 + (1 if any(block.one_vector is not None for block in blocks) else 0),
        success=bool(best.success or np.isfinite(chi2)),
        message=str(best.message),
        m_sigma=m_sigma,
        diagnostics={
            "A_lower_hit": bool(abs(params["A"] - bounds[0][0]) < 1.0e-5),
            "A_upper_hit": bool(abs(params["A"] - bounds[0][1]) < 1.0e-3),
            "m_lower_hit": bool(abs(params["m"] - bounds[1][0]) < 1.0e-3),
            "m_upper_hit": bool(abs(params["m"] - bounds[1][1]) < 1.0e-3),
            "converged": bool(best.success),
        },
    )


def estimate_shape_m_sigma(fixed: dict[str, float], A: float, m: float, blocks: list[GaussianBlock]) -> float | None:
    h = 0.03

    def obj(m_value: float) -> float:
        params = {**fixed, "A": A, "m": m_value}
        return sum(block_chi2("rewrite_power", params, block)[0] for block in blocks)

    try:
        f0 = obj(m)
        fp = obj(m + h)
        fm = obj(m - h)
        curvature = (fp - 2.0 * f0 + fm) / (h * h)
        if curvature <= 0.0 or not np.isfinite(curvature):
            return None
        return float(math.sqrt(2.0 / curvature))
    except Exception:
        return None


def b2_calibration(planck: GaussianBlock, bao: GaussianBlock, sn: GaussianBlock, base: FitResult) -> tuple[list[dict[str, object]], dict[str, object]]:
    rng = np.random.default_rng(SEED)
    rows: list[dict[str, object]] = []
    base_params = dict(base.params)
    fid_base = {"omega_b": 0.0225, "omega_cdm": 0.1181, "H0": 68.3, "m": 1.0}
    scores_null = []
    scores_by_amp: dict[float, list[float]] = {amp: [] for amp in INJECTION_AMPLITUDES}
    cases: list[tuple[str, int, dict[str, float], float]] = [
        ("lcdm_null", NULL_REALIZATIONS, {"omega_b": base_params["omega_b"], "omega_cdm": base_params["omega_cdm"], "H0": base_params["H0"]}, 0.0)
    ]
    cases.extend(
        ("rewrite_injection", INJECT_REALIZATIONS, {**fid_base, "A": amp}, amp)
        for amp in INJECTION_AMPLITUDES
    )
    for kind, n, params, injection_amp in cases:
        for i in range(n):
            model = "rewrite_power" if kind == "rewrite_injection" else "lcdm"
            mock_bao = make_mock_block(bao, model, params, rng, "desi_dr2_bao")
            mock_sn = make_mock_block(sn, model, params, rng, "pantheon_plus")
            fits = fit_rewrite_splits(split_blocks(planck, mock_bao, mock_sn), start={**base.params, **({"A": 0.70, "m": 0.0} if kind == "lcdm_null" else params)})
            score = staging_score(fits)
            if kind == "lcdm_null":
                scores_null.append(score)
            else:
                scores_by_amp[injection_amp].append(score)
            rows.append({"kind": kind, "realization": i, "injection_A": injection_amp, "staging_score": score})
    rank_summary = rank_calibration(scores_null)
    threshold = float(rank_summary["null_threshold_p95"])
    tpr_by_amp = {amp: float(np.mean(np.asarray(scores) > threshold)) for amp, scores in scores_by_amp.items()}
    detected = [amp for amp, tpr in tpr_by_amp.items() if tpr >= 0.8]
    a_detect = float(min(detected)) if detected else math.nan
    true_positive_rate = float(tpr_by_amp.get(INJECTION_AMPLITUDES[0], math.nan))
    false_alarm_rate = float(np.mean(np.asarray(scores_null) > threshold))
    summary = {
        **rank_summary,
        "null_false_alarm_rate_empirical": false_alarm_rate,
        "rewrite_true_positive_rate": true_positive_rate,
        "anti_vacuity_pass": bool(detected),
        "A_detect": a_detect,
        **{f"tpr_A_{amp:g}": tpr for amp, tpr in tpr_by_amp.items()},
    }
    for row in rows:
        row.update(summary)
    return rows, summary


def b2_real_and_b3(planck: GaussianBlock, bao: GaussianBlock, sn: GaussianBlock, base: FitResult, calibration: dict[str, object]) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, object]]:
    splits = split_blocks(planck, bao, sn)
    rewrite_fits = fit_rewrite_splits(splits, start={**base.params, "A": 0.70, "m": 0.0})
    w_fits = {name: fit_model("w0wa", name, blocks, start=base.params) for name, blocks in splits.items() if name in ("joint", "bao_only", "sn_only")}
    score = staging_score(rewrite_fits)
    threshold = float(calibration["null_threshold_p95"])
    fires = bool(score > threshold and calibration["anti_vacuity_pass"])
    rows = []
    for split, fit in rewrite_fits.items():
        rows.append(
            {
                "split": split,
                "model": "rewrite_power",
                "chi2": fit.chi2,
                "n_data": fit.n_data,
                "A": fit.params.get("A", math.nan),
                "m": fit.params.get("m", math.nan),
                "m_sigma": fit.m_sigma if fit.m_sigma is not None else math.nan,
                "omega_m": omega_m_from_params(fit.params),
                "A_lower_hit": (fit.diagnostics or {}).get("A_lower_hit", False),
                "A_upper_hit": (fit.diagnostics or {}).get("A_upper_hit", False),
                "m_lower_hit": (fit.diagnostics or {}).get("m_lower_hit", False),
                "m_upper_hit": (fit.diagnostics or {}).get("m_upper_hit", False),
                "converged": (fit.diagnostics or {}).get("converged", fit.success),
                "staging_score": score,
                "null_threshold_p95": threshold,
                "structured_dependence_fires": fires,
            }
        )
    for split, fit in w_fits.items():
        rows.append(
            {
                "split": split,
                "model": "w0wa",
                "chi2": fit.chi2,
                "n_data": fit.n_data,
                "A": math.nan,
                "m": math.nan,
                "m_sigma": math.nan,
                "omega_m": omega_m_from_params(fit.params),
                "A_lower_hit": False,
                "A_upper_hit": False,
                "m_lower_hit": False,
                "m_upper_hit": False,
                "converged": fit.success,
                "staging_score": score,
                "null_threshold_p95": threshold,
                "structured_dependence_fires": fires,
            }
        )
    route_rows = []
    joint = rewrite_fits["joint"]
    for split in ("sn_only", "bao_only"):
        fit = rewrite_fits[split]
        omega_resid = abs(omega_m_from_params(fit.params) - omega_m_from_params(joint.params))
        amp_resid = abs(fit.params["A"] - joint.params["A"])
        if not calibration["anti_vacuity_pass"]:
            status = "calibration_not_antivacuous_no_route_claim"
        else:
            status = "above_null_calibration" if score > threshold else "within_null_calibration"
        route_rows.append(
            {
                "route_a": split,
                "route_b": "joint",
                "parameter": "Omega_m",
                "unsigned_residual": omega_resid,
                "calibration_statistic": score,
                "null_threshold_p95": threshold,
                "status": status,
            }
        )
        route_rows.append(
            {
                "route_a": split,
                "route_b": "joint",
                "parameter": "A",
                "unsigned_residual": amp_resid,
                "calibration_statistic": score,
                "null_threshold_p95": threshold,
                "status": status,
            }
        )
    return rows, route_rows, {"real_staging_score": score, "real_structured_dependence_fires": fires}


def verdict_payload(
    model_rows: list[dict[str, object]],
    chart: dict[str, object],
    calibration: dict[str, object],
    real: dict[str, object],
) -> dict[str, object]:
    rewrite = next(row for row in model_rows if row["model"] == "rewrite_power")
    m_best = float(rewrite["m"])
    m_for_constant = float(rewrite["m_median"]) if np.isfinite(float(rewrite.get("m_median", math.nan))) else m_best
    m_sigma = float(rewrite["m_sigma"]) if np.isfinite(float(rewrite["m_sigma"])) else math.inf
    constant_threshold = min(2.0 * m_sigma, 0.25)
    constant_compatible = abs(m_for_constant) <= constant_threshold
    if not calibration["anti_vacuity_pass"]:
        bottom_line = "staging_audit_not_anti_vacuous_no_structured_claim"
    elif constant_compatible and not real["real_structured_dependence_fires"]:
        bottom_line = "rewrite_collapses_to_constant_or_no_calibrated_staging"
    elif real["real_structured_dependence_fires"]:
        bottom_line = "calibrated_structured_audit_feature_present"
    else:
        bottom_line = "no_calibrated_structured_dependence"
    return {
        "schema_version": 1,
        "packet": "WP-DEA",
        "status": "audit_result_not_detection_claim",
        "b1_rewrite_constant_compatible": bool(constant_compatible),
        "b1_rewrite_delta_aic_vs_lcdm": float(rewrite["delta_AIC_vs_lcdm"]),
        "b1_rewrite_m_best": m_best,
        "b1_rewrite_m_median": m_for_constant,
        "b1_rewrite_m_q16": float(rewrite["m_q16"]) if np.isfinite(float(rewrite.get("m_q16", math.nan))) else math.nan,
        "b1_rewrite_m_q84": float(rewrite["m_q84"]) if np.isfinite(float(rewrite.get("m_q84", math.nan))) else math.nan,
        "b1_rewrite_m_sigma": m_sigma,
        "b1b": chart,
        **{f"b2_{key}": calibration[key] for key in RANK_METADATA_FIELDS},
        "b2_null_threshold_p95": calibration["null_threshold_p95"],
        "b2_rewrite_true_positive_rate": calibration["rewrite_true_positive_rate"],
        "b2_A_detect": calibration["A_detect"],
        "b2_anti_vacuity_pass": calibration["anti_vacuity_pass"],
        "b2_real_staging_score": real["real_staging_score"],
        "b2_real_structured_dependence_fires": real["real_structured_dependence_fires"],
        "overall_bottom_line": bottom_line,
        "r025_quarantine": "fitted rewrite amplitudes are in-sample fits, never retrodictions",
    }


def write_verdict_markdown(payload: dict[str, object]) -> None:
    text = f"""# DE Audit Verdict

Status: audit result, not a detection claim.

## B1

- Rewrite `m = {payload['b1_rewrite_m_best']:.6g} +/- {payload['b1_rewrite_m_sigma']:.6g}`.
- Rewrite Delta AIC vs LambdaCDM: {payload['b1_rewrite_delta_aic_vs_lcdm']:.6g}.
- Constant-compatible rewrite: {payload['b1_rewrite_constant_compatible']}.

## B1b

- Fluid-chart phantom crossing z: {payload['b1b']['crossing_z']}.
- Additive Delta_H finite: {payload['b1b']['delta_h_finite']}.
- Delta_H range: [{payload['b1b']['delta_h_min']:.6g}, {payload['b1b']['delta_h_max']:.6g}].

## B2

The finite-rank level bound requires exchangeable scores under a fixed design;
the fitted real-data anchor does not establish that premise. Injection rates
are empirical finite-grid rates.

- Conditional finite-rank staging threshold: {payload['b2_null_threshold_p95']:.6g}.
- Rewrite-injection true-positive rate: {payload['b2_rewrite_true_positive_rate']:.6g}.
- Real staging score: {payload['b2_real_staging_score']:.6g}.
- Real structured dependence fires: {payload['b2_real_structured_dependence_fires']}.

## Honest grading

Bottom line: {payload['overall_bottom_line']}.

R025 quarantine: fitted amplitudes are in-sample parameters and are never reported as retrodictions. The phantom-crossing readout is a representation statement only: the additive correction chart is finite for the same expansion history, but this does not choose the physical interpretation.
"""
    (RESULTS / "VERDICT.md").write_text(text, encoding="utf-8")


def main() -> int:
    cap_threads()
    RESULTS.mkdir(parents=True, exist_ok=True)
    planck, bao, sn_full = load_blocks()
    full_e1_n_data = int(planck.data.size + bao.data.size + sn_full.data.size)
    fits = fit_main_models(planck, bao, sn_full, full_e1_n_data=full_e1_n_data)
    rows = model_table_rows(fits)
    write_csv(
        RESULTS / "B1_model_table.csv",
        rows,
        [
            "model",
            "split",
            "chi2",
            "n_data",
            "k",
            "AIC",
            "BIC",
            "delta_AIC_vs_lcdm",
            "delta_BIC_vs_lcdm",
            "omega_m",
            "H0",
            "w0_fld",
            "wa_fld",
            "A",
            "m",
            "m_sigma",
            "m_median",
            "m_q16",
            "m_q84",
            "A_median",
            "A_q16",
            "A_q84",
            "A_lower_hit",
            "A_upper_hit",
            "m_lower_hit",
            "m_upper_hit",
            "sn_M_profiled",
            "fit_mode",
            "same_likelihood_as_lcdm",
            "success",
        ],
    )
    chart = load_frozen_b1b_or_generate(fits["w0wa"])
    sn = compress_sn_for_audit(sn_full)
    calibration_rows, calibration = b2_calibration(planck, bao, sn, fits["lcdm"])
    write_csv(
        RESULTS / "B2_calibration.csv",
        calibration_rows,
        [
            "kind",
            "realization",
            "injection_A",
            "staging_score",
            "null_threshold_p95",
            "null_false_alarm_rate_empirical",
            *RANK_METADATA_FIELDS,
            "rewrite_true_positive_rate",
            "anti_vacuity_pass",
            "A_detect",
            *[f"tpr_A_{amp:g}" for amp in INJECTION_AMPLITUDES],
        ],
    )
    audit_rows, route_rows, real = b2_real_and_b3(planck, bao, sn, fits["lcdm"], calibration)
    write_csv(
        RESULTS / "B2_staging_audit.csv",
        audit_rows,
        [
            "split",
            "model",
            "chi2",
            "n_data",
            "A",
            "m",
            "m_sigma",
            "omega_m",
            "A_lower_hit",
            "A_upper_hit",
            "m_lower_hit",
            "m_upper_hit",
            "converged",
            "staging_score",
            "null_threshold_p95",
            "structured_dependence_fires",
        ],
    )
    write_csv(
        RESULTS / "B3_route_residuals.csv",
        route_rows,
        ["route_a", "route_b", "parameter", "unsigned_residual", "calibration_statistic", "null_threshold_p95", "status"],
    )
    payload = verdict_payload(rows, chart, calibration, real)
    (RESULTS / "verdict.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_verdict_markdown(payload)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
