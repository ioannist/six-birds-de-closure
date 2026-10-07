#!/usr/bin/env python3
"""E5-v3 staging-axis non-vacuity pre-mortem.

This is value-free: it uses published MAP theory curves, data covariances,
and legal nuisance covariance responses. It does not run the E5 certificate.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import time
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from sbt_cosmo.audits.metrics import nonvac_metrics

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "E5_v3_nonvac"

THREAD_CAPS = {
    "OMP_NUM_THREADS": "1",
    "OPENBLAS_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
    "VECLIB_MAXIMUM_THREADS": "1",
    "CCL_NUM_THREADS": "1",
}

HSC_MAP = {
    "Omega_m": 0.226,
    "omega_b": 0.0245,
    "h": 0.652,
    "n_s": 0.920,
    "S8": 0.792,
    "m_nu": 0.06,
    "ia_model": "tatt",
    "A1": 0.07,
    "eta1": -2.4,
    "A2": 0.78,
    "eta2": -2.6,
    "b_ta": 0.38,
    "z_pivot_IA": 0.62,
    "dz": [0.010, 0.005, -0.046, -0.144],
    "m": [-0.007, 0.009, 0.004, -0.003],
    "baryonic_effects": {"model": "vandaalen19", "fbar": 0.7},
    "nz_variant": "original",
}

KIDS_MAP = {
    "omega_b": 0.024054728386330965,
    "omega_cdm": 0.15533896707470593,
    "h": 0.7576293916845687,
    "n_s": 1.0030959525314076,
    "sigma8": 0.8036589717533703,
    "m_nu": 0.06,
    "A_IA": 0.0,
    "eta_IA": 0.0,
    "dz": [0.0] * 6,
    "m": [0.0] * 6,
}

KIDS_MASSDEP_DIR = ROOT / "data/raw/kids_massdep_ia"
KIDS_F_R = np.asarray([0.158, 0.198, 0.206, 0.258, 0.207, 0.026], dtype=np.float64)
KIDS_LOG10_M_PIV = 13.5

CMBL_MAP = {
    "Omega_b": 0.049,
    "Omega_c": 0.265,
    "h": 0.67,
    "n_s": 0.965,
    "sigma8": 0.811,
    "m_nu": 0.06,
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path: Path, obj: Any) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as fh:
        json.dump(obj, fh, indent=2, sort_keys=True)
        fh.write("\n")
    return sha256_file(path)


def set_thread_caps() -> dict[str, str | None]:
    for key, value in THREAD_CAPS.items():
        os.environ[key] = value
    return {key: os.environ.get(key) for key in THREAD_CAPS}


def uniform_sigma(lo: float, hi: float) -> float:
    return (float(hi) - float(lo)) / np.sqrt(12.0)


def eval_model(probe: Any, params: Mapping[str, Any]) -> np.ndarray:
    return np.asarray(probe.model(dict(params)), dtype=np.float64)


def hsc_rows(probe: Any) -> tuple[np.ndarray, np.ndarray]:
    pairs = []
    ell = []
    for row in probe._sacc["rows"]:  # noqa: SLF001 - diagnostic uses row metadata.
        pairs.append((int(row["tracer_0"].split("_")[1]), int(row["tracer_1"].split("_")[1])))
        ell.append(float(row["ell"]))
    return np.asarray(pairs, dtype=np.int64), np.asarray(ell, dtype=np.float64)


def kids_rows(n_bins: int = 6, n_modes: int = 6) -> tuple[np.ndarray, np.ndarray]:
    pairs: list[tuple[int, int]] = []
    modes: list[int] = []
    for i in range(n_bins):
        for j in range(i, n_bins):
            for mode in range(n_modes):
                pairs.append((i, j))
                modes.append(mode + 1)
    return np.asarray(pairs, dtype=np.int64), np.asarray(modes, dtype=np.int64)


SCALE_CUT_GRIDS = {
    "HSC-Y3": [1000, 1500, 2000, 3000, 5000],
    "CMB-lensing": [1000, 1500, 2000, 3000, 5000],
    "KiDS-Legacy": [3, 4, 5, 6],
}


def scale_cut_increment(base: np.ndarray, scale: np.ndarray, lower: float, upper: float, data_vector: np.ndarray | None = None) -> np.ndarray:
    """Return the genuine adjacent-cut staging perturbation.

    This is ``theta(cut_upper) - theta(cut_lower)`` represented in the full
    native vector: the newly admitted scale range is populated by theory and
    all other rows are zero. ``data_vector`` is accepted only to make the
    no-data-amplitude-dependence property testable; it is deliberately unused.
    """
    del data_vector
    scale_arr = np.asarray(scale, dtype=np.float64)
    t = np.zeros_like(np.asarray(base, dtype=np.float64))
    mask = (scale_arr > float(lower)) & (scale_arr <= float(upper))
    t[mask] = np.asarray(base, dtype=np.float64)[mask]
    return t


def metric_norm(t: np.ndarray, covariance: np.ndarray) -> float:
    return float(np.sqrt(max(float(t @ np.linalg.solve(covariance, t)), 0.0)))


def metric_orthogonalize(t: np.ndarray, basis: np.ndarray | None, covariance: np.ndarray) -> tuple[np.ndarray, dict[str, float]]:
    if basis is None or basis.size == 0:
        return t, {"projection_fraction": 0.0, "residual_max_abs_cosine": 0.0}
    metric_basis = np.linalg.solve(covariance, basis)
    gram = basis.T @ metric_basis
    rhs = basis.T @ np.linalg.solve(covariance, t)
    coeff = np.linalg.pinv(gram, rcond=1.0e-10) @ rhs
    projection = basis @ coeff
    residual = t - projection
    t_norm = metric_norm(t, covariance)
    proj_norm = metric_norm(projection, covariance)
    residual_norm = metric_norm(residual, covariance)
    max_cos = 0.0
    for col in basis.T:
        col_norm = metric_norm(col, covariance)
        if col_norm > 0.0 and residual_norm > 0.0:
            cos = abs(float(residual @ np.linalg.solve(covariance, col))) / (residual_norm * col_norm)
            max_cos = max(max_cos, cos)
    return residual, {
        "projection_fraction": float(proj_norm / t_norm) if t_norm > 0.0 else 0.0,
        "residual_max_abs_cosine": float(max_cos),
    }


def ranks(values: np.ndarray) -> np.ndarray:
    order = np.argsort(values)
    out = np.empty(values.size, dtype=np.float64)
    out[order] = np.arange(values.size, dtype=np.float64)
    return out


def spearman_rho(x: np.ndarray, y: np.ndarray) -> float:
    if x.size < 2 or y.size < 2:
        return 0.0
    rx = ranks(np.asarray(x, dtype=np.float64))
    ry = ranks(np.asarray(y, dtype=np.float64))
    rx -= rx.mean()
    ry -= ry.mean()
    denom = float(np.linalg.norm(rx) * np.linalg.norm(ry))
    return float(rx @ ry / denom) if denom > 0.0 else 0.0


def scale_order_control(rows: list[dict[str, Any]]) -> dict[str, Any]:
    scale_rows = [row for row in rows if row["axis"].startswith("scale_cut_")]
    if len(scale_rows) < 2:
        return {
            "n_adjacent_cuts": len(scale_rows),
            "ordered_spearman_rho": None,
            "reversed_spearman_rho": None,
            "randomized_median_abs_rho": None,
            "zero_control_killed": None,
            "interpretation": "Scale-order controls are certificate-level tests on lambda_max(Xi_C-Omega), not NONVAC norm gates.",
        }
    order = np.arange(len(scale_rows), dtype=np.float64)
    norms = np.asarray([row["norm_post"] for row in scale_rows], dtype=np.float64)
    ordered = spearman_rho(order, norms)
    reversed_rho = spearman_rho(order[::-1], norms)
    rng = np.random.default_rng(20260601)
    random_rhos = []
    for _ in range(128):
        random_rhos.append(abs(spearman_rho(rng.permutation(order), norms)))
    return {
        "n_adjacent_cuts": len(scale_rows),
        "ordered_spearman_rho": ordered,
        "reversed_spearman_rho": reversed_rho,
        "randomized_median_abs_rho": float(np.median(random_rhos)),
        "zero_control_killed": bool(reversed_rho < 0.6 and float(np.median(random_rhos)) < 0.6),
        "interpretation": "NONVAC uses norms, so reversing one cut increment sends t -> -t and cannot change eligibility. This diagnostic is recorded for later G-E5-ZERO, not used to fail NONVAC.",
    }


def amplitude_rescale_check(t: np.ndarray, cov: np.ndarray, cov_marg: np.ndarray, data_vector: np.ndarray) -> dict[str, float]:
    original = nonvac_metrics(t, cov, cov_marg)
    rescaled_t = scale_cut_increment(t, np.ones_like(t), 0.0, 1.0, data_vector=10.0 * data_vector)
    rescaled = nonvac_metrics(rescaled_t, cov, cov_marg)
    rel_changes = []
    for key in ("norm_pre", "norm_post", "retained"):
        denom = max(abs(float(original[key])), 1.0e-30)
        rel_changes.append(abs(float(original[key]) - float(rescaled[key])) / denom)
    return {"data_amplitude_factor": 10.0, "max_relative_change": float(max(rel_changes))}


def finite_diff(probe: Any, params: Mapping[str, Any], key: str, index: int | None, step: float) -> np.ndarray:
    p_plus = dict(params)
    p_minus = dict(params)
    if index is None:
        p_plus[key] = float(params.get(key, 0.0)) + step
        p_minus[key] = float(params.get(key, 0.0)) - step
    else:
        p_plus[key] = list(params.get(key, []))
        p_minus[key] = list(params.get(key, []))
        p_plus[key][index] = float(p_plus[key][index]) + step
        p_minus[key][index] = float(p_minus[key][index]) - step
    return (eval_model(probe, p_plus) - eval_model(probe, p_minus)) / (2.0 * step)


def hsc_dz_basis(probe: Any) -> np.ndarray:
    rows = []
    for i, step in enumerate([0.012, 0.011, 0.02, 0.02]):
        print(f"[NONVAC] HSC dz response {i+1}", flush=True)
        rows.append(finite_diff(probe, HSC_MAP, "dz", i, step))
    return np.column_stack(rows)


def kids_dz_basis(probe: Any) -> tuple[np.ndarray, np.ndarray]:
    cov = np.loadtxt(ROOT / "data/raw/kids_legacy/KiDS_Legacy_cosmic_shear_data_release/data/Nz_covariance.txt")
    rows = []
    for i, step in enumerate(np.sqrt(np.diag(cov))):
        print(f"[NONVAC] KiDS dz response {i+1}", flush=True)
        rows.append(finite_diff(probe, KIDS_MAP, "dz", i, max(float(step), 0.005)))
    return np.column_stack(rows), cov


def kids_massdep_means_cov() -> tuple[np.ndarray, np.ndarray]:
    means = np.loadtxt(KIDS_MASSDEP_DIR / "massdep_means.txt", dtype=np.float64)
    cov = np.loadtxt(KIDS_MASSDEP_DIR / "massdep_cov.txt", dtype=np.float64)
    if means.shape != (8,) or cov.shape != (8, 8):
        raise ValueError("KiDS mass-dependent IA files must be an 8-vector and 8x8 covariance")
    return means, cov


def kids_massdep_aia_bins(params: np.ndarray) -> np.ndarray:
    a_ia = float(params[0])
    beta = float(params[1])
    log10_m_mean = np.asarray(params[2:], dtype=np.float64)
    mass_ratio = 10.0 ** (log10_m_mean - KIDS_LOG10_M_PIV)
    return a_ia * KIDS_F_R * mass_ratio**beta


def kids_massdep_model(probe: Any, params: Mapping[str, Any], massdep_params: np.ndarray) -> np.ndarray:
    return eval_model(
        probe,
        {
            **params,
            "ia_model": "nla",
            "A_IA_bins": kids_massdep_aia_bins(massdep_params),
            "eta_IA": 0.0,
        },
    )


def kids_massdep_ia_basis(probe: Any) -> tuple[np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    means, cov = kids_massdep_means_cov()
    cols = []
    sigmas = np.sqrt(np.clip(np.diag(cov), 0.0, None))
    for i, sigma in enumerate(sigmas):
        step = max(float(0.05 * sigma), 1.0e-4)
        print(f"[NONVAC] KiDS official massdep IA response {i+1}", flush=True)
        p_plus = means.copy()
        p_minus = means.copy()
        p_plus[i] += step
        p_minus[i] -= step
        cols.append((kids_massdep_model(probe, KIDS_MAP, p_plus) - kids_massdep_model(probe, KIDS_MAP, p_minus)) / (2.0 * step))
    meta = {
        "parameter_order": ["A_IA", "beta", "log10_M_mean_1", "log10_M_mean_2", "log10_M_mean_3", "log10_M_mean_4", "log10_M_mean_5", "log10_M_mean_6"],
        "means": means.tolist(),
        "covariance_path": "data/raw/kids_massdep_ia/massdep_cov.txt",
        "means_path": "data/raw/kids_massdep_ia/massdep_means.txt",
        "model_path": "data/raw/kids_massdep_ia/mass_dependent_ia_model.py",
        "effective_A_IA_bins_at_mean": kids_massdep_aia_bins(means).tolist(),
    }
    return np.column_stack(cols), cov, means, meta


def sigma_from_responses(responses: np.ndarray, nuisance_cov: np.ndarray) -> np.ndarray:
    return responses @ nuisance_cov @ responses.T


def build_kids_sigma_nuis(probe: Any) -> tuple[np.ndarray, dict[str, Any], np.ndarray, np.ndarray]:
    dz_basis, dz_cov = kids_dz_basis(probe)
    sigma_nuis = sigma_from_responses(dz_basis, dz_cov)
    ia_basis, ia_cov, _, ia_meta = kids_massdep_ia_basis(probe)
    sigma_nuis += sigma_from_responses(ia_basis, ia_cov)
    print("[NONVAC] KiDS baryon proxy response", flush=True)
    p_plus = {**KIDS_MAP, "baryonic_effects": {"model": "vandaalen19", "fbar": 0.75}}
    p_minus = {**KIDS_MAP, "baryonic_effects": {"model": "vandaalen19", "fbar": 0.65}}
    g_bary = (eval_model(probe, p_plus) - eval_model(probe, p_minus)) / 0.10
    sigma_nuis += uniform_sigma(7.3, 8.3) ** 2 * np.outer(g_bary, g_bary)
    meta = {
        "dz_covariance": "Official KiDS-Legacy Nz_covariance.txt",
        "ia": "Official KiDS mass-dependent IA prior covariance propagated through per-bin NLA amplitudes.",
        "ia_massdep": ia_meta,
        "baryon": "vanDaalen19 fbar proxy with logT_AGN U(7.3,8.3) width from KiDS values.ini; baryon axes are non-decisive.",
        "shear_calibration_m": "No explicit shear-m prior appears in the released KiDS-Legacy COSEBIs pipeline config inspected here; no widened m prior was invented.",
        "nuisance_legality": "legal_official_massdep_ia",
    }
    return sigma_nuis, meta, dz_basis, dz_cov


class ProbeProxy:
    """Small wrapper applying fixed parameter overrides before model calls."""

    def __init__(self, probe: Any, overrides: Mapping[str, Any]):
        self.probe = probe
        self.overrides = dict(overrides)

    def model(self, params: Mapping[str, Any]) -> np.ndarray:
        return self.probe.model({**params, **self.overrides})


def build_cmbl_sigma_nuis(size: int) -> tuple[np.ndarray, dict[str, Any]]:
    return np.zeros((size, size), dtype=np.float64), {
        "note": "No m/dz/IA nuisance subspace exists for the compressed CMB-lensing bandpower adapter; published covariance is used directly."
    }


def axis_row(
    family: str,
    axis: str,
    t: np.ndarray,
    cov: np.ndarray,
    cov_marg: np.ndarray,
    eligible: bool,
    note: str = "",
    *,
    nuisance_legality: str = "legal",
    diagnostics: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    metrics = nonvac_metrics(t, cov, cov_marg)
    return {
        "family": family,
        "axis": axis,
        "norm_pre": metrics["norm_pre"],
        "norm_post": metrics["norm_post"],
        "retained": metrics["retained"],
        "NONVAC_pass": bool(metrics["NONVAC_pass"]),
        "eligible_as_decisive": bool(eligible),
        "eligible_NONVAC_pass": bool(eligible and metrics["NONVAC_pass"]),
        "nuisance_legality": nuisance_legality,
        "diagnostics": dict(diagnostics or {}),
        "note": note,
    }


def hsc_rows_nonvac() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

    probe = build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "original"})
    probe_recal = build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "desi_recal"})
    cov = probe.covariance()
    omega = np.load(RESULTS / "Omega_HSC_pipeline.npy")
    cov_marg = np.load(RESULTS / "HSC_Sigma_marg.npy")
    print("[NONVAC] HSC base/recal", flush=True)
    base = eval_model(probe, HSC_MAP)
    recal = eval_model(probe_recal, {**HSC_MAP, "nz_variant": "desi_recal"})
    pairs, ell = hsc_rows(probe)
    dz_basis = hsc_dz_basis(probe)
    rows = [
        axis_row("HSC-Y3", "photo_z_original_minus_desi_recal", base - recal, cov, cov_marg, True, "Reviewer expected FAIL."),
    ]
    low_pair = (pairs[:, 0] < 2) & (pairs[:, 1] < 2)
    rows.append(axis_row("HSC-Y3", "photo_z_lowz_bins_1_2", (base - recal) * low_pair, cov, cov_marg, True))
    for lower, upper in zip(SCALE_CUT_GRIDS["HSC-Y3"][:-1], SCALE_CUT_GRIDS["HSC-Y3"][1:], strict=True):
        t = scale_cut_increment(base, ell, lower, upper, data_vector=probe.data_vector())
        if np.any(t):
            rows.append(
                axis_row(
                    "HSC-Y3",
                    f"scale_cut_lmax_{upper}_minus_{lower}",
                    t,
                    cov,
                    cov_marg,
                    True,
                    "Genuine adjacent lmax cut increment; zeros outside newly admitted ell range.",
                    diagnostics={"amplitude_rescale": amplitude_rescale_check(t, cov, cov_marg, probe.data_vector())},
                )
            )
    high = (pairs[:, 0] >= 2) & (pairs[:, 1] >= 2)
    low = (pairs[:, 0] < 2) & (pairs[:, 1] < 2)
    tomo_raw = np.zeros_like(base)
    tomo_raw[high] = base[high]
    tomo_raw[low] = -base[low]
    tomo, tomo_diag = metric_orthogonalize(tomo_raw, dz_basis, cov_marg)
    rows.append(
        axis_row(
            "HSC-Y3",
            "redshift_tomographic_orthogonalized_to_dz",
            tomo,
            cov,
            cov_marg,
            True,
            "Orthogonalized against dz span in the Sigma_marg^-1 metric.",
            diagnostics={"metric_projection": tomo_diag},
        )
    )
    nla = eval_model(probe, {**HSC_MAP, "ia_model": "nla", "A_IA": 1.0, "eta_IA": 0.0, "A1": 1.0, "A2": 0.0, "b_ta": 0.0})
    rows.append(axis_row("HSC-Y3", "IA_model_TATT_minus_NLA", base - nla, cov, cov_marg, True))
    no_baryon = eval_model(probe, {k: v for k, v in HSC_MAP.items() if k != "baryonic_effects"})
    rows.append(axis_row("HSC-Y3", "baryon_vanDaalen19_minus_no_baryon", base - no_baryon, cov, cov_marg, False, "Baryon proxy is not eligible as decisive."))
    meta = {
        "Sigma_marg": "reused results/E5/HSC_Sigma_marg.npy from legal settle2",
        "Omega_HSC_pipeline": "reused results/E5/Omega_HSC_pipeline.npy from legal settle2",
        "omega_trace": float(np.trace(omega)),
        "scale_cut_grid": SCALE_CUT_GRIDS["HSC-Y3"],
        "scale_order_control": scale_order_control(rows),
    }
    return rows, meta


def kids_rows_nonvac() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

    probe = build_weak_lensing_probe({"probe_id": "kids_legacy_shear"})
    cov = probe.covariance()
    print("[NONVAC] KiDS base", flush=True)
    massdep_means, _ = kids_massdep_means_cov()
    base = kids_massdep_model(probe, KIDS_MAP, massdep_means)
    sigma_nuis, meta, dz_basis, dz_cov = build_kids_sigma_nuis(probe)
    cov_marg = cov + sigma_nuis
    pairs, modes = kids_rows()
    rows = []
    for lower, upper in zip(SCALE_CUT_GRIDS["KiDS-Legacy"][:-1], SCALE_CUT_GRIDS["KiDS-Legacy"][1:], strict=True):
        t = scale_cut_increment(base, modes, lower, upper, data_vector=probe.data_vector())
        if np.any(t):
            rows.append(
                axis_row(
                    "KiDS-Legacy",
                    f"scale_cut_modes_1-{upper}_minus_1-{lower}",
                    t,
                    cov,
                    cov_marg,
                    True,
                    "Genuine adjacent COSEBIs mode-grid increment with official mass-dependent IA covariance in Sigma_nuis.",
                    nuisance_legality="legal_official_massdep_ia",
                    diagnostics={"amplitude_rescale": amplitude_rescale_check(t, cov, cov_marg, probe.data_vector())},
                )
            )
    high = (pairs[:, 0] >= 3) & (pairs[:, 1] >= 3)
    low = (pairs[:, 0] < 3) & (pairs[:, 1] < 3)
    tomo_raw = np.zeros_like(base)
    tomo_raw[high] = base[high]
    tomo_raw[low] = -base[low]
    tomo, tomo_diag = metric_orthogonalize(tomo_raw, dz_basis, cov_marg)
    rows.append(
        axis_row(
            "KiDS-Legacy",
            "redshift_tomographic_orthogonalized_to_dz",
            tomo,
            cov,
            cov_marg,
            True,
            "Orthogonalized against dz span in Sigma_marg^-1 with official mass-dependent IA covariance in Sigma_nuis.",
            nuisance_legality="legal_official_massdep_ia",
            diagnostics={"metric_projection": tomo_diag},
        )
    )
    evals, evecs = np.linalg.eigh(dz_basis @ dz_cov @ dz_basis.T)
    principal = evecs[:, int(np.argmax(evals))] * float(np.sqrt(max(evals.max(), 0.0)))
    rows.append(
        axis_row(
            "KiDS-Legacy",
            "photo_z_dz_principal_direction",
            principal,
            cov,
            cov_marg,
            True,
            "Principal propagated dz-covariance direction; no external recalibrated-n(z) pair is in the manifest.",
            nuisance_legality="legal_official_massdep_ia",
        )
    )
    nla = eval_model(probe, {**KIDS_MAP, "ia_model": "nla", "A_IA": 1.0, "eta_IA": 0.0})
    tatt = eval_model(probe, {**KIDS_MAP, "ia_model": "tatt", "A1": 1.0, "eta1": 0.0, "A2": 0.5, "eta2": 0.0, "b_ta": 0.3})
    rows.append(
        axis_row(
            "KiDS-Legacy",
            "IA_model_TATT_minus_NLA",
            tatt - nla,
            cov,
            cov_marg,
            True,
            "Adapter-level TATT-vs-NLA contrast; official KiDS IA nuisance covariance is the mass-dependent NLA covariance, not TATT.",
            nuisance_legality="legal_official_massdep_ia",
        )
    )
    no_baryon = kids_massdep_model(probe, KIDS_MAP, massdep_means)
    baryon = kids_massdep_model(probe, {**KIDS_MAP, "baryonic_effects": {"model": "vandaalen19", "fbar": 0.7}}, massdep_means)
    rows.append(axis_row("KiDS-Legacy", "baryon_vanDaalen19_minus_no_baryon", baryon - no_baryon, cov, cov_marg, False, "Baryon proxy is not eligible as decisive."))
    meta["Sigma_nuis_trace"] = float(np.trace(sigma_nuis))
    meta["scale_cut_grid"] = SCALE_CUT_GRIDS["KiDS-Legacy"]
    meta["scale_order_control"] = scale_order_control(rows)
    return rows, meta


def cmbl_rows_nonvac() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

    probe = build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"})
    cov = probe.covariance()
    print("[NONVAC] CMB-lensing base", flush=True)
    base = eval_model(probe, CMBL_MAP)
    sigma_nuis, meta = build_cmbl_sigma_nuis(base.size)
    cov_marg = cov + sigma_nuis
    L = np.load(ROOT / "data/processed/cmb_lensing/bin_centers_L.npy")
    rows = []
    for lower, upper in zip(SCALE_CUT_GRIDS["CMB-lensing"][:-1], SCALE_CUT_GRIDS["CMB-lensing"][1:], strict=True):
        t = scale_cut_increment(base, L, lower, upper, data_vector=probe.data_vector())
        if np.any(t):
            rows.append(
                axis_row(
                    "CMB-lensing",
                    f"scale_cut_Lmax_{upper}_minus_{lower}",
                    t,
                    cov,
                    cov_marg,
                    True,
                    "Genuine adjacent Lmax cut increment; zeros outside newly admitted L range.",
                    diagnostics={"amplitude_rescale": amplitude_rescale_check(t, cov, cov_marg, probe.data_vector())},
                )
            )
    no_baryon = eval_model(probe, CMBL_MAP)
    baryon = eval_model(probe, {**CMBL_MAP, "baryonic_effects": {"model": "vandaalen19", "fbar": 0.7}})
    rows.append(axis_row("CMB-lensing", "baryon_vanDaalen19_minus_no_baryon", baryon - no_baryon, cov, cov_marg, False, "Baryon proxy is not eligible as decisive."))
    meta["scale_cut_grid"] = SCALE_CUT_GRIDS["CMB-lensing"]
    meta["scale_order_control"] = scale_order_control(rows)
    return rows, meta


def write_csv(path: Path, rows: list[dict[str, Any]]) -> str:
    fields = [
        "family",
        "axis",
        "norm_pre",
        "norm_post",
        "retained",
        "NONVAC_pass",
        "eligible_as_decisive",
        "eligible_NONVAC_pass",
        "nuisance_legality",
        "diagnostics",
        "note",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            serialized = dict(row)
            serialized["diagnostics"] = json.dumps(serialized.get("diagnostics", {}), sort_keys=True)
            writer.writerow({field: serialized[field] for field in fields})
    return sha256_file(path)


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    families = sorted({row["family"] for row in rows})
    return {
        family: {
            "eligible_axes": [row["axis"] for row in rows if row["family"] == family and row["eligible_as_decisive"]],
            "nonvac_axes_all": [row["axis"] for row in rows if row["family"] == family and row["NONVAC_pass"]],
            "eligible_nonvac_axes": [row["axis"] for row in rows if row["family"] == family and row["eligible_NONVAC_pass"]],
            "has_eligible_nonvac_axis": any(row["family"] == family and row["eligible_NONVAC_pass"] for row in rows),
        }
        for family in families
    }


def main() -> None:
    start = time.perf_counter()
    thread_caps = set_thread_caps()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)
    all_rows: list[dict[str, Any]] = []
    metadata: dict[str, Any] = {}
    for name, fn in [("HSC-Y3", hsc_rows_nonvac), ("KiDS-Legacy", kids_rows_nonvac), ("CMB-lensing", cmbl_rows_nonvac)]:
        rows, meta = fn()
        all_rows.extend(rows)
        metadata[name] = meta
    csv_hash = write_csv(RESULTS / "E5_v3_nonvac.csv", all_rows)
    summary = summarize(all_rows)
    hsc_passes = summary["HSC-Y3"]["eligible_nonvac_axes"]
    output = {
        "schema_version": 1,
        "design_version": "E5-v3-NONVAC-premortem",
        "thread_caps": thread_caps,
        "gate": "G-E5-NONVAC(family,axis): norm_post>=2.0 and retained>=0.25",
        "rows": all_rows,
        "summary_by_family": summary,
        "metadata": metadata,
        "outputs": {"csv": {"path": "results/E5/E5_v3_nonvac.csv", "sha256": csv_hash}},
        "honest_branch": {
            "kids_has_axis": summary["KiDS-Legacy"]["has_eligible_nonvac_axis"],
            "cmblensing_has_axis": summary["CMB-lensing"]["has_eligible_nonvac_axis"],
            "hsc_candidate_axes": hsc_passes,
            "hsc_has_candidate_axis": bool(hsc_passes),
            "bottom_line": (
                "HSC has at least one eligible non-vacuous axis for manager/reviewer confirmation."
                if hsc_passes
                else "HSC has no eligible non-vacuous axis in this premortem; HSC should be diagnostic unless manager/reviewer add a fourth family."
            ),
        },
        "runtime_seconds": float(time.perf_counter() - start),
        "load_average_end": os.getloadavg(),
        "stopped_before_certificate": True,
    }
    json_hash = write_json(RESULTS / "E5_v3_nonvac.json", output)
    write_json(RUNS / "summary.json", {"results_sha256": json_hash, "stopped_before_certificate": True})
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
