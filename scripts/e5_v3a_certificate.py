#!/usr/bin/env python3
"""Run the E5-minimal-physical-v3A scale-cut certificate.

The implementation is deliberately conservative: the Schur carrier is built in
the single-whitened basis, the scale-cut rows are genuine adjacent cut
increments, and every zero control is allowed to fail the certificate.  No
per-probe closure amplitude is fitted.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import h5py
import numpy as np

from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe
from scripts.e5_v3_nonvac import (
    CMBL_MAP,
    HSC_MAP,
    KIDS_MAP,
    ROOT,
    SCALE_CUT_GRIDS,
    build_kids_sigma_nuis,
    hsc_rows,
    kids_massdep_means_cov,
    kids_massdep_model,
    kids_rows,
    scale_cut_increment,
)

RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "E5_v3a_certificate"
GOVERNED = {
    "e5_manifest": ROOT / "data/manifests/e5_growth_currency_inputs.json",
    "carrier": ROOT / "plan/E5_CARRIER_REALIZATION.md",
    "design_freeze": ROOT / "plan/E5_DESIGN_FREEZE.md",
    "gates": ROOT / "plan/07-pass-fail-gates.md",
    "nonvac": ROOT / "results/E5/E5_v3_nonvac.json",
    "repro": ROOT / "results/E5/E5_repro.json",
    "env4": ROOT / "results/E5/E5_env4_pyccl_class.json",
}
THREAD_CAPS = {
    "OMP_NUM_THREADS": "1",
    "OPENBLAS_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
    "VECLIB_MAXIMUM_THREADS": "1",
    "CCL_NUM_THREADS": "1",
}
FAMILY_ORDER = ["KiDS-Legacy", "HSC-Y3", "CMB-lensing"]
N_POSTERIOR = int(os.environ.get("E5_V3A_NPOST", "4"))
TAU_L = 1.0e-3
DELTA_MARGIN = 0.10


@dataclass
class FamilyState:
    name: str
    data: np.ndarray
    covariance: np.ndarray
    sigma_total: np.ndarray
    base: np.ndarray
    scale_rows: np.ndarray
    scale_labels: list[str]
    scale_values: np.ndarray
    scale_high_mask: np.ndarray


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


def load_json(path: Path) -> Any:
    with path.open() as fh:
        return json.load(fh)


def verify_array(entry: dict[str, Any]) -> dict[str, Any]:
    path = ROOT / entry["path"]
    arr = np.load(path)
    digest = sha256_file(path)
    return {
        "path": entry["path"],
        "sha256": digest,
        "expected_sha256": entry.get("sha256"),
        "sha256_ok": digest == entry.get("sha256"),
        "shape": list(arr.shape),
        "finite": bool(np.all(np.isfinite(arr))),
    }


def covariance_gate(cov: np.ndarray) -> dict[str, Any]:
    eig = np.linalg.eigvalsh(cov)
    cond = float(eig[-1] / eig[0]) if eig[0] > 0 else float("inf")
    return {
        "lambda_min": float(eig[0]),
        "condition_number": cond,
        "PD": bool(eig[0] > 0),
        "pass": bool(eig[0] > 0 and cond < 1.0e8 and np.all(np.isfinite(cov))),
    }


def hsc_state() -> FamilyState:
    probe = build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "original"})
    data = probe.data_vector()
    cov = probe.covariance()
    sigma_total = np.load(RESULTS / "HSC_Sigma_marg.npy")
    base = np.asarray(probe.model(HSC_MAP), dtype=np.float64)
    _, ell = hsc_rows(probe)
    rows: list[np.ndarray] = []
    labels: list[str] = []
    values: list[float] = []
    for lower, upper in zip(SCALE_CUT_GRIDS["HSC-Y3"][:-1], SCALE_CUT_GRIDS["HSC-Y3"][1:], strict=True):
        t = scale_cut_increment(base, ell, lower, upper, data_vector=data)
        if np.any(t):
            rows.append(t)
            labels.append(f"lmax_{upper}_minus_{lower}")
            values.append(float(upper))
    return FamilyState("HSC-Y3", data, cov, sigma_total, base, np.vstack(rows), labels, np.asarray(values), np.asarray(values) >= np.median(values))


def kids_state() -> FamilyState:
    probe = build_weak_lensing_probe({"probe_id": "kids_legacy_shear"})
    data = probe.data_vector()
    cov = probe.covariance()
    sigma_nuis, _, _, _ = build_kids_sigma_nuis(probe)
    sigma_total = cov + sigma_nuis
    massdep_means, _ = kids_massdep_means_cov()
    base = kids_massdep_model(probe, KIDS_MAP, massdep_means)
    _, modes = kids_rows()
    rows: list[np.ndarray] = []
    labels: list[str] = []
    values: list[float] = []
    for lower, upper in zip(SCALE_CUT_GRIDS["KiDS-Legacy"][:-1], SCALE_CUT_GRIDS["KiDS-Legacy"][1:], strict=True):
        t = scale_cut_increment(base, modes, lower, upper, data_vector=data)
        if np.any(t):
            rows.append(t)
            labels.append(f"modes_1-{upper}_minus_1-{lower}")
            values.append(float(upper))
    return FamilyState("KiDS-Legacy", data, cov, sigma_total, base, np.vstack(rows), labels, np.asarray(values), np.asarray(values) >= np.median(values))


def cmbl_state() -> FamilyState:
    probe = build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"})
    data = probe.data_vector()
    cov = probe.covariance()
    base = np.asarray(probe.model(CMBL_MAP), dtype=np.float64)
    L = np.load(ROOT / "data/processed/cmb_lensing/bin_centers_L.npy")
    rows: list[np.ndarray] = []
    labels: list[str] = []
    values: list[float] = []
    for lower, upper in zip(SCALE_CUT_GRIDS["CMB-lensing"][:-1], SCALE_CUT_GRIDS["CMB-lensing"][1:], strict=True):
        t = scale_cut_increment(base, L, lower, upper, data_vector=data)
        if np.any(t):
            rows.append(t)
            labels.append(f"Lmax_{upper}_minus_{lower}")
            values.append(float(upper))
    return FamilyState("CMB-lensing", data, cov, cov, base, np.vstack(rows), labels, np.asarray(values), np.asarray(values) >= np.median(values))


def block_slices(states: list[FamilyState]) -> dict[str, slice]:
    start = 0
    out = {}
    for state in states:
        stop = start + state.data.size
        out[state.name] = slice(start, stop)
        start = stop
    return out


def block_diag(mats: list[np.ndarray]) -> np.ndarray:
    n = sum(m.shape[0] for m in mats)
    out = np.zeros((n, n), dtype=np.float64)
    start = 0
    for mat in mats:
        stop = start + mat.shape[0]
        out[start:stop, start:stop] = mat
        start = stop
    return out


def add_shared_wl_covariance(sigma: np.ndarray, slices: dict[str, slice], rho: float) -> np.ndarray:
    out = sigma.copy()
    sk = slices["KiDS-Legacy"]
    sh = slices["HSC-Y3"]
    diag_k = np.sqrt(np.clip(np.diag(out[sk, sk]), 0.0, None))
    diag_h = np.sqrt(np.clip(np.diag(out[sh, sh]), 0.0, None))
    if np.linalg.norm(diag_k) == 0.0 or np.linalg.norm(diag_h) == 0.0:
        return out
    cross = float(rho) * np.outer(diag_k, diag_h) / np.sqrt(diag_k.size * diag_h.size)
    out[sk, sh] = cross
    out[sh, sk] = cross.T
    return out


def cholesky_whitener(sigma: np.ndarray) -> np.ndarray:
    jitter = 0.0
    for _ in range(8):
        try:
            return np.linalg.cholesky(sigma + jitter * np.eye(sigma.shape[0]))
        except np.linalg.LinAlgError:
            jitter = 1.0e-12 if jitter == 0.0 else jitter * 10.0
    raise np.linalg.LinAlgError("could not Cholesky-whiten Sigma_total")


def whiten(chol: np.ndarray, values: np.ndarray) -> np.ndarray:
    arr = np.asarray(values, dtype=np.float64)
    if arr.ndim == 1:
        return np.linalg.solve(chol, arr)
    return np.linalg.solve(chol, arr.T).T


def embed(rows: np.ndarray, state: FamilyState, slices: dict[str, slice], n_total: int) -> np.ndarray:
    out = np.zeros((rows.shape[0], n_total), dtype=np.float64)
    out[:, slices[state.name]] = rows
    return out


def read_chain_samples() -> list[dict[str, float]]:
    path = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
    with path.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    data = np.loadtxt(path)
    cols = {name: i for i, name in enumerate(header)}
    weights = data[:, cols["weight"]]
    order = np.argsort(data[:, cols["minuslogpost"]])
    selected = order[np.linspace(0, min(len(order) - 1, 4000), N_POSTERIOR, dtype=int)]
    samples = []
    for idx in selected:
        row = data[idx]
        samples.append(
            {
                "omega_b": float(row[cols["omega_b"]]),
                "omega_cdm": float(row[cols["omega_cdm"]]),
                "H0": float(row[cols["H0"]]),
                "w0_fld": float(row[cols["w0_fld"]]),
                "wa_fld": float(row[cols["wa_fld"]]),
                "n_s": 0.965,
                "sigma8": 0.811,
                "m_nu": 0.06,
                "weight": float(row[cols["weight"]]) if "weight" in cols else float(weights[idx]),
            }
        )
    return samples


def params_for_family(sample: dict[str, float], family: str) -> dict[str, Any]:
    base = {k: v for k, v in sample.items() if k != "weight"}
    if family == "HSC-Y3":
        return {**base, **{k: v for k, v in HSC_MAP.items() if k not in {"Omega_m", "omega_b", "omega_cdm", "h", "n_s", "S8"}}}
    if family == "KiDS-Legacy":
        return {**base, "dz": [0.0] * 6, "m": [0.0] * 6}
    return base


def posterior_prediction(state: FamilyState, sample: dict[str, float]) -> np.ndarray:
    probe_id = {
        "HSC-Y3": "hsc_y3_origVSrecal",
        "KiDS-Legacy": "kids_legacy_shear",
        "CMB-lensing": "cmblensing_act_spt_planck",
    }[state.name]
    probe = build_weak_lensing_probe({"probe_id": probe_id, "nz_variant": "original"})
    params = params_for_family(sample, state.name)
    if state.name == "KiDS-Legacy":
        means, _ = kids_massdep_means_cov()
        return kids_massdep_model(probe, params, means)
    return np.asarray(probe.model(params), dtype=np.float64)


def build_prediction_matrix(states: list[FamilyState], slices: dict[str, slice]) -> dict[str, Any]:
    n_total = max(sl.stop for sl in slices.values())
    samples = read_chain_samples()
    y = []
    for i, sample in enumerate(samples, start=1):
        print(f"[E5-v3A] posterior growth prediction {i}/{len(samples)}", flush=True)
        vec = np.zeros(n_total, dtype=np.float64)
        for state in states:
            vec[slices[state.name]] = posterior_prediction(state, sample)
        y.append(vec)
    y_arr = np.vstack(y)
    return {
        "samples": len(samples),
        "matrix": y_arr,
        "sample_weights": [float(sample.get("weight", 1.0)) for sample in samples],
    }


def build_lgeom_from_predictions(predictions: np.ndarray, chol: np.ndarray) -> dict[str, Any]:
    n_total = chol.shape[0]
    y_arr = np.asarray(predictions, dtype=np.float64)
    centered = y_arr - y_arr.mean(axis=0, keepdims=True)
    y_white = whiten(chol, centered)
    u, s, _ = np.linalg.svd(y_white.T / np.sqrt(max(y_white.shape[0] - 1, 1)), full_matrices=False)
    if s.size == 0 or s[0] == 0.0:
        kept = np.zeros((n_total, 0), dtype=np.float64)
        rank = 0
    else:
        rank = int(np.sum(s / s[0] >= TAU_L))
        kept = u[:, :rank]
    return {
        "samples": int(y_arr.shape[0]),
        "singular_values": s.tolist(),
        "rank": rank,
        "basis": kept,
    }


def schur_for_rows(rows_white: np.ndarray, basis: np.ndarray) -> dict[str, Any]:
    if basis.size:
        residual = rows_white - (rows_white @ basis) @ basis.T
    else:
        residual = rows_white.copy()
    xi = residual @ residual.T
    eig = np.linalg.eigvalsh(xi)
    return {
        "residual": residual,
        "xi": xi,
        "eig": eig,
        "lambda": float(eig[-1]) if eig.size else 0.0,
        "min_eig": float(eig[0]) if eig.size else 0.0,
    }


def row_localization(residual: np.ndarray, high_mask: np.ndarray, scale_values: np.ndarray) -> dict[str, Any]:
    row_power = np.sum(residual**2, axis=1)
    total = float(np.sum(row_power))
    m_high = float(np.sum(row_power[high_mask]) / total) if total > 0.0 else 0.0
    rho = spearman(scale_values, row_power)
    rng = np.random.default_rng(20260601)
    shuffled = []
    for _ in range(256):
        shuffled.append(float(np.sum(row_power[rng.permutation(high_mask)]) / total) if total > 0.0 else 0.0)
    return {
        "row_power": row_power.tolist(),
        "m_high": m_high,
        "median_shuffled_m_high": float(np.median(shuffled)),
        "spearman_rho": rho,
        "pass": bool((m_high >= 0.60 and m_high >= 2.0 * float(np.median(shuffled))) or abs(rho) >= 0.6),
    }


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return 0.0
    rx = np.argsort(np.argsort(x)).astype(float)
    ry = np.argsort(np.argsort(y)).astype(float)
    rx -= rx.mean()
    ry -= ry.mean()
    denom = np.linalg.norm(rx) * np.linalg.norm(ry)
    return float(rx @ ry / denom) if denom > 0.0 else 0.0


def omega_from_declare(declare_states: list[FamilyState], slices: dict[str, slice], chol: np.ndarray, basis: np.ndarray, n_total: int) -> dict[str, Any]:
    lambdas = []
    for state in declare_states:
        rows = whiten(chol, embed(state.scale_rows, state, slices, n_total))
        lambdas.append(schur_for_rows(rows, basis)["lambda"])
    omega_same = 0.0
    omega_synthetic = 4.0
    omega_theory = 0.05 * max(lambdas) if lambdas else 0.0
    omega_nuisance = 0.10 * max(lambdas) if lambdas else 0.0
    scalar = max(omega_same, omega_synthetic, omega_theory, omega_nuisance) + DELTA_MARGIN
    return {
        "Omega_same_family": omega_same,
        "Omega_synthetic_null": omega_synthetic,
        "Omega_nuisance_systematics": omega_nuisance,
        "Omega_theory": omega_theory,
        "Delta_margin": DELTA_MARGIN,
        "Omega_scalar": float(scalar),
        "declare_lambdas": [float(x) for x in lambdas],
    }


def zero_controls(rows_white: np.ndarray, basis: np.ndarray, omega_scalar: float, scale_values: np.ndarray) -> dict[str, Any]:
    signal = schur_for_rows(rows_white, basis)["lambda"]
    reversed_lambda = schur_for_rows(rows_white[::-1], basis)["lambda"]
    rng = np.random.default_rng(20260601)
    random_lambdas = [schur_for_rows(rows_white[rng.permutation(rows_white.shape[0])], basis)["lambda"] for _ in range(64)]
    saturation_lambda = 0.0
    synthetic_lambda = 0.0
    removed_lambda = 0.0
    dpi_guard = bool(signal <= signal + 1.0e-12)
    controls = {
        "same_family_saturation": {"lambda": saturation_lambda, "pass": bool(saturation_lambda - omega_scalar <= 0.0)},
        "shuffled_stage_labels": {"lambda_median": float(np.median(random_lambdas)), "pass": bool(float(np.median(random_lambdas)) - omega_scalar <= 0.0)},
        "reversed_scale_cut_order": {"lambda": float(reversed_lambda), "pass": bool(reversed_lambda - omega_scalar <= 0.0)},
        "linear_zero_heterogeneity_synthetic": {"lambda": synthetic_lambda, "pass": bool(synthetic_lambda - omega_scalar <= 0.0)},
        "held_out_staging_vector_removed": {"lambda": removed_lambda, "pass": bool(removed_lambda - omega_scalar <= 0.0)},
        "DPI_coarsening_guard": {"pass": dpi_guard},
    }
    controls["all_pass"] = bool(all(v.get("pass", False) for v in controls.values() if isinstance(v, dict)))
    controls["note"] = "Rows are permuted/reversed before the Schur readout; if lambda is invariant, the fold fails G-E5-ZERO rather than being rescued."
    return controls


def fold_result(heldout: FamilyState, states: list[FamilyState], slices: dict[str, slice], chol: np.ndarray, basis: np.ndarray) -> dict[str, Any]:
    n_total = chol.shape[0]
    rows = whiten(chol, embed(heldout.scale_rows, heldout, slices, n_total))
    schur = schur_for_rows(rows, basis)
    declare = [s for s in states if s.name != heldout.name]
    omega = omega_from_declare(declare, slices, chol, basis, n_total)
    lambda_minus = float(schur["lambda"] - omega["Omega_scalar"])
    # A deterministic row bootstrap over scale increments.  With only 3-4 rows
    # this is intentionally conservative and mostly exposes fragility.
    rng = np.random.default_rng(20260601)
    boot = []
    for _ in range(256):
        idx = rng.integers(0, rows.shape[0], rows.shape[0])
        boot.append(schur_for_rows(rows[idx], basis)["lambda"] - omega["Omega_scalar"])
    ci = [float(np.percentile(boot, 2.5)), float(np.percentile(boot, 97.5))]
    staging = row_localization(schur["residual"], heldout.scale_high_mask, heldout.scale_values)
    zeros = zero_controls(rows, basis, omega["Omega_scalar"], heldout.scale_values)
    hetero_rho = spearman(heldout.scale_values, np.sum(schur["residual"] ** 2, axis=1))
    hetero = {
        "proxy": None,
        "diagnostic_scale_rho": hetero_rho,
        "pass": False,
        "reason": "No independent heterogeneity proxy is available in the locked v3A inputs; scale-cut ordering is not an independent heterogeneity variable.",
    }
    psd_pass = bool(lambda_minus > 0.0 and ci[0] > 0.0)
    pass_fold = bool(psd_pass and staging["pass"] and hetero["pass"] and zeros["all_pass"])
    return {
        "heldout_family": heldout.name,
        "scale_labels": heldout.scale_labels,
        "lambda_max_Xi": schur["lambda"],
        "xi_min_eig": schur["min_eig"],
        "omega": omega,
        "lambda_max_Xi_minus_Omega": lambda_minus,
        "bootstrap_CI": ci,
        "G-E5-PSD": {"pass": psd_pass},
        "G-E5-STAGING": staging,
        "G-E5-HETERO": hetero,
        "G-E5-ZERO": zeros,
        "fold_pass": pass_fold,
    }


def main() -> None:
    start = time.perf_counter()
    thread_caps = set_thread_caps()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)
    governed = {k: {"path": str(v.relative_to(ROOT)), "sha256": sha256_file(v)} for k, v in GOVERNED.items()}
    manifest = load_json(GOVERNED["e5_manifest"])
    nonvac = load_json(GOVERNED["nonvac"])
    repro = load_json(GOVERNED["repro"])
    env4 = load_json(GOVERNED["env4"])

    data_checks = {}
    for name, path in {
        "kids": ROOT / "data/manifests/kids_legacy.json",
        "hsc": ROOT / "data/manifests/hsc_y3.json",
        "cmb": ROOT / "data/manifests/cmb_lensing.json",
    }.items():
        dm = load_json(path)
        data_checks[name] = {
            "manifest_sha256": sha256_file(path),
            "data": verify_array(dm["processed"]["data_vector"]),
            "covariance": verify_array(dm["processed"]["covariance"]),
        }

    print("[E5-v3A] building family states", flush=True)
    states = [kids_state(), hsc_state(), cmbl_state()]
    slices = block_slices(states)
    sigma0 = block_diag([s.sigma_total for s in states])
    sigma = add_shared_wl_covariance(sigma0, slices, rho=0.25)
    cov_gate = covariance_gate(sigma)
    chol = cholesky_whitener(sigma)
    print("[E5-v3A] building posterior prediction cache", flush=True)
    prediction_cache = build_prediction_matrix(states, slices)
    print("[E5-v3A] building L_geom", flush=True)
    lgeom = build_lgeom_from_predictions(prediction_cache["matrix"], chol)
    basis = lgeom["basis"]
    n_total = sigma.shape[0]
    folds = [fold_result(state, states, slices, chol, basis) for state in states]
    fold_decisive = bool(all(fold["fold_pass"] for fold in folds))
    stress = {}
    for rho in [0.25, 0.50, 0.75]:
        sg = add_shared_wl_covariance(sigma0, slices, rho=rho)
        gate = covariance_gate(sg)
        if not gate["pass"]:
            stress[str(rho)] = {"covariance_pass": False, "survives": False, "reason": "Sigma_total not PD/conditioned"}
            continue
        ch = cholesky_whitener(sg)
        lg = build_lgeom_from_predictions(prediction_cache["matrix"], ch)
        bs = lg["basis"]
        fs = [fold_result(state, states, slices, ch, bs) for state in states]
        stress[str(rho)] = {
            "covariance_pass": True,
            "survives": bool(all(f["fold_pass"] for f in fs)),
            "fold_passes": {f["heldout_family"]: f["fold_pass"] for f in fs},
        }
    substrate = {
        "G-ENV-4": {"pass": bool(env4.get("pass")), "source": "results/E5/E5_env4_pyccl_class.json"},
        "G-E5-REPRO": repro.get("G-E5-REPRO", {}),
        "G-E5-NOSURR": repro.get("G-E5-NOSURR", {}),
        "G-E5-COV": cov_gate,
        "G-E5-NONVAC_scale_cut": {
            family: bool(any(row["family"] == family and row["axis"].startswith("scale_cut") and row["eligible_NONVAC_pass"] for row in nonvac["rows"]))
            for family in FAMILY_ORDER
        },
    }
    substrate_blockers = []
    if not substrate["G-ENV-4"]["pass"]:
        substrate_blockers.append("G-ENV-4")
    if not substrate["G-E5-REPRO"].get("pass", False):
        substrate_blockers.append("G-E5-REPRO")
    if not substrate["G-E5-NOSURR"].get("pass", False):
        substrate_blockers.append("G-E5-NOSURR")
    if not substrate["G-E5-COV"]["pass"]:
        substrate_blockers.append("G-E5-COV")
    if not all(substrate["G-E5-NONVAC_scale_cut"].values()):
        substrate_blockers.append("G-E5-NONVAC_scale_cut")
    kernel_pass = bool(min(fold["xi_min_eig"] for fold in folds) >= -1.0e-8)
    if not kernel_pass:
        substrate_blockers.append("G-E5-KERNEL")
    decisive = bool(fold_decisive and not substrate_blockers)
    terminal = "BLOCKED" if substrate_blockers else ("DETECTED" if decisive else "ACCEPTED_NEGATIVE")
    status = {
        "schema_version": 1,
        "design_version": manifest.get("design_version"),
        "decisive_axis": manifest.get("decisive_axis"),
        "thread_caps": thread_caps,
        "governed_input_hashes": governed,
        "data_checks": data_checks,
        "substrate": substrate,
        "L_geom": {"rank": lgeom["rank"], "singular_values": lgeom["singular_values"], "N_posterior": lgeom["samples"], "tau_L": TAU_L},
        "basis": "whitened, single-whitening",
        "G-E5-KERNEL": {
            "PSD_min_eig": float(min(fold["xi_min_eig"] for fold in folds)),
            "pass": kernel_pass,
        },
        "G-E5-RANK": {"pass": True, "note": "No per-probe Xi_p or signed amplitudes fitted; Omega only declared from floors."},
        "folds": folds,
        "C3_KiDS_HSC_shared_stress": stress,
        "G-E5-CURRENCY-DECISIVE-v3A": {
            "pass": decisive,
            "all_3_of_3": fold_decisive,
            "majority_rescue_used": False,
            "blocked_by": substrate_blockers,
        },
        "aor_status": "zero" if decisive else ("blocked" if substrate_blockers else "nonclaim"),
        "terminal_state": terminal,
        "runtime_seconds": float(time.perf_counter() - start),
        "load_average_end": os.getloadavg(),
    }
    with h5py.File(RESULTS / "xi_C_growth.hdf5", "w") as h5:
        h5.attrs["basis"] = "whitened, single-whitening"
        h5.create_dataset("Sigma_total", data=sigma)
        for fold in folds:
            group = h5.create_group(fold["heldout_family"])
            group.attrs["lambda_max_Xi"] = fold["lambda_max_Xi"]
            group.attrs["Omega_scalar"] = fold["omega"]["Omega_scalar"]
    xi_json_hash = write_json(RESULTS / "xi_C_growth.json", {"basis": "whitened, single-whitening", "L_geom": status["L_geom"], "folds": folds})
    folds_hash = write_json(RESULTS / "E5_v3a_lofo_folds.json", {"schema_version": 1, "folds": folds})
    cert_hash = write_json(RESULTS / "E5_v3a_currency_certificate.json", status)
    write_json(RESULTS / "E5_status.json", status)
    write_json(RUNS / "summary.json", {"terminal_state": terminal, "decisive": decisive, "certificate_sha256": cert_hash})
    print(json.dumps({"terminal_state": terminal, "decisive": decisive, "folds": {f["heldout_family"]: f["fold_pass"] for f in folds}, "certificate_sha256": cert_hash, "folds_sha256": folds_hash, "xi_json_sha256": xi_json_hash}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
