#!/usr/bin/env python3
"""Characterize E5 closure currency as a shadow price.

This runner does not evaluate a pass/fail certificate. It conditions the
combined covariance with a declared eigen-quotient, builds the same
single-whitened Schur carrier used by E5-v3A, then records whether the closure
amplitude emerges with the scale/nonlinearity budget and whether it tracks an
independent nonlinear-power ratio.
"""

from __future__ import annotations

import csv
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

for _key in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "CCL_NUM_THREADS",
):
    os.environ.setdefault(_key, "1")

import matplotlib.pyplot as plt
import numpy as np

from sbt_cosmo.growth.power import build_ccl_cosmology
from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe
from scripts.e5_v3_nonvac import (
    CMBL_MAP,
    HSC_MAP,
    KIDS_MAP,
    ROOT,
    SCALE_CUT_GRIDS,
    kids_massdep_means_cov,
    kids_massdep_model,
)
from scripts.e5_v3a_certificate import (
    FAMILY_ORDER,
    add_shared_wl_covariance,
    block_diag,
    block_slices,
    cmbl_state,
    hsc_state,
    kids_state,
)

RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "E5_shadowprice"
REL_EIGEN_FLOOR = float(os.environ.get("E5_SHADOW_REL_EIGEN_FLOOR", "1e-8"))
N_POSTERIOR = int(os.environ.get("E5_SHADOW_NPOST", "4"))
TAU_L = 1.0e-3
DELTA_MARGIN = 0.10
BOOTSTRAPS = 256

GOVERNED = {
    "e5_manifest": ROOT / "data/manifests/e5_growth_currency_inputs.json",
    "carrier": ROOT / "plan/E5_CARRIER_REALIZATION.md",
    "design_freeze": ROOT / "plan/E5_DESIGN_FREEZE.md",
    "gates": ROOT / "plan/07-pass-fail-gates.md",
    "nonvac": ROOT / "results/E5/E5_v3_nonvac.json",
    "v3a_certificate": ROOT / "results/E5/E5_v3a_currency_certificate.json",
}


@dataclass(frozen=True)
class EigWhitener:
    vectors: np.ndarray
    values: np.ndarray
    raw_eigenvalues: np.ndarray
    relative_floor: float

    def whiten(self, arr: np.ndarray) -> np.ndarray:
        data = np.asarray(arr, dtype=np.float64)
        if data.ndim == 1:
            return (data @ self.vectors) / np.sqrt(self.values)
        return (data @ self.vectors) / np.sqrt(self.values)[None, :]

    def metadata(self) -> dict[str, Any]:
        positive = self.raw_eigenvalues[self.raw_eigenvalues > 0.0]
        raw_cond = float(positive[-1] / positive[0]) if positive.size else float("inf")
        conditioned_cond = float(self.values[-1] / self.values[0]) if self.values.size else float("inf")
        return {
            "method": "eigen_quotient",
            "relative_eigenvalue_floor": self.relative_floor,
            "input_dimension": int(self.raw_eigenvalues.size),
            "retained_rank": int(self.values.size),
            "dropped_rank": int(self.raw_eigenvalues.size - self.values.size),
            "raw_lambda_min": float(self.raw_eigenvalues[0]),
            "raw_lambda_max": float(self.raw_eigenvalues[-1]),
            "raw_condition_number_positive": raw_cond,
            "conditioned_lambda_min": float(self.values[0]) if self.values.size else None,
            "conditioned_lambda_max": float(self.values[-1]) if self.values.size else None,
            "conditioned_condition_number": conditioned_cond,
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


def covariance_quotient(sigma: np.ndarray) -> EigWhitener:
    eig, vec = np.linalg.eigh(np.asarray(sigma, dtype=np.float64))
    order = np.argsort(eig)
    eig = eig[order]
    vec = vec[:, order]
    max_eig = float(eig[-1])
    keep = (eig > 0.0) & (eig / max_eig >= REL_EIGEN_FLOOR)
    if not np.any(keep):
        raise ValueError("covariance quotient retained no modes")
    return EigWhitener(vectors=vec[:, keep], values=eig[keep], raw_eigenvalues=eig, relative_floor=REL_EIGEN_FLOOR)


def read_shadow_samples(n_samples: int) -> tuple[list[dict[str, float]], list[int]]:
    path = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
    with path.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    data = np.loadtxt(path)
    cols = {name: i for i, name in enumerate(header)}
    weights = data[:, cols["weight"]] if "weight" in cols else np.ones(data.shape[0])
    weights = np.clip(weights.astype(np.float64), 0.0, None)
    weights = weights / weights.sum() if weights.sum() > 0.0 else np.full(data.shape[0], 1.0 / data.shape[0])
    rng = np.random.default_rng(20260601)
    replace = n_samples > data.shape[0]
    indices = rng.choice(data.shape[0], size=n_samples, replace=replace, p=weights)
    samples = []
    for idx in indices:
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
                "weight": float(row[cols["weight"]]) if "weight" in cols else 1.0,
            }
        )
    return samples, [int(i) for i in indices]


def params_for_family(sample: dict[str, float], family: str) -> dict[str, Any]:
    base = {k: v for k, v in sample.items() if k != "weight"}
    if family == "HSC-Y3":
        return {**base, **{k: v for k, v in HSC_MAP.items() if k not in {"Omega_m", "omega_b", "omega_cdm", "h", "n_s", "S8"}}}
    if family == "KiDS-Legacy":
        return {**base, "dz": [0.0] * 6, "m": [0.0] * 6}
    return base


def build_probe_cache() -> dict[str, Any]:
    return {
        "HSC-Y3": build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "original"}),
        "KiDS-Legacy": build_weak_lensing_probe({"probe_id": "kids_legacy_shear"}),
        "CMB-lensing": build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"}),
        "kids_massdep_means": kids_massdep_means_cov()[0],
    }


def posterior_prediction_cached(state: Any, sample: dict[str, float], probe_cache: dict[str, Any]) -> np.ndarray:
    params = params_for_family(sample, state.name)
    if state.name == "KiDS-Legacy":
        return kids_massdep_model(probe_cache[state.name], params, probe_cache["kids_massdep_means"])
    return np.asarray(probe_cache[state.name].model(params), dtype=np.float64)


def build_prediction_matrix(states: list[Any], slices: dict[str, slice], n_total: int) -> dict[str, Any]:
    RUNS.mkdir(parents=True, exist_ok=True)
    cache = RUNS / f"prediction_cache_shadow_v2_N{N_POSTERIOR}.npz"
    if cache.is_file():
        data = np.load(cache)
        matrix = np.asarray(data["matrix"], dtype=np.float64)
        if matrix.shape == (N_POSTERIOR, n_total):
            print(f"[shadowprice] using cached posterior predictions {cache}", flush=True)
            return {
                "matrix": matrix,
                "cache_path": str(cache.relative_to(ROOT)),
                "from_cache": True,
                "sample_indices": data["sample_indices"].astype(int).tolist(),
                "timings_seconds": data["timings_seconds"].astype(float).tolist(),
            }
    samples, sample_indices = read_shadow_samples(N_POSTERIOR)
    probe_cache = build_probe_cache()
    rows = []
    timings = []
    for i, sample in enumerate(samples, start=1):
        t0 = time.perf_counter()
        print(f"[shadowprice] posterior growth prediction {i}/{len(samples)}", flush=True)
        vec = np.zeros(n_total, dtype=np.float64)
        for state in states:
            vec[slices[state.name]] = posterior_prediction_cached(state, sample, probe_cache)
        rows.append(vec)
        timings.append(float(time.perf_counter() - t0))
    matrix = np.vstack(rows)
    np.savez_compressed(cache, matrix=matrix, sample_indices=np.asarray(sample_indices, dtype=np.int64), timings_seconds=np.asarray(timings, dtype=np.float64))
    return {
        "matrix": matrix,
        "cache_path": str(cache.relative_to(ROOT)),
        "from_cache": False,
        "sample_indices": sample_indices,
        "timings_seconds": timings,
    }


def build_lgeom(predictions: np.ndarray, whitener: EigWhitener) -> dict[str, Any]:
    centered = predictions - predictions.mean(axis=0, keepdims=True)
    y_white = whitener.whiten(centered)
    u, s, _ = np.linalg.svd(y_white.T / np.sqrt(max(y_white.shape[0] - 1, 1)), full_matrices=False)
    rank = int(np.sum(s / s[0] >= TAU_L)) if s.size and s[0] > 0.0 else 0
    return {
        "rank": rank,
        "basis": u[:, :rank] if rank else np.zeros((y_white.shape[1], 0), dtype=np.float64),
        "singular_values": s.tolist(),
        "N_posterior": int(predictions.shape[0]),
        "tau_L": TAU_L,
    }


def embed_rows(rows: np.ndarray, state: Any, slices: dict[str, slice], n_total: int) -> np.ndarray:
    out = np.zeros((rows.shape[0], n_total), dtype=np.float64)
    out[:, slices[state.name]] = rows
    return out


def schur(rows_white: np.ndarray, basis: np.ndarray) -> dict[str, Any]:
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
        "lambda_raw": float(eig[-1]) if eig.size else 0.0,
        "min_eig": float(eig[0]) if eig.size else 0.0,
    }


def omega_budget(lambda_raw: float, n_rows: int) -> dict[str, float]:
    omega_same = 0.0
    omega_synthetic = 4.0 * max(1.0, np.sqrt(max(n_rows, 1)) / 2.0)
    omega_theory = 0.05 * max(lambda_raw, 0.0)
    omega_nuisance = 0.10 * max(lambda_raw, 0.0)
    scalar = max(omega_same, omega_synthetic, omega_theory, omega_nuisance) + DELTA_MARGIN
    return {
        "Omega_same_family": float(omega_same),
        "Omega_synthetic_null": float(omega_synthetic),
        "Omega_theory": float(omega_theory),
        "Omega_nuisance_systematics": float(omega_nuisance),
        "Delta_margin": float(DELTA_MARGIN),
        "Omega_scalar": float(scalar),
    }


def lambda_for_rows(rows_white: np.ndarray, basis: np.ndarray) -> dict[str, Any]:
    out = schur(rows_white, basis)
    omega = omega_budget(out["lambda_raw"], rows_white.shape[0])
    return {
        "lambda_raw": out["lambda_raw"],
        "lambda_minus_omega": float(out["lambda_raw"] - omega["Omega_scalar"]),
        "omega": omega,
        "min_eig": out["min_eig"],
        "residual": out["residual"],
    }


def bootstrap_lambda(rows_white: np.ndarray, basis: np.ndarray) -> list[float]:
    rng = np.random.default_rng(20260601)
    values = []
    for _ in range(BOOTSTRAPS):
        idx = rng.integers(0, rows_white.shape[0], rows_white.shape[0])
        values.append(lambda_for_rows(rows_white[idx], basis)["lambda_minus_omega"])
    return values


def row_entries(states: list[Any], slices: dict[str, slice], whitener: EigWhitener) -> list[dict[str, Any]]:
    n_total = max(sl.stop for sl in slices.values())
    entries: list[dict[str, Any]] = []
    for state in states:
        full = embed_rows(state.scale_rows, state, slices, n_total)
        white = whitener.whiten(full)
        for i, label in enumerate(state.scale_labels):
            entries.append(
                {
                    "family": state.name,
                    "label": label,
                    "stage_index": int(i + 1),
                    "scale_value": float(state.scale_values[i]),
                    "high_stage": bool(state.scale_high_mask[i]),
                    "row_white": white[i],
                }
            )
    return entries


def kids_effective_ell() -> dict[int, float]:
    from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

    probe = build_weak_lensing_probe({"probe_id": "kids_legacy_shear"})
    ell, wn = probe._wn  # noqa: SLF001 - characterization uses the COSEBIs filter support.
    out = {}
    for mode in SCALE_CUT_GRIDS["KiDS-Legacy"][1:]:
        weights = np.abs(wn[int(mode) - 1])
        out[int(mode)] = float(ell[int(np.argmax(weights))])
    return out


def nonlinearity_ratio(family: str, scale_value: float) -> dict[str, float]:
    import pyccl as ccl

    if family == "HSC-Y3":
        params = HSC_MAP
        z_eff = 0.70
        ell_eff = scale_value
    elif family == "CMB-lensing":
        params = CMBL_MAP
        z_eff = 2.0
        ell_eff = scale_value
    else:
        params = KIDS_MAP
        z_eff = 0.60
        ell_eff = kids_effective_ell().get(int(scale_value), 1000.0)
    cosmo = build_ccl_cosmology(params)
    a = 1.0 / (1.0 + z_eff)
    chi = float(ccl.comoving_radial_distance(cosmo, a))
    k = float((ell_eff + 0.5) / chi)
    p_lin = float(ccl.linear_matter_power(cosmo, k, a))
    p_nl = float(ccl.nonlin_matter_power(cosmo, k, a))
    return {"z_eff": z_eff, "ell_eff": float(ell_eff), "k_1_per_Mpc": k, "R_nl_over_lin": p_nl / p_lin}


def ranks(x: np.ndarray) -> np.ndarray:
    order = np.argsort(x)
    out = np.empty_like(order, dtype=np.float64)
    out[order] = np.arange(x.size, dtype=np.float64)
    return out


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    x_arr = np.asarray(x, dtype=np.float64)
    y_arr = np.asarray(y, dtype=np.float64)
    if x_arr.size < 2 or y_arr.size < 2:
        return 0.0
    rx = ranks(x_arr)
    ry = ranks(y_arr)
    rx -= rx.mean()
    ry -= ry.mean()
    denom = float(np.linalg.norm(rx) * np.linalg.norm(ry))
    return float(rx @ ry / denom) if denom > 0.0 else 0.0


def spearman_ci(x: list[float], y: list[float]) -> dict[str, Any]:
    x_arr = np.asarray(x, dtype=np.float64)
    y_arr = np.asarray(y, dtype=np.float64)
    rho = spearman(x_arr, y_arr)
    rng = np.random.default_rng(20260601)
    boot = []
    if x_arr.size >= 3:
        for _ in range(BOOTSTRAPS):
            idx = rng.integers(0, x_arr.size, x_arr.size)
            boot.append(spearman(x_arr[idx], y_arr[idx]))
    return {
        "spearman": float(rho),
        "bootstrap_CI": [float(np.percentile(boot, 2.5)), float(np.percentile(boot, 97.5))] if boot else None,
        "n": int(x_arr.size),
    }


def emergence_curve(entries: list[dict[str, Any]], basis: np.ndarray, family: str | None = None) -> list[dict[str, Any]]:
    subset = [e for e in entries if family is None or e["family"] == family]
    if not subset:
        return []
    max_stage = max(e["stage_index"] for e in subset)
    curve = []
    for stage in range(1, max_stage + 1):
        rows = np.vstack([e["row_white"] for e in subset if e["stage_index"] <= stage])
        if rows.size == 0:
            continue
        value = lambda_for_rows(rows, basis)
        boot = bootstrap_lambda(rows, basis)
        scale_values = [e["scale_value"] for e in subset if e["stage_index"] <= stage]
        curve.append(
            {
                "family": family or "pooled",
                "stage": int(stage),
                "n_rows": int(rows.shape[0]),
                "scale_max": float(max(scale_values)),
                "lambda_raw": value["lambda_raw"],
                "lambda_minus_omega": value["lambda_minus_omega"],
                "lambda_minus_omega_CI": [float(np.percentile(boot, 2.5)), float(np.percentile(boot, 97.5))],
                "omega": value["omega"],
            }
        )
    return curve


def residual_power(entries: list[dict[str, Any]], basis: np.ndarray, family: str | None = None) -> dict[str, Any]:
    subset = [e for e in entries if family is None or e["family"] == family]
    rows = np.vstack([e["row_white"] for e in subset])
    value = lambda_for_rows(rows, basis)
    power = np.sum(value["residual"] ** 2, axis=1)
    for entry, p in zip(subset, power, strict=True):
        entry["residual_power"] = float(p)
    high = np.asarray([e["high_stage"] for e in subset], dtype=bool)
    m_high = float(power[high].sum() / power.sum()) if power.sum() > 0.0 and np.any(high) else 0.0
    return {
        "lambda_minus_omega": value["lambda_minus_omega"],
        "lambda_raw": value["lambda_raw"],
        "omega": value["omega"],
        "m_high": m_high,
        "n_rows": int(rows.shape[0]),
    }


def stage_scramble_control(entries: list[dict[str, Any]], basis: np.ndarray, family: str | None = None) -> dict[str, Any]:
    subset = [e for e in entries if family is None or e["family"] == family]
    true_curve = emergence_curve(entries, basis, family)
    true_rho = spearman(np.asarray([r["stage"] for r in true_curve], dtype=float), np.asarray([r["lambda_minus_omega"] for r in true_curve], dtype=float))
    rng = np.random.default_rng(20260601)
    random_rhos = []
    random_final = []
    for _ in range(BOOTSTRAPS):
        perm = rng.permutation([e["stage_index"] for e in subset])
        synthetic = [{**e, "stage_index": int(p)} for e, p in zip(subset, perm, strict=True)]
        curve = emergence_curve(synthetic, basis, None)
        random_rhos.append(spearman(np.asarray([r["stage"] for r in curve], dtype=float), np.asarray([r["lambda_minus_omega"] for r in curve], dtype=float)))
        random_final.append(curve[-1]["lambda_minus_omega"])
    return {
        "true_emergence_spearman": float(true_rho),
        "scrambled_median_spearman": float(np.median(random_rhos)),
        "scrambled_CI_spearman": [float(np.percentile(random_rhos, 2.5)), float(np.percentile(random_rhos, 97.5))],
        "scrambled_median_final_lambda": float(np.median(random_final)),
        "p_abs_scrambled_ge_true": float(np.mean(np.abs(random_rhos) >= abs(true_rho))),
    }


def dpi_control(entries: list[dict[str, Any]], basis: np.ndarray, family: str | None = None) -> dict[str, Any]:
    subset = [e for e in entries if family is None or e["family"] == family]
    rows = [e["row_white"] for e in subset]
    full = lambda_for_rows(np.vstack(rows), basis)["lambda_minus_omega"]
    coarse_rows = []
    for i in range(0, len(rows), 2):
        if i + 1 < len(rows):
            coarse_rows.append(rows[i] + rows[i + 1])
        else:
            coarse_rows.append(rows[i])
    coarse = lambda_for_rows(np.vstack(coarse_rows), basis)["lambda_minus_omega"]
    return {
        "full_lambda": float(full),
        "coarse_lambda": float(coarse),
        "margin_coarse_minus_full": float(coarse - full),
        "DPI_not_increased": bool(coarse <= full + 1.0e-10),
    }


def write_curve_csv(path: Path, curves: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(
            fh,
            fieldnames=["family", "stage", "n_rows", "scale_max", "lambda_raw", "Omega_scalar", "lambda_minus_omega", "ci_low", "ci_high"],
        )
        writer.writeheader()
        for row in curves:
            writer.writerow(
                {
                    "family": row["family"],
                    "stage": row["stage"],
                    "n_rows": row["n_rows"],
                    "scale_max": row["scale_max"],
                    "lambda_raw": row["lambda_raw"],
                    "Omega_scalar": row["omega"]["Omega_scalar"],
                    "lambda_minus_omega": row["lambda_minus_omega"],
                    "ci_low": row["lambda_minus_omega_CI"][0],
                    "ci_high": row["lambda_minus_omega_CI"][1],
                }
            )


def write_curve_plot(path: Path, curves: list[dict[str, Any]]) -> None:
    families = sorted({row["family"] for row in curves})
    plt.figure(figsize=(8, 5))
    for family in families:
        rows = [row for row in curves if row["family"] == family]
        x = [row["stage"] for row in rows]
        y = [row["lambda_minus_omega"] for row in rows]
        lo = [row["lambda_minus_omega_CI"][0] for row in rows]
        hi = [row["lambda_minus_omega_CI"][1] for row in rows]
        plt.plot(x, y, marker="o", label=family)
        plt.fill_between(x, lo, hi, alpha=0.15)
    plt.axhline(0.0, color="black", linewidth=0.8)
    plt.xlabel("cumulative scale stage")
    plt.ylabel("lambda_max(Xi_C) - Omega")
    plt.legend()
    plt.tight_layout()
    path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(path, dpi=160)
    plt.close()


def main() -> None:
    start = time.perf_counter()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)
    governed = {name: {"path": str(path.relative_to(ROOT)), "sha256": sha256_file(path)} for name, path in GOVERNED.items()}

    print("[shadowprice] building family states", flush=True)
    states = [kids_state(), hsc_state(), cmbl_state()]
    slices = block_slices(states)
    sigma0 = block_diag([state.sigma_total for state in states])
    sigma = add_shared_wl_covariance(sigma0, slices, rho=0.25)
    whitener = covariance_quotient(sigma)
    n_total = sigma.shape[0]

    print("[shadowprice] building posterior prediction matrix", flush=True)
    prediction_info = build_prediction_matrix(states, slices, n_total)
    lgeom = build_lgeom(prediction_info["matrix"], whitener)
    basis = lgeom["basis"]
    entries = row_entries(states, slices, whitener)

    nl_cache: dict[tuple[str, float], dict[str, float]] = {}
    for entry in entries:
        key = (entry["family"], entry["scale_value"])
        if key not in nl_cache:
            nl_cache[key] = nonlinearity_ratio(*key)
        entry.update(nl_cache[key])

    curves: list[dict[str, Any]] = []
    curves.extend(emergence_curve(entries, basis, None))
    for family in FAMILY_ORDER:
        curves.extend(emergence_curve(entries, basis, family))

    families = ["pooled", *FAMILY_ORDER]
    emergence = {}
    nonlinear = {}
    controls = {}
    residuals = {}
    for family in families:
        fam = None if family == "pooled" else family
        curve = [row for row in curves if row["family"] == family]
        stages = [row["stage"] for row in curve]
        lambdas = [row["lambda_minus_omega"] for row in curve]
        slack = next((row for row in curve if row["lambda_minus_omega_CI"][0] <= 0.0 <= row["lambda_minus_omega_CI"][1] or row["lambda_minus_omega"] <= 0.0), None)
        emergence[family] = {
            "spearman_stage_lambda": spearman_ci(stages, lambdas),
            "slope_last_minus_first": float(lambdas[-1] - lambdas[0]) if len(lambdas) >= 2 else 0.0,
            "slack_point": slack,
        }
        residuals[family] = residual_power(entries, basis, fam)
        subset = [e for e in entries if fam is None or e["family"] == fam]
        nonlinear[family] = {
            "residual_power_vs_R": spearman_ci([e["R_nl_over_lin"] for e in subset], [e["residual_power"] for e in subset]),
            "lambda_vs_mean_R": spearman_ci(
                [float(np.mean([e["R_nl_over_lin"] for e in subset if e["stage_index"] <= row["stage"]])) for row in curve],
                lambdas,
            ),
        }
        controls[family] = {
            "stage_scramble": stage_scramble_control(entries, basis, fam),
            "DPI": dpi_control(entries, basis, fam),
            "m_high": residuals[family]["m_high"],
        }

    rows_json = [
        {k: v for k, v in entry.items() if k != "row_white"}
        for entry in entries
    ]
    output = {
        "schema_version": 1,
        "analysis_type": "shadow_price_characterization_no_pass_fail",
        "governed_input_hashes": governed,
        "thread_caps": {key: os.environ.get(key) for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "CCL_NUM_THREADS")},
        "covariance_conditioning": whitener.metadata(),
        "Sigma_total_shared_rho_KH": 0.25,
        "L_geom": {k: v for k, v in lgeom.items() if k != "basis"},
        "prediction_profile": {
            "cache_path": prediction_info["cache_path"],
            "from_cache": prediction_info["from_cache"],
            "N_post": int(prediction_info["matrix"].shape[0]),
            "sample_indices_hash": hashlib.sha256(np.asarray(prediction_info["sample_indices"], dtype=np.int64).tobytes()).hexdigest(),
            "timings_seconds": prediction_info["timings_seconds"],
            "median_seconds_per_sample": float(np.median(prediction_info["timings_seconds"])) if prediction_info["timings_seconds"] else None,
            "max_seconds_per_sample": float(np.max(prediction_info["timings_seconds"])) if prediction_info["timings_seconds"] else None,
        },
        "kernel": {
            "basis": "whitened eigen-quotient, single-whitening",
            "min_Xi_eig_all_rows": lambda_for_rows(np.vstack([e["row_white"] for e in entries]), basis)["min_eig"],
        },
        "row_table": rows_json,
        "emergence": emergence,
        "nonlinearity_tracking": nonlinear,
        "controls": controls,
        "residuals": residuals,
        "runtime_seconds": float(time.perf_counter() - start),
        "interpretation_guardrail": "No decisive pass/fail, ACCEPTED_NEGATIVE, or BLOCKED verdict is emitted by this characterization runner.",
    }
    json_hash = write_json(RESULTS / "E5_shadowprice.json", output)
    write_curve_csv(RESULTS / "E5_shadowprice_lambda_curve.csv", curves)
    write_curve_plot(RESULTS / "E5_shadowprice_lambda_curve.png", curves)
    print(json.dumps({"output": "results/E5/E5_shadowprice.json", "sha256": json_hash, "runtime_seconds": output["runtime_seconds"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
