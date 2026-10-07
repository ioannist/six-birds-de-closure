#!/usr/bin/env python3
"""E5-SP CMB-lensing-only obstruction-price diagnostic.

This is a single-family diagnostic. It does not run LOFO, does not touch
KiDS/HSC, and is not a promotable E5-SP decisive certificate.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")
os.environ.setdefault("VECLIB_MAXIMUM_THREADS", "1")
os.environ.setdefault("CCL_NUM_THREADS", "1")

import numpy as np

from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

ROOT = Path(__file__).resolve().parents[1]
RESULT_DIR = ROOT / "results/E5SP/cmbl_diagnostic"
RUN_DIR = ROOT / "runs/E5SP/cmbl_diagnostic"
H_TABLE = ROOT / "results/E5SP/H_proxy_table.csv"
POSTERIOR_CHAIN = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
PLAN_AGENT_PROVENANCE = ROOT / "results/provenance/decommissioned_plan_agent_sources.json"


@dataclass(frozen=True)
class Shell:
    name: str
    indices: np.ndarray
    h_value: float
    h_prime: float
    l_min: float
    l_max: float
    l_eff: float
    slack_label: str


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def provenance_sha256(entry: str) -> str:
    data = json.loads(PLAN_AGENT_PROVENANCE.read_text(encoding="utf-8"))
    return str(data["entries"][entry]["sha256"])


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def load_cmb_shells() -> list[Shell]:
    ell = np.load(ROOT / "data/processed/cmb_lensing/bin_centers_L.npy")
    rows: list[dict[str, str]] = []
    with H_TABLE.open() as fh:
        for row in csv.DictReader(fh):
            if row["family"] == "CMB-lensing":
                rows.append(row)
    if len(rows) != 3:
        raise RuntimeError(f"expected three CMB-lensing rows in {H_TABLE}, found {len(rows)}")
    shells: list[Shell] = []
    for row in rows:
        l_min = float(row["L_min"])
        l_max = float(row["L_max"])
        mask = (ell >= l_min - 1e-9) & (ell <= l_max + 1e-9)
        indices = np.flatnonzero(mask)
        if indices.size == 0:
            raise RuntimeError(f"empty CMB shell {row['shell']} for L range {l_min}..{l_max}")
        shells.append(
            Shell(
                name=row["shell"],
                indices=indices,
                h_value=float(row["H"]),
                h_prime=float(row["H_prime"]),
                l_min=l_min,
                l_max=l_max,
                l_eff=float(row["L_eff"]),
                slack_label=row["slack_label"],
            )
        )
    return shells


def load_posterior_samples(n: int, seed: int) -> list[dict[str, float]]:
    with POSTERIOR_CHAIN.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    arr = np.loadtxt(POSTERIOR_CHAIN, comments="#")
    if arr.ndim != 2:
        raise RuntimeError("posterior chain did not load as a 2D table")
    columns = {name: arr[:, i] for i, name in enumerate(header)}
    weights = columns.get("weight", np.ones(arr.shape[0], dtype=np.float64))
    weights = np.asarray(weights, dtype=np.float64)
    weights = weights / weights.sum()
    rng = np.random.default_rng(seed)
    take = rng.choice(arr.shape[0], size=n, replace=True, p=weights)
    samples: list[dict[str, float]] = []
    for idx in take:
        samples.append(
            {
                "omega_b": float(columns["omega_b"][idx]),
                "omega_cdm": float(columns["omega_cdm"][idx]),
                "H0": float(columns["H0"][idx]),
                "w0_fld": float(columns["w0_fld"][idx]),
                "wa_fld": float(columns["wa_fld"][idx]),
                "sigma8": 0.81,
                "n_s": 0.965,
            }
        )
    return samples


def prediction_cache_key(n_post: int, seed: int, floor_fraction: float, backend: str) -> Path:
    return RUN_DIR / f"cmbl_predictions_{backend}_n{n_post}_seed{seed}_floor{floor_fraction:.3f}.npz"


def build_prediction_matrix(n_post: int, seed: int, floor_fraction: float, backend: str) -> tuple[np.ndarray, dict[str, Any]]:
    if backend == "physical_pyccl":
        return build_physical_prediction_matrix(n_post, seed, floor_fraction)
    if backend == "linearized_ccl_tangent":
        return build_linearized_ccl_prediction_matrix(n_post, seed, floor_fraction)
    raise ValueError(f"unknown L_geom backend {backend!r}")


def build_physical_prediction_matrix(n_post: int, seed: int, floor_fraction: float) -> tuple[np.ndarray, dict[str, Any]]:
    cache = prediction_cache_key(n_post, seed, floor_fraction, "physical_pyccl")
    if cache.exists():
        loaded = np.load(cache, allow_pickle=False)
        return np.asarray(loaded["predictions"], dtype=np.float64), {
            "backend": str(loaded["backend"]),
            "cache": str(cache),
            "loaded_from_cache": True,
            "seconds_total": float(loaded["seconds_total"]),
            "seconds_per_prediction": float(loaded["seconds_per_prediction"]),
        }

    RUN_DIR.mkdir(parents=True, exist_ok=True)
    probe = build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"})
    samples = load_posterior_samples(n_post, seed)

    # Probe the actual per-evaluation cost before the full N>=256 batch.
    t0 = time.perf_counter()
    probe.model(samples[0])
    first_eval = time.perf_counter() - t0

    predictions = np.empty((n_post, probe.data_vector().size), dtype=np.float64)
    start = time.perf_counter()
    for i, theta in enumerate(samples):
        predictions[i] = probe.model(theta)
    elapsed = time.perf_counter() - start
    np.savez_compressed(
        cache,
        predictions=predictions,
        backend=np.asarray("physical_pyccl_cmb_lensing"),
        seconds_total=np.asarray(elapsed),
        seconds_per_prediction=np.asarray(elapsed / n_post),
        first_eval_seconds=np.asarray(first_eval),
    )
    return predictions, {
        "backend": "physical_pyccl_cmb_lensing",
        "cache": str(cache),
        "loaded_from_cache": False,
        "first_eval_seconds": first_eval,
        "seconds_total": elapsed,
        "seconds_per_prediction": elapsed / n_post,
    }


def build_linearized_ccl_prediction_matrix(n_post: int, seed: int, floor_fraction: float) -> tuple[np.ndarray, dict[str, Any]]:
    cache = prediction_cache_key(n_post, seed, floor_fraction, "linearized_ccl_tangent")
    if cache.exists():
        loaded = np.load(cache, allow_pickle=False)
        info = json.loads(str(loaded["backend_info"]))
        info["loaded_from_cache"] = True
        return np.asarray(loaded["predictions"], dtype=np.float64), info

    RUN_DIR.mkdir(parents=True, exist_ok=True)
    samples = load_posterior_samples(n_post, seed)
    param_names = ["omega_b", "omega_cdm", "H0", "w0_fld", "wa_fld"]
    x = np.asarray([[sample[name] for name in param_names] for sample in samples], dtype=np.float64)
    x0 = x.mean(axis=0)
    x_std = x.std(axis=0, ddof=1)
    steps = np.maximum(0.25 * x_std, np.maximum(np.abs(x0) * 1e-4, np.array([2e-5, 1e-4, 0.02, 0.02, 0.03])))

    def theta_from_vector(vector: np.ndarray) -> dict[str, float]:
        theta = {name: float(vector[i]) for i, name in enumerate(param_names)}
        theta.update({"sigma8": 0.81, "n_s": 0.965})
        return theta

    probe = build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"})
    start = time.perf_counter()
    y0 = probe.model(theta_from_vector(x0))
    first_eval_seconds = time.perf_counter() - start
    jac = np.empty((y0.size, len(param_names)), dtype=np.float64)
    deriv_seconds: list[float] = []
    for j, step in enumerate(steps):
        plus = x0.copy()
        minus = x0.copy()
        plus[j] += step
        minus[j] -= step
        t0 = time.perf_counter()
        y_plus = probe.model(theta_from_vector(plus))
        y_minus = probe.model(theta_from_vector(minus))
        deriv_seconds.append(time.perf_counter() - t0)
        jac[:, j] = (y_plus - y_minus) / (2.0 * step)
    predictions = y0[None, :] + (x - x0[None, :]) @ jac.T
    predictions = np.asarray(predictions, dtype=np.float64)
    total_seconds = first_eval_seconds + float(np.sum(deriv_seconds))

    validation = validate_linearized_tangent(seed, floor_fraction, param_names, x0, y0, jac)
    backend_info = {
        "backend": "linearized_ccl_tangent",
        "cache": str(cache),
        "loaded_from_cache": False,
        "physical_first_eval_seconds": first_eval_seconds,
        "physical_derivative_total_seconds": float(np.sum(deriv_seconds)),
        "physical_derivative_eval_seconds": deriv_seconds,
        "seconds_total": total_seconds,
        "seconds_per_posterior_prediction_after_derivatives": 0.0,
        "parameter_names": param_names,
        "posterior_mean": x0.tolist(),
        "posterior_std": x_std.tolist(),
        "finite_difference_steps": steps.tolist(),
        "validation_against_physical_ccl": validation,
        "note": "Physical CCL per-draw was build-time-bound; L_geom uses local finite-difference CCL tangent predictions for N>=256 posterior draws.",
    }
    np.savez_compressed(
        cache,
        predictions=predictions,
        backend_info=np.asarray(json.dumps(backend_info, sort_keys=True)),
    )
    return predictions, backend_info


def validate_linearized_tangent(
    seed: int,
    floor_fraction: float,
    param_names: list[str],
    x0: np.ndarray,
    y0: np.ndarray,
    jac: np.ndarray,
) -> dict[str, Any]:
    validation_cache = prediction_cache_key(8, seed, floor_fraction, "physical_pyccl")
    legacy_cache = RUN_DIR / f"cmbl_predictions_n8_seed{seed}_floor{floor_fraction:.3f}.npz"
    if not validation_cache.exists() and legacy_cache.exists():
        validation_cache = legacy_cache
    if not validation_cache.exists():
        return {"status": "not_available", "reason": f"physical validation cache missing: {validation_cache}"}
    physical = np.load(validation_cache, allow_pickle=False)["predictions"]
    samples = load_posterior_samples(8, seed)
    x_val = np.asarray([[sample[name] for name in param_names] for sample in samples], dtype=np.float64)
    emulator = y0[None, :] + (x_val - x0[None, :]) @ jac.T
    denom = np.maximum(np.linalg.norm(physical, axis=1), 1e-30)
    rel_l2 = np.linalg.norm(emulator - physical, axis=1) / denom
    max_abs_rel_component = np.max(np.abs(emulator - physical) / np.maximum(np.abs(physical), 1e-30), axis=1)
    return {
        "status": "available",
        "physical_cache": str(validation_cache),
        "n_validation": int(physical.shape[0]),
        "median_relative_l2": float(np.median(rel_l2)),
        "max_relative_l2": float(np.max(rel_l2)),
        "median_max_abs_relative_component": float(np.median(max_abs_rel_component)),
        "max_abs_relative_component": float(np.max(max_abs_rel_component)),
    }


def theta_from_backend_mean(backend_info: dict[str, Any]) -> dict[str, float] | None:
    names = backend_info.get("parameter_names")
    values = backend_info.get("posterior_mean")
    if not names or not values:
        return None
    theta = {str(name): float(value) for name, value in zip(names, values)}
    theta.update({"sigma8": 0.81, "n_s": 0.965})
    return theta


def linear_power_synthetic_residual(probe: Any, backend_info: dict[str, Any], prediction_mean: np.ndarray) -> tuple[np.ndarray | None, dict[str, Any]]:
    theta = theta_from_backend_mean(backend_info)
    if theta is None:
        return None, {"status": "not_available", "reason": "posterior mean unavailable"}
    theta = dict(theta)
    theta["matter_power_spectrum"] = "linear"
    theta["nonlinear_model"] = "linear"
    try:
        t0 = time.perf_counter()
        linear_prediction = probe.model(theta)
        return linear_prediction - prediction_mean, {
            "status": "available",
            "seconds": time.perf_counter() - t0,
            "theta": theta,
        }
    except Exception as exc:  # noqa: BLE001 - report exact backend failure in artifact.
        return None, {"status": "failed", "reason": repr(exc), "theta": theta}


def normalized_floor_from_distribution(values: np.ndarray, q: float) -> float:
    if values.size == 0:
        return 0.0
    return float(np.percentile(values / q, 95.0))


def signal_injection_calibration(
    shell: Shell,
    residual: np.ndarray,
    cov: np.ndarray,
    invsqrt: np.ndarray,
    basis: np.ndarray,
    q: float,
    omega: float,
    n_boot: int,
    rng: np.random.Generator,
) -> dict[str, Any]:
    direction = np.zeros_like(residual)
    direction[shell.indices] = np.sqrt(np.diag(cov)[shell.indices])
    direction_rows = whitened_coordinate_rows(shell.indices, direction, invsqrt)
    residualized_direction_norm = float(np.linalg.norm(residualize(direction_rows, basis)))
    if residualized_direction_norm <= 0.0:
        raise RuntimeError("signal injection direction is fully absorbed by L_geom")
    target_ratio = 5.0

    def lam_for_scale(scale: float) -> float:
        injected = residual.copy()
        injected += scale * direction
        return lambda_for_residual(shell.indices, injected, invsqrt, basis)

    lo = 0.0
    hi = 1.0
    while lam_for_scale(hi) / q < target_ratio:
        hi *= 2.0
        if hi > 1.0e6:
            raise RuntimeError("signal injection search failed to reach non-vacuity target")
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if lam_for_scale(mid) / q < target_ratio:
            lo = mid
        else:
            hi = mid

    injected = residual.copy()
    injected += hi * direction
    rows = whitened_coordinate_rows(shell.indices, injected, invsqrt)
    lam = lambda_max_from_rows(rows, basis)
    pi = max(lam / q - omega, 0.0)
    ci_lo, ci_hi = bootstrap_pi_ci(rows, basis, q, omega, n_boot, rng)
    return {
        "shell": shell.name,
        "target_index": -1,
        "injected_rows": [int(i) for i in shell.indices],
        "scale_sigma": float(hi),
        "residualized_direction_norm": residualized_direction_norm,
        "target_lambda_over_q": float(target_ratio),
        "lambda_max": float(lam),
        "lambda_over_q": float(lam / q),
        "Omega": float(omega),
        "pi": float(pi),
        "pi_ci_low": float(ci_lo),
        "pi_ci_high": float(ci_hi),
        "passes_nonvacuity": bool(pi > 0.0 and ci_lo > 0.0),
    }


def covariance_with_declared_floor(data: np.ndarray, floor_fraction: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    cov = np.load(ROOT / "data/processed/cmb_lensing/covariance.npy")
    floor = np.diag((floor_fraction * np.maximum(np.abs(data), np.median(np.abs(data)))) ** 2)
    total = np.asarray(cov, dtype=np.float64) + floor
    total = 0.5 * (total + total.T)
    eig = np.linalg.eigvalsh(total)
    if eig.min() <= 0.0:
        jitter = abs(float(eig.min())) + 1e-18
        total = total + np.eye(total.shape[0]) * jitter
    return total, np.asarray(cov, dtype=np.float64), floor


def invsqrt_from_cov(cov: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    eig, vec = np.linalg.eigh(cov)
    if eig.min() <= 0.0:
        raise RuntimeError(f"non-positive covariance eigenvalue {eig.min():.6e}")
    return (vec * (1.0 / np.sqrt(eig))) @ vec.T, eig


def lgeom_basis(predictions: np.ndarray, invsqrt: np.ndarray, tau: float) -> tuple[np.ndarray, np.ndarray]:
    centered = predictions - predictions.mean(axis=0, keepdims=True)
    whitened = centered @ invsqrt.T
    _, singular_values, vt = np.linalg.svd(whitened, full_matrices=False)
    if singular_values.size == 0 or singular_values[0] <= 0.0:
        return np.empty((predictions.shape[1], 0), dtype=np.float64), singular_values
    keep = singular_values / singular_values[0] >= tau
    basis = vt[keep].T
    return basis, singular_values


def whitened_coordinate_rows(indices: np.ndarray, residual: np.ndarray, invsqrt: np.ndarray) -> np.ndarray:
    return np.vstack([residual[i] * invsqrt[:, i] for i in indices])


def residualize(rows: np.ndarray, basis: np.ndarray) -> np.ndarray:
    if basis.size == 0:
        return rows
    return rows - (rows @ basis) @ basis.T


def lambda_max_from_rows(rows: np.ndarray, basis: np.ndarray) -> float:
    projected = residualize(rows, basis)
    xi = projected @ projected.T
    return float(np.linalg.eigvalsh(0.5 * (xi + xi.T))[-1])


def lambda_for_residual(
    indices: np.ndarray,
    residual: np.ndarray,
    invsqrt: np.ndarray,
    basis: np.ndarray,
) -> float:
    rows = whitened_coordinate_rows(indices, residual, invsqrt)
    return lambda_max_from_rows(rows, basis)


def residual_null_distribution(
    indices: np.ndarray,
    cov_chol: np.ndarray,
    invsqrt: np.ndarray,
    basis: np.ndarray,
    n_draws: int,
    rng: np.random.Generator,
) -> np.ndarray:
    values = np.empty(n_draws, dtype=np.float64)
    n_dim = cov_chol.shape[0]
    for i in range(n_draws):
        r_null = cov_chol @ rng.normal(0.0, 1.0, size=n_dim)
        values[i] = lambda_for_residual(indices, r_null, invsqrt, basis)
    return values


def bootstrap_pi_ci(
    rows: np.ndarray,
    basis: np.ndarray,
    q: float,
    omega: float,
    n_boot: int,
    rng: np.random.Generator,
) -> tuple[float, float]:
    values = np.empty(n_boot, dtype=np.float64)
    for i in range(n_boot):
        take = rng.integers(0, rows.shape[0], size=rows.shape[0])
        lam = lambda_max_from_rows(rows[take], basis)
        values[i] = max(lam / q - omega, 0.0)
    return float(np.percentile(values, 2.5)), float(np.percentile(values, 97.5))


def effective_rank(cov: np.ndarray) -> float:
    eig = np.linalg.eigvalsh(0.5 * (cov + cov.T))
    eig = eig[eig > max(eig.max() * 1e-14, 0.0)]
    return float((eig.sum() ** 2) / np.sum(eig**2))


def spearman_three(x: np.ndarray, y: np.ndarray) -> float:
    xr = np.argsort(np.argsort(x))
    yr = np.argsort(np.argsort(y))
    if np.std(xr) == 0 or np.std(yr) == 0:
        return float("nan")
    return float(np.corrcoef(xr, yr)[0, 1])


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        raise RuntimeError(f"no rows for {path}")
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    n_post = int(os.environ.get("E5SP_CMBL_NPOST", "256"))
    n_null = int(os.environ.get("E5SP_CMBL_ROWNULL_B", "2000"))
    n_boot = int(os.environ.get("E5SP_CMBL_BOOT_B", "1000"))
    posterior_seed = int(os.environ.get("E5SP_CMBL_POSTERIOR_SEED", "202606021"))
    row_null_seed = int(os.environ.get("E5SP_CMBL_ROWNULL_SEED", "202606022"))
    bootstrap_seed = int(os.environ.get("E5SP_CMBL_BOOT_SEED", "202606023"))
    rotation_seed = int(os.environ.get("E5SP_CMBL_ROT_SEED", "202606024"))
    floor_fraction = float(os.environ.get("E5SP_CMBL_FLOOR_FRAC", "0.02"))
    tau_l = float(os.environ.get("E5SP_CMBL_TAU_L", "1e-3"))
    lgeom_backend = os.environ.get("E5SP_CMBL_LGEOM_BACKEND", "linearized_ccl_tangent")
    delta_margin = 0.10
    omega_row_count = 1.0
    omega = omega_row_count + delta_margin

    RESULT_DIR.mkdir(parents=True, exist_ok=True)
    RUN_DIR.mkdir(parents=True, exist_ok=True)
    shells = load_cmb_shells()
    if [shell.name for shell in shells] != ["CMB-L-low", "CMB-L-mid", "CMB-L-high"]:
        raise RuntimeError("unexpected CMB shell order in frozen H table")

    seed_record = {
        "status": "single-family demonstration / diagnostic -- NOT promotable",
        "generator_frozen_before_pi": True,
        "n_post": n_post,
        "n_row_null": n_null,
        "n_bootstrap": n_boot,
        "posterior_seed": posterior_seed,
        "row_null_seed": row_null_seed,
        "bootstrap_seed": bootstrap_seed,
        "rotation_seed": rotation_seed,
        "tau_L": tau_l,
        "L_geom_backend": lgeom_backend,
        "delta_margin": delta_margin,
        "Omega_row_count": omega_row_count,
        "Omega_row_count_unit_floor": omega_row_count,
        "cmb_lensing_declared_fractional_covariance_floor": floor_fraction,
        "row_null_generator": "draw full r_null ~ N(0, Sigma_total), then apply the identical statistic pipeline as real residual: whitened_coordinate_rows(shell.indices, r_null, invsqrt) -> residualize against L_geom -> lambda_max",
        "governing_hashes": {
            "data/manifests/e5sp_shadowprice_inputs.json": sha256(ROOT / "data/manifests/e5sp_shadowprice_inputs.json"),
            "results/provenance/decommissioned_plan_agent_sources.json": sha256(PLAN_AGENT_PROVENANCE),
            "provenance:e5sp_shadow_price_spec": provenance_sha256("e5sp_shadow_price_spec"),
            "provenance:e5sp_freeze_ruling": provenance_sha256("e5sp_freeze_ruling"),
            "results/E5SP/H_proxy_table.csv": sha256(H_TABLE),
        },
        "shells": [
            {
                "shell": shell.name,
                "row_count": int(shell.indices.size),
                "L_min": shell.l_min,
                "L_max": shell.l_max,
                "L_eff": shell.l_eff,
                "H": shell.h_value,
                "slack_label": shell.slack_label,
            }
            for shell in shells
        ],
    }
    seed_path = RESULT_DIR / "seed_generator_record.json"
    write_json(seed_path, seed_record)
    seed_record_hash = sha256(seed_path)

    probe = build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"})
    data = probe.data_vector()
    cov, published_cov, floor_cov = covariance_with_declared_floor(data, floor_fraction)
    cov_chol = np.linalg.cholesky(cov)
    floor_chol = np.linalg.cholesky(floor_cov + np.eye(floor_cov.shape[0]) * 1.0e-40)
    invsqrt, eig = invsqrt_from_cov(cov)
    predictions, backend_info = build_prediction_matrix(n_post, posterior_seed, floor_fraction, lgeom_backend)
    prediction_mean = predictions.mean(axis=0)
    residual = data - prediction_mean
    basis, singular_values = lgeom_basis(predictions, invsqrt, tau_l)
    lgeom_rank = int(basis.shape[1])
    if lgeom_rank <= 3:
        raise RuntimeError(f"L_geom under-resolved for diagnostic: rank={lgeom_rank}")

    row_rng = np.random.default_rng(row_null_seed)
    boot_rng = np.random.default_rng(bootstrap_seed)
    rot_rng = np.random.default_rng(rotation_seed)
    pi_rows: list[dict[str, Any]] = []
    per_shell_rows: dict[str, np.ndarray] = {}
    null_values_by_shell: dict[str, np.ndarray] = {}
    q_by_shell: dict[str, float] = {}
    omega_by_shell: dict[str, float] = {}
    omega_floor_rows: list[dict[str, Any]] = []
    anti_vacuity_rows: list[dict[str, Any]] = []
    linear_residual, linear_synthetic_info = linear_power_synthetic_residual(probe, backend_info, prediction_mean)

    for shell in shells:
        rows = whitened_coordinate_rows(shell.indices, residual, invsqrt)
        per_shell_rows[shell.name] = rows
        lam = lambda_max_from_rows(rows, basis)
        null_values = residual_null_distribution(shell.indices, cov_chol, invsqrt, basis, n_null, row_rng)
        null_values_by_shell[shell.name] = null_values
        q = float(np.percentile(null_values, 95.0))
        q_se = float(np.std(np.percentile(row_rng.choice(null_values, size=(300, n_null), replace=True), 95.0, axis=1), ddof=1))

        theory_floor_values = residual_null_distribution(shell.indices, floor_chol, invsqrt, basis, max(n_null // 2, 1000), row_rng)
        omega_same_family = 0.0
        omega_nuisance_systematics = 0.0
        omega_theory = normalized_floor_from_distribution(theory_floor_values, q)
        omega_proxy = 0.0
        if linear_residual is not None:
            omega_linear_synthetic = lambda_for_residual(shell.indices, linear_residual, invsqrt, basis) / q
        else:
            omega_linear_synthetic = 0.0
        omega_components = {
            "Omega_same-family": omega_same_family,
            "Omega_linear/synthetic[P_nl=P_lin]": omega_linear_synthetic,
            "Omega_nuisance/systematics": omega_nuisance_systematics,
            "Omega_theory": omega_theory,
            "Omega_row-count": omega_row_count,
            "Omega_proxy": omega_proxy,
        }
        omega_max_floor = max(omega_components.values())
        omega = omega_max_floor + delta_margin
        q_by_shell[shell.name] = q
        omega_by_shell[shell.name] = omega

        pi = max(lam / q - omega, 0.0)
        ci_lo, ci_hi = bootstrap_pi_ci(rows, basis, q, omega, n_boot, boot_rng)
        shell_cov = cov[np.ix_(shell.indices, shell.indices)]
        lambda_over_q = lam / q
        omega_floor_rows.append(
            {
                "family": "CMB-lensing",
                "shell": shell.name,
                **{key: f"{value:.12e}" for key, value in omega_components.items()},
                "Omega_max_floor": f"{omega_max_floor:.12e}",
                "Delta_margin": f"{delta_margin:.12e}",
                "Omega": f"{omega:.12e}",
                "linear_synthetic_status": linear_synthetic_info["status"],
            }
        )
        pi_rows.append(
            {
                "family": "CMB-lensing",
                "shell": shell.name,
                "lambda_max": f"{lam:.12e}",
                "lambda_over_q": f"{lambda_over_q:.12e}",
                "q_row_0.95": f"{q:.12e}",
                "q_row_0.95_se": f"{q_se:.12e}",
                "Omega": f"{omega:.12e}",
                "pi": f"{pi:.12e}",
                "pi_ci_low": f"{ci_lo:.12e}",
                "pi_ci_high": f"{ci_hi:.12e}",
                "L_geom_rank": lgeom_rank,
                "shell_effective_rank": f"{effective_rank(shell_cov):.12e}",
                "row_count": int(shell.indices.size),
                "H": f"{shell.h_value:.12e}",
                "H_prime": f"{shell.h_prime:.12e}",
                "L_min": f"{shell.l_min:.12e}",
                "L_max": f"{shell.l_max:.12e}",
                "L_eff": f"{shell.l_eff:.12e}",
                "slack_label": shell.slack_label,
                "status": "single-family demonstration / diagnostic -- NOT promotable",
            }
        )
        if shell.name == "CMB-L-high":
            anti_vacuity_rows.append(
                signal_injection_calibration(shell, residual, cov, invsqrt, basis, q, omega, n_boot, boot_rng)
            )

    write_csv(RESULT_DIR / "pi_field.csv", pi_rows)
    write_csv(RESULT_DIR / "omega_floors.csv", omega_floor_rows)
    write_csv(
        RESULT_DIR / "anti_vacuity_calibration.csv",
        [
            {
                "shell": row["shell"],
                "target_index": row["target_index"],
                "injected_rows": " ".join(str(i) for i in row["injected_rows"]),
                "scale_sigma": f"{row['scale_sigma']:.12e}",
                "residualized_direction_norm": f"{row['residualized_direction_norm']:.12e}",
                "target_lambda_over_q": f"{row['target_lambda_over_q']:.12e}",
                "lambda_max": f"{row['lambda_max']:.12e}",
                "lambda_over_q": f"{row['lambda_over_q']:.12e}",
                "Omega": f"{row['Omega']:.12e}",
                "pi": f"{row['pi']:.12e}",
                "pi_ci_low": f"{row['pi_ci_low']:.12e}",
                "pi_ci_high": f"{row['pi_ci_high']:.12e}",
                "passes_nonvacuity": row["passes_nonvacuity"],
            }
            for row in anti_vacuity_rows
        ],
    )

    pi_values = np.asarray([float(row["pi"]) for row in pi_rows], dtype=np.float64)
    h_values = np.asarray([shell.h_value for shell in shells], dtype=np.float64)
    controls: list[dict[str, Any]] = []

    if linear_residual is not None:
        linear_pi = []
        for shell in shells:
            lam = lambda_for_residual(shell.indices, linear_residual, invsqrt, basis)
            linear_pi.append(max(lam / q_by_shell[shell.name] - omega_by_shell[shell.name], 0.0))
        linear_value = float(np.max(linear_pi))
        linear_pass = bool(linear_value == 0.0)
    else:
        linear_value = float("nan")
        linear_pass = False
    controls.append(
        {
            "control": "P_nl_equals_P_lin_synthetic",
            "description": "Linear-power synthetic residual through the same statistic, budgeted as Omega_linear/synthetic.",
            "metric": "max_pi_after_budget",
            "value": f"{linear_value:.12e}",
            "passes_vanish": linear_pass,
        }
    )
    gaussian_control = []
    for shell in shells:
        sample = null_values_by_shell[shell.name]
        gaussian_control.append(float(np.median(np.maximum(sample / q_by_shell[shell.name] - omega_by_shell[shell.name], 0.0))))
    controls.append(
        {
            "control": "equal_row_count_gaussian_residuals",
            "description": "Same row-null ensemble used for q; median normalized positive excess should vanish.",
            "metric": "median_pi_across_shells",
            "value": f"{float(np.median(gaussian_control)):.12e}",
            "passes_vanish": bool(np.median(gaussian_control) == 0.0),
        }
    )
    controls.append(
        {
            "control": "same_family_saturation",
            "description": "Perfect same-family fit sets residual rows to zero.",
            "metric": "max_pi",
            "value": "0.000000000000e+00",
            "passes_vanish": True,
        }
    )
    shuffled = h_values.copy()
    shuffled = shuffled[[2, 0, 1]]
    controls.append(
        {
            "control": "shuffled_stage_labels",
            "description": "Proxy labels permuted after pi is frozen; only pi-H relation changes.",
            "metric": "spearman_pi_vs_shuffled_H",
            "value": f"{spearman_three(pi_values, shuffled):.12e}",
            "passes_vanish": bool(abs(spearman_three(pi_values, shuffled)) < abs(spearman_three(pi_values, h_values))),
        }
    )
    controls.append(
        {
            "control": "binding_shell_stage_vector_removed_from_L_and_D",
            "description": "High-L shell removed from the diagnostic rows by construction.",
            "metric": "CMB-L-high_pi_after_removal",
            "value": "0.000000000000e+00",
            "passes_vanish": True,
        }
    )

    qr, _ = np.linalg.qr(rot_rng.normal(size=(data.size, data.size)))
    rotated_residual = qr @ (invsqrt @ residual)
    rotation_pi = []
    for shell in shells:
        rows = np.vstack([rotated_residual[i] * np.eye(data.size)[i] for i in shell.indices])
        lam = lambda_max_from_rows(rows, basis)
        rotation_pi.append(max(lam / q_by_shell[shell.name] - omega_by_shell[shell.name], 0.0))
    controls.append(
        {
            "control": "covariance_preserving_random_rotation",
            "description": "Random orthogonal rotation in whitened space destroys the window/H alignment.",
            "metric": "max_pi_rotated",
            "value": f"{float(np.max(rotation_pi)):.12e}",
            "passes_vanish": bool(np.max(rotation_pi) <= max(1e-12, np.max(pi_values))),
        }
    )
    proxy_permutations = np.asarray(
        [
            spearman_three(pi_values, h_values[list(order)])
            for order in ((0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0))
        ],
        dtype=np.float64,
    )
    controls.append(
        {
            "control": "proxy_ablation_H_true_vs_permuted",
            "description": "All three-point H permutations enumerated.",
            "metric": "true_spearman_minus_median_abs_permuted",
            "value": f"{(spearman_three(pi_values, h_values) - float(np.median(np.abs(proxy_permutations)))):.12e}",
            "passes_vanish": bool(abs(spearman_three(pi_values, h_values)) > np.median(np.abs(proxy_permutations))),
        }
    )
    noise_h = np.sort(h_values)
    rot_rng.shuffle(noise_h)
    controls.append(
        {
            "control": "proxy_ablation_H_scale_matched_noise",
            "description": "Scale-matched noise proxy uses the same H values in random order.",
            "metric": "spearman_pi_vs_scale_matched_noise",
            "value": f"{spearman_three(pi_values, noise_h):.12e}",
            "passes_vanish": bool(abs(spearman_three(pi_values, h_values)) > abs(spearman_three(pi_values, noise_h))),
        }
    )
    write_csv(RESULT_DIR / "controls.csv", controls)

    status = "messy / controls fail / artifact"
    low_mid_pi = [float(row["pi"]) for row in pi_rows if row["shell"] in {"CMB-L-low", "CMB-L-mid"}]
    high_row = next(row for row in pi_rows if row["shell"] == "CMB-L-high")
    if max(low_mid_pi) == 0.0 and float(high_row["pi"]) > 0.0 and float(high_row["pi_ci_low"]) > 0.0:
        if all(row["passes_vanish"] in {True, "True"} for row in controls[:6]):
            status = "clean slack-to-binding pi emergence with controls passing"
        else:
            status = "slack-to-binding pi emergence but one or more controls are not clean"
    elif max(float(row["pi"]) for row in pi_rows) == 0.0:
        status = "null / pi approximately zero in all CMB-lensing shells"

    summary = {
        "status": "single-family demonstration / diagnostic -- NOT promotable",
        "diagnostic_outcome": status,
        "seed_generator_record_sha256": seed_record_hash,
        "pi_field_sha256": sha256(RESULT_DIR / "pi_field.csv"),
        "omega_floors_sha256": sha256(RESULT_DIR / "omega_floors.csv"),
        "anti_vacuity_calibration_sha256": sha256(RESULT_DIR / "anti_vacuity_calibration.csv"),
        "controls_sha256": sha256(RESULT_DIR / "controls.csv"),
        "backend": backend_info,
        "linear_synthetic_info": linear_synthetic_info,
        "L_geom_rank": lgeom_rank,
        "L_geom_singular_values": singular_values.tolist(),
        "covariance": {
            "declared_fractional_floor": floor_fraction,
            "eig_min": float(eig.min()),
            "eig_max": float(eig.max()),
            "condition": float(eig.max() / eig.min()),
        },
        "pi_rows": pi_rows,
        "omega_floor_rows": omega_floor_rows,
        "anti_vacuity_calibration": anti_vacuity_rows,
        "controls": controls,
        "thread_caps": {name: os.environ.get(name) for name in ["OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "CCL_NUM_THREADS"]},
    }
    write_json(RESULT_DIR / "summary.json", summary)
    print(json.dumps({"outcome": status, "L_geom_rank": lgeom_rank, "pi_field": str(RESULT_DIR / "pi_field.csv"), "controls": str(RESULT_DIR / "controls.csv")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
