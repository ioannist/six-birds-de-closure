#!/usr/bin/env python3
"""E5-SP HSC carrier-identifiability preflight.

This is a go/no-go diagnostic for whether an E5-SP3 carrier-controlled design
is worth building. It is HSC-only and not promotable.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import time
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
OUT = ROOT / "results/E5SP/e5ci_carrier_identifiability"
RUN = ROOT / "runs/E5SP/e5ci_carrier_identifiability"
H_TABLE = ROOT / "results/E5SP/H_proxy_table.csv"
CHAIN = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
N_POST = int(os.environ.get("E5CI_NPOST", "256"))
N_ROW_NULL = int(os.environ.get("E5CI_ROWNULL_B", "2000"))
N_BOOT = int(os.environ.get("E5CI_BOOT_B", "1000"))
N_VALIDATE = int(os.environ.get("E5CI_VALIDATE_DRAWS", "2"))
SEED = int(os.environ.get("E5CI_SEED", "202606031"))
TAU_L = 1.0e-3
DELTA_MARGIN = 0.10
CARRIERS = ["linear", "nonlinear", "nonlinear_plus_nuisance"]

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


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def hsc_central_geometry() -> dict[str, float]:
    h = float(HSC_MAP["h"])
    omega_b = float(HSC_MAP["omega_b"])
    omega_nu = float(HSC_MAP["m_nu"]) / 93.14
    omega_cdm = float(HSC_MAP["Omega_m"]) * h**2 - omega_b - omega_nu
    sigma8 = float(HSC_MAP["S8"]) / np.sqrt(float(HSC_MAP["Omega_m"]) / 0.3)
    return {
        "omega_b": omega_b,
        "omega_cdm": omega_cdm,
        "H0": 100.0 * h,
        "w0_fld": -1.0,
        "wa_fld": 0.0,
        "sigma8": sigma8,
        "n_s": float(HSC_MAP["n_s"]),
        "m_nu": float(HSC_MAP["m_nu"]),
    }


def hsc_theta(vector: np.ndarray, names: list[str], carrier: str) -> dict[str, Any]:
    theta: dict[str, Any] = {name: float(vector[i]) for i, name in enumerate(names)}
    theta.update(
        {
            "sigma8": hsc_central_geometry()["sigma8"],
            "n_s": float(HSC_MAP["n_s"]),
            "m_nu": float(HSC_MAP["m_nu"]),
            "ia_model": HSC_MAP["ia_model"],
            "A1": HSC_MAP["A1"],
            "eta1": HSC_MAP["eta1"],
            "A2": HSC_MAP["A2"],
            "eta2": HSC_MAP["eta2"],
            "b_ta": HSC_MAP["b_ta"],
            "z_pivot_IA": HSC_MAP["z_pivot_IA"],
            "dz": list(HSC_MAP["dz"]),
            "m": list(HSC_MAP["m"]),
            "nz_variant": "original",
        }
    )
    if carrier == "linear":
        theta["matter_power_spectrum"] = "linear"
        theta["nonlinear_model"] = "linear"
        theta["baryonic_effects"] = None
    else:
        theta["baryonic_effects"] = HSC_MAP["baryonic_effects"]
    return theta


def posterior_delta_samples(n: int, seed: int) -> tuple[np.ndarray, list[str], np.ndarray, np.ndarray]:
    with CHAIN.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    arr = np.loadtxt(CHAIN, comments="#")
    cols = {name: i for i, name in enumerate(header)}
    names = ["omega_b", "omega_cdm", "H0", "w0_fld", "wa_fld"]
    values = np.column_stack([arr[:, cols[name]] for name in names])
    weights = arr[:, cols["weight"]] if "weight" in cols else np.ones(arr.shape[0])
    weights = np.clip(weights, 0.0, None)
    weights = weights / weights.sum()
    mean = np.sum(weights[:, None] * values, axis=0)
    rng = np.random.default_rng(seed)
    indices = rng.choice(values.shape[0], size=n, replace=True, p=weights)
    deltas = values[indices] - mean[None, :]
    central = hsc_central_geometry()
    x0 = np.asarray([central[name] for name in names], dtype=np.float64)
    return x0[None, :] + deltas, names, mean, values[indices].std(axis=0, ddof=1)


def hsc_shells(probe: Any) -> list[dict[str, Any]]:
    h_rows = {}
    with H_TABLE.open() as fh:
        for row in csv.DictReader(fh):
            if row["family"] == "HSC-Y3":
                h_rows[row["shell"]] = row
    rows = probe._sacc["rows"]  # noqa: SLF001 - native HSC row metadata for shelling.
    ells = np.asarray([float(row["ell"]) for row in rows], dtype=np.float64)
    shells = []
    for shell, (lo, hi) in [
        ("ell-300-600", (300.0, 600.0)),
        ("ell-600-1000", (600.0, 1000.0)),
        ("ell-1000-1500", (1000.0, 1500.0)),
        ("ell-1500-1800", (1500.0, 1800.0)),
    ]:
        idx = np.flatnonzero((ells >= lo - 1e-9) & (ells <= hi + 1e-9))
        if idx.size == 0:
            raise RuntimeError(f"empty HSC shell {shell}")
        frozen = h_rows[shell]
        shells.append(
            {
                "shell": shell,
                "indices": idx,
                "H": float(frozen["H"]),
                "L_min": lo,
                "L_max": hi,
            }
        )
    return shells


def hsc_shells_from_h_table() -> list[dict[str, Any]]:
    rows = {}
    with H_TABLE.open() as fh:
        for row in csv.DictReader(fh):
            if row["family"] == "HSC-Y3":
                rows[row["shell"]] = row
    shells = []
    for shell, (lo, hi) in [
        ("ell-300-600", (300.0, 600.0)),
        ("ell-600-1000", (600.0, 1000.0)),
        ("ell-1000-1500", (1000.0, 1500.0)),
        ("ell-1500-1800", (1500.0, 1800.0)),
    ]:
        frozen = rows[shell]
        shells.append({"shell": shell, "H": float(frozen["H"]), "L_min": lo, "L_max": hi})
    return shells


def build_linearized_predictions(probe: Any, carrier: str) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    cache = RUN / f"hsc_{carrier}_linearized_n{N_POST}_seed{SEED}.npz"
    if cache.exists():
        loaded = np.load(cache, allow_pickle=False)
        return loaded["predictions"], loaded["y0"], json.loads(str(loaded["info"]))

    RUN.mkdir(parents=True, exist_ok=True)
    x, names, posterior_mean, posterior_std = posterior_delta_samples(N_POST, SEED)
    x0 = x.mean(axis=0)
    steps = np.maximum(0.25 * posterior_std, np.maximum(np.abs(x0) * 1e-4, np.array([2e-5, 1e-4, 0.02, 0.02, 0.03])))

    print(f"[E5CI] {carrier}: central HSC physical eval", flush=True)
    start = time.perf_counter()
    y0 = np.asarray(probe.model(hsc_theta(x0, names, carrier)), dtype=np.float64)
    first_eval = time.perf_counter() - start
    print(f"[E5CI] {carrier}: central eval seconds={first_eval:.3f}", flush=True)
    jac = np.empty((y0.size, len(names)), dtype=np.float64)
    derivative_seconds = []
    for j, step in enumerate(steps):
        xp = x0.copy()
        xm = x0.copy()
        xp[j] += step
        xm[j] -= step
        print(f"[E5CI] {carrier}: finite difference {j + 1}/{len(names)} {names[j]} step={step:.6g}", flush=True)
        t0 = time.perf_counter()
        yp = np.asarray(probe.model(hsc_theta(xp, names, carrier)), dtype=np.float64)
        ym = np.asarray(probe.model(hsc_theta(xm, names, carrier)), dtype=np.float64)
        derivative_seconds.append(time.perf_counter() - t0)
        print(f"[E5CI] {carrier}: derivative {names[j]} seconds={derivative_seconds[-1]:.3f}", flush=True)
        jac[:, j] = (yp - ym) / (2.0 * step)
    predictions = y0[None, :] + (x - x0[None, :]) @ jac.T
    validation = validate_linearized_hsc(probe, carrier, x, names, x0, y0, jac)
    info = {
        "backend": "linearized_ccl_tangent",
        "carrier": carrier,
        "n_post": N_POST,
        "parameter_names": names,
        "central_vector": x0.tolist(),
        "posterior_mean_E1": posterior_mean.tolist(),
        "posterior_std_E1_sample": posterior_std.tolist(),
        "finite_difference_steps": steps.tolist(),
        "first_eval_seconds": first_eval,
        "derivative_seconds": derivative_seconds,
        "total_ccl_seconds": first_eval + float(np.sum(derivative_seconds)),
        "validation_against_physical_ccl": validation,
    }
    np.savez_compressed(cache, predictions=predictions, y0=y0, info=np.asarray(json.dumps(info, sort_keys=True)))
    return predictions, y0, info


def validate_linearized_hsc(
    probe: Any,
    carrier: str,
    x: np.ndarray,
    names: list[str],
    x0: np.ndarray,
    y0: np.ndarray,
    jac: np.ndarray,
) -> dict[str, Any]:
    n_val = min(N_VALIDATE, x.shape[0])
    if n_val <= 0:
        return {"status": "disabled", "n_validation": 0}
    physical = []
    emulator = []
    seconds = []
    for i in range(n_val):
        print(f"[E5CI] {carrier}: validation physical draw {i + 1}/{n_val}", flush=True)
        t0 = time.perf_counter()
        yi = np.asarray(probe.model(hsc_theta(x[i], names, carrier)), dtype=np.float64)
        seconds.append(time.perf_counter() - t0)
        physical.append(yi)
        emulator.append(y0 + (x[i] - x0) @ jac.T)
        print(f"[E5CI] {carrier}: validation draw {i + 1} seconds={seconds[-1]:.3f}", flush=True)
    physical_arr = np.vstack(physical)
    emulator_arr = np.vstack(emulator)
    denom = np.maximum(np.linalg.norm(physical_arr, axis=1), 1e-30)
    rel_l2 = np.linalg.norm(emulator_arr - physical_arr, axis=1) / denom
    max_abs_rel_component = np.max(
        np.abs(emulator_arr - physical_arr) / np.maximum(np.abs(physical_arr), 1e-30),
        axis=1,
    )
    return {
        "status": "available",
        "n_validation": int(n_val),
        "seconds": seconds,
        "median_relative_l2": float(np.median(rel_l2)),
        "max_relative_l2": float(np.max(rel_l2)),
        "median_max_abs_relative_component": float(np.median(max_abs_rel_component)),
        "max_abs_relative_component": float(np.max(max_abs_rel_component)),
    }


def invsqrt(cov: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    cov = 0.5 * (cov + cov.T)
    eig, vec = np.linalg.eigh(cov)
    if eig.min() <= 0.0:
        cov = cov + np.eye(cov.shape[0]) * (abs(float(eig.min())) + 1e-18)
        eig, vec = np.linalg.eigh(cov)
    return (vec * (1.0 / np.sqrt(eig))) @ vec.T, eig


def lgeom_basis(predictions: np.ndarray, W: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    centered = predictions - predictions.mean(axis=0, keepdims=True)
    white = centered @ W.T
    _, s, vt = np.linalg.svd(white, full_matrices=False)
    keep = s / s[0] >= TAU_L if s.size and s[0] > 0 else np.zeros_like(s, dtype=bool)
    return vt[keep].T, s


def whitened_rows(indices: np.ndarray, residual: np.ndarray, W: np.ndarray) -> np.ndarray:
    return np.vstack([residual[i] * W[:, i] for i in indices])


def lambda_rows(rows: np.ndarray, basis: np.ndarray) -> float:
    if basis.size:
        rows = rows - (rows @ basis) @ basis.T
    xi = rows @ rows.T
    return float(np.linalg.eigvalsh(0.5 * (xi + xi.T))[-1])


def lambda_residual(indices: np.ndarray, residual: np.ndarray, W: np.ndarray, basis: np.ndarray) -> float:
    return lambda_rows(whitened_rows(indices, residual, W), basis)


def row_null(indices: np.ndarray, chol: np.ndarray, W: np.ndarray, basis: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    values = np.empty(N_ROW_NULL, dtype=np.float64)
    for i in range(N_ROW_NULL):
        residual = chol @ rng.normal(size=chol.shape[0])
        values[i] = lambda_residual(indices, residual, W, basis)
    return values


def bootstrap_ci(rows: np.ndarray, basis: np.ndarray, q: float, omega: float, rng: np.random.Generator) -> tuple[float, float]:
    vals = np.empty(N_BOOT, dtype=np.float64)
    for i in range(N_BOOT):
        take = rng.integers(0, rows.shape[0], size=rows.shape[0])
        vals[i] = max(lambda_rows(rows[take], basis) / q - omega, 0.0)
    return float(np.percentile(vals, 2.5)), float(np.percentile(vals, 97.5))


def effective_rank(cov: np.ndarray) -> float:
    eig = np.linalg.eigvalsh(0.5 * (cov + cov.T))
    eig = eig[eig > max(eig.max() * 1e-14, 0.0)]
    return float(eig.sum() ** 2 / np.sum(eig**2))


def anti_vacuity(shell: dict[str, Any], residual: np.ndarray, cov: np.ndarray, W: np.ndarray, basis: np.ndarray, q: float, omega: float, rng: np.random.Generator) -> dict[str, Any]:
    direction = np.zeros_like(residual)
    idx = shell["indices"]
    direction[idx] = np.sqrt(np.diag(cov)[idx])
    direction_norm = float(np.linalg.norm(whitened_rows(idx, direction, W)))

    def ratio(scale: float) -> float:
        return lambda_residual(idx, residual + scale * direction, W, basis) / q

    lo = 0.0
    hi = 1.0
    while ratio(hi) < 5.0:
        hi *= 2.0
        if hi > 1.0e6:
            raise RuntimeError(f"anti-vacuity injection failed for {shell['shell']}")
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if ratio(mid) < 5.0:
            lo = mid
        else:
            hi = mid
    injected = residual + hi * direction
    rows = whitened_rows(idx, injected, W)
    lam = lambda_rows(rows, basis)
    pi = max(lam / q - omega, 0.0)
    ci_lo, ci_hi = bootstrap_ci(rows, basis, q, omega, rng)
    return {
        "anti_vacuity_pi": pi,
        "anti_vacuity_ci_low": ci_lo,
        "anti_vacuity_ci_high": ci_hi,
        "anti_vacuity_passes": bool(pi > 0.0 and ci_lo > 0.0),
        "anti_vacuity_scale_sigma": hi,
        "anti_vacuity_direction_norm": direction_norm,
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def carrier_run(probe: Any, carrier: str, cov: np.ndarray, shells: list[dict[str, Any]], rng: np.random.Generator) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    predictions, y0, info = build_linearized_predictions(probe, "linear" if carrier == "linear" else "nonlinear")
    W, eig = invsqrt(cov)
    basis, s = lgeom_basis(predictions, W)
    rank = int(basis.shape[1])
    if rank <= 3:
        raise RuntimeError(f"{carrier} L_geom under-resolved: rank={rank}")
    data = probe.data_vector()
    residual = data - y0
    chol = np.linalg.cholesky(0.5 * (cov + cov.T))
    rows_out = []
    for shell in shells:
        idx = shell["indices"]
        rows = whitened_rows(idx, residual, W)
        lam = lambda_rows(rows, basis)
        null = row_null(idx, chol, W, basis, rng)
        q = float(np.percentile(null, 95.0))
        q_se = float(np.std(np.percentile(rng.choice(null, size=(300, N_ROW_NULL), replace=True), 95.0, axis=1), ddof=1))
        omega_components = {
            "Omega_same-family": 0.0,
            "Omega_linear/synthetic[P_nl=P_lin]": 0.0,
            "Omega_nuisance/systematics": 0.0 if carrier != "nonlinear_plus_nuisance" else 1.0,
            "Omega_theory": 0.0,
            "Omega_row-count": 1.0,
            "Omega_proxy": 0.0,
        }
        omega = max(omega_components.values()) + DELTA_MARGIN
        pi = max(lam / q - omega, 0.0)
        ci_lo, ci_hi = bootstrap_ci(rows, basis, q, omega, rng)
        av = anti_vacuity(shell, residual, cov, W, basis, q, omega, rng)
        rows_out.append(
            {
                "carrier": carrier,
                "shell": shell["shell"],
                "H": f"{shell['H']:.12e}",
                "lambda_max": f"{lam:.12e}",
                "lambda_over_q": f"{(lam / q):.12e}",
                "q_row_0.95": f"{q:.12e}",
                "q_row_0.95_se": f"{q_se:.12e}",
                "Omega": f"{omega:.12e}",
                "pi": f"{pi:.12e}",
                "pi_ci_low": f"{ci_lo:.12e}",
                "pi_ci_high": f"{ci_hi:.12e}",
                "L_geom_rank": rank,
                "shell_effective_rank": f"{effective_rank(cov[np.ix_(idx, idx)]):.12e}",
                "anti_vacuity_pi": f"{av['anti_vacuity_pi']:.12e}",
                "anti_vacuity_ci_low": f"{av['anti_vacuity_ci_low']:.12e}",
                "anti_vacuity_ci_high": f"{av['anti_vacuity_ci_high']:.12e}",
                "anti_vacuity_passes": av["anti_vacuity_passes"],
                **{key: f"{value:.12e}" for key, value in omega_components.items()},
            }
        )
    meta = {
        "carrier": carrier,
        "L_geom_rank": rank,
        "singular_values": s.tolist(),
        "cov_eig_min": float(eig.min()),
        "cov_eig_max": float(eig.max()),
        "cov_condition": float(eig.max() / eig.min()),
        "prediction_backend": info,
    }
    return rows_out, meta


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    RUN.mkdir(parents=True, exist_ok=True)
    for stale in [OUT / "pi_by_carrier.csv", OUT / "verdict.json", OUT / "backend_validation.json"]:
        try:
            stale.unlink()
        except FileNotFoundError:
            pass
    probe = build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "original"})
    shells = hsc_shells(probe)
    cov_data = np.load(ROOT / "data/processed/hsc_y3/covariance.npy")
    cov_marg = np.load(ROOT / "results/E5/HSC_Sigma_marg.npy")
    rng = np.random.default_rng(SEED)
    all_rows: list[dict[str, Any]] = []
    metas = {}
    start = time.perf_counter()
    for carrier, cov in [
        ("linear", cov_data),
        ("nonlinear", cov_data),
        ("nonlinear_plus_nuisance", cov_marg),
    ]:
        print(f"[E5CI] starting carrier={carrier}", flush=True)
        rows, meta = carrier_run(probe, carrier, cov, shells, rng)
        all_rows.extend(rows)
        metas[carrier] = meta
        write_csv(OUT / "pi_by_carrier.csv", all_rows)
        (OUT / "backend_validation.json").write_text(json.dumps(metas, indent=2, sort_keys=True) + "\n")
        print(f"[E5CI] checkpoint wrote {len(all_rows)} rows after carrier={carrier}", flush=True)

    by_carrier = {}
    for carrier in ["linear", "nonlinear", "nonlinear_plus_nuisance"]:
        rows = [row for row in all_rows if row["carrier"] == carrier]
        positive = any(float(row["pi"]) > 0.0 and float(row["pi_ci_low"]) > 0.0 for row in rows)
        live = all(str(row["anti_vacuity_passes"]) == "True" or row["anti_vacuity_passes"] is True for row in rows)
        by_carrier[carrier] = {"positive_pi_ci_excludes_zero": positive, "anti_vacuity_all_shells_pass": live}

    if not all(item["anti_vacuity_all_shells_pass"] for item in by_carrier.values()):
        overall = "NO-GO"
        reason = "at least one carrier's anti-vacuity calibration failed"
    elif not by_carrier["nonlinear"]["positive_pi_ci_excludes_zero"]:
        overall = "NO-GO"
        reason = "model-null: pi does not survive the nonlinear carrier"
    elif not by_carrier["nonlinear_plus_nuisance"]["positive_pi_ci_excludes_zero"]:
        overall = "NO-GO"
        reason = "systematics-proxy: pi survives nonlinear carrier but is absorbed by legal HSC nuisance covariance"
    else:
        overall = "GO"
        reason = "pi survives nonlinear and nonlinear+legal-nuisance carriers with live anti-vacuity gates"

    verdict = {
        "status": "carrier-identifiability preflight -- go/no-go for E5-SP3, NOT promotable",
        "overall": overall,
        "reason": reason,
        "criteria": {
            "C1_pi_survives_nonlinear": by_carrier["nonlinear"]["positive_pi_ci_excludes_zero"],
            "C2_pi_survives_nonlinear_plus_nuisance": by_carrier["nonlinear_plus_nuisance"]["positive_pi_ci_excludes_zero"],
            "C3_all_anti_vacuity_live": all(item["anti_vacuity_all_shells_pass"] for item in by_carrier.values()),
        },
        "by_carrier": by_carrier,
        "disclosures": {
            "geometry": "N>=256 E1/E2 w0wa posterior deltas applied as local tangent around HSC Dalal+23 MAP",
            "carrier_backend": "linearized CCL tangent; carrier1 uses CCL linear matter power, carrier2/3 use nonlinear HALOFIT plus HSC baryon proxy",
            "carrier3_nuisance": "uses results/E5/HSC_Sigma_marg.npy from legal analytic nuisance marginalization; nuisance directions include m_i, dz_i, TATT A1/A2/b_ta, and baryon proxy per scripts/e5_hsc_settle.py",
            "sigma8_ns": "HSC Dalal+23 MAP S8 converted to sigma8; n_s fixed at HSC MAP 0.920",
            "no_timeout": "No per-vector timeout precheck is active in this run; physical HSC evaluations are allowed to finish.",
        },
        "runtime_seconds": time.perf_counter() - start,
        "metas": metas,
        "hashes": {
            "manifest": sha256(ROOT / "data/manifests/e5sp_shadowprice_inputs.json"),
            "H_proxy_table": sha256(H_TABLE),
            "script": sha256(Path(__file__)),
            "pi_by_carrier": sha256(OUT / "pi_by_carrier.csv"),
        },
    }
    (OUT / "verdict.json").write_text(json.dumps(verdict, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"overall": overall, "reason": reason, "out": str((OUT / "pi_by_carrier.csv").relative_to(ROOT))}, indent=2))


if __name__ == "__main__":
    main()
