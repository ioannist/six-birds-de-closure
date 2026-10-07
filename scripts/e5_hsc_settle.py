#!/usr/bin/env python3
"""Legal HSC-Y3 residual-settling diagnostic via analytic marginalization.

This supersedes the earlier illegal nuisance-profile diagnostic. Nuisances are
not optimized. They enter only through a prior-weighted response covariance:
Sigma_marg = Sigma_data + sum_k sigma_k^2 g_k g_k^T.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "HSC_settle"

THREAD_CAPS = {
    "OMP_NUM_THREADS": "1",
    "OPENBLAS_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
    "VECLIB_MAXIMUM_THREADS": "1",
    "CCL_NUM_THREADS": "1",
}

# Dalal+23 MAP values from arXiv:2304.00701, Table "fiducial constraints".
# The HSC paper used HMCode2016 A_bary. pyccl 3.1.2 does not expose HMCode
# A_bary directly, so the baryon response below is a stamped CCL proxy.
DALAL23_MAP = {
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
    "A_bary_hmcode2016": 2.97,
    "baryonic_effects": {"model": "vandaalen19", "fbar": 0.7},
    "nz_variant": "original",
}

SOURCE = {
    "paper": "Dalal et al. 2023, Hyper Suprime-Cam Year 3 Results: Cosmology from Cosmic Shear Power Spectra",
    "arxiv": "2304.00701",
    "priors": "Table labelled fiducial parameters and priors; lines in arXiv source tab:fid_parameters",
    "map_values": "Table labelled fiducial constraints; lines in arXiv source tab:fid_parameters_values",
}


@dataclass(frozen=True)
class Nuisance:
    name: str
    sigma: float
    step: float
    citation: str
    prior: str
    setter: Callable[[dict[str, Any], float], None]


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
    """Return the standard deviation of U(lo, hi)."""
    return (float(hi) - float(lo)) / np.sqrt(12.0)


def hsc_pairs(probe: Any) -> np.ndarray:
    pairs: list[tuple[int, int]] = []
    for row in probe._sacc["rows"]:  # noqa: SLF001 - diagnostic uses native SACC row map.
        pairs.append((int(row["tracer_0"].split("_")[1]), int(row["tracer_1"].split("_")[1])))
    return np.asarray(pairs, dtype=np.int64)


def chi2(data: np.ndarray, theory: np.ndarray, covariance: np.ndarray) -> float:
    delta = np.asarray(data, dtype=np.float64) - np.asarray(theory, dtype=np.float64)
    return float(delta @ np.linalg.solve(covariance, delta))


def whiten(covariance: np.ndarray, vector: np.ndarray) -> np.ndarray:
    chol = np.linalg.cholesky(covariance)
    return np.linalg.solve(chol, np.asarray(vector, dtype=np.float64))


def set_vector_component(key: str, index: int, value: float) -> Callable[[dict[str, Any], float], None]:
    def setter(params: dict[str, Any], raw_value: float) -> None:
        vec = list(params[key])
        vec[index] = float(raw_value)
        params[key] = vec

    return setter


def set_scalar(key: str) -> Callable[[dict[str, Any], float], None]:
    def setter(params: dict[str, Any], raw_value: float) -> None:
        params[key] = float(raw_value)

    return setter


def set_baryon_proxy(value: float) -> Callable[[dict[str, Any], float], None]:
    def setter(params: dict[str, Any], raw_value: float) -> None:
        params["baryonic_effects"] = {"model": "vandaalen19", "fbar": float(raw_value)}

    return setter


def nuisance_list() -> list[Nuisance]:
    dz_map = np.asarray(DALAL23_MAP["dz"], dtype=np.float64)
    m_map = np.asarray(DALAL23_MAP["m"], dtype=np.float64)
    table_prior = "Dalal+23 arXiv:2304.00701 fiducial-prior table"
    table_values = "Dalal+23 arXiv:2304.00701 fiducial-constraints/MAP table"
    return [
        *[
            Nuisance(
                name=f"m{i+1}",
                sigma=0.01,
                step=0.01,
                citation=f"{table_prior}: Delta m^({i+1}) ~ N(0, 0.01); MAP from {table_values}",
                prior="Gaussian N(0,0.01)",
                setter=set_vector_component("m", i, m_map[i]),
            )
            for i in range(4)
        ],
        Nuisance(
            name="dz1",
            sigma=0.024,
            step=0.012,
            citation=f"{table_prior}: Delta z^(1) ~ N(0,0.024); MAP from {table_values}",
            prior="Gaussian N(0,0.024)",
            setter=set_vector_component("dz", 0, dz_map[0]),
        ),
        Nuisance(
            name="dz2",
            sigma=0.022,
            step=0.011,
            citation=f"{table_prior}: Delta z^(2) ~ N(0,0.022); MAP from {table_values}",
            prior="Gaussian N(0,0.022)",
            setter=set_vector_component("dz", 1, dz_map[1]),
        ),
        Nuisance(
            name="dz3",
            sigma=uniform_sigma(-1.0, 1.0),
            step=0.02,
            citation=f"{table_prior}: Delta z^(3) ~ U(-1,1); Gaussian-equivalent sigma used for analytic covariance",
            prior="Uniform U(-1,1), converted to sigma=(2/sqrt(12))",
            setter=set_vector_component("dz", 2, dz_map[2]),
        ),
        Nuisance(
            name="dz4",
            sigma=uniform_sigma(-1.0, 1.0),
            step=0.02,
            citation=f"{table_prior}: Delta z^(4) ~ U(-1,1); Gaussian-equivalent sigma used for analytic covariance",
            prior="Uniform U(-1,1), converted to sigma=(2/sqrt(12))",
            setter=set_vector_component("dz", 3, dz_map[3]),
        ),
        Nuisance(
            name="A1",
            sigma=uniform_sigma(-6.0, 6.0),
            step=0.25,
            citation=f"{table_prior}: A1 ~ U(-6,6); MAP from {table_values}",
            prior="Uniform U(-6,6), converted to sigma=(12/sqrt(12))",
            setter=set_scalar("A1"),
        ),
        Nuisance(
            name="A2",
            sigma=uniform_sigma(-6.0, 6.0),
            step=0.25,
            citation=f"{table_prior}: A2 ~ U(-6,6); MAP from {table_values}",
            prior="Uniform U(-6,6), converted to sigma=(12/sqrt(12))",
            setter=set_scalar("A2"),
        ),
        Nuisance(
            name="b_ta",
            sigma=uniform_sigma(0.0, 2.0),
            step=0.10,
            citation=f"{table_prior}: b_ta ~ U(0,2); MAP from {table_values}",
            prior="Uniform U(0,2), converted to sigma=(2/sqrt(12))",
            setter=set_scalar("b_ta"),
        ),
        Nuisance(
            name="baryon_proxy_fbar",
            sigma=uniform_sigma(2.0, 3.13),
            step=0.05,
            citation=(
                f"{table_prior}: HMCode2016 A_bary ~ U(2,3.13); pyccl 3.1.2 lacks this parameter, "
                "so this is stamped as a CCL vanDaalen19 fbar response proxy with the published A_bary prior width"
            ),
            prior="Proxy for HMCode2016 A_bary U(2,3.13), converted to sigma=(1.13/sqrt(12))",
            setter=set_baryon_proxy(float(DALAL23_MAP["baryonic_effects"]["fbar"])),
        ),
    ]


def evaluate_model(probe: Any, params: Mapping[str, Any]) -> np.ndarray:
    return np.asarray(probe.model(dict(params)), dtype=np.float64)


def derivative_response(probe: Any, base_params: Mapping[str, Any], nuisance: Nuisance) -> tuple[np.ndarray, dict[str, Any]]:
    p_plus = dict(base_params)
    p_minus = dict(base_params)
    if nuisance.name.startswith("m") or nuisance.name.startswith("dz"):
        # Copy vector-valued entries before mutation.
        p_plus["m"] = list(base_params["m"])
        p_plus["dz"] = list(base_params["dz"])
        p_minus["m"] = list(base_params["m"])
        p_minus["dz"] = list(base_params["dz"])
    if nuisance.name == "baryon_proxy_fbar":
        center = float(base_params["baryonic_effects"]["fbar"])
    else:
        center = _get_center_value(base_params, nuisance.name)
    nuisance.setter(p_plus, center + nuisance.step)
    nuisance.setter(p_minus, center - nuisance.step)
    t0 = time.perf_counter()
    theta_plus = evaluate_model(probe, p_plus)
    theta_minus = evaluate_model(probe, p_minus)
    seconds = time.perf_counter() - t0
    response = (theta_plus - theta_minus) / (2.0 * nuisance.step)
    return response, {
        "name": nuisance.name,
        "sigma": nuisance.sigma,
        "finite_difference_step": nuisance.step,
        "citation": nuisance.citation,
        "prior": nuisance.prior,
        "center": center,
        "seconds": float(seconds),
        "response_norm": float(np.linalg.norm(response)),
        "sigma_response_norm": float(nuisance.sigma * np.linalg.norm(response)),
    }


def _get_center_value(params: Mapping[str, Any], name: str) -> float:
    if name.startswith("m"):
        return float(params["m"][int(name[1:]) - 1])
    if name.startswith("dz"):
        return float(params["dz"][int(name[2:]) - 1])
    return float(params[name])


def shear_m_response(base_theory: np.ndarray, pairs: np.ndarray, m_values: np.ndarray, index: int) -> np.ndarray:
    factor = np.zeros(base_theory.shape, dtype=np.float64)
    factor[pairs[:, 0] == index] += 1.0 / (1.0 + m_values[index])
    factor[pairs[:, 1] == index] += 1.0 / (1.0 + m_values[index])
    return base_theory * factor


def build_nuisance_covariance(
    probe: Any,
    base_params: Mapping[str, Any],
    base_theory: np.ndarray,
    pairs: np.ndarray,
) -> tuple[np.ndarray, list[dict[str, Any]]]:
    responses: list[np.ndarray] = []
    rows: list[dict[str, Any]] = []
    nuisances = nuisance_list()
    for index, nuisance in enumerate(nuisances, start=1):
        print(f"[HSC settle legal] derivative {index:02d}/{len(nuisances)}: {nuisance.name}", flush=True)
        if nuisance.name.startswith("m"):
            m_index = int(nuisance.name[1:]) - 1
            response = shear_m_response(base_theory, pairs, np.asarray(base_params["m"], dtype=np.float64), m_index)
            meta = {
                "name": nuisance.name,
                "sigma": nuisance.sigma,
                "finite_difference_step": None,
                "citation": nuisance.citation,
                "prior": nuisance.prior,
                "center": float(base_params["m"][m_index]),
                "seconds": 0.0,
                "response_norm": float(np.linalg.norm(response)),
                "sigma_response_norm": float(nuisance.sigma * np.linalg.norm(response)),
                "derivative": "analytic multiplicative shear-calibration response at MAP",
            }
        else:
            response, meta = derivative_response(probe, base_params, nuisance)
        responses.append(response)
        rows.append(meta)
    sigma_nuis = np.zeros((responses[0].size, responses[0].size), dtype=np.float64)
    for response, nuisance in zip(responses, nuisances, strict=True):
        sigma_nuis += nuisance.sigma**2 * np.outer(response, response)
    return sigma_nuis, rows


def coherence_test(covariance: np.ndarray, residual: np.ndarray, staging: np.ndarray) -> dict[str, Any]:
    r_tilde = whiten(covariance, residual)
    s_tilde = whiten(covariance, staging)
    r_norm = float(np.linalg.norm(r_tilde))
    s_norm = float(np.linalg.norm(s_tilde))
    alignment = float(abs(np.dot(r_tilde, s_tilde)) / (r_norm * s_norm))
    fraction = float((np.dot(r_tilde, s_tilde) / s_norm) ** 2 / (r_norm**2))
    rng = np.random.default_rng(20260601)
    n_random = 50000
    random_dirs = rng.normal(size=(n_random, r_tilde.size))
    random_dirs /= np.linalg.norm(random_dirs, axis=1)[:, None]
    random_alignment = np.abs(random_dirs @ (r_tilde / r_norm))
    p_random = float((np.count_nonzero(random_alignment >= alignment) + 1) / (n_random + 1))

    n_shuffle = 20000
    shuffled_alignment = np.empty(n_shuffle, dtype=np.float64)
    for i in range(n_shuffle):
        permuted = rng.permutation(s_tilde)
        shuffled_alignment[i] = abs(np.dot(r_tilde, permuted)) / (r_norm * np.linalg.norm(permuted))
    p_shuffle = float((np.count_nonzero(shuffled_alignment >= alignment) + 1) / (n_shuffle + 1))

    return {
        "metric": "Sigma_marg^{-1/2}; random/shuffled nulls generated in the nuisance-marginalized whitened space",
        "residual_norm_whitened": r_norm,
        "staging_norm_whitened": s_norm,
        "alignment_abs_cosine": alignment,
        "residual_variance_fraction_along_staging": fraction,
        "random_direction_null": {
            "n": n_random,
            "mean": float(np.mean(random_alignment)),
            "median": float(np.median(random_alignment)),
            "p95": float(np.quantile(random_alignment, 0.95)),
            "p99": float(np.quantile(random_alignment, 0.99)),
            "p_value_ge_observed": p_random,
        },
        "shuffled_staging_null": {
            "n": n_shuffle,
            "mean": float(np.mean(shuffled_alignment)),
            "median": float(np.median(shuffled_alignment)),
            "p95": float(np.quantile(shuffled_alignment, 0.95)),
            "p99": float(np.quantile(shuffled_alignment, 0.99)),
            "p_value_ge_observed": p_shuffle,
        },
        "decision_rule": "staging-coherent if alignment exceeds marginalized random-direction p95 and p_random<0.05",
        "staging_coherent": bool(alignment > np.quantile(random_alignment, 0.95) and p_random < 0.05),
    }


def covariance_summary(matrix: np.ndarray, path: Path) -> dict[str, Any]:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.save(path, matrix)
    eig = np.linalg.eigvalsh(matrix)
    return {
        "path": str(path.relative_to(ROOT)),
        "sha256": sha256_file(path),
        "shape": list(matrix.shape),
        "trace": float(np.trace(matrix)),
        "frobenius_norm": float(np.linalg.norm(matrix)),
        "min_eigenvalue": float(eig[0]),
        "max_eigenvalue": float(eig[-1]),
        "rank_tol_1e_minus_12": int(np.linalg.matrix_rank(matrix, tol=1e-12)),
    }


def write_response_csv(rows: list[dict[str, Any]]) -> str:
    path = RESULTS / "HSC_settle_nuisance_responses.csv"
    fields = ["name", "sigma", "finite_difference_step", "center", "response_norm", "sigma_response_norm", "prior"]
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row[field] for field in fields})
    return sha256_file(path)


def update_status(summary: Mapping[str, Any]) -> str | None:
    status_path = RESULTS / "E5_status.json"
    if not status_path.exists():
        return None
    status = json.loads(status_path.read_text())
    status["HSC_SETTLE"] = summary
    return write_json(status_path, status)


def main() -> None:
    start = time.perf_counter()
    thread_caps = set_thread_caps()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)

    from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

    probe_original = build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "original"})
    probe_recal = build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal", "nz_variant": "desi_recal"})
    pairs = hsc_pairs(probe_original)

    data = probe_original.data_vector()
    cov_data = probe_original.covariance()
    base_params = dict(DALAL23_MAP)

    print("[HSC settle legal] evaluating MAP original-n(z) theory", flush=True)
    t0 = time.perf_counter()
    theta_map = evaluate_model(probe_original, base_params)
    base_eval_seconds = time.perf_counter() - t0

    print("[HSC settle legal] evaluating MAP DESI-recal n(z) theory", flush=True)
    t0 = time.perf_counter()
    theta_recal = evaluate_model(probe_recal, {**base_params, "nz_variant": "desi_recal"})
    recal_eval_seconds = time.perf_counter() - t0

    sigma_nuis, response_rows = build_nuisance_covariance(probe_original, base_params, theta_map, pairs)
    cov_marg = cov_data + sigma_nuis

    residual = data - theta_map
    staging = theta_map - theta_recal
    chi2_data = chi2(data, theta_map, cov_data)
    chi2_marg = chi2(data, theta_map, cov_marg)
    coherence = coherence_test(cov_marg, residual, staging)

    omega_path = RESULTS / "Omega_HSC_pipeline.npy"
    sigma_marg_path = RESULTS / "HSC_Sigma_marg.npy"
    omega_summary = covariance_summary(sigma_nuis, omega_path)
    sigma_marg_summary = covariance_summary(cov_marg, sigma_marg_path)
    response_csv_hash = write_response_csv(response_rows)

    chi2_acceptable = bool(chi2_marg / data.size < 1.3)
    benign = bool(chi2_acceptable and not coherence["staging_coherent"])

    summary_for_status = {
        "status": "benign_budgeted" if benign else "staging_coherent_or_underbudgeted_diagnostic",
        "method": "analytic_nuisance_marginalization",
        "chi2_marg_per_dof": float(chi2_marg / data.size),
        "alignment_abs_cosine": coherence["alignment_abs_cosine"],
        "random_p_value_ge_observed": coherence["random_direction_null"]["p_value_ge_observed"],
        "Omega_HSC_pipeline_path": omega_summary["path"],
        "supersedes_illegal_free_m_profile": True,
    }
    status_hash = update_status(summary_for_status)

    output = {
        "schema_version": 2,
        "design_version": "E5-minimal-physical-v2",
        "purpose": "Legal HSC residual-settling diagnostic; no free nuisance fit; no E5 certificate run",
        "thread_caps": thread_caps,
        "source": SOURCE,
        "supersedes": {
            "previous_wp": "WP-HSC-SETTLE",
            "reason": "Previous diagnostic optimized shear calibration over +/-0.10 without prior penalty; invalid for HSC ~1% m priors.",
            "invalidated_fields_from_schema_v1": [
                "candidate_profile",
                "best_tatt_profile",
                "best_overall_profile",
                "post_baryon_hsc_chi2_per_data_dof_after_profile",
                "coherence_test computed after free-m absorption",
                "Omega_HSC_pipeline_floor_excess_chi2_per_dof scalar",
            ],
        },
        "dalal23_map_parameters_used": DALAL23_MAP,
        "nuisance_priors": response_rows,
        "method": {
            "formula": "Sigma_marg = Sigma_data + Sigma_nuis; Sigma_nuis = sum_k sigma_k^2 g_k g_k^T",
            "g_k": "central finite difference of the HSC cl_ee theory vector at the Dalal+23 MAP",
            "uniform_priors": "converted to Gaussian-equivalent sigma=(hi-lo)/sqrt(12) for analytic covariance marginalization",
            "no_free_fit": True,
            "no_prior_widening": True,
            "baryon_limitation": "HSC used HMCode2016 A_bary; pyccl 3.1.2 lacks that parameter, so baryon response is a stamped CCL vanDaalen19 fbar proxy carrying the published A_bary prior width.",
        },
        "base_evaluation": {
            "seconds_original": float(base_eval_seconds),
            "seconds_desi_recal": float(recal_eval_seconds),
            "chi2_data": chi2_data,
            "chi2_data_per_dof": float(chi2_data / data.size),
            "chi2_marg": chi2_marg,
            "chi2_marg_per_dof": float(chi2_marg / data.size),
            "dof": int(data.size),
        },
        "coherence_test": coherence,
        "Omega_HSC_pipeline": omega_summary,
        "Sigma_marg": sigma_marg_summary,
        "outputs": {
            "nuisance_response_csv": {
                "path": "results/E5/HSC_settle_nuisance_responses.csv",
                "sha256": response_csv_hash,
            },
            "status_update": {"path": "results/E5/E5_status.json", "sha256": status_hash},
        },
        "verdict": {
            "hsc_residual_status": "benign_budgeted" if benign else "staging_coherent_or_underbudgeted_diagnostic",
            "hsc_remains_decisive": benign,
            "chi2_acceptable_rule": "chi2_marg/dof < 1.3 for this diagnostic; reported rather than hidden",
            "chi2_acceptable": chi2_acceptable,
            "staging_coherent": coherence["staging_coherent"],
            "interpretation": (
                "Legal nuisance covariance absorbs the residual and the marginalized residual is not staging-aligned."
                if benign
                else "Legal nuisance covariance does not justify a benign decisive HSC fold under the recorded rule, or the residual is staging-aligned; manager/Eddy review required."
            ),
        },
        "runtime_seconds": float(time.perf_counter() - start),
        "load_average_end": os.getloadavg(),
        "stopped_before_certificate": True,
    }
    report_hash = write_json(RESULTS / "E5_hsc_settle.json", output)
    write_json(RUNS / "summary.json", {"results_sha256": report_hash, "stopped_before_certificate": True})
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
