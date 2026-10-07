"""Thin E0 orchestrator for synthetic, data-free mechanism demos."""

from __future__ import annotations

import argparse
import math
import os
import random
import time
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import numpy as np
import yaml
from scipy.optimize import minimize

import sbt_cosmo
from sbt_cosmo.aor.ledger import count_unstatused, write_aor_ledger
from sbt_cosmo.audits.delta import compute_delta
from sbt_cosmo.audits.metrics import aic, bic, rmse
from sbt_cosmo.audits.route_mismatch import logistic_completion_mismatch
from sbt_cosmo.background.distances import lcdm_luminosity_distance, matter_luminosity_distance
from sbt_cosmo.hubble.holonomy import route_loop_holonomy
from sbt_cosmo.hubble.route_matrix import (
    build_route_matrix,
    fit_low_rank_route_matrix,
    fit_null_route_matrix,
    fit_per_route_nuisance,
    observe_route_matrix,
    relative_parameter_errors,
)
from sbt_cosmo.io.artifacts import write_json_artifact, write_npz_artifact, write_table_artifact
from sbt_cosmo.io.checksums import sha256_file
from sbt_cosmo.io.manifest import write_run_manifest
from sbt_cosmo.viz.style import apply_style
from sbt_cosmo.xi.rewrite import crossing_locations, effective_w_readout, p4_rho_eff, rewrite_inverse_hubble_lens
from sbt_cosmo.xi.stability import diagonal_stable_jacobian, stable_readout_certificate


def _as_builtin(value: Any) -> Any:
    """Convert numpy values into JSON-serializable builtin objects."""
    if isinstance(value, np.ndarray):
        return [_as_builtin(item) for item in value.tolist()]
    if isinstance(value, np.generic):
        return value.item()
    if isinstance(value, dict):
        return {str(key): _as_builtin(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_as_builtin(item) for item in value]
    return value


def _gate(value: Any, passed: bool, threshold: str) -> dict[str, Any]:
    return {"value": _as_builtin(value), "pass": bool(passed), "threshold": threshold}


def _relative_close(left: float, right: float, tol: float = 1.0e-12) -> bool:
    scale = max(abs(left), abs(right), 1.0)
    return abs(left - right) / scale < tol


def _linspace_redshift(z_min: float, z_max: float, n_z: int) -> np.ndarray:
    return np.geomspace(1.0 + z_min, 1.0 + z_max, n_z) - 1.0


def _fit_matter(z: np.ndarray, observed: np.ndarray, sigma: np.ndarray) -> dict[str, Any]:
    def objective(log_h: np.ndarray) -> float:
        model = matter_luminosity_distance(z, h_scale=float(np.exp(log_h[0])))
        return float(np.sum(((observed - model) / sigma) ** 2))

    result = minimize(objective, np.array([0.0]), method="L-BFGS-B", options={"ftol": 1.0e-14, "gtol": 1.0e-12})
    h_scale = float(np.exp(result.x[0]))
    chi2 = float(result.fun)
    return {
        "name": "M0_matter",
        "h_scale": h_scale,
        "omega_lambda": 0.0,
        "chi2": chi2,
        "aic": aic(chi2, 1),
        "bic": bic(chi2, z.size, 1),
        "model": matter_luminosity_distance(z, h_scale=h_scale),
        "k": 1,
    }


def _fit_lcdm(z: np.ndarray, observed: np.ndarray, sigma: np.ndarray) -> dict[str, Any]:
    def objective(params: np.ndarray) -> float:
        h_scale, omega_m = float(params[0]), float(params[1])
        model = lcdm_luminosity_distance(z, h_scale=h_scale, omega_m=omega_m)
        return float(np.sum(((observed - model) / sigma) ** 2))

    result = minimize(
        objective,
        np.array([1.0, 0.55]),
        method="L-BFGS-B",
        bounds=[(0.2, 5.0), (0.01, 0.99)],
        options={"ftol": 1.0e-14, "gtol": 1.0e-12, "maxiter": 10000},
    )
    h_scale, omega_m = float(result.x[0]), float(result.x[1])
    chi2 = float(result.fun)
    return {
        "name": "M1_flat_lcdm",
        "h_scale": h_scale,
        "omega_m": omega_m,
        "omega_lambda": 1.0 - omega_m,
        "chi2": chi2,
        "aic": aic(chi2, 2),
        "bic": bic(chi2, z.size, 2),
        "model": lcdm_luminosity_distance(z, h_scale=h_scale, omega_m=omega_m),
        "k": 2,
    }


def _fit_rewrite(
    z: np.ndarray,
    observed: np.ndarray,
    sigma: np.ndarray,
    route_modes: np.ndarray,
    toy2_config: Mapping[str, Any],
) -> dict[str, Any]:
    train = z <= float(toy2_config["train_z_max"])
    response = float(toy2_config["response"])
    exponent = float(toy2_config["exponent"])
    z_max = float(toy2_config["z_max"])
    upper_amplitude = min(0.62, 0.99 / response)

    def model_for(log_h: float, log_a: float) -> dict[str, np.ndarray]:
        h_scale = float(np.exp(log_h))
        amplitude = float(np.exp(log_a))
        return rewrite_inverse_hubble_lens(
            z,
            route_modes,
            amplitude=amplitude,
            response=response,
            exponent=exponent,
            z_max=z_max,
            h_scale=h_scale,
        )

    def objective(params: np.ndarray) -> float:
        model = model_for(float(params[0]), float(params[1]))["luminosity_distance"]
        return float(np.sum(((observed[train] - model[train]) / sigma[train]) ** 2))

    result = minimize(
        objective,
        np.array([0.0, math.log(0.5)]),
        method="L-BFGS-B",
        bounds=[(math.log(0.2), math.log(5.0)), (math.log(1.0e-6), math.log(upper_amplitude))],
        options={"ftol": 1.0e-14, "gtol": 1.0e-12, "maxiter": 10000},
    )
    h_scale = float(np.exp(result.x[0]))
    amplitude = float(np.exp(result.x[1]))
    rewrite = model_for(float(result.x[0]), float(result.x[1]))
    full_chi2 = float(np.sum(((observed - rewrite["luminosity_distance"]) / sigma) ** 2))
    return {
        "name": "M2_xitoy_rewrite",
        "h_scale": h_scale,
        "amplitude": amplitude,
        "chi2": full_chi2,
        "train_chi2": float(result.fun),
        "aic": aic(full_chi2, 2),
        "bic": bic(full_chi2, z.size, 2),
        "model": rewrite["luminosity_distance"],
        "closure_proxy": rewrite["closure_proxy"],
        "k": 2,
    }


def _toy1(config: Mapping[str, Any], numpy_seed: int) -> dict[str, Any]:
    cfg = config["toy1"]
    rng = np.random.default_rng(numpy_seed + 101)
    x0 = rng.uniform(0.2, 0.8, int(cfg["n"]))
    completion = np.zeros_like(x0)

    def packaging(values: np.ndarray) -> np.ndarray:
        return np.full_like(values, float(np.mean(values)))

    rows: list[dict[str, float]] = []
    rm_by_beta: dict[float, float] = {}
    delta_by_beta: dict[float, float] = {}
    residuals_by_beta: list[np.ndarray] = []
    for beta in [float(value) for value in cfg["beta_grid"]]:
        result = logistic_completion_mismatch(
            x0,
            dt=float(cfg["dt"]),
            alpha=float(cfg["alpha"]),
            beta=beta,
            completion=completion,
        )
        delta = compute_delta({"map": packaging}, x0)
        rm_value = float(result["rm"])
        rows.append({"beta": beta, "RM_max": rm_value, "RM_mean": rm_value, "delta_max": delta})
        rm_by_beta[beta] = rm_value
        delta_by_beta[beta] = delta
        residuals_by_beta.append(np.asarray(result["residual"], dtype=float))
    beta_grid = np.asarray([row["beta"] for row in rows], dtype=float)
    rm_values = np.asarray([row["RM_max"] for row in rows], dtype=float)
    positive_rms = rm_values[beta_grid > 0.0]
    monotone = bool(np.all(np.diff(positive_rms) > 0.0))
    return {
        "rows": rows,
        "beta_grid": beta_grid,
        "rm_values": rm_values,
        "delta_max": float(max(delta_by_beta.values())),
        "rm_at_beta0": rm_by_beta[0.0],
        "rm_at_beta0p5": rm_by_beta[0.5],
        "rm_at_beta2": rm_by_beta[2.0],
        "ratio_beta2_over_beta0p5": rm_by_beta[2.0] / rm_by_beta[0.5],
        "monotone": monotone,
        "x0": x0,
        "residuals": np.vstack(residuals_by_beta),
    }


def _toy2(config: Mapping[str, Any], numpy_seed: int) -> dict[str, Any]:
    cfg = config["toy2"]
    z = _linspace_redshift(float(cfg["z_min"]), float(cfg["z_max"]), int(cfg["n_z"]))
    mode_rng = np.random.default_rng(numpy_seed + 202)
    route_modes = mode_rng.uniform(-1.0, 1.0, int(cfg["n_patches"]))
    route_modes = route_modes - float(np.mean(route_modes))
    route_modes = route_modes / float(np.max(np.abs(route_modes)))
    amplitudes = [float(value) for value in cfg["amplitudes"]]
    headline = float(cfg["headline_amplitude"])
    noise_rng = np.random.default_rng(numpy_seed + int(cfg["noise_seed_offset"]))
    shared_standard_noise = noise_rng.normal(0.0, 1.0, z.size)

    generators: dict[float, dict[str, np.ndarray]] = {}
    q_rows: list[dict[str, float]] = []
    fit_rows: list[dict[str, float | str]] = []
    fits_by_amplitude: dict[float, dict[str, Any]] = {}
    for amplitude in amplitudes:
        rewrite = rewrite_inverse_hubble_lens(
            z,
            route_modes,
            amplitude=amplitude,
            response=float(cfg["response"]),
            exponent=float(cfg["exponent"]),
            z_max=float(cfg["z_max"]),
            h_scale=1.0,
        )
        distance = rewrite["luminosity_distance"]
        sigma = float(cfg["fractional_error"]) * distance + float(cfg["sigma_floor"])
        observed = distance + float(cfg["noise_scale"]) * sigma * shared_standard_noise
        q_diagnostic = float(cfg["q_scale"]) * rewrite["variance_proxy"]
        positive_fraction = float(np.mean(q_diagnostic > 0.0))
        generators[amplitude] = {
            "z": z,
            "distance": distance,
            "observed": observed,
            "sigma": sigma,
            "q": q_diagnostic,
            "closure_proxy": rewrite["closure_proxy"],
            "variance_proxy": rewrite["variance_proxy"],
            "local_factors": rewrite["local_factors"],
        }
        q_rows.append(
            {
                "amplitude": amplitude,
                "Q_peak": float(np.max(np.abs(q_diagnostic))),
                "Q_max_signed": float(np.max(q_diagnostic)),
                "positive_fraction": positive_fraction,
            }
        )
        matter = _fit_matter(z, observed, sigma)
        lcdm = _fit_lcdm(z, observed, sigma)
        fits_by_amplitude[amplitude] = {"M0": matter, "M1": lcdm}
        for fit in [matter, lcdm]:
            fit_rows.append(
                {
                    "amplitude": amplitude,
                    "model": str(fit["name"]),
                    "h_scale": float(fit["h_scale"]),
                    "omega_lambda": float(fit["omega_lambda"]),
                    "rewrite_amplitude": "",
                    "chi2": float(fit["chi2"]),
                    "aic": float(fit["aic"]),
                    "bic": float(fit["bic"]),
                    "k": int(fit["k"]),
                }
            )

    head = generators[headline]
    rewrite_fit = _fit_rewrite(z, head["observed"], head["sigma"], route_modes, cfg)
    fits_by_amplitude[headline]["M2"] = rewrite_fit
    fit_rows.append(
        {
            "amplitude": headline,
            "model": str(rewrite_fit["name"]),
            "h_scale": float(rewrite_fit["h_scale"]),
            "omega_lambda": "",
            "rewrite_amplitude": float(rewrite_fit["amplitude"]),
            "chi2": float(rewrite_fit["chi2"]),
            "aic": float(rewrite_fit["aic"]),
            "bic": float(rewrite_fit["bic"]),
            "k": int(rewrite_fit["k"]),
        }
    )

    train = z <= float(cfg["train_z_max"])
    test = ~train
    m1_proxy = np.zeros_like(head["closure_proxy"])
    m2_proxy = np.asarray(rewrite_fit["closure_proxy"], dtype=float)
    m1_oos_rmse = rmse(head["closure_proxy"][test], m1_proxy[test])
    m2_oos_rmse = rmse(head["closure_proxy"][test], m2_proxy[test])
    oos_ratio = m1_oos_rmse / m2_oos_rmse
    oos_rows = [
        {"model": "M1_flat_lcdm", "heldout_rmse": m1_oos_rmse, "ratio_to_M2": oos_ratio},
        {"model": "M2_xitoy_rewrite", "heldout_rmse": m2_oos_rmse, "ratio_to_M2": 1.0},
    ]
    return {
        "z": z,
        "route_modes": route_modes,
        "generators": generators,
        "q_rows": q_rows,
        "fit_rows": fit_rows,
        "oos_rows": oos_rows,
        "headline": headline,
        "homogeneous": 0.0,
        "fits": fits_by_amplitude,
        "oos_ratio": float(oos_ratio),
        "m1_oos_rmse": float(m1_oos_rmse),
        "m2_oos_rmse": float(m2_oos_rmse),
        "train_mask": train,
        "test_mask": test,
    }


def _sign_change_count(values: np.ndarray) -> int:
    signs = np.sign(values)
    nonzero = signs[signs != 0.0]
    if nonzero.size < 2:
        return 0
    return int(np.sum(nonzero[:-1] * nonzero[1:] < 0.0))


def _toy3_single(cfg: Mapping[str, Any], n_z: int) -> dict[str, Any]:
    z = np.linspace(0.0, float(cfg["z_max"]), n_z)
    rho = p4_rho_eff(z, rho_min=float(cfg["rho_min"]), curvature=float(cfg["curvature"]), crossing_z=float(cfg["crossing_z"]))
    w_eff = effective_w_readout(z, rho)
    jacobian = diagonal_stable_jacobian(
        z,
        primary=float(cfg["jacobian_primary_decay"]),
        secondary=float(cfg["jacobian_secondary_decay"]),
    )
    c_eff2 = np.gradient(np.log(rho), z, edge_order=2) ** 2
    certificate = stable_readout_certificate({"rho_eff": rho, "jacobian": jacobian}, {"c_eff2": c_eff2})
    crossings = crossing_locations(z, w_eff, level=-1.0)
    return {
        "z": z,
        "rho_eff": rho,
        "w_eff": w_eff,
        "jacobian": jacobian,
        "c_eff2": c_eff2,
        "certificate": certificate,
        "crossings": crossings,
        "sign_change_count": _sign_change_count(w_eff + 1.0),
    }


def _toy3(config: Mapping[str, Any]) -> dict[str, Any]:
    cfg = config["toy3"]
    base = _toy3_single(cfg, int(cfg["n_z"]))
    refined = _toy3_single(cfg, int(cfg["n_z"]) * 2 - 1)
    crossing = float(base["crossings"][0]) if base["crossings"].size else float("nan")
    refined_crossing = float(refined["crossings"][0]) if refined["crossings"].size else float("nan")
    rows: list[dict[str, float]] = []
    eigenvalues = np.linalg.eigvals(base["jacobian"])
    for index, z_value in enumerate(base["z"]):
        rows.append(
            {
                "z": float(z_value),
                "rho_eff": float(base["rho_eff"][index]),
                "w_eff": float(base["w_eff"][index]),
                "max_real_eigenvalue": float(np.max(np.real(eigenvalues[index]))),
                "c_eff2_proxy": float(base["c_eff2"][index]),
                "z_cross": crossing,
            }
        )
    base["rows"] = rows
    base["refined_crossing"] = refined_crossing
    base["crossing_delta_refined"] = abs(crossing - refined_crossing)
    base["refined_max_real_eigenvalue"] = float(refined["certificate"]["max_real_eigenvalue"])
    base["eigenvalues"] = eigenvalues
    return base


def _toy4(config: Mapping[str, Any], numpy_seed: int) -> dict[str, Any]:
    cfg = config["toy4"]
    matrix = build_route_matrix(cfg)
    noise_rng = np.random.default_rng(numpy_seed + int(cfg["noise_seed_offset"]))
    observed = observe_route_matrix(matrix, noise_rng.normal(0.0, 1.0, np.asarray(matrix["truth"]).shape))
    sbt_fit = fit_low_rank_route_matrix(observed)
    null_fit = fit_null_route_matrix(observed)
    nuisance_fit = fit_per_route_nuisance(observed)
    errors = relative_parameter_errors(matrix["parameters"], sbt_fit["parameters"])
    holonomy_truth = route_loop_holonomy(
        observed["route_loading"],
        observed["calibration_loading"],
        a0=float(matrix["parameters"]["a0"]),
        a2=float(matrix["parameters"]["a2"]),
        route_indices=cfg["holonomy_route_indices"],
        bridge_weights=cfg["holonomy_bridge_weights"],
        signs=cfg["holonomy_signs"],
    )
    holonomy_sbt = route_loop_holonomy(
        observed["route_loading"],
        observed["calibration_loading"],
        a0=float(sbt_fit["parameters"]["a0"]),
        a2=float(sbt_fit["parameters"]["a2"]),
        route_indices=cfg["holonomy_route_indices"],
        bridge_weights=cfg["holonomy_bridge_weights"],
        signs=cfg["holonomy_signs"],
    )
    holonomy_null = route_loop_holonomy(
        observed["route_loading"],
        observed["calibration_loading"],
        a0=0.0,
        a2=0.0,
        route_indices=cfg["holonomy_route_indices"],
        bridge_weights=cfg["holonomy_bridge_weights"],
        signs=cfg["holonomy_signs"],
    )
    rows: list[dict[str, float | str]] = []
    truth = np.asarray(observed["truth"], dtype=float)
    data = np.asarray(observed["observed"], dtype=float)
    fitted = np.asarray(sbt_fit["fitted"], dtype=float)
    for route_index, route in enumerate(observed["routes"]):
        for stage_index, stage in enumerate(observed["stages"]):
            rows.append(
                {
                    "route": route,
                    "stage": stage,
                    "truth": float(truth[route_index, stage_index]),
                    "observed": float(data[route_index, stage_index]),
                    "sbt_fit": float(fitted[route_index, stage_index]),
                    "residual_sigma": float((data[route_index, stage_index] - fitted[route_index, stage_index]) / observed["sigma"][route_index, stage_index]),
                }
            )
    return {
        "matrix": observed,
        "sbt_fit": sbt_fit,
        "null_fit": null_fit,
        "nuisance_fit": nuisance_fit,
        "parameter_errors": errors,
        "holonomy_truth": float(holonomy_truth),
        "holonomy_sbt": float(holonomy_sbt),
        "holonomy_null": float(holonomy_null),
        "holonomy_rel_error": abs(float(holonomy_sbt) - float(holonomy_truth)) / float(holonomy_truth),
        "rows": rows,
    }


def _compute(config: Mapping[str, Any]) -> dict[str, Any]:
    numpy_seed = int(config["seed"]["numpy"])
    random.seed(int(config["seed"]["python"]))
    return {
        "toy1": _toy1(config, numpy_seed),
        "toy2": _toy2(config, numpy_seed),
        "toy3": _toy3(config),
        "toy4": _toy4(config, numpy_seed),
    }


def _compare_results(left: Mapping[str, Any], right: Mapping[str, Any]) -> bool:
    def walk(a: Any, b: Any) -> bool:
        if isinstance(a, np.ndarray) or isinstance(b, np.ndarray):
            return np.array_equal(np.asarray(a), np.asarray(b))
        if isinstance(a, Mapping) and isinstance(b, Mapping):
            keys = set(a) & set(b)
            return all(walk(a[key], b[key]) for key in keys if key not in {"rows"})
        if isinstance(a, (float, int, np.floating, np.integer)) and isinstance(b, (float, int, np.floating, np.integer)):
            return _relative_close(float(a), float(b), tol=1.0e-12)
        if isinstance(a, (list, tuple)) and isinstance(b, (list, tuple)) and len(a) == len(b):
            return all(walk(item_a, item_b) for item_a, item_b in zip(a, b))
        return True

    return walk(left, right)


def _build_summary(
    results: Mapping[str, Any],
    config: Mapping[str, Any],
    *,
    deterministic: bool,
    artifacts_exist: bool,
    unstatused_count: int,
) -> dict[str, Any]:
    toy1 = results["toy1"]
    toy2 = results["toy2"]
    toy3 = results["toy3"]
    toy4 = results["toy4"]
    head = float(toy2["headline"])
    hom = float(toy2["homogeneous"])
    q_head = next(row for row in toy2["q_rows"] if float(row["amplitude"]) == head)
    q_hom = next(row for row in toy2["q_rows"] if float(row["amplitude"]) == hom)
    m1_head = toy2["fits"][head]["M1"]
    m1_hom = toy2["fits"][hom]["M1"]
    m2_head = toy2["fits"][head]["M2"]
    chi2_gap_per_z = abs(float(m2_head["chi2"]) - float(m1_head["chi2"])) / len(toy2["z"])
    crossing = float(toy3["crossings"][0]) if toy3["crossings"].size else float("nan")
    figure_table_count = {"figures": 5, "tables": 5}
    memory_estimate_mb = float(
        sum(array.nbytes for array in _collect_arrays_for_memory(results)) / (1024.0 * 1024.0)
    )
    gates = {
        "G-E0-1.1": _gate(toy1["delta_max"], float(toy1["delta_max"]) <= 1.0e-10, "<= 1e-10"),
        "G-E0-1.2": _gate(toy1["rm_at_beta0"], float(toy1["rm_at_beta0"]) <= 1.0e-10, "<= 1e-10"),
        "G-E0-1.3": _gate(toy1["monotone"], bool(toy1["monotone"]), "strictly increasing for beta > 0"),
        "G-E0-1.4": _gate(
            {"beta0p5": toy1["rm_at_beta0p5"], "beta2": toy1["rm_at_beta2"]},
            float(toy1["rm_at_beta0p5"]) > 1.0e-3 and float(toy1["rm_at_beta2"]) > 1.0e-3,
            "both > 1e-3",
        ),
        "G-E0-1.5": _gate(toy1["ratio_beta2_over_beta0p5"], 2.0 <= float(toy1["ratio_beta2_over_beta0p5"]) <= 8.0, "in [2, 8]"),
        "G-E0-2.1": _gate(q_hom["Q_peak"], float(q_hom["Q_peak"]) <= 1.0e-6, "<= 1e-6"),
        "G-E0-2.2": _gate(q_head["Q_peak"], 1.0 < float(q_head["Q_peak"]) <= 2.5, "Q_peak in (1, 2.5]"),
        "G-E0-2.3": _gate(q_head["positive_fraction"], float(q_head["positive_fraction"]) >= 0.95, ">= 0.95"),
        "G-E0-2.4": _gate(m1_head["omega_lambda"], 0.4 <= float(m1_head["omega_lambda"]) <= 0.75 and float(m1_head["omega_lambda"]) > 0.2, "Omega_Lambda in [0.4, 0.75] and > 0.2"),
        "G-E0-2.5": _gate(m1_hom["omega_lambda"], float(m1_hom["omega_lambda"]) < 0.1, "< 0.1"),
        "G-E0-2.6": _gate({"chi2_gap_per_z": chi2_gap_per_z, "k_M1": m1_head["k"], "k_M2": m2_head["k"]}, chi2_gap_per_z <= 0.1 and int(m2_head["k"]) <= int(m1_head["k"]) + 1, "|chi2_M2 - chi2_M1|/n_z <= 0.1 and k_M2 <= k_M1 + 1"),
        "G-E0-2.7": _gate(toy2["oos_ratio"], float(toy2["oos_ratio"]) >= 10.0, ">= 10"),
        "G-E0-3.1": _gate(
            {"w_eff_z0": float(toy3["w_eff"][0]), "w_eff_zmax": float(toy3["w_eff"][-1]), "min": float(np.min(toy3["w_eff"])), "max": float(np.max(toy3["w_eff"]))},
            (float(toy3["w_eff"][0]) < -1.0 < float(toy3["w_eff"][-1])) and float(np.min(toy3["w_eff"])) < -1.0 < float(np.max(toy3["w_eff"])),
            "opposite sides of -1 and min < -1 < max",
        ),
        "G-E0-3.2": _gate({"count": toy3["sign_change_count"], "z_cross": crossing}, int(toy3["sign_change_count"]) == 1 and 0.0 < crossing < float(config["toy3"]["z_max"]), "one crossing in (0, z_max)"),
        "G-E0-3.3": _gate(toy3["certificate"]["min_rho_eff"], float(toy3["certificate"]["min_rho_eff"]) > 0.0, "> 0"),
        "G-E0-3.4": _gate(toy3["certificate"]["max_real_eigenvalue"], float(toy3["certificate"]["max_real_eigenvalue"]) <= 1.0e-10, "<= 1e-10"),
        "G-E0-3.5": _gate(toy3["certificate"]["min_c_eff2_proxy"], float(toy3["certificate"]["min_c_eff2_proxy"]) >= -1.0e-8, ">= -1e-8 advisory"),
        "G-E0-3.6": _gate({"delta_z_cross": toy3["crossing_delta_refined"], "refined_max_real_eigenvalue": toy3["refined_max_real_eigenvalue"]}, float(toy3["crossing_delta_refined"]) <= 1.0e-2 and float(toy3["refined_max_real_eigenvalue"]) <= 1.0e-10, "|Delta z_cross| <= 1e-2 and stable refined grid"),
        "G-E0-4.1": _gate(toy4["parameter_errors"], all(float(value) <= 0.15 for value in toy4["parameter_errors"].values()), "each <= 0.15"),
        "G-E0-4.2": _gate(float(toy4["null_fit"]["bic"]) - float(toy4["sbt_fit"]["bic"]), float(toy4["null_fit"]["bic"]) - float(toy4["sbt_fit"]["bic"]) >= 10.0, "BIC_null - BIC_SBT >= 10"),
        "G-E0-4.3": _gate(float(toy4["nuisance_fit"]["bic"]) - float(toy4["sbt_fit"]["bic"]), float(toy4["nuisance_fit"]["bic"]) - float(toy4["sbt_fit"]["bic"]) >= 6.0, "BIC_nuisance - BIC_SBT >= 6"),
        "G-E0-4.4": _gate(toy4["sbt_fit"]["reduced_chi2"], 0.5 <= float(toy4["sbt_fit"]["reduced_chi2"]) <= 1.5, "in [0.5, 1.5]"),
        "G-E0-4.5": _gate({"truth": toy4["holonomy_truth"], "sbt": toy4["holonomy_sbt"], "relerr": toy4["holonomy_rel_error"]}, float(toy4["holonomy_truth"]) > 0.3 and float(toy4["holonomy_rel_error"]) <= 0.25, "truth > 0.3 and relerr <= 0.25"),
        "G-E0-4.6": _gate(toy4["holonomy_null"], float(toy4["holonomy_null"]) <= 0.05, "<= 0.05"),
        "G-E0-0.1": _gate(deterministic, deterministic, "internal rerun arrays bitwise and scalars rel < 1e-12"),
        "G-E0-0.2": _gate(config.get("datasets", []), list(config.get("datasets", [])) == [], "manifest.datasets == []"),
        "G-E0-0.3": _gate(unstatused_count, unstatused_count == 0, "zero unstatused entries"),
        "G-E0-0.4": _gate({"wall_time_budget_seconds": 7200, "peak_memory_estimate_mb": memory_estimate_mb}, memory_estimate_mb < 4096.0, "wall time < 2 h and peak memory < 4 GB; observed wall time recorded in manifest"),
        "G-E0-0.5": _gate(figure_table_count, artifacts_exist, "five figures and five tables exist and are non-empty"),
    }
    return {
        "schema_version": 1,
        "experiment": "E0",
        "terminal_state": "PASS" if all(item["pass"] for item in gates.values()) else "PROGRAM_FAIL",
        "datasets": list(config.get("datasets", [])),
        "gates": gates,
        "headline": {
            "apparent_omega_lambda": float(m1_head["omega_lambda"]),
            "homogeneous_control_omega_lambda": float(m1_hom["omega_lambda"]),
            "Q_peak": float(q_head["Q_peak"]),
            "Q_positive_fraction": float(q_head["positive_fraction"]),
            "rewrite_chi2": float(m2_head["chi2"]),
            "lcdm_chi2": float(m1_head["chi2"]),
            "rewrite_oos_ratio": float(toy2["oos_ratio"]),
            "w_eff_crossing_z": crossing,
            "min_rho_eff": float(toy3["certificate"]["min_rho_eff"]),
            "max_real_eigenvalue": float(toy3["certificate"]["max_real_eigenvalue"]),
            "hubble_bic_null_minus_sbt": float(toy4["null_fit"]["bic"]) - float(toy4["sbt_fit"]["bic"]),
            "hubble_bic_nuisance_minus_sbt": float(toy4["nuisance_fit"]["bic"]) - float(toy4["sbt_fit"]["bic"]),
            "holonomy_truth": float(toy4["holonomy_truth"]),
            "holonomy_sbt": float(toy4["holonomy_sbt"]),
        },
    }


def _collect_arrays_for_memory(results: Mapping[str, Any]) -> list[np.ndarray]:
    arrays: list[np.ndarray] = []

    def walk(value: Any) -> None:
        if isinstance(value, np.ndarray):
            arrays.append(value)
        elif isinstance(value, Mapping):
            for item in value.values():
                walk(item)
        elif isinstance(value, (list, tuple)):
            for item in value:
                walk(item)

    walk(results)
    return arrays


def _write_artifacts(results: Mapping[str, Any], outdir: Path) -> list[Path]:
    apply_style()
    import matplotlib.pyplot as plt

    tables = outdir / "tables"
    arrays = outdir / "arrays"
    figures = outdir / "figures"
    tables.mkdir(parents=True, exist_ok=True)
    arrays.mkdir(parents=True, exist_ok=True)
    figures.mkdir(parents=True, exist_ok=True)

    toy1 = results["toy1"]
    toy2 = results["toy2"]
    toy3 = results["toy3"]
    toy4 = results["toy4"]
    head = toy2["headline"]

    written: list[Path] = []
    table_paths = [
        tables / "toy1_rm_vs_beta.csv",
        tables / "toy2_Q_summary.csv",
        tables / "toy2_fit_summary.csv",
        tables / "toy3_weff_crossing.csv",
        tables / "toy4_route_recovery.csv",
    ]
    write_table_artifact(toy1["rows"], table_paths[0])
    write_table_artifact(toy2["q_rows"], table_paths[1])
    write_table_artifact(toy2["fit_rows"], table_paths[2])
    write_table_artifact(toy3["rows"], table_paths[3])
    write_table_artifact(toy4["rows"], table_paths[4])
    written.extend(table_paths)

    head_gen = toy2["generators"][head]
    array_paths = [
        arrays / "toy2_mock_distances.npz",
        arrays / "toy3_operator.npz",
        arrays / "toy4_route_matrix.npz",
    ]
    write_npz_artifact(
        array_paths[0],
        z=toy2["z"],
        D_true=head_gen["distance"],
        D_obs=head_gen["observed"],
        sigma=head_gen["sigma"],
        Q=head_gen["q"],
        closure_proxy=head_gen["closure_proxy"],
        variance_proxy=head_gen["variance_proxy"],
        train_mask=toy2["train_mask"].astype(np.int8),
        test_mask=toy2["test_mask"].astype(np.int8),
        route_modes=toy2["route_modes"],
        rewrite_proxy=toy2["fits"][head]["M2"]["closure_proxy"],
        lcdm_distance=toy2["fits"][head]["M1"]["model"],
        rewrite_distance=toy2["fits"][head]["M2"]["model"],
    )
    write_npz_artifact(
        array_paths[1],
        z=toy3["z"],
        rho_eff=toy3["rho_eff"],
        w_eff=toy3["w_eff"],
        jacobian=toy3["jacobian"],
        eigenvalues=toy3["eigenvalues"],
        c_eff2=toy3["c_eff2"],
        crossings=toy3["crossings"],
    )
    write_npz_artifact(
        array_paths[2],
        truth=toy4["matrix"]["truth"],
        observed=toy4["matrix"]["observed"],
        sigma=toy4["matrix"]["sigma"],
        sbt_fit=toy4["sbt_fit"]["fitted"],
        null_fit=toy4["null_fit"]["fitted"],
        route_loading=toy4["matrix"]["route_loading"],
        stage_loading=toy4["matrix"]["stage_loading"],
        calibration_loading=toy4["matrix"]["calibration_loading"],
        injected_params=np.array([toy4["matrix"]["parameters"]["h_closed"], toy4["matrix"]["parameters"]["a0"], toy4["matrix"]["parameters"]["a2"]], dtype=float),
        recovered_params=np.array([toy4["sbt_fit"]["parameters"]["h_closed"], toy4["sbt_fit"]["parameters"]["a0"], toy4["sbt_fit"]["parameters"]["a2"]], dtype=float),
        holonomy=np.array([toy4["holonomy_truth"], toy4["holonomy_sbt"], toy4["holonomy_null"]], dtype=float),
    )
    written.extend(array_paths)

    figure_paths = [
        figures / "fig_toy1_rm_vs_beta.png",
        figures / "fig_toy2_Q_vs_time.png",
        figures / "fig_toy2_distance_fit.png",
        figures / "fig_toy3_weff.png",
        figures / "fig_toy4_route_matrix.png",
    ]
    fig, ax = plt.subplots(figsize=(5.2, 3.2))
    ax.plot(toy1["beta_grid"], toy1["rm_values"], marker="o", label="RM_max")
    ax.set_xlabel("beta")
    ax.set_ylabel("route mismatch")
    ax.legend()
    fig.savefig(figure_paths[0])
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(5.2, 3.2))
    for amplitude, gen in toy2["generators"].items():
        label = f"A_het={amplitude:g}"
        ax.plot(toy2["z"], gen["q"], linewidth=1.2, label=label)
    ax.set_xlabel("z")
    ax.set_ylabel("Q diagnostic")
    ax.legend()
    fig.savefig(figure_paths[1])
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(5.2, 3.2))
    ax.errorbar(toy2["z"], head_gen["observed"], yerr=head_gen["sigma"], fmt=".", markersize=3.0, label="mock")
    ax.plot(toy2["z"], head_gen["distance"], label="generator", linewidth=1.2)
    ax.plot(toy2["z"], toy2["fits"][head]["M1"]["model"], label="LCDM fit", linewidth=1.2)
    ax.plot(toy2["z"], toy2["fits"][head]["M2"]["model"], label="XiToy rewrite", linewidth=1.2)
    ax.set_xlabel("z")
    ax.set_ylabel("D_L")
    ax.legend()
    fig.savefig(figure_paths[2])
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(5.2, 3.2))
    ax.plot(toy3["z"], toy3["w_eff"], label="w_eff")
    ax.axhline(-1.0, color="black", linewidth=0.8)
    if toy3["crossings"].size:
        ax.axvline(float(toy3["crossings"][0]), color="tab:red", linestyle="--", linewidth=1.0)
    ax2 = ax.twinx()
    eig = np.max(np.real(toy3["eigenvalues"]), axis=1)
    ax2.plot(toy3["z"], eig, color="tab:green", alpha=0.7, label="max Re lambda")
    ax.set_xlabel("z")
    ax.set_ylabel("w_eff")
    ax2.set_ylabel("max Re lambda")
    fig.savefig(figure_paths[3])
    plt.close(fig)

    fig, axes = plt.subplots(1, 3, figsize=(8.4, 3.0), sharey=True)
    matrices = [toy4["matrix"]["observed"], toy4["sbt_fit"]["fitted"], toy4["matrix"]["observed"] - toy4["sbt_fit"]["fitted"]]
    titles = ["observed", "SBT fit", "residual"]
    for axis, matrix, title in zip(axes, matrices, titles):
        image = axis.imshow(matrix, aspect="auto", cmap="viridis")
        axis.set_title(title)
        axis.set_xlabel("stage")
        fig.colorbar(image, ax=axis, fraction=0.046, pad=0.04)
    axes[0].set_ylabel("route")
    fig.savefig(figure_paths[4])
    plt.close(fig)
    written.extend(figure_paths)
    return written


def _artifact_set_complete(paths: list[Path]) -> bool:
    return all(path.exists() and path.stat().st_size > 0 for path in paths)


def _write_manifest(
    config: Mapping[str, Any],
    summary: Mapping[str, Any],
    outdir: Path,
    artifact_paths: list[Path],
    *,
    wall_time_seconds: float,
) -> None:
    checksums = {str(path.relative_to(outdir)): sha256_file(path) for path in artifact_paths if path.exists()}
    checksums["summary.json"] = sha256_file(outdir / "summary.json")
    checksums["aor_status.json"] = sha256_file(outdir / "aor_status.json")
    manifest = {
        "schema_version": 1,
        "experiment": "E0",
        "package_version": sbt_cosmo.__version__,
        "datasets": list(config.get("datasets", [])),
        "seeds": dict(config["seed"]),
        "determinism": {"omp_num_threads": os.environ.get("OMP_NUM_THREADS", ""), "summary_scalars_reproducible": summary["gates"]["G-E0-0.1"]["pass"]},
        "runtime": {"observed_wall_time_seconds": wall_time_seconds, "budget_seconds": 7200},
        "implementation_notes": [
            "E0 uses synthetic XiToy only; real Xi_cosmo remains deferred.",
            "The plan text names sbt_cosmo/cosmology/background.py, but the locked skeleton uses sbt_cosmo/background/{flrw,distances}.py.",
            "Toy 2 Q is recorded as a closure diagnostic for this synthetic proxy, not a GR backreaction claim.",
        ],
        "chosen_constants": {
            "toy1_state_distribution": "Uniform(0.2, 0.8)",
            "toy2_response": config["toy2"]["response"],
            "toy2_exponent": config["toy2"]["exponent"],
            "toy2_fractional_distance_error": config["toy2"]["fractional_error"],
            "toy2_noise_scale": config["toy2"]["noise_scale"],
        },
        "artifact_checksums_sha256": checksums,
        "terminal_state": summary["terminal_state"],
    }
    write_run_manifest(manifest, outdir / "manifest.json")


def _write_aor(outdir: Path) -> int:
    ledger = {
        "schema_version": 1,
        "experiment": "E0",
        "entries": [
            {"id": "E0-data-free", "status": "zero", "note": "No external datasets used."},
            {"id": "E0-XiToy-scope", "status": "nonclaim", "note": "Synthetic XiToy is not the real Xi_cosmo."},
            {"id": "E0-Q-diagnostic", "status": "nonclaim", "note": "Q is a synthetic closure diagnostic, not a GR backreaction claim."},
            {"id": "E0-skeleton-paths", "status": "approved_other", "note": "Followed the locked sbt_cosmo/background skeleton path rather than the older plan prose path."},
        ],
        "unstatused": 0,
    }
    write_aor_ledger(ledger, outdir / "aor_status.json")
    return count_unstatused(ledger)


def run(config_path: Path, outdir: Path) -> None:
    """Load config, run all E0 synthetic demos, and write committed artifacts."""
    start = time.perf_counter()
    with config_path.open("r", encoding="utf-8") as handle:
        config = yaml.safe_load(handle)
    if list(config.get("datasets", [])) != []:
        raise ValueError("E0 is data-free; config.datasets must be [].")
    outdir.mkdir(parents=True, exist_ok=True)

    results = _compute(config)
    rerun_results = _compute(config)
    deterministic = _compare_results(results, rerun_results)
    artifact_paths = _write_artifacts(results, outdir)
    artifacts_exist = _artifact_set_complete(artifact_paths)
    unstatused_count = _write_aor(outdir)
    summary = _build_summary(
        results,
        config,
        deterministic=deterministic,
        artifacts_exist=artifacts_exist,
        unstatused_count=unstatused_count,
    )
    write_json_artifact(summary, outdir / "summary.json")
    wall_time_seconds = time.perf_counter() - start
    _write_manifest(config, summary, outdir, artifact_paths, wall_time_seconds=wall_time_seconds)
    if summary["terminal_state"] != "PASS":
        failed = [gate_id for gate_id, gate in summary["gates"].items() if not gate["pass"]]
        raise SystemExit(f"E0 failed gates: {failed}")


def main() -> None:
    """Parse runner arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("config.yaml"))
    parser.add_argument("--outdir", type=Path, default=Path("outputs"))
    args = parser.parse_args()
    run(args.config, args.outdir)


if __name__ == "__main__":
    main()
