"""Synthetic Hubble route-matrix builder and low-rank fit."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import numpy as np

from sbt_cosmo.audits.metrics import bic
from sbt_cosmo.hubble.routes import HUBBLE_ROUTE_IDS, validate_hubble_route_id


def build_route_matrix(config: Mapping[str, Any]) -> Any:
    """Build the H0 route matrix H0^(r, ell) from route-tagged inputs."""
    routes = tuple(config.get("routes", HUBBLE_ROUTE_IDS))
    for route in routes:
        validate_hubble_route_id(route)
    stages = tuple(config["stages"])
    h_closed = float(config["h_closed"])
    a0 = float(config["a0"])
    a2 = float(config["a2"])
    sigma = float(config["sigma"])
    route_loading = np.asarray(config["route_loading"], dtype=float)
    stage_loading = np.asarray(config["stage_loading"], dtype=float)
    calibration_loading = np.asarray(config["calibration_loading"], dtype=float)
    if route_loading.shape != (len(routes),):
        raise ValueError("route_loading length must match routes.")
    if calibration_loading.shape != (len(routes),):
        raise ValueError("calibration_loading length must match routes.")
    if stage_loading.shape != (len(stages),):
        raise ValueError("stage_loading length must match stages.")
    truth = (
        h_closed
        + a0 * route_loading[:, None]
        + a2 * np.outer(calibration_loading, stage_loading)
    )
    sigma_matrix = np.full_like(truth, sigma, dtype=float)
    return {
        "routes": routes,
        "stages": stages,
        "truth": truth,
        "sigma": sigma_matrix,
        "route_loading": route_loading,
        "stage_loading": stage_loading,
        "calibration_loading": calibration_loading,
        "parameters": {"h_closed": h_closed, "a0": a0, "a2": a2},
    }


def observe_route_matrix(matrix: Mapping[str, Any], noise: Any) -> dict[str, Any]:
    """Add deterministic caller-supplied noise to a synthetic route matrix."""
    truth = np.asarray(matrix["truth"], dtype=float)
    sigma = np.asarray(matrix["sigma"], dtype=float)
    noise_arr = np.asarray(noise, dtype=float)
    if noise_arr.shape != truth.shape:
        raise ValueError("noise shape must match route matrix truth.")
    observed = truth + sigma * noise_arr
    result = dict(matrix)
    result["observed"] = observed
    return result


def fit_low_rank_route_matrix(matrix: Mapping[str, Any]) -> dict[str, Any]:
    """Fit H_closed, a0, and a2 by weighted least squares."""
    observed = np.asarray(matrix["observed"], dtype=float)
    sigma = np.asarray(matrix["sigma"], dtype=float)
    route_loading = np.asarray(matrix["route_loading"], dtype=float)
    stage_loading = np.asarray(matrix["stage_loading"], dtype=float)
    calibration_loading = np.asarray(matrix["calibration_loading"], dtype=float)
    basis0 = np.ones(observed.size, dtype=float)
    basis1 = np.repeat(route_loading, stage_loading.size)
    basis2 = np.outer(calibration_loading, stage_loading).ravel()
    design = np.column_stack([basis0, basis1, basis2])
    y = observed.ravel()
    w = 1.0 / sigma.ravel() ** 2
    xtw = design.T * w
    params = np.linalg.solve(xtw @ design, xtw @ y)
    fitted = (design @ params).reshape(observed.shape)
    chi2 = float(np.sum(((observed - fitted) / sigma) ** 2))
    dof = observed.size - design.shape[1]
    return {
        "parameters": {"h_closed": float(params[0]), "a0": float(params[1]), "a2": float(params[2])},
        "fitted": fitted,
        "chi2": chi2,
        "dof": int(dof),
        "reduced_chi2": float(chi2 / dof),
        "bic": bic(chi2, observed.size, design.shape[1]),
    }


def fit_null_route_matrix(matrix: Mapping[str, Any]) -> dict[str, Any]:
    """Fit the route-independent Hubble null."""
    observed = np.asarray(matrix["observed"], dtype=float)
    sigma = np.asarray(matrix["sigma"], dtype=float)
    y = observed.ravel()
    w = 1.0 / sigma.ravel() ** 2
    mean = float(np.sum(w * y) / np.sum(w))
    fitted = np.full_like(observed, mean)
    chi2 = float(np.sum(((observed - fitted) / sigma) ** 2))
    return {
        "parameters": {"h_closed": mean},
        "fitted": fitted,
        "chi2": chi2,
        "dof": int(observed.size - 1),
        "reduced_chi2": float(chi2 / (observed.size - 1)),
        "bic": bic(chi2, observed.size, 1),
    }


def fit_per_route_nuisance(matrix: Mapping[str, Any]) -> dict[str, Any]:
    """Return the saturated per-cell nuisance benchmark."""
    observed = np.asarray(matrix["observed"], dtype=float)
    n_parameters = observed.size
    return {
        "parameters": {"nuisance_cells": int(n_parameters)},
        "fitted": observed.copy(),
        "chi2": 0.0,
        "dof": 0,
        "reduced_chi2": 0.0,
        "bic": bic(0.0, observed.size, n_parameters),
    }


def relative_parameter_errors(truth: Mapping[str, float], fit: Mapping[str, float]) -> dict[str, float]:
    """Return absolute relative parameter errors for the low-rank fit."""
    errors: dict[str, float] = {}
    for name, true_value in truth.items():
        denom = max(abs(float(true_value)), np.finfo(float).eps)
        errors[name] = abs(float(fit[name]) - float(true_value)) / denom
    return errors
