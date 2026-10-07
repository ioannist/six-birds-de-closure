#!/usr/bin/env python3
"""Run R0 Hubble power/exactness pre-mortem.

This runner intentionally uses only closed-form Gaussian fits. It freezes the
R0 bridge-affinity orientation before any affinity scoring, then evaluates the
R0-A power gate on the external Hubble routes from the corrected E4 value
manifest. R0-B is evaluated only if R0-A passes.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
R0_MANIFEST = ROOT / "data" / "manifests" / "r0_bridge_affinities.json"
E4_VALUE_MANIFEST = ROOT / "results" / "E4" / "E4_ROUTE_VALUE_MANIFEST.json"
RESULTS = ROOT / "results" / "R0"
RUNS = ROOT / "runs" / "R0" / "R0_hubble_power_exactness"

EXTERNAL_ROUTES = [
    "cepheid_sn",
    "trgb_sn",
    "jwst_trgb_sn",
    "jagb_sn",
    "time_delay",
    "siren",
]

IN_SAMPLE_EXCLUDED = ["cmb_bao", "inverse_ladder"]

BRIDGE_FAMILY = {
    "cepheid_sn": "Cepheid",
    "trgb_sn": "TRGB",
    "jwst_trgb_sn": "TRGB",
    "jagb_sn": "JAGB",
    "time_delay": "time_delay",
    "siren": "siren",
}

ROUTE_FAMILY = {
    "cepheid_sn": "cepheid",
    "trgb_sn": "CCHP",
    "jwst_trgb_sn": "CCHP",
    "jagb_sn": "CCHP",
    "time_delay": "time_delay",
    "siren": "siren",
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_sha256(obj: Any) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def write_json(path: Path, obj: Any) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as fh:
        json.dump(obj, fh, indent=2, sort_keys=True)
        fh.write("\n")
    return sha256_file(path)


def load_json(path: Path) -> Any:
    with path.open() as fh:
        return json.load(fh)


def freeze_orientation() -> dict[str, Any]:
    """Freeze structural orientation fields before any affinity scoring."""
    manifest = load_json(R0_MANIFEST)
    manifest_hash = sha256_file(R0_MANIFEST)

    convention = manifest.get("orientation_convention")
    if not convention or str(convention).startswith("TODO"):
        convention = (
            "positive edge orientation is the manifest i->j direction; "
            "cycle orientation is heldout_edges followed by tree_path_edges "
            "as declared in the locked manifest"
        )

    edges = []
    for edge in manifest["edges"]:
        edges.append(
            {
                "edge_id": edge["edge_id"],
                "i": edge["i"],
                "j": edge["j"],
                "orientation": edge.get("orientation") or f"{edge['i']}->{edge['j']}",
            }
        )

    cycles = []
    for cycle in manifest["test_cycles"]:
        orientation = cycle.get("orientation")
        if not orientation or str(orientation).startswith("TODO"):
            orientation = {
                "rule": "heldout_edges_then_tree_path_edges",
                "edge_order": list(cycle.get("heldout_edges", [])) + list(cycle.get("tree_path_edges", [])),
                "edge_sign_rule": "use manifest i->j as +1; reverse traversal would be -1",
            }
        cycles.append(
            {
                "cycle_id": cycle["cycle_id"],
                "orientation": orientation,
                "heldout_edges": list(cycle.get("heldout_edges", [])),
                "tree_path_edges": list(cycle.get("tree_path_edges", [])),
            }
        )

    payload = {
        "schema_version": 1,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source_manifest": str(R0_MANIFEST.relative_to(ROOT)),
        "source_manifest_sha256": manifest_hash,
        "orientation_convention": convention,
        "edge_orientations": edges,
        "cycle_orientations": cycles,
        "anti_posthoc_note": (
            "This file records route/edge/cycle orientation only. Numeric bridge-affinity "
            "values are not scored before this orientation payload is written."
        ),
    }
    payload["orientation_payload_sha256"] = canonical_sha256(payload)
    freeze_path = RESULTS / "R0_orientation_freeze.json"
    file_hash = write_json(freeze_path, payload)
    payload["orientation_freeze_file"] = str(freeze_path.relative_to(ROOT))
    payload["orientation_freeze_file_sha256"] = file_hash
    return payload


def _route_value(route: dict[str, Any]) -> tuple[float, float]:
    value_keys = ["h0", "H0", "value", "H0_km_s_Mpc", "mean"]
    sigma_keys = ["sigma", "sigma_sym", "uncertainty", "err", "std"]
    value = None
    sigma = None
    for key in value_keys:
        if key in route:
            value = route[key]
            break
    for key in sigma_keys:
        if key in route:
            sigma = route[key]
            break
    if value is None and "measurement" in route:
        meas = route["measurement"]
        for key in value_keys:
            if key in meas:
                value = meas[key]
                break
        for key in sigma_keys:
            if key in meas:
                sigma = meas[key]
                break
    if value is None or sigma is None:
        raise KeyError(f"Cannot parse H0 value/sigma from route: {route}")
    return float(value), float(sigma)


@dataclass
class RouteData:
    route_id: str
    h0: float
    sigma: float
    bridge: str
    family: str
    provenance: dict[str, Any]


def load_external_routes() -> list[RouteData]:
    manifest = load_json(E4_VALUE_MANIFEST)
    by_id = {r["route_id"]: r for r in manifest["routes"]}
    missing = [r for r in EXTERNAL_ROUTES if r not in by_id]
    if missing:
        raise KeyError(f"E4 value manifest missing external routes: {missing}")
    leaked = [r for r in IN_SAMPLE_EXCLUDED if r in EXTERNAL_ROUTES]
    if leaked:
        raise RuntimeError(f"in-sample routes leaked into R0 external set: {leaked}")
    routes = []
    for rid in EXTERNAL_ROUTES:
        h0, sigma = _route_value(by_id[rid])
        routes.append(
            RouteData(
                route_id=rid,
                h0=h0,
                sigma=sigma,
                bridge=BRIDGE_FAMILY[rid],
                family=ROUTE_FAMILY[rid],
                provenance=by_id[rid],
            )
        )
    return routes


def build_covariance(
    routes: list[RouteData],
    shared_mb_sigma: float = 0.7,
    shared_trgb_anchor_sigma: float = 1.0,
) -> tuple[np.ndarray, dict[str, Any]]:
    """Build the external-route covariance from E4 shared-calibration assumptions."""
    n = len(routes)
    C = np.diag([r.sigma**2 for r in routes])
    ids = [r.route_id for r in routes]
    stellar = {"cepheid_sn", "trgb_sn", "jwst_trgb_sn", "jagb_sn"}
    for i, ri in enumerate(ids):
        for j, rj in enumerate(ids):
            if i >= j:
                continue
            if ri in stellar and rj in stellar:
                C[i, j] += shared_mb_sigma**2
                C[j, i] += shared_mb_sigma**2
            if {ri, rj} == {"trgb_sn", "jwst_trgb_sn"}:
                C[i, j] += shared_trgb_anchor_sigma**2
                C[j, i] += shared_trgb_anchor_sigma**2
    C, jitter = ensure_pd(C)
    assumptions = {
        "source": str(E4_VALUE_MANIFEST.relative_to(ROOT)),
        "external_routes_only": EXTERNAL_ROUTES,
        "hard_excluded_in_sample_routes": IN_SAMPLE_EXCLUDED,
        "shared_SN_zero_point_M_B_sigma": shared_mb_sigma,
        "shared_SN_zero_point_M_B_covariance": shared_mb_sigma**2,
        "shared_TRGB_anchor_sigma_between_trgb_and_jwst_trgb": shared_trgb_anchor_sigma,
        "shared_TRGB_anchor_covariance": shared_trgb_anchor_sigma**2,
        "approximation_floor_sigma_external_routes": 0.0,
        "pd_jitter_added": jitter,
    }
    return C, assumptions


def ensure_pd(C: np.ndarray) -> tuple[np.ndarray, float]:
    eig = np.linalg.eigvalsh(C)
    min_eig = float(np.min(eig))
    if min_eig > 1e-10:
        return C, 0.0
    jitter = abs(min_eig) + 1e-8
    return C + np.eye(C.shape[0]) * jitter, jitter


def effective_n(C: np.ndarray) -> dict[str, Any]:
    d = np.sqrt(np.diag(C))
    corr = C / np.outer(d, d)
    eig = np.linalg.eigvalsh(corr)
    neff = float((np.sum(eig) ** 2) / np.sum(eig**2))
    return {
        "N_routes": int(C.shape[0]),
        "N_eff": neff,
        "threshold": 5.0,
        "pass": bool(neff >= 5.0),
        "correlation_eigenvalues": [float(x) for x in eig],
        "definition": "(sum eigenvalues of route correlation matrix)^2 / sum eigenvalues^2",
    }


def design_matrix(routes: list[RouteData], model: str) -> tuple[np.ndarray, list[str]]:
    n = len(routes)
    cols = [np.ones(n)]
    names = ["H0"]
    if model == "M_0":
        return np.column_stack(cols), names
    if model == "M_bridge":
        cats = sorted({r.bridge for r in routes})
        ref = cats[0]
        for cat in cats[1:]:
            cols.append(np.array([1.0 if r.bridge == cat else 0.0 for r in routes]))
            names.append(f"bridge[{cat}]_minus_{ref}")
        return np.column_stack(cols), names
    if model == "M_family":
        cats = sorted({r.family for r in routes})
        ref = cats[0]
        for cat in cats[1:]:
            cols.append(np.array([1.0 if r.family == cat else 0.0 for r in routes]))
            names.append(f"family[{cat}]_minus_{ref}")
        return np.column_stack(cols), names
    if model == "M_saturated":
        ref = routes[0].route_id
        for route in routes[1:]:
            cols.append(np.array([1.0 if r.route_id == route.route_id else 0.0 for r in routes]))
            names.append(f"route[{route.route_id}]_minus_{ref}")
        return np.column_stack(cols), names
    raise ValueError(f"unknown model: {model}")


def fit_gls(y: np.ndarray, C: np.ndarray, X: np.ndarray) -> dict[str, Any]:
    Cinv = np.linalg.pinv(C, rcond=1e-12)
    fisher = X.T @ Cinv @ X
    beta_cov = np.linalg.pinv(fisher, rcond=1e-12)
    beta = beta_cov @ (X.T @ Cinv @ y)
    pred = X @ beta
    resid = y - pred
    chi2 = float(resid.T @ Cinv @ resid)
    return {"beta": beta, "beta_cov": beta_cov, "pred": pred, "resid": resid, "chi2": chi2}


def logpdf_normal(x: float, mean: float, var: float) -> float:
    var = float(var)
    if not math.isfinite(var) or var <= 0:
        raise ValueError("predictive variance must be finite and positive")
    return -0.5 * (math.log(2.0 * math.pi * var) + ((x - mean) ** 2) / var)


def loo_pointwise_plugin(y: np.ndarray, C: np.ndarray, X: np.ndarray) -> np.ndarray:
    """Plug-in row-wise LOO that ignores residual cross-covariance conditioning.

    Kept only as a diagnostic. Gate decisions use ``loo_pointwise_conditional``.
    """
    vals = []
    n = len(y)
    for i in range(n):
        keep = [j for j in range(n) if j != i]
        C_train = C[np.ix_(keep, keep)]
        X_train = X[keep, :]
        y_train = y[keep]
        fit = fit_gls(y_train, C_train, X_train)
        xi = X[i, :]
        pred = float(xi @ fit["beta"])
        var = float(C[i, i] + xi @ fit["beta_cov"] @ xi.T)
        vals.append(logpdf_normal(float(y[i]), pred, var))
    return np.array(vals)


class UnidentifiedPrediction(ValueError):
    """A held-out contrast is not determined by the training design."""


def loo_pointwise_conditional(y: np.ndarray, C: np.ndarray, X: np.ndarray) -> np.ndarray:
    """Exact conditional Gaussian leave-one-route-out predictive density.

    For each held-out route ``i``, fit the linear Gaussian model to the other
    routes under their correlated covariance block, then evaluate the closed-form
    conditional predictive density

        y_i | y_o ~ N(C_io C_oo^-1 y_o + A beta_hat,
                     C_ii - C_io C_oo^-1 C_oi + A Cov(beta) A^T)

    where ``A = x_i - C_io C_oo^-1 X_o``. This is the multivariate-Gaussian LOO
    quantity used by the R0 gate. The covariance must be positive definite,
    and every held-out contrast must be estimable from the training design.
    A pseudoinverse alone does not provide a prior on unidentified parameters.
    """
    vals = []
    n = len(y)
    np.linalg.cholesky(C)
    for i in range(n):
        keep = [j for j in range(n) if j != i]
        C_oo = C[np.ix_(keep, keep)]
        C_io = C[np.ix_([i], keep)]
        C_oi = C[np.ix_(keep, [i])]
        C_oo_inv = np.linalg.pinv(C_oo, rcond=1e-12)
        X_o = X[keep, :]
        y_o = y[keep]
        fit = fit_gls(y_o, C_oo, X_o)
        xi = X[i : i + 1, :]
        gain = C_io @ C_oo_inv
        A = xi - gain @ X_o
        row_projector = np.linalg.pinv(X_o, rcond=1e-12) @ X_o
        if np.linalg.norm(A - A @ row_projector) > 1e-10 * max(1.0, float(np.linalg.norm(A))):
            raise UnidentifiedPrediction(f"held-out route {i} is not estimable; an explicit prior is required")
        pred = float((gain @ y_o.reshape(-1, 1) + A @ fit["beta"].reshape(-1, 1))[0, 0])
        conditional_var = float(C[i, i] - (gain @ C_oi)[0, 0])
        param_var = float((A @ fit["beta_cov"] @ A.T)[0, 0])
        vals.append(logpdf_normal(float(y[i]), pred, conditional_var + param_var))
    return np.array(vals)


def score_model(name: str, routes: list[RouteData], y: np.ndarray, C: np.ndarray) -> dict[str, Any]:
    X, param_names = design_matrix(routes, name)
    fit = fit_gls(y, C, X)
    n = len(y)
    k = X.shape[1]
    try:
        loo = loo_pointwise_conditional(y, C, X)
        loo_status = "identified"
    except UnidentifiedPrediction as error:
        loo = None
        loo_status = str(error)
    loo_plugin = loo_pointwise_plugin(y, C, X)
    elpd = float(np.sum(loo)) if loo is not None else None
    se = (float(math.sqrt(n * np.var(loo, ddof=1))) if n > 1 else 0.0) if loo is not None else None
    elpd_plugin = float(np.sum(loo_plugin))
    se_plugin = float(math.sqrt(n * np.var(loo_plugin, ddof=1))) if n > 1 else 0.0
    return {
        "model": name,
        "k": int(k),
        "chi2": fit["chi2"],
        "BIC": float(fit["chi2"] + k * math.log(n)),
        "AIC": float(fit["chi2"] + 2 * k),
        "AIC_proxy": float(fit["chi2"] + 2 * k),
        "elpd_LOO": elpd,
        "SE_elpd_LOO": se,
        "elpd_LOO_type": "conditional_correlated_gaussian" if loo is not None else "unidentified_without_prior",
        "elpd_LOO_status": loo_status,
        "elpd_LOO_plugin": elpd_plugin,
        "SE_elpd_LOO_plugin": se_plugin,
        "penalized_score": float(fit["chi2"] + k * math.log(n)),
        "param_names": param_names,
        "params": [float(x) for x in fit["beta"]],
        "predicted_H0": {r.route_id: float(v) for r, v in zip(routes, fit["pred"])},
        "residuals": {r.route_id: float(v) for r, v in zip(routes, fit["resid"])},
        "loo_pointwise": [float(x) for x in loo] if loo is not None else None,
        "loo_pointwise_plugin": [float(x) for x in loo_plugin],
    }


def score_all(routes: list[RouteData], C: np.ndarray) -> dict[str, dict[str, Any]]:
    y = np.array([r.h0 for r in routes], dtype=float)
    return {model: score_model(model, routes, y, C) for model in ("M_0", "M_bridge", "M_family", "M_saturated")}


def add_deltas(scores: dict[str, dict[str, Any]]) -> None:
    null = scores["M_0"]
    for name, score in scores.items():
        if score["loo_pointwise"] is not None and null["loo_pointwise"] is not None:
            diff = np.array(score["loo_pointwise"]) - np.array(null["loo_pointwise"])
            se_delta = float(math.sqrt(len(diff) * np.var(diff, ddof=1))) if len(diff) > 1 else 0.0
            delta_elpd = float(score["elpd_LOO"] - null["elpd_LOO"])
        else:
            se_delta = None
            delta_elpd = None
        score["delta_vs_M0"] = {
            "delta_BIC_null_minus_model": float(null["BIC"] - score["BIC"]),
            "delta_AIC_proxy_null_minus_model": float(null["AIC_proxy"] - score["AIC_proxy"]),
            "delta_elpd_LOO_model_minus_null": delta_elpd,
            "SE_delta_elpd_LOO": se_delta,
            "elpd_rule_pass": bool(delta_elpd is not None and se_delta > 0 and delta_elpd >= 2.0 * se_delta),
            "BIC_rule_pass": bool((null["BIC"] - score["BIC"]) >= 6.0),
            "AIC_proxy_report_only": "AIC_proxy = chi2 + 2k; not a WAIC and not used for G-R0-POWER",
        }


def heldout_logpredict(
    train_routes: list[RouteData],
    test_routes: list[RouteData],
    train_C: np.ndarray,
    full_C: np.ndarray,
    full_index: dict[str, int],
    model: str,
) -> float:
    y_train = np.array([r.h0 for r in train_routes])
    X_train, _ = design_matrix(train_routes, model)
    fit = fit_gls(y_train, train_C, X_train)

    # Use the same model coding from the training set for held-out rows. For
    # unseen categories, the indicator is zero, so the prediction falls back to
    # the learned common quotient. This is the intended OOS penalty for
    # over-specific oracles.
    _, param_names = design_matrix(train_routes, model)
    test_X = []
    ref_names = param_names[1:]
    for route in test_routes:
        row = [1.0]
        for name in ref_names:
            if name.startswith("bridge["):
                cat = name.split("[", 1)[1].split("]", 1)[0]
                row.append(1.0 if route.bridge == cat else 0.0)
            elif name.startswith("family["):
                cat = name.split("[", 1)[1].split("]", 1)[0]
                row.append(1.0 if route.family == cat else 0.0)
            elif name.startswith("route["):
                rid = name.split("[", 1)[1].split("]", 1)[0]
                row.append(1.0 if route.route_id == rid else 0.0)
            else:
                row.append(0.0)
        test_X.append(row)
    train_idx = [full_index[r.route_id] for r in train_routes]
    test_idx = [full_index[r.route_id] for r in test_routes]
    C_to = full_C[np.ix_(test_idx, train_idx)]
    C_tt = full_C[np.ix_(test_idx, test_idx)]
    gain = np.linalg.solve(train_C, C_to.T).T
    A = np.asarray(test_X) - gain @ X_train
    projector = np.linalg.pinv(X_train, rcond=1e-12) @ X_train
    if np.linalg.norm(A - A @ projector) > 1e-10 * max(1.0, float(np.linalg.norm(A))):
        raise UnidentifiedPrediction("family holdout has unidentified predictive contrasts")
    mean = gain @ y_train + A @ fit["beta"]
    predictive_cov = C_tt - gain @ C_to.T + A @ fit["beta_cov"] @ A.T
    factor = np.linalg.cholesky(0.5 * (predictive_cov + predictive_cov.T))
    residual = np.array([r.h0 for r in test_routes]) - mean
    whitened = np.linalg.solve(factor, residual)
    return float(-0.5 * (len(test_routes) * math.log(2 * math.pi)
                        + 2 * np.log(np.diag(factor)).sum() + whitened @ whitened))


def leave_one_family_out(routes: list[RouteData], C: np.ndarray) -> dict[str, Any]:
    families = sorted({r.family for r in routes})
    full_index = {r.route_id: i for i, r in enumerate(routes)}
    rows = []
    for family in families:
        train_idx = [i for i, r in enumerate(routes) if r.family != family]
        test_idx = [i for i, r in enumerate(routes) if r.family == family]
        train_routes = [routes[i] for i in train_idx]
        test_routes = [routes[i] for i in test_idx]
        C_train = C[np.ix_(train_idx, train_idx)]
        null_elpd = heldout_logpredict(train_routes, test_routes, C_train, C, full_index, "M_0")
        candidates = {}
        for model in ("M_bridge", "M_family"):
            candidates[model] = heldout_logpredict(train_routes, test_routes, C_train, C, full_index, model)
        best_model = max(candidates, key=candidates.get)
        best_elpd = candidates[best_model]
        rows.append(
            {
                "heldout_family": family,
                "n_heldout": len(test_routes),
                "null_elpd": float(null_elpd),
                "best_non_saturated_model": best_model,
                "best_non_saturated_elpd": float(best_elpd),
                "delta_elpd_best_minus_null": float(best_elpd - null_elpd),
                "beats_null": bool(best_elpd > null_elpd),
            }
        )
    return {"rows": rows, "pass": bool(all(r["beats_null"] for r in rows))}


def power_gate(
    routes: list[RouteData],
    scores: dict[str, dict[str, Any]],
    neff: dict[str, Any],
    lofo: dict[str, Any],
    stress: dict[str, Any],
) -> dict[str, Any]:
    non_sat = [scores["M_bridge"], scores["M_family"]]
    oracle_wins = []
    for score in non_sat:
        d = score["delta_vs_M0"]
        oracle_wins.append(
            {
                "model": score["model"],
                "BIC_rule_pass": d["BIC_rule_pass"],
                "elpd_rule_pass": d["elpd_rule_pass"],
                "passes_any": bool(d["BIC_rule_pass"] or d["elpd_rule_pass"]),
                "delta_BIC_null_minus_model": d["delta_BIC_null_minus_model"],
                "delta_elpd_LOO_model_minus_null": d["delta_elpd_LOO_model_minus_null"],
                "SE_delta_elpd_LOO": d["SE_delta_elpd_LOO"],
                "delta_AIC_proxy_null_minus_model": d["delta_AIC_proxy_null_minus_model"],
            }
        )
    at_least_one_oracle = any(r["passes_any"] for r in oracle_wins)
    saturated = scores["M_saturated"]
    zero_control = {
        "saturated_chi2": saturated["chi2"],
        "chi2_zero": bool(abs(saturated["chi2"]) < 1e-8),
        "saturated_penalized_score": saturated["penalized_score"],
        "best_non_saturated_or_null_penalized_score": float(
            min(scores[m]["penalized_score"] for m in ("M_0", "M_bridge", "M_family"))
        ),
        "saturated_loses_on_penalized_score": bool(
            saturated["penalized_score"] > min(scores[m]["penalized_score"] for m in ("M_0", "M_bridge", "M_family"))
        ),
    }
    gate_pass = bool(neff["pass"] and at_least_one_oracle and lofo["pass"] and stress["pass"])
    return {
        "gate_id": "G-R0-POWER",
        "pass": gate_pass,
        "conjuncts": {
            "N_eff_ge_5": neff,
            "non_saturated_oracle_beats_M0": {"pass": at_least_one_oracle, "oracle_wins": oracle_wins},
            "leave_one_family_out_beats_null": lofo,
            "covariance_stress_survives": stress,
            "saturated_zero_control": zero_control,
        },
        "route_partition": {
            "external_routes_used": [r.route_id for r in routes],
            "hard_excluded_in_sample_routes": IN_SAMPLE_EXCLUDED,
        },
    }


def covariance_stress(routes: list[RouteData]) -> dict[str, Any]:
    C, assumptions = build_covariance(routes, shared_mb_sigma=0.95, shared_trgb_anchor_sigma=1.35)
    scores = score_all(routes, C)
    add_deltas(scores)
    non_sat = [scores["M_bridge"], scores["M_family"]]
    rows = []
    for score in non_sat:
        d = score["delta_vs_M0"]
        rows.append(
            {
                "model": score["model"],
                "delta_BIC_null_minus_model": d["delta_BIC_null_minus_model"],
                "delta_elpd_LOO_model_minus_null": d["delta_elpd_LOO_model_minus_null"],
                "SE_delta_elpd_LOO": d["SE_delta_elpd_LOO"],
                "delta_AIC_proxy_null_minus_model": d["delta_AIC_proxy_null_minus_model"],
                "passes_any": bool(d["BIC_rule_pass"] or d["elpd_rule_pass"]),
            }
        )
    return {
        "stress_assumptions": assumptions,
        "rows": rows,
        "pass": bool(any(r["passes_any"] for r in rows)),
    }


def graph_diagnostics(power_pass: bool) -> dict[str, Any]:
    manifest = load_json(R0_MANIFEST)
    routes = {r["route_id"] for r in manifest["routes"]}
    edges = manifest["edges"]
    parent: dict[str, str] = {}

    def find(x: str) -> str:
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for route in routes:
        parent[route] = route
    for edge in edges:
        a, b = find(edge["i"]), find(edge["j"])
        if a != b:
            parent[a] = b
    components = len({find(r) for r in routes})
    beta_structural = len(edges) - len(routes) + components
    beta_decisive = int(manifest["cycle_availability"]["beta1_decisive_eligible"])
    edge_type_counts: dict[str, int] = {}
    for edge in edges:
        edge_type_counts[edge["edge_type"]] = edge_type_counts.get(edge["edge_type"], 0) + 1
    cycles = []
    for cycle in manifest["test_cycles"]:
        held_types = [next(e for e in edges if e["edge_id"] == eid)["edge_type"] for eid in cycle["heldout_edges"]]
        cycles.append(
            {
                "cycle_id": cycle["cycle_id"],
                "decisive_eligible": bool(cycle.get("decisive_eligible")),
                "structurally_closed": bool(cycle.get("structurally_closed")),
                "heldout_edges": cycle.get("heldout_edges", []),
                "tree_path_edges": cycle.get("tree_path_edges", []),
                "heldout_edge_types": held_types,
            }
        )
    if not power_pass:
        status = "skipped_power_failed"
        gate = {"gate_id": "G-R0-EXACTNESS", "status": status, "pass": None}
    elif beta_decisive == 0:
        status = "exact_vacuous_beta1_decisive_eligible_zero"
        gate = {
            "gate_id": "G-R0-EXACTNESS",
            "status": status,
            "pass": False,
            "reason": "No held-out decisive-eligible cycle in locked manifest.",
        }
    else:
        status = "blocked_requires_numeric_affinity_fetch"
        gate = {
            "gate_id": "G-R0-EXACTNESS",
            "status": status,
            "pass": False,
            "reason": "Unexpected positive decisive rank; numeric affinity fetch/scoring not implemented in this packet.",
        }
    return {
        "status": status,
        "beta1_structural": int(beta_structural),
        "beta1_decisive_eligible": beta_decisive,
        "edge_type_counts": edge_type_counts,
        "cycles": cycles,
        "G-R0-EXACTNESS": gate,
    }


def write_power_outputs(
    routes: list[RouteData],
    C: np.ndarray,
    cov_assumptions: dict[str, Any],
    scores: dict[str, dict[str, Any]],
    neff: dict[str, Any],
    lofo: dict[str, Any],
    stress: dict[str, Any],
    gate: dict[str, Any],
) -> dict[str, str]:
    RESULTS.mkdir(parents=True, exist_ok=True)
    serial_scores = []
    for score in scores.values():
        row = {k: v for k, v in score.items() if k not in {"loo_pointwise", "predicted_H0", "residuals", "params", "param_names"}}
        row.update(
            {
                "params": score["params"],
                "param_names": score["param_names"],
                "predicted_H0": score["predicted_H0"],
                "residuals": score["residuals"],
            }
        )
        serial_scores.append(row)

    power_json = {
        "schema_version": 1,
        "routes": [
            {
                "route_id": r.route_id,
                "H0": r.h0,
                "sigma": r.sigma,
                "bridge_family": r.bridge,
                "route_family": r.family,
            }
            for r in routes
        ],
        "covariance": {
            "route_order": [r.route_id for r in routes],
            "matrix": C.tolist(),
            "assumptions": cov_assumptions,
        },
        "models": serial_scores,
        "gate": gate,
    }
    hashes = {}
    hashes["power_json"] = write_json(RESULTS / "R0_power_oracles.json", power_json)

    with (RESULTS / "R0_power_oracles.csv").open("w", newline="") as fh:
        fieldnames = [
            "model",
            "chi2",
            "k",
            "BIC",
            "AIC",
            "AIC_proxy",
            "elpd_LOO",
            "SE_elpd_LOO",
            "elpd_LOO_plugin",
            "SE_elpd_LOO_plugin",
            "delta_BIC_null_minus_model",
            "delta_elpd_LOO_model_minus_null",
            "SE_delta_elpd_LOO",
            "delta_AIC_proxy_null_minus_model",
            "penalized_score",
        ]
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        for score in scores.values():
            d = score["delta_vs_M0"]
            writer.writerow(
                {
                    "model": score["model"],
                    "chi2": score["chi2"],
                    "k": score["k"],
                    "BIC": score["BIC"],
                    "AIC": score["AIC"],
                    "AIC_proxy": score["AIC_proxy"],
                    "elpd_LOO": score["elpd_LOO"],
                    "SE_elpd_LOO": score["SE_elpd_LOO"],
                    "elpd_LOO_plugin": score["elpd_LOO_plugin"],
                    "SE_elpd_LOO_plugin": score["SE_elpd_LOO_plugin"],
                    "delta_BIC_null_minus_model": d["delta_BIC_null_minus_model"],
                    "delta_elpd_LOO_model_minus_null": d["delta_elpd_LOO_model_minus_null"],
                    "SE_delta_elpd_LOO": d["SE_delta_elpd_LOO"],
                    "delta_AIC_proxy_null_minus_model": d["delta_AIC_proxy_null_minus_model"],
                    "penalized_score": score["penalized_score"],
                }
            )
    hashes["power_csv"] = sha256_file(RESULTS / "R0_power_oracles.csv")
    hashes["neff_json"] = write_json(RESULTS / "R0_neff.json", neff)
    hashes["lofo_covstress_json"] = write_json(
        RESULTS / "R0_loFo_covstress.json",
        {"leave_one_family_out": lofo, "covariance_stress": stress},
    )
    zero = gate["conjuncts"]["saturated_zero_control"]
    hashes["zero_control_json"] = write_json(RESULTS / "R0_power_zero_control.json", zero)
    return hashes


def update_aor_status(status: dict[str, Any]) -> None:
    path = ROOT / "results" / "aor_status_table.csv"
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = ["experiment", "gate", "aor_status", "terminal_state", "next_front", "notes"]
    rows = []
    if path.exists():
        with path.open(newline="") as fh:
            reader = csv.DictReader(fh)
            if reader.fieldnames == fieldnames:
                rows = [r for r in reader if r.get("experiment") != "R0"]
    rows.append(
        {
            "experiment": "R0",
            "gate": "G-R0-POWER/G-R0-EXACTNESS",
            "aor_status": status["aor_status"],
            "terminal_state": status["terminal_state"],
            "next_front": status["next_front"],
            "notes": status["bridge_row_status"],
        }
    )
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    start = time.perf_counter()
    for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
        os.environ.setdefault(var, "1")

    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)

    orientation = freeze_orientation()

    routes = load_external_routes()
    C, cov_assumptions = build_covariance(routes)
    neff = effective_n(C)
    scores = score_all(routes, C)
    add_deltas(scores)
    lofo = leave_one_family_out(routes, C)
    stress = covariance_stress(routes)
    gate = power_gate(routes, scores, neff, lofo, stress)
    power_hashes = write_power_outputs(routes, C, cov_assumptions, scores, neff, lofo, stress, gate)

    graph = graph_diagnostics(bool(gate["pass"]))
    graph_hash = write_json(RESULTS / "R0_affinity_graph.json", graph)
    if graph["status"] == "skipped_power_failed":
        cycle = {
            "status": "skipped_power_failed",
            "reason": "R0-B exactness is evaluated only if G-R0-POWER passes.",
            "G-R0-EXACTNESS": graph["G-R0-EXACTNESS"],
        }
        exact_null = {
            "status": "skipped_power_failed",
            "flat_exact_form_control": None,
            "orientation_permutation_null": None,
            "reason": "R0-B skipped by R0-A power failure.",
        }
    elif graph["beta1_decisive_eligible"] == 0:
        cycle = {
            "status": graph["status"],
            "A_gamma": None,
            "p_global": None,
            "reason": "No decisive-eligible held-out cycles in locked manifest.",
            "G-R0-EXACTNESS": graph["G-R0-EXACTNESS"],
        }
        exact_null = {
            "status": graph["status"],
            "flat_exact_form_control": {"A_gamma": 0.0, "interpretation": "vacuous exact-form control"},
            "orientation_permutation_null": None,
            "reason": "No decisive cycle to permute.",
        }
    else:
        cycle = {"status": graph["status"], "G-R0-EXACTNESS": graph["G-R0-EXACTNESS"]}
        exact_null = {"status": graph["status"]}
    cycle_hash = write_json(RESULTS / "R0_cycle_holonomy.json", cycle)
    exact_hash = write_json(RESULTS / "R0_exactform_null.json", exact_null)

    if gate["pass"]:
        if graph["G-R0-EXACTNESS"].get("pass") is True:
            aor_status = "promotable"
            terminal_state = "BRANCH_E4B"
            next_front = "E4b"
            bridge_row_status = "bridge obstruction promotable"
        else:
            aor_status = "nonclaim"
            terminal_state = "ACCEPTED_NEGATIVE"
            next_front = "E5"
            bridge_row_status = "objectivity-not-earned (exact-form null)"
    else:
        aor_status = "blocked"
        terminal_state = "ACCEPTED_NEGATIVE"
        next_front = "E5"
        bridge_row_status = "objectivity-not-earned / underpowered"

    status = {
        "schema_version": 1,
        "terminal_state": terminal_state,
        "aor_status": aor_status,
        "next_front": next_front,
        "bridge_row_status": bridge_row_status,
        "G-R0-POWER": gate,
        "G-R0-EXACTNESS": graph["G-R0-EXACTNESS"],
        "E4b_branch": "promote" if terminal_state == "BRANCH_E4B" else "skip",
        "program_fail": False,
        "runtime_seconds": float(time.perf_counter() - start),
    }
    status_hash = write_json(RESULTS / "R0_status.json", status)
    update_aor_status(status)

    run_manifest = {
        "schema_version": 1,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "inputs": {
            "r0_bridge_affinities": {
                "path": str(R0_MANIFEST.relative_to(ROOT)),
                "sha256": sha256_file(R0_MANIFEST),
            },
            "orientation_freeze": {
                "path": "results/R0/R0_orientation_freeze.json",
                "sha256": sha256_file(RESULTS / "R0_orientation_freeze.json"),
                "payload_sha256": orientation["orientation_payload_sha256"],
            },
            "e4_route_value_manifest": {
                "path": str(E4_VALUE_MANIFEST.relative_to(ROOT)),
                "sha256": sha256_file(E4_VALUE_MANIFEST),
            },
            "runner": {
                "path": "scripts/r0_hubble_power_exactness.py",
                "sha256": sha256_file(ROOT / "scripts" / "r0_hubble_power_exactness.py"),
            },
        },
        "environment_threads": {
            var: os.environ.get(var)
            for var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS")
        },
        "outputs": {
            **power_hashes,
            "orientation_freeze_json": sha256_file(RESULTS / "R0_orientation_freeze.json"),
            "affinity_graph_json": graph_hash,
            "cycle_holonomy_json": cycle_hash,
            "exactform_null_json": exact_hash,
            "status_json": status_hash,
        },
    }
    manifest_hash = write_json(RESULTS / "manifests" / "R0_run_manifest.json", run_manifest)
    summary = {
        "status": status,
        "power_model_table": [
            {
                "model": score["model"],
                "chi2": score["chi2"],
                "k": score["k"],
                "BIC": score["BIC"],
                "elpd_LOO": score["elpd_LOO"],
                "SE_elpd_LOO": score["SE_elpd_LOO"],
                "delta_vs_M0": score["delta_vs_M0"],
            }
            for score in scores.values()
        ],
        "N_eff": neff,
        "orientation_freeze_sha256": sha256_file(RESULTS / "R0_orientation_freeze.json"),
        "run_manifest_sha256": manifest_hash,
    }
    write_json(RUNS / "summary.json", summary)

    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
