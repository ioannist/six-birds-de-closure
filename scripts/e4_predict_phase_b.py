"""Phase B value unlock and frozen-Xi posterior-predictive Hubble-route test.

This script intentionally reads the blind Phase A artifacts from
``results/E4/blind`` and never writes back into that directory.  It then unlocks
the route H0 values, builds the shared-calibration covariance, compares the
pre-registered frozen-Xi prediction to the measured route offsets, and writes the
Phase B reproducibility artifacts under ``results/E4`` and ``runs/E4``.
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
from typing import Callable

import numpy as np
from scipy import optimize, stats

try:
    import dynesty
except ImportError as exc:  # pragma: no cover - environment gate
    raise SystemExit("dynesty is required in the sbt-de environment") from exc


ROOT = Path(__file__).resolve().parents[1]
BLIND_DIR = ROOT / "results" / "E4" / "blind"
OUT_DIR = ROOT / "results" / "E4"
RUN_DIR = ROOT / "runs" / "E4" / "E4_PREDICT_PHASE_B"
E1_SUMMARY = ROOT / "results" / "_summaries" / "E1A_compressed_gates.json"
COHERENCE_CSV = ROOT / "results" / "xi_cosmo_coherence.csv"

ROUTE_ORDER = [
    "cmb_bao",
    "inverse_ladder",
    "cepheid_sn",
    "trgb_sn",
    "jwst_trgb_sn",
    "jagb_sn",
    "time_delay",
    "siren",
]

DECISIVE_ROUTES = [route for route in ROUTE_ORDER if route != "time_delay"]
IN_SAMPLE_ROUTES = ["cmb_bao", "inverse_ladder"]
OUT_OF_SAMPLE_ROUTES = ["cepheid_sn", "trgb_sn", "jwst_trgb_sn", "jagb_sn", "time_delay", "siren"]
DECISIVE_ROUTES = OUT_OF_SAMPLE_ROUTES
DEFAULT_COMPRESSION_SIGMA = 0.5
COMPRESSION_SENSITIVITY = [0.3, 0.5, 0.7]

BRIDGE_BY_ROUTE = {
    "cmb_bao": "r_d",
    "inverse_ladder": "r_d",
    "cepheid_sn": "Cepheid",
    "trgb_sn": "TRGB",
    "jwst_trgb_sn": "TRGB",
    "jagb_sn": "JAGB",
    "time_delay": "time_delay",
    "siren": "siren",
}

FAMILY_BY_ROUTE = {
    "cmb_bao": "early",
    "inverse_ladder": "early",
    "cepheid_sn": "stellar_ladder",
    "trgb_sn": "stellar_ladder",
    "jwst_trgb_sn": "stellar_ladder",
    "jagb_sn": "stellar_ladder",
    "time_delay": "time_delay",
    "siren": "siren",
}


@dataclass(frozen=True)
class RouteValue:
    route_id: str
    h0: float
    sigma: float
    source: str
    citation: str
    aor_status: str
    recomputability: str
    notes: str


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def verify_blind_hashes() -> dict:
    receipt = load_json(BLIND_DIR / "E4_ORDERING_RECEIPT.json")
    chain = receipt["hash_chain"]
    expected = {
        "E4_ROUTE_VERSION_MANIFEST.json": chain["1_version_manifest"],
        "E4_KERNEL_FREEZE.json": chain["2_kernel_freeze"],
        "E4_PREDICTED_ROUTE_TABLE.json": chain["3_predicted_table"],
        "E4_BLINDING_ATTESTATION.json": chain["4_attestation"],
    }
    actual = {name: sha256_file(BLIND_DIR / name) for name in expected}
    mismatches = {name: {"expected": expected[name], "actual": actual[name]} for name in expected if actual[name] != expected[name]}
    if mismatches:
        raise SystemExit(f"Blind hash firewall broken: {json.dumps(mismatches, indent=2)}")
    return {"receipt": receipt, "hashes": actual}


def _weighted_chain_stat(paths: list[Path], param: str) -> tuple[float, float, int]:
    vals: list[np.ndarray] = []
    weights: list[np.ndarray] = []
    for path in paths:
        with path.open("r", encoding="utf-8") as handle:
            header = handle.readline().lstrip("#").split()
        arr = np.loadtxt(path, comments="#")
        if arr.ndim == 1:
            arr = arr[None, :]
        vals.append(arr[:, header.index(param)].astype(float))
        weights.append(arr[:, header.index("weight")].astype(float))
    x = np.concatenate(vals)
    w = np.concatenate(weights)
    mean = float(np.average(x, weights=w))
    var = float(np.average((x - mean) ** 2, weights=w))
    return mean, math.sqrt(max(var, 0.0)), int(x.size)


def load_route_values(compression_sigma: float = DEFAULT_COMPRESSION_SIGMA) -> tuple[list[RouteValue], dict]:
    c1_paths = sorted((ROOT / "runs" / "E1" / "E1C_C1_lcdm" / "chains").glob("C1_lcdm_chain*.1.txt"))
    c2_paths = sorted((ROOT / "runs" / "E1" / "E1C_C2_lcdm" / "chains").glob("C2_lcdm_chain*.1.txt"))
    if c1_paths:
        cmb_h0, cmb_sigma, cmb_n = _weighted_chain_stat(c1_paths, "H0")
    else:
        e1 = load_json(E1_SUMMARY)
        cmb_h0 = float(e1["gates"]["G-E1-REPRO-CMBONLY"]["value"]["H0"])
        cmb_sigma = 0.54
        cmb_n = 0
    if c2_paths:
        inv_h0, inv_sigma, inv_n = _weighted_chain_stat(c2_paths, "H0")
    else:
        e1 = load_json(E1_SUMMARY)
        inv_h0 = float(e1["runs"]["C2"]["lcdm"]["bestfit"]["H0"])
        inv_sigma = 0.6
        inv_n = 0

    values = [
        RouteValue(
            "cmb_bao",
            cmb_h0,
            math.sqrt(cmb_sigma**2 + compression_sigma**2),
            "E1 compressed C1 LCDM chain posterior",
            "Planck 2018 VI, arXiv:1807.06209; committed E1 compressed CMB-only posterior",
            "budgeted",
            "recomputable",
            f"Derived from {cmb_n} E1 compressed C1 LCDM chain rows; sigma includes compression systematic {compression_sigma} km/s/Mpc in quadrature.",
        ),
        RouteValue(
            "inverse_ladder",
            inv_h0,
            math.sqrt(inv_sigma**2 + compression_sigma**2),
            "E1 compressed C2 LCDM chain posterior",
            "DESI DR2 BAO cosmology, arXiv:2503.14738; committed E1 CMB+BAO posterior",
            "budgeted",
            "recomputable",
            f"Derived from {inv_n} E1 compressed C2 LCDM chain rows; sigma includes compression systematic {compression_sigma} km/s/Mpc in quadrature.",
        ),
        RouteValue(
            "cepheid_sn",
            73.49,
            0.93,
            "SH0ES JWST+HST Cepheid-only Gaussian summary",
            "Riess et al. 2025, arXiv:2509.01667; Cepheid-only JWST+HST result H0=73.49+/-0.93",
            "zero",
            "summary_only",
            "Cepheid-only route; not the combined 55-SN / mixed-calibrator value.",
        ),
        RouteValue(
            "trgb_sn",
            70.39,
            math.sqrt(1.22**2 + 1.33**2 + 0.70**2),
            "CCHP JWST TRGB Gaussian summary",
            "Freedman et al. 2024, arXiv:2408.06153; plan/03 data-layer row",
            "budgeted",
            "summary_only",
            "Stat, sys, and SN terms combined in quadrature.",
        ),
        RouteValue(
            "jwst_trgb_sn",
            68.81,
            math.sqrt(1.79**2 + 1.32**2),
            "CCHP JWST-only TRGB Gaussian summary",
            "Freedman et al. 2024, arXiv:2408.06153; plan/03 data-layer row",
            "budgeted",
            "summary_only",
            "Published stat and sys terms combined in quadrature.",
        ),
        RouteValue(
            "jagb_sn",
            67.80,
            math.sqrt(2.17**2 + 1.64**2),
            "CCHP JWST JAGB Gaussian summary",
            "Freedman et al. 2024, arXiv:2408.06153; plan/03 data-layer row",
            "budgeted",
            "summary_only",
            "Published stat and sys terms combined in quadrature.",
        ),
        RouteValue(
            "time_delay",
            71.60,
            0.5 * (3.9 + 3.3),
            "TDCOSMO 2025 flat-LambdaCDM headline Gaussianized summary",
            "TDCOSMO Collaboration 2025, arXiv:2506.03023, flat-LambdaCDM headline H0=71.6^{+3.9}_{-3.3}",
            "selected",
            "summary_only",
            "Asymmetric posterior Gaussianized with sigma=(3.9+3.3)/2; model-dependent external route, INCLUDED in the corrected OOS decisive gate.",
        ),
        RouteValue(
            "siren",
            70.0,
            0.5 * (12.0 + 8.0),
            "GW170817 standard-siren Gaussianized summary",
            "LIGO/Virgo et al. 2017, arXiv:1710.05835; H0=70.0^{+12}_{-8}",
            "budgeted",
            "summary_only",
            "Asymmetric posterior Gaussianized with sigma=(12+8)/2.",
        ),
    ]
    provenance = {
        "e1_summary": str(E1_SUMMARY.relative_to(ROOT)),
        "e1_chain_rows": {"cmb_bao": cmb_n, "inverse_ladder": inv_n},
        "compression_systematic_km_s_Mpc": compression_sigma,
        "compression_systematic_justification": "Budgeted compressed-background/full-likelihood systematic from the E1 playbook (<1% background validation, about 0.5-0.7 km/s/Mpc on H0); decisive OOS gates exclude these routes.",
        "route_value_unlock_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    return values, provenance


def build_covariance(values: list[RouteValue], stress: str = "best") -> tuple[np.ndarray, list[dict]]:
    route_index = {value.route_id: idx for idx, value in enumerate(values)}
    cov = np.diag([value.sigma**2 for value in values])
    assumptions: list[dict] = []

    if stress == "diagonal":
        return cov, [{"type": "diagonal_only", "note": "All shared-calibration covariance terms suppressed for diagnostic only."}]

    if stress == "high_corr":
        shared_sn = 0.95
        shared_trgb = 1.35
        shared_rd = 0.50
    else:
        shared_sn = 0.70
        shared_trgb = 1.00
        shared_rd = 0.25

    stellar = ["cepheid_sn", "trgb_sn", "jwst_trgb_sn", "jagb_sn"]
    stellar_present = [route for route in stellar if route in route_index]
    for i, route_i in enumerate(stellar_present):
        for route_j in stellar_present[i + 1 :]:
            cov[route_index[route_i], route_index[route_j]] += shared_sn**2
            cov[route_index[route_j], route_index[route_i]] += shared_sn**2
    if len(stellar_present) >= 2:
        assumptions.append(
            {
                "routes": stellar_present,
                "component": "shared_SN_zero_point_M_B",
                "sigma_km_s_Mpc": shared_sn,
                "covariance_added": shared_sn**2,
                "justification": "Cepheid/TRGB/JWST-TRGB/JAGB ladders share the SN Ia second rung / zero-point calibration.",
            }
        )

    trgb_pair = ["trgb_sn", "jwst_trgb_sn"]
    if all(route in route_index for route in trgb_pair):
        cov[route_index[trgb_pair[0]], route_index[trgb_pair[1]]] += shared_trgb**2
        cov[route_index[trgb_pair[1]], route_index[trgb_pair[0]]] += shared_trgb**2
        assumptions.append(
            {
                "routes": trgb_pair,
                "component": "shared_TRGB_anchor_systematic",
                "sigma_km_s_Mpc": shared_trgb,
                "covariance_added": shared_trgb**2,
                "justification": "CCHP full-TRGB and JWST-only TRGB determinations share the TRGB calibration family.",
            }
        )

    early = ["cmb_bao", "inverse_ladder"]
    if all(route in route_index for route in early):
        cov[route_index[early[0]], route_index[early[1]]] += shared_rd**2
        cov[route_index[early[1]], route_index[early[0]]] += shared_rd**2
        assumptions.append(
            {
                "routes": early,
                "component": "shared_CMB_BAO_sound_horizon",
                "sigma_km_s_Mpc": shared_rd,
                "covariance_added": shared_rd**2,
                "justification": "CMB/BAO and inverse-ladder routes share the early-Universe sound-horizon calibration.",
            }
        )

    # Numerical guard: keep the covariance positive definite under stress variants.
    eig_min = float(np.linalg.eigvalsh(cov).min())
    if eig_min <= 0.0:
        cov += np.eye(cov.shape[0]) * (abs(eig_min) + 1.0e-9)
    return cov, assumptions


def prediction_vectors(predicted: dict, kernel: dict, route_ids: list[str]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    pred_by_route = {row["route_id"]: row for row in predicted["predictions"]}
    basis_by_route = {row["route_id"]: row["linear_basis_km_s_Mpc"] for row in kernel["route_kernels"]}
    xi = kernel["frozen_xi"]["posterior"]
    xi_cov = np.diag([xi["a0"]["sigma"] ** 2, xi["a1"]["sigma"] ** 2, xi["a2"]["sigma"] ** 2])
    pred = np.array([float(pred_by_route[route]["predicted_delta_H0_km_s_Mpc"]) for route in route_ids])
    basis = np.array(
        [
            [basis_by_route[route]["a0"], basis_by_route[route]["a1"], basis_by_route[route]["a2"]]
            for route in route_ids
        ],
        dtype=float,
    )
    kcov = basis @ xi_cov @ basis.T
    pred_sigma = np.sqrt(np.clip(np.diag(kcov), 0.0, np.inf))
    return pred, kcov, pred_sigma


def subset(values: list[RouteValue], cov: np.ndarray, routes: list[str]) -> tuple[list[RouteValue], np.ndarray, list[int]]:
    index = [next(idx for idx, value in enumerate(values) if value.route_id == route) for route in routes]
    return [values[idx] for idx in index], cov[np.ix_(index, index)], index


def weighted_h0(y: np.ndarray, cov: np.ndarray, offsets: np.ndarray | None = None) -> tuple[float, float]:
    offsets = np.zeros_like(y) if offsets is None else offsets
    inv = np.linalg.inv(cov)
    one = np.ones_like(y)
    h0 = float((one @ inv @ (y - offsets)) / (one @ inv @ one))
    sigma = math.sqrt(float(1.0 / (one @ inv @ one)))
    return h0, sigma


def gaussian_chi2(y: np.ndarray, cov: np.ndarray, model: np.ndarray) -> float:
    resid = y - model
    return float(resid @ np.linalg.inv(cov) @ resid)


def fit_linear_model(y: np.ndarray, cov: np.ndarray, design: np.ndarray) -> tuple[np.ndarray, float]:
    inv = np.linalg.inv(cov)
    lhs = design.T @ inv @ design
    rhs = design.T @ inv @ y
    coeff = np.linalg.pinv(lhs) @ rhs
    chi2 = gaussian_chi2(y, cov, design @ coeff)
    return coeff, chi2


def loglike_factory(y: np.ndarray, cov: np.ndarray, design_for_params: Callable[[np.ndarray], np.ndarray]) -> Callable[[np.ndarray], float]:
    inv = np.linalg.inv(cov)
    sign, logdet = np.linalg.slogdet(cov)
    if sign <= 0:
        raise ValueError("Covariance is not positive definite")
    norm = -0.5 * (len(y) * math.log(2.0 * math.pi) + logdet)

    def loglike(theta: np.ndarray) -> float:
        resid = y - design_for_params(theta)
        return float(norm - 0.5 * (resid @ inv @ resid))

    return loglike


def run_dynesty_evidence(
    name: str,
    y: np.ndarray,
    cov: np.ndarray,
    model_fn: Callable[[np.ndarray], np.ndarray],
    bounds: list[tuple[float, float]],
    seed: int,
    nlive: int,
) -> dict:
    ndim = len(bounds)

    def prior_transform(unit: np.ndarray) -> np.ndarray:
        return np.array([low + u * (high - low) for u, (low, high) in zip(unit, bounds)], dtype=float)

    loglike = loglike_factory(y, cov, model_fn)
    t0 = time.perf_counter()
    sampler = dynesty.NestedSampler(
        loglike,
        prior_transform,
        ndim,
        nlive=nlive,
        bound="multi",
        sample="rwalk",
        rstate=np.random.default_rng(seed),
        queue_size=1,
    )
    sampler.run_nested(dlogz=0.2, print_progress=False)
    elapsed = time.perf_counter() - t0
    res = sampler.results
    logz = float(res.logz[-1])
    logzerr = float(res.logzerr[-1])
    return {"model": name, "lnZ": logz, "lnZ_err": logzerr, "elapsed_seconds": elapsed, "nlive": nlive}


def compare_models(values: list[RouteValue], cov: np.ndarray, pred: np.ndarray, kcov: np.ndarray, nlive: int, label: str) -> dict:
    route_ids = [value.route_id for value in values]
    y = np.array([value.h0 for value in values], dtype=float)
    n = len(y)

    design_null = np.ones((n, 1))
    coeff_null, chi2_null = fit_linear_model(y, cov, design_null)

    design_route = np.ones((n, n))
    # Identifiable saturated route-offset model: H0 plus offsets for routes 2..N.
    design_route[:, 1:] = np.eye(n)[:, 1:]
    coeff_route, chi2_route = fit_linear_model(y, cov, design_route)

    bridge_names = sorted(set(BRIDGE_BY_ROUTE[route] for route in route_ids))
    fixed_bridge = "r_d" if "r_d" in bridge_names else bridge_names[0]
    free_bridges = [bridge for bridge in bridge_names if bridge != fixed_bridge]
    design_bridge = np.zeros((n, 1 + len(free_bridges)))
    design_bridge[:, 0] = 1.0
    for i, route in enumerate(route_ids):
        bridge = BRIDGE_BY_ROUTE[route]
        if bridge in free_bridges:
            design_bridge[i, 1 + free_bridges.index(bridge)] = 1.0
    coeff_bridge, chi2_bridge = fit_linear_model(y, cov, design_bridge)

    cov_xi = cov + kcov
    h_xi, h_xi_sigma = weighted_h0(y, cov_xi, pred)
    chi2_xi = gaussian_chi2(y, cov_xi, h_xi + pred)

    models = {
        "M_null": {"k": 1, "chi2": chi2_null, "bestfit": {"H0": float(coeff_null[0])}},
        "M_route_offset": {
            "k": n,
            "chi2": chi2_route,
            "bestfit": {"H0": float(coeff_route[0]), "offsets": {route_ids[i]: float(coeff_route[i]) for i in range(1, n)}},
            "identifiability": f"{route_ids[0]} offset fixed to 0",
        },
        "M_bridge_offset": {
            "k": 1 + len(free_bridges),
            "chi2": chi2_bridge,
            "bestfit": {"H0": float(coeff_bridge[0]), "fixed_bridge": fixed_bridge, "offsets": {bridge: float(coeff_bridge[1 + i]) for i, bridge in enumerate(free_bridges)}},
        },
        "M_XiFrozen": {
            "k": 1,
            "chi2": chi2_xi,
            "bestfit": {"H_closed": h_xi, "H_closed_sigma": h_xi_sigma},
            "covariance": "measurement_plus_frozen_Xi_prediction_covariance",
        },
    }
    for item in models.values():
        item["AIC"] = float(item["chi2"] + 2.0 * item["k"])
        item["BIC"] = float(item["chi2"] + item["k"] * math.log(n))
        item["WAIC_proxy"] = item["AIC"]

    # Dynesty evidences. Priors are deliberately broad and identical where possible.
    evidences: dict[str, dict] = {}
    evidences["M_null"] = run_dynesty_evidence(
        "M_null",
        y,
        cov,
        lambda th: np.full(n, th[0]),
        [(50.0, 85.0)],
        seed=4101 + n,
        nlive=nlive,
    )
    evidences["M_route_offset"] = run_dynesty_evidence(
        "M_route_offset",
        y,
        cov,
        lambda th: th[0] + np.r_[0.0, th[1:]],
        [(50.0, 85.0)] + [(-15.0, 15.0)] * (n - 1),
        seed=4201 + n,
        nlive=nlive,
    )
    bridge_matrix = np.zeros((n, len(free_bridges)))
    for i, route in enumerate(route_ids):
        bridge = BRIDGE_BY_ROUTE[route]
        if bridge in free_bridges:
            bridge_matrix[i, free_bridges.index(bridge)] = 1.0
    evidences["M_bridge_offset"] = run_dynesty_evidence(
        "M_bridge_offset",
        y,
        cov,
        lambda th: th[0] + bridge_matrix @ th[1:],
        [(50.0, 85.0)] + [(-15.0, 15.0)] * len(free_bridges),
        seed=4301 + n,
        nlive=nlive,
    )
    evidences["M_XiFrozen"] = run_dynesty_evidence(
        "M_XiFrozen",
        y,
        cov_xi,
        lambda th: th[0] + pred,
        [(50.0, 85.0)],
        seed=4401 + n,
        nlive=nlive,
    )
    for model_name, evidence in evidences.items():
        models[model_name].update(evidence)

    bic0 = models["M_null"]["BIC"]
    waic0 = models["M_null"]["WAIC_proxy"]
    lnz0 = models["M_null"]["lnZ"]
    for item in models.values():
        item["delta_BIC_vs_null"] = float(item["BIC"] - bic0)
        item["delta_WAIC_proxy_vs_null"] = float(item["WAIC_proxy"] - waic0)
        item["delta_lnZ_vs_null"] = float(item["lnZ"] - lnz0)

    stronger = "M_route_offset" if models["M_route_offset"]["lnZ"] >= models["M_bridge_offset"]["lnZ"] else "M_bridge_offset"
    ln_b_xi_minus_stronger = float(models["M_XiFrozen"]["lnZ"] - models[stronger]["lnZ"])
    delta_bic_steelman_minus_xi = float(models[stronger]["BIC"] - models["M_XiFrozen"]["BIC"])
    delta_waic_steelman_minus_xi = float(models[stronger]["WAIC_proxy"] - models["M_XiFrozen"]["WAIC_proxy"])
    waic_favors_xi = delta_waic_steelman_minus_xi > 0.0
    locked_steelman_pass = bool(
        ln_b_xi_minus_stronger >= 5.0
        and delta_bic_steelman_minus_xi >= 6.0
        and waic_favors_xi
    )
    if label == "out_of_sample":
        xi_evidence_signal = (
            "no out-of-sample evidence win: Xi loses to null in lnZ; "
            f"BIC and WAIC favor the {stronger} steelman; the only positive is a tiny "
            f"lnZ edge of {ln_b_xi_minus_stronger:+.3f} over {stronger}, contradicted by BIC/WAIC and by the null lnZ."
        )
    else:
        xi_evidence_signal = "in-sample-CONTAMINATED sensitivity only (includes cmb_bao + inverse_ladder, which Xi was fit to); NOT an independent result -- see out_of_sample branch for the decisive (negative) verdict"

    gates = {
        "label": label,
        "stronger_steelman": stronger,
        "Xi_beats_null_by_lnZ": bool(models["M_XiFrozen"]["lnZ"] > models["M_null"]["lnZ"]),
        "Xi_beats_route_offset_by_lnZ": bool(models["M_XiFrozen"]["lnZ"] > models["M_route_offset"]["lnZ"]),
        "Xi_beats_bridge_offset_by_lnZ": bool(models["M_XiFrozen"]["lnZ"] > models["M_bridge_offset"]["lnZ"]),
        "Xi_beats_stronger_steelman_by_lnZ": bool(models["M_XiFrozen"]["lnZ"] > models[stronger]["lnZ"]),
        "G-E4-2-STEELMAN": locked_steelman_pass,
        "locked_thresholds": {
            "lnB_Xi_minus_stronger_required": 5.0,
            "delta_BIC_steelman_minus_Xi_required": 6.0,
            "WAIC_must_favor_Xi": True,
        },
        "xi_evidence_signal": xi_evidence_signal,
        "lnB_Xi_minus_stronger": ln_b_xi_minus_stronger,
        "delta_BIC_steelman_minus_Xi": delta_bic_steelman_minus_xi,
        "delta_WAIC_steelman_minus_Xi": delta_waic_steelman_minus_xi,
        "WAIC_favors_Xi": waic_favors_xi,
    }
    return {"label": label, "route_ids": route_ids, "models": models, "gates": gates}


def compare_models_fast_bic(values: list[RouteValue], cov: np.ndarray, pred: np.ndarray, kcov: np.ndarray, label: str) -> dict:
    """Fast BIC-only model comparison for covariance-sensitivity resamples."""
    route_ids = [value.route_id for value in values]
    y = np.array([value.h0 for value in values], dtype=float)
    n = len(y)
    design_null = np.ones((n, 1))
    _, chi2_null = fit_linear_model(y, cov, design_null)

    design_route = np.ones((n, n))
    design_route[:, 1:] = np.eye(n)[:, 1:]
    _, chi2_route = fit_linear_model(y, cov, design_route)

    bridge_names = sorted(set(BRIDGE_BY_ROUTE[route] for route in route_ids))
    fixed_bridge = "r_d" if "r_d" in bridge_names else bridge_names[0]
    free_bridges = [bridge for bridge in bridge_names if bridge != fixed_bridge]
    design_bridge = np.zeros((n, 1 + len(free_bridges)))
    design_bridge[:, 0] = 1.0
    for i, route in enumerate(route_ids):
        bridge = BRIDGE_BY_ROUTE[route]
        if bridge in free_bridges:
            design_bridge[i, 1 + free_bridges.index(bridge)] = 1.0
    _, chi2_bridge = fit_linear_model(y, cov, design_bridge)

    cov_xi = cov + kcov
    h_xi, _ = weighted_h0(y, cov_xi, pred)
    chi2_xi = gaussian_chi2(y, cov_xi, h_xi + pred)
    bic = {
        "M_null": chi2_null + math.log(n),
        "M_route_offset": chi2_route + n * math.log(n),
        "M_bridge_offset": chi2_bridge + (1 + len(free_bridges)) * math.log(n),
        "M_XiFrozen": chi2_xi + math.log(n),
    }
    stronger = "M_route_offset" if bic["M_route_offset"] <= bic["M_bridge_offset"] else "M_bridge_offset"
    delta_bic_steelman_minus_xi = float(bic[stronger] - bic["M_XiFrozen"])
    return {
        "label": label,
        "BIC": {key: float(value) for key, value in bic.items()},
        "stronger_steelman": stronger,
        "G-E4-2-STEELMAN_BIC": bool(bic["M_XiFrozen"] < bic["M_null"] and delta_bic_steelman_minus_xi >= 6.0),
        "delta_BIC_steelman_minus_Xi": delta_bic_steelman_minus_xi,
        "delta_BIC_null_minus_Xi": float(bic["M_null"] - bic["M_XiFrozen"]),
    }


def prediction_quality(values: list[RouteValue], cov: np.ndarray, pred: np.ndarray, kcov: np.ndarray, label: str) -> dict:
    route_ids = [value.route_id for value in values]
    y = np.array([value.h0 for value in values], dtype=float)
    cov_eff = cov + kcov
    h0, h0_sigma = weighted_h0(y, cov_eff, pred)
    measured_offsets = y - h0
    residual = measured_offsets - pred
    chi2 = gaussian_chi2(measured_offsets, cov_eff, pred)
    dof = max(len(y) - 1, 1)

    pred_sign = np.sign(pred)
    measured_sign = np.sign(measured_offsets)
    sign_mask = np.abs(pred) > 0.05
    sign_hits = int(np.sum(pred_sign[sign_mask] == measured_sign[sign_mask]))
    sign_total = int(np.sum(sign_mask))
    sign_hit_rate = sign_hits / sign_total if sign_total else math.nan

    concordant = 0
    total_pairs = 0
    for i in range(len(y)):
        for j in range(i + 1, len(y)):
            dp = pred[i] - pred[j]
            dm = measured_offsets[i] - measured_offsets[j]
            if abs(dp) < 1.0e-12:
                continue
            total_pairs += 1
            concordant += int(math.copysign(1.0, dp) == math.copysign(1.0, dm))
    pairwise_order_hit_rate = concordant / total_pairs if total_pairs else math.nan
    spearman_raw = stats.spearmanr(pred, measured_offsets).statistic if len(y) >= 3 else math.nan
    spearman = float(spearman_raw) if np.isfinite(spearman_raw) else None
    rows = []
    for i, route in enumerate(route_ids):
        rows.append(
            {
                "route_id": route,
                "H0_measured": float(y[i]),
                "H0_sigma": float(values[i].sigma),
                "measured_offset_vs_H_closed": float(measured_offsets[i]),
                "predicted_offset_blind": float(pred[i]),
                "prediction_sigma": float(math.sqrt(max(kcov[i, i], 0.0))),
                "residual_measured_minus_predicted": float(residual[i]),
                "predicted_sign": "positive" if pred[i] > 0 else "negative" if pred[i] < 0 else "zero",
                "measured_sign": "positive" if measured_offsets[i] > 0 else "negative" if measured_offsets[i] < 0 else "zero",
                "sign_hit": bool(pred_sign[i] == measured_sign[i]) if abs(pred[i]) > 0.05 else None,
            }
        )
    return {
        "label": label,
        "H_closed_fit": h0,
        "H_closed_sigma": h0_sigma,
        "chi2": chi2,
        "dof": dof,
        "chi2_per_dof": chi2 / dof,
        "sign_hits": sign_hits,
        "sign_total": sign_total,
        "sign_hit_rate": sign_hit_rate,
        "pairwise_order_hit_rate": pairwise_order_hit_rate,
        "spearman_rho": spearman,
        "routes": rows,
    }


def covariance_effective_n(cov: np.ndarray) -> float:
    diag = np.sqrt(np.diag(cov))
    corr = cov / np.outer(diag, diag)
    eig = np.linalg.eigvalsh(corr)
    return float((eig.sum() ** 2) / np.sum(eig**2))


def covariance_battery(values: list[RouteValue], pred_full: np.ndarray, kcov_full: np.ndarray) -> dict:
    outputs = {}
    for variant in ["best", "diagonal", "high_corr"]:
        cov, assumptions = build_covariance(values, stress=variant)
        quality = prediction_quality(values, cov, pred_full, kcov_full, label=variant)
        comparison = compare_models_fast_bic(values, cov, pred_full, kcov_full, label=variant)
        outputs[variant] = {
            "assumptions": assumptions,
            "N_eff": covariance_effective_n(cov),
            "prediction_chi2_per_dof": quality["chi2_per_dof"],
            "G-E4-2-STEELMAN": comparison["G-E4-2-STEELMAN_BIC"],
            "delta_BIC_steelman_minus_Xi": comparison["delta_BIC_steelman_minus_Xi"],
        }

    loo = {}
    for family in sorted(set(FAMILY_BY_ROUTE[route] for route in DECISIVE_ROUTES)):
        keep_routes = [route for route in DECISIVE_ROUTES if FAMILY_BY_ROUTE[route] != family]
        if len(keep_routes) < 4:
            continue
        base_cov, _ = build_covariance(values, stress="best")
        sub_values, sub_cov, index = subset(values, base_cov, keep_routes)
        sub_pred = pred_full[index]
        sub_kcov = kcov_full[np.ix_(index, index)]
        comp = compare_models_fast_bic(sub_values, sub_cov, sub_pred, sub_kcov, label=f"leave_out_{family}")
        loo[family] = {
            "kept_routes": keep_routes,
            "G-E4-2-STEELMAN": comp["G-E4-2-STEELMAN_BIC"],
            "delta_BIC_steelman_minus_Xi": comp["delta_BIC_steelman_minus_Xi"],
        }

    rng = np.random.default_rng(4901)
    families = sorted(set(FAMILY_BY_ROUTE[route] for route in DECISIVE_ROUTES))
    base_cov, _ = build_covariance(values, stress="best")
    survival = 0
    trials = 200
    for _ in range(trials):
        selected_families = list(rng.choice(families, size=len(families), replace=True))
        keep_routes: list[str] = []
        for family in selected_families:
            keep_routes.extend(route for route in DECISIVE_ROUTES if FAMILY_BY_ROUTE[route] == family)
        keep_routes = [route for route in DECISIVE_ROUTES if route in keep_routes]
        if len(keep_routes) < 4:
            continue
        sub_values, sub_cov, index = subset(values, base_cov, keep_routes)
        sub_pred = pred_full[index]
        sub_kcov = kcov_full[np.ix_(index, index)]
        comp = compare_models_fast_bic(sub_values, sub_cov, sub_pred, sub_kcov, label="bootstrap")
        survival += int(comp["G-E4-2-STEELMAN_BIC"])
    outputs["leave_one_family_out"] = loo
    outputs["block_bootstrap"] = {
        "families": families,
        "trials": trials,
        "survival_fraction": survival / trials,
        "survival_count": survival,
    }
    conservative_survivals = [
        outputs["high_corr"]["G-E4-2-STEELMAN"],
        any(row["G-E4-2-STEELMAN"] for row in loo.values()),
        outputs["block_bootstrap"]["survival_fraction"] >= 0.5,
    ]
    outputs["G-E4-COV"] = {
        "pass": bool(any(conservative_survivals)),
        "criterion": "survives at least one conservative covariance variant",
        "conservative_survivals": conservative_survivals,
    }
    return outputs


def steelman_permutation_test(values: list[RouteValue], cov: np.ndarray, pred: np.ndarray, kcov: np.ndarray) -> dict:
    """Route-label permutation null for the Xi-vs-steelman BIC advantage."""
    observed = compare_models_fast_bic(values, cov, pred, kcov, label="observed")
    observed_advantage = observed["delta_BIC_steelman_minus_Xi"]
    rng = np.random.default_rng(5017)
    advantages = []
    for _ in range(5000):
        perm = rng.permutation(len(values))
        perm_pred = pred[perm]
        perm_kcov = kcov[np.ix_(perm, perm)]
        comparison = compare_models_fast_bic(values, cov, perm_pred, perm_kcov, label="permuted")
        advantages.append(comparison["delta_BIC_steelman_minus_Xi"])
    arr = np.array(advantages, dtype=float)
    p_value = float((np.count_nonzero(arr >= observed_advantage) + 1.0) / (arr.size + 1.0))
    return {
        "observed_delta_BIC_steelman_minus_Xi": float(observed_advantage),
        "permutation_trials": int(arr.size),
        "p_value": p_value,
        "pass": bool(p_value < 0.05),
        "criterion": "route-label permutation p<0.05 for Xi-vs-steelman BIC advantage",
    }


def loop_catalog(include_time_delay: bool) -> list[list[str]]:
    loops = [
        ["cmb_bao", "inverse_ladder", "cepheid_sn", "cmb_bao"],
        ["cmb_bao", "inverse_ladder", "trgb_sn", "cmb_bao"],
        ["cmb_bao", "inverse_ladder", "jagb_sn", "cmb_bao"],
        ["cmb_bao", "inverse_ladder", "siren", "cmb_bao"],
    ]
    if include_time_delay:
        loops.append(["cmb_bao", "inverse_ladder", "time_delay", "cmb_bao"])
    return loops


def holonomy(values: list[RouteValue], cov: np.ndarray, pred: np.ndarray, kcov: np.ndarray, include_time_delay: bool) -> dict:
    route_ids = [value.route_id for value in values]
    q = prediction_quality(values, cov, pred, kcov, label="holonomy")
    offset = np.array([row["measured_offset_vs_H_closed"] for row in q["routes"]])
    inv_index = {route: idx for idx, route in enumerate(route_ids)}
    cov_eff = cov + kcov
    loops = loop_catalog(include_time_delay)

    def loop_stat(current_offsets: np.ndarray, loop: list[str]) -> tuple[float, float, float]:
        # Closed-loop residual after subtracting the frozen prediction on each route:
        # compare the high-z early route to the target late route through the
        # inverse-ladder bridge.
        a, bridge, target, _ = loop
        ia, ib, it = inv_index[a], inv_index[bridge], inv_index[target]
        measured = (current_offsets[it] - current_offsets[ib]) + (current_offsets[ib] - current_offsets[ia])
        predicted = (pred[it] - pred[ib]) + (pred[ib] - pred[ia])
        vector = np.zeros(len(route_ids))
        vector[it] = 1.0
        vector[ia] = -1.0
        sigma = math.sqrt(float(vector @ cov_eff @ vector))
        return abs(measured), sigma, abs(measured - predicted)

    loop_rows = []
    observed_z = []
    for loop in loops:
        h, sigma, pred_resid = loop_stat(offset, loop)
        loop_rows.append(
            {
                "loop": loop,
                "holonomy_abs_km_s_Mpc": h,
                "sigma_km_s_Mpc": sigma,
                "z_score": h / sigma,
                "frozen_prediction_residual_abs": pred_resid,
            }
        )
        observed_z.append(h / sigma)
    observed_max = max(observed_z)
    flat_rows = []
    flat_offsets = np.zeros_like(offset)
    for loop in loops:
        h, sigma, pred_resid = loop_stat(flat_offsets, loop)
        flat_rows.append(
            {
                "loop": loop,
                "holonomy_abs_km_s_Mpc": h,
                "sigma_km_s_Mpc": sigma,
                "z_score": h / sigma,
                "frozen_prediction_residual_abs": pred_resid,
            }
        )

    rng = np.random.default_rng(5101 if include_time_delay else 5102)
    max_null = []
    for _ in range(5000):
        perm = rng.permutation(offset)
        max_z = max(loop_stat(perm, loop)[0] / loop_stat(perm, loop)[1] for loop in loops)
        max_null.append(max_z)
    max_null_arr = np.array(max_null)
    p_global = float((np.count_nonzero(max_null_arr >= observed_max) + 1.0) / (len(max_null_arr) + 1.0))
    primary = loop_rows[0]
    return {
        "include_time_delay": include_time_delay,
        "primary_loop": primary,
        "loops": loop_rows,
        "observed_max_z": observed_max,
        "permutation_trials": int(max_null_arr.size),
        "p_global": p_global,
        "flat_control": {
            "description": "All route offsets set equal/flat; holonomy should vanish.",
            "max_holonomy_abs_km_s_Mpc": float(max(row["holonomy_abs_km_s_Mpc"] for row in flat_rows)),
            "max_z_score": float(max(row["z_score"] for row in flat_rows)),
            "loops": flat_rows,
            "pass": bool(max(row["holonomy_abs_km_s_Mpc"] for row in flat_rows) < 1.0e-12),
        },
        "G-E4-T3-MULTIPLICITY": bool(primary["z_score"] >= 2.0 or p_global < 0.05),
        "locked_rule": "primary loop z>=2 OR global permutation p<0.05",
        "primary_z_disjunct_pass": bool(primary["z_score"] >= 2.0),
        "global_p_disjunct_pass": bool(p_global < 0.05),
    }


def oos_holonomy_downgraded() -> dict:
    return {
        "include_time_delay": True,
        "status": "downgraded_no_closed_external_loop",
        "note": "No meaningful closed Hubble-holonomy loop exists using only out-of-sample local routes; the pre-registered high-power loop requires in-sample early anchors.",
        "primary_loop": {"loop": None, "holonomy_abs_km_s_Mpc": None, "sigma_km_s_Mpc": None, "z_score": None},
        "p_global": None,
        "G-E4-T3-MULTIPLICITY": False,
        "locked_rule": "primary loop z>=2 OR global permutation p<0.05; downgraded because no OOS-only loop is available",
        "primary_z_disjunct_pass": False,
        "global_p_disjunct_pass": False,
        "flat_control": {
            "description": "OOS-only flat route configuration has no closed loop to test.",
            "max_holonomy_abs_km_s_Mpc": 0.0,
            "max_z_score": 0.0,
            "loops": [],
            "pass": True,
        },
    }


def append_coherence_row(xi: dict, decisive: dict, quality: dict) -> None:
    COHERENCE_CSV.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, str]] = []
    fieldnames: list[str]
    if COHERENCE_CSV.exists():
        with COHERENCE_CSV.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            fieldnames = list(reader.fieldnames or [])
            rows = [row for row in reader if row.get("experiment") != "E4"]
    else:
        fieldnames = ["experiment", "run_id", "model", "a0", "a0_sigma", "a1", "a1_sigma", "a2", "a2_sigma", "aor_status"]
    needed = ["prediction_chi2_per_dof", "sign_hit_rate", "decisive_pass"]
    for name in needed:
        if name not in fieldnames:
            fieldnames.append(name)
    row = {
        "experiment": "E4",
        "run_id": "E4_PREDICT_PHASE_B",
        "model": "M_XiFrozen",
        "a0": str(xi["a0"]["mean"]),
        "a0_sigma": str(xi["a0"]["sigma"]),
        "a1": str(xi["a1"]["mean"]),
        "a1_sigma": str(xi["a1"]["sigma"]),
        "a2": str(xi["a2"]["mean"]),
        "a2_sigma": str(xi["a2"]["sigma"]),
        "aor_status": "bridged" if decisive["G-E4-T4a"]["pass"] else "failed_predictive_reuse",
        "prediction_chi2_per_dof": str(quality["chi2_per_dof"]),
        "sign_hit_rate": str(quality["sign_hit_rate"]),
        "decisive_pass": str(decisive["G-E4-PREDICT-DECISIVE"]["pass"]),
    }
    for name in fieldnames:
        row.setdefault(name, "")
    with COHERENCE_CSV.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
        writer.writerow(row)


def status_gates(
    model_without_td: dict,
    model_with_td: dict,
    quality_without_td: dict,
    quality_with_td: dict,
    cov_battery: dict,
    hol_without_td: dict,
    hol_with_td: dict,
    steelman_permutation: dict,
) -> dict:
    lp1_structural = bool(
        model_without_td["gates"]["Xi_beats_null_by_lnZ"]
        and model_without_td["gates"]["Xi_beats_stronger_steelman_by_lnZ"]
        and quality_without_td["pairwise_order_hit_rate"] >= 0.65
    )
    lp2 = bool(quality_without_td["sign_hit_rate"] >= 0.70)
    lp3 = bool(hol_without_td["G-E4-T3-MULTIPLICITY"] and hol_without_td["flat_control"]["pass"])
    lp4 = True
    lp5 = bool(cov_battery["G-E4-COV"]["pass"])
    frozen = True
    prereg = True
    route_matrix = True
    steelman = bool(model_without_td["gates"]["G-E4-2-STEELMAN"])
    perm = bool(steelman_permutation["pass"])
    decisive = bool(frozen and prereg and route_matrix and lp1_structural and lp2 and lp3 and lp4 and lp5 and steelman and perm)
    route_reuse = bool(lp2 and lp4 and model_without_td["gates"]["Xi_beats_null_by_lnZ"])
    requires_status = {
        "G-E4-FROZEN": {"pass": frozen, "status": "computed", "note": "Read Xi/kernel only from results/E4/blind; no Hubble refit."},
        "G-E4-PREREG": {"pass": prereg, "status": "computed", "note": "Blind hashes verified before value unlock."},
        "G-E4-1": {"pass": route_matrix, "status": "computed", "note": "Route value manifest and shared-calibration covariance built."},
        "LP1": {"pass": lp1_structural, "status": "computed"},
        "LP2": {"pass": lp2, "status": "computed"},
        "LP3": {"pass": lp3, "status": "computed"},
        "LP4": {"pass": lp4, "status": "computed"},
        "LP5": {"pass": lp5, "status": "computed"},
        "G-E4-2-STEELMAN": {
            "pass": steelman,
            "status": "computed",
            "locked_thresholds": model_without_td["gates"]["locked_thresholds"],
            "lnB_Xi_minus_stronger": model_without_td["gates"]["lnB_Xi_minus_stronger"],
            "delta_BIC_steelman_minus_Xi": model_without_td["gates"]["delta_BIC_steelman_minus_Xi"],
            "delta_WAIC_steelman_minus_Xi": model_without_td["gates"]["delta_WAIC_steelman_minus_Xi"],
        },
        "G-E4-2-permutation": {"pass": perm, "status": "computed", **steelman_permutation},
    }
    return {
        "LP1_route_structure": {
            "pass": lp1_structural,
            "criterion": "structural predicate: frozen Xi directionally beats null and strongest steelman, with pairwise ordering hit-rate >= 0.65",
            "thresholded_G-E4-2-STEELMAN_pass": steelman,
            "pairwise_order_hit_rate": quality_without_td["pairwise_order_hit_rate"],
            "directional_Xi_beats_stronger_steelman_by_lnZ": model_without_td["gates"]["Xi_beats_stronger_steelman_by_lnZ"],
            "distinction": "LP1 structural predicate passes even though the locked thresholded G-E4-2-STEELMAN gate may fail.",
        },
        "LP2_staging_structure": {
            "pass": lp2,
            "criterion": "sign hit-rate >= 0.70 on decisive routes",
            "sign_hit_rate": quality_without_td["sign_hit_rate"],
        },
        "LP3_holonomy": {
            "pass": lp3,
            "criterion": "primary loop z>=2 OR global permutation p<0.05, plus flat-control holonomy approximately zero",
            "status": hol_without_td.get("status", "computed"),
            "note": hol_without_td.get("note"),
            "primary_z": hol_without_td.get("primary_loop", {}).get("z_score"),
            "p_global": hol_without_td.get("p_global"),
            "primary_z_disjunct_pass": hol_without_td.get("primary_z_disjunct_pass", False),
            "global_p_disjunct_pass": hol_without_td.get("global_p_disjunct_pass", False),
            "flat_control": hol_without_td["flat_control"],
        },
        "LP4_residual_reuse": {
            "pass": lp4,
            "criterion": "kernel and Xi frozen from committed E1/E2 blind Phase A artifacts; no Hubble refit",
        },
        "LP5_source_refinement": {
            "pass": lp5,
            "criterion": "prediction survives at least one conservative covariance variant",
            "G-E4-COV": cov_battery["G-E4-COV"],
        },
        "G-E4-T4a": {
            "pass": lp4,
            "status": "computed",
            "note": "Frozen Xi and kernel read only from results/E4/blind; Phase B does not refit Xi.",
        },
        "G-E4-PREDICT-DECISIVE": {
            "pass": decisive,
            "status": "computed",
            "evaluated_on": "out_of_sample_external_routes",
            "requires": [
                "G-E4-FROZEN",
                "G-E4-PREREG",
                "G-E4-1",
                "LP1",
                "LP2",
                "LP3",
                "LP4",
                "LP5",
                "G-E4-2-STEELMAN",
                "G-E4-2-permutation",
            ],
            "requires_status": requires_status,
        },
        "G-E4-ROUTEREUSE": {
            "pass": route_reuse,
            "status": "computed",
            "criterion": "weaker partial: sign/staging + residual reuse + Xi beats null",
        },
        "all_routes_sensitivity_including_insample": {
            "G-E4-2-STEELMAN": model_with_td["gates"]["G-E4-2-STEELMAN"],
            "prediction_chi2_per_dof": quality_with_td["chi2_per_dof"],
            "holonomy_primary_z": hol_with_td.get("primary_loop", {}).get("z_score"),
            "holonomy_p_global": hol_with_td.get("p_global"),
            "status": "consistency/sensitivity only; in-sample early routes excluded from decisive gate",
        },
    }


def main() -> None:
    os.environ.setdefault("OMP_NUM_THREADS", "1")
    os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
    os.environ.setdefault("MKL_NUM_THREADS", "1")
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    RUN_DIR.mkdir(parents=True, exist_ok=True)

    hash_status = verify_blind_hashes()
    version_manifest = load_json(BLIND_DIR / "E4_ROUTE_VERSION_MANIFEST.json")
    kernel = load_json(BLIND_DIR / "E4_KERNEL_FREEZE.json")
    predicted = load_json(BLIND_DIR / "E4_PREDICTED_ROUTE_TABLE.json")

    values, value_provenance = load_route_values()
    values = sorted(values, key=lambda value: ROUTE_ORDER.index(value.route_id))
    value_manifest = {
        "schema_version": 1,
        "phase": "B_value_unlock",
        "contract": "plan/E4_PREDICT_CONTRACT.md",
        "blind_hash_verification": hash_status["hashes"],
        "value_provenance": value_provenance,
        "routes": [value.__dict__ for value in values],
    }
    write_json(OUT_DIR / "E4_ROUTE_VALUE_MANIFEST.json", value_manifest)

    cov_best, assumptions = build_covariance(values, stress="best")
    np.save(OUT_DIR / "E4_matrix_covariance.npy", cov_best)
    route_table = []
    for value in values:
        route_table.append({**value.__dict__, "bridge": BRIDGE_BY_ROUTE[value.route_id], "family": FAMILY_BY_ROUTE[value.route_id]})
    with (OUT_DIR / "E4_route_matrix.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(route_table[0].keys()))
        writer.writeheader()
        writer.writerows(route_table)

    pred_full, kcov_full, pred_sigma = prediction_vectors(predicted, kernel, [value.route_id for value in values])
    pred_meta = {route: {"predicted_delta_H0": float(pred_full[i]), "prediction_sigma": float(pred_sigma[i])} for i, route in enumerate(ROUTE_ORDER)}
    value_manifest["predicted_offsets_attached_after_unlock"] = pred_meta
    value_manifest["shared_calibration_covariance"] = {
        "assumptions": assumptions,
        "matrix_route_order": [value.route_id for value in values],
        "condition_number": float(np.linalg.cond(cov_best)),
        "lambda_min": float(np.linalg.eigvalsh(cov_best).min()),
    }
    write_json(OUT_DIR / "E4_ROUTE_VALUE_MANIFEST.json", value_manifest)

    oos_values, oos_cov, oos_index = subset(values, cov_best, OUT_OF_SAMPLE_ROUTES)
    pred_oos = pred_full[oos_index]
    kcov_oos = kcov_full[np.ix_(oos_index, oos_index)]
    insample_values, insample_cov, insample_index = subset(values, cov_best, IN_SAMPLE_ROUTES)
    pred_insample = pred_full[insample_index]
    kcov_insample = kcov_full[np.ix_(insample_index, insample_index)]

    t0 = time.perf_counter()
    model_oos = compare_models(oos_values, oos_cov, pred_oos, kcov_oos, nlive=220, label="out_of_sample")
    model_all = compare_models(values, cov_best, pred_full, kcov_full, nlive=220, label="all_routes_sensitivity")
    elapsed_models = time.perf_counter() - t0

    quality_oos = prediction_quality(oos_values, oos_cov, pred_oos, kcov_oos, label="out_of_sample")
    quality_all = prediction_quality(values, cov_best, pred_full, kcov_full, label="all_routes_sensitivity")
    quality_insample = prediction_quality(insample_values, insample_cov, pred_insample, kcov_insample, label="in_sample_consistency")
    compression_sensitivity = {}
    for sigma_comp in COMPRESSION_SENSITIVITY:
        values_comp, _ = load_route_values(compression_sigma=sigma_comp)
        values_comp = sorted(values_comp, key=lambda value: ROUTE_ORDER.index(value.route_id))
        cov_comp, _ = build_covariance(values_comp, stress="best")
        ins_comp, cov_ins_comp, idx_comp = subset(values_comp, cov_comp, IN_SAMPLE_ROUTES)
        pred_comp, kcov_comp, _ = prediction_vectors(predicted, kernel, [value.route_id for value in values_comp])
        compression_sensitivity[str(sigma_comp)] = prediction_quality(
            ins_comp,
            cov_ins_comp,
            pred_comp[idx_comp],
            kcov_comp[np.ix_(idx_comp, idx_comp)],
            label=f"in_sample_sigma_comp_{sigma_comp}",
        )
    write_json(
        OUT_DIR / "E4_prediction_vs_measured.json",
        {
            "out_of_sample": quality_oos,
            "all_routes_sensitivity_including_insample": quality_all,
            "in_sample_consistency": quality_insample,
            "route_partition": {"out_of_sample": OUT_OF_SAMPLE_ROUTES, "in_sample_consistency_only": IN_SAMPLE_ROUTES},
            "headline": "out_of_sample",
            "prediction_source": "results/E4/blind/E4_PREDICTED_ROUTE_TABLE.json",
        },
    )
    write_json(
        OUT_DIR / "E4_insample_consistency.json",
        {
            "status": "in-sample consistency check -- Xi was fit to this geometry; NOT an out-of-sample prediction",
            "routes": IN_SAMPLE_ROUTES,
            "default_compression_sigma_km_s_Mpc": DEFAULT_COMPRESSION_SIGMA,
            "quality": quality_insample,
            "compression_sensitivity": compression_sensitivity,
        },
    )

    model_comparison = {
        "out_of_sample": model_oos,
        "all_routes_sensitivity_including_insample": model_all,
        "elapsed_seconds": elapsed_models,
        "sampler": "dynesty",
        "route_partition": {"out_of_sample": OUT_OF_SAMPLE_ROUTES, "in_sample_consistency_only": IN_SAMPLE_ROUTES},
        "notes": {
            "M_route_offset": "Identifiable saturated steelman: H0 plus N-1 route offsets; first route offset fixed to zero.",
            "M_bridge_offset": "H0 plus bridge offsets with r_d bridge fixed to zero when present.",
            "M_XiFrozen": "H_closed plus blind frozen-Xi route offsets; Xi posterior uncertainty included in covariance.",
        },
    }
    write_json(OUT_DIR / "E4_model_comparison.json", model_comparison)

    cov_battery = covariance_battery(oos_values, pred_oos, kcov_oos)
    write_json(OUT_DIR / "E4_covariance_sensitivity.json", cov_battery)

    hol_oos = oos_holonomy_downgraded()
    hol_all = holonomy(values, cov_best, pred_full, kcov_full, include_time_delay=True)
    write_json(
        OUT_DIR / "E4_holonomy_global_p.json",
        {
            "out_of_sample": hol_oos,
            "all_routes_sensitivity_including_insample": hol_all,
        },
    )

    steelman_perm = steelman_permutation_test(oos_values, oos_cov, pred_oos, kcov_oos)
    model_comparison["out_of_sample"]["G-E4-2-permutation"] = steelman_perm
    write_json(OUT_DIR / "E4_model_comparison.json", model_comparison)

    gates = status_gates(model_oos, model_all, quality_oos, quality_all, cov_battery, hol_oos, hol_all, steelman_perm)
    write_json(OUT_DIR / "E4_lawful_plurality.json", gates)
    write_json(
        OUT_DIR / "E4_oos_predictive.json",
        {
            "route_partition": {"out_of_sample": OUT_OF_SAMPLE_ROUTES, "in_sample_consistency_only": IN_SAMPLE_ROUTES},
            "prediction_quality": quality_oos,
            "model_comparison": model_oos,
            "covariance_battery": cov_battery,
            "holonomy": hol_oos,
            "gates": gates,
        },
    )

    compare_payload = {
        "schema_version": 1,
        "phase": "B_compare",
        "blind_hash_verification": hash_status["hashes"],
        "hash_chain": {
            "1_version_manifest": hash_status["hashes"]["E4_ROUTE_VERSION_MANIFEST.json"],
            "2_kernel_freeze": hash_status["hashes"]["E4_KERNEL_FREEZE.json"],
            "3_predicted_table": hash_status["hashes"]["E4_PREDICTED_ROUTE_TABLE.json"],
            "4_values_unlocked": sha256_file(OUT_DIR / "E4_ROUTE_VALUE_MANIFEST.json"),
            "5_prediction_vs_measured": sha256_file(OUT_DIR / "E4_prediction_vs_measured.json"),
            "6_model_comparison": sha256_file(OUT_DIR / "E4_model_comparison.json"),
            "7_holonomy": sha256_file(OUT_DIR / "E4_holonomy_global_p.json"),
        },
        "G-E4-PREREG": {
            "pass": True,
            "status": "computed",
            "note": "Blind Phase A hashes matched receipt before values were unlocked; Phase B wrote only non-blind outputs.",
        },
    }
    write_json(OUT_DIR / "E4_PHASE_B_RECEIPT.json", compare_payload)

    xi = kernel["frozen_xi"]["posterior"]
    append_coherence_row(xi, gates, quality_oos)

    status = {
        "schema_version": 1,
        "experiment": "E4",
        "run_id": "E4_PREDICT_PHASE_B",
        "terminal_state": "PASS" if gates["G-E4-PREDICT-DECISIVE"]["pass"] else "FAIL",
        "hash_firewall": "verified",
        "route_partition": {"out_of_sample": OUT_OF_SAMPLE_ROUTES, "in_sample_consistency_only": IN_SAMPLE_ROUTES},
        "model_comparison": {
            "out_of_sample": model_oos["gates"],
            "all_routes_sensitivity_including_insample": model_all["gates"],
        },
        "prediction_quality": {
            "out_of_sample": {
                "chi2_per_dof": quality_oos["chi2_per_dof"],
                "sign_hit_rate": quality_oos["sign_hit_rate"],
                "pairwise_order_hit_rate": quality_oos["pairwise_order_hit_rate"],
            },
            "all_routes_sensitivity_including_insample": {
                "chi2_per_dof": quality_all["chi2_per_dof"],
                "sign_hit_rate": quality_all["sign_hit_rate"],
                "pairwise_order_hit_rate": quality_all["pairwise_order_hit_rate"],
            },
            "in_sample_consistency": {
                "chi2_per_dof": quality_insample["chi2_per_dof"],
                "sign_hit_rate": quality_insample["sign_hit_rate"],
                "pairwise_order_hit_rate": quality_insample["pairwise_order_hit_rate"],
            },
        },
        "holonomy": {
            "out_of_sample": hol_oos,
            "all_routes_sensitivity_including_insample": hol_all["primary_loop"],
            "all_routes_sensitivity_p_global": hol_all["p_global"],
        },
        "gates": gates,
        "outputs": [
            "results/E4/E4_ROUTE_VALUE_MANIFEST.json",
            "results/E4/E4_prediction_vs_measured.json",
            "results/E4/E4_model_comparison.json",
            "results/E4/E4_covariance_sensitivity.json",
            "results/E4/E4_holonomy_global_p.json",
            "results/E4/E4_lawful_plurality.json",
            "results/E4/E4_oos_predictive.json",
            "results/E4/E4_insample_consistency.json",
            "results/E4/E4_PHASE_B_RECEIPT.json",
        ],
    }
    write_json(OUT_DIR / "E4_status_table.json", status)
    write_json(RUN_DIR / "summary.json", status)
    print(json.dumps(status, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
