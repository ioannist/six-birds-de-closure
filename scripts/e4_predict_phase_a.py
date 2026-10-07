"""Phase-A blind E4 frozen-Xi Hubble-route prediction.

This runner writes only value-free E4-PREDICT artifacts under
``results/E4/blind``. It reads only the committed frozen-Xi summaries and the
sealed route/version information encoded below from the E4 contract/spec.
"""

from __future__ import annotations

import csv
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from sbt_cosmo.xi.kernels import hubble_route_kernel, hubble_route_kernel_basis

RESULTS = ROOT / "results" / "E4" / "blind"
H_UNIT_KM_S_MPC = 70.0


def _local_sn_window(name: str) -> dict[str, Any]:
    return {
        "name": name,
        "type": "top_hat",
        "z_min": 0.01,
        "z_max": 0.15,
        "z_eff": 0.05,
        "normalization": "unit_area",
        "probe": "SN",
        "weight": 1.0,
    }


ROUTES: list[dict[str, Any]] = [
    {
        "route_id": "cmb_bao",
        "route_family": "CMB->BAO",
        "determination": "Planck 2018 base-LCDM anchor with DESI DR2 BAO route structure",
        "arxiv": [{"id": "1807.06209", "version_or_date": "Planck 2018"}, {"id": "2503.14738", "version_or_date": "DESI DR2 sealed-spec current"}],
        "role": "headline",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": False,
        "covariance_source_availability": "available from Phase-B Planck/DESI covariance or committed E1 compressed covariance; no values in Phase A",
        "kernel": {
            "W_r": [
                {
                    "name": "BAO high-z inverse-distance response",
                    "type": "top_hat",
                    "z_min": 0.50,
                    "z_max": 2.30,
                    "z_eff": 1.20,
                    "normalization": "unit_area",
                    "probe": "BAO",
                    "weight": 1.0,
                }
            ],
            "B_b": [{"bridge": "r_d", "probe": "BAO", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "inverse_ladder",
        "route_family": "inverse_ladder",
        "determination": "DESI DR2 BAO + BBN/inverse-ladder route derived from committed E1 inputs",
        "arxiv": [{"id": "2503.14738", "version_or_date": "DESI DR2 sealed-spec current"}],
        "role": "headline",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": False,
        "covariance_source_availability": "derived from committed E1 summaries in Phase B; no values in Phase A",
        "kernel": {
            "W_r": [
                {
                    "name": "BAO-to-low-z inverse-ladder response",
                    "type": "top_hat",
                    "z_min": 0.01,
                    "z_max": 1.50,
                    "z_eff": 0.60,
                    "normalization": "unit_area",
                    "probe": "BAO",
                    "weight": 1.0,
                }
            ],
            "B_b": [{"bridge": "r_d", "probe": "BAO", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "cepheid_sn",
        "route_family": "Cepheid->SN",
        "determination": "SH0ES JWST+HST Cepheid-to-SN route",
        "arxiv": [{"id": "2509.01667", "version_or_date": "sealed-spec current"}],
        "role": "headline",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": True,
        "covariance_source_availability": "published summary covariance and shared SN/M_B covariance to be unlocked by Phase B",
        "kernel": {
            "W_r": [_local_sn_window("Cepheid low-z SN response")],
            "B_b": [{"bridge": "Cepheid", "probe": "SN", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "trgb_sn",
        "route_family": "TRGB->SN",
        "determination": "CCHP JWST TRGB-to-SN route",
        "arxiv": [{"id": "2408.06153", "version_or_date": "sealed-spec pinned CCHP version"}],
        "role": "headline",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": True,
        "covariance_source_availability": "published stat/sys/SN covariance components to be unlocked by Phase B",
        "kernel": {
            "W_r": [_local_sn_window("TRGB low-z SN response")],
            "B_b": [{"bridge": "TRGB", "probe": "SN", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "jwst_trgb_sn",
        "route_family": "JWST_TRGB->SN",
        "determination": "CCHP JWST-only TRGB-to-SN route variant",
        "arxiv": [{"id": "2408.06153", "version_or_date": "sealed-spec pinned CCHP version"}],
        "role": "variant",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": True,
        "covariance_source_availability": "published stat/sys covariance components to be unlocked by Phase B",
        "kernel": {
            "W_r": [_local_sn_window("JWST-only TRGB low-z SN response")],
            "B_b": [{"bridge": "TRGB", "probe": "SN", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "jagb_sn",
        "route_family": "JAGB->SN",
        "determination": "CCHP JWST JAGB-to-SN route",
        "arxiv": [{"id": "2408.06153", "version_or_date": "sealed-spec pinned CCHP version"}],
        "role": "headline",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": True,
        "covariance_source_availability": "published stat/sys covariance components to be unlocked by Phase B",
        "kernel": {
            "W_r": [_local_sn_window("JAGB low-z SN response")],
            "B_b": [{"bridge": "JAGB", "probe": "SN", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "time_delay",
        "route_family": "time_delay",
        "determination": "TDCOSMO 2025 strong-lens time-delay route",
        "arxiv": [{"id": "2506.03023", "version_or_date": "2025 headline sealed-spec current"}],
        "role": "headline_time_delay",
        "include": True,
        "decisive_without_time_delay": False,
        "summary_only": True,
        "covariance_source_availability": "posterior family/model-dependence covariance to be unlocked by Phase B",
        "kernel": {
            "W_r": [
                {
                    "name": "lens-source time-delay distance response",
                    "type": "top_hat",
                    "z_min": 0.30,
                    "z_max": 2.00,
                    "z_eff": 0.80,
                    "normalization": "unit_area",
                    "probe": "time_delay",
                    "weight": 1.0,
                }
            ],
            "B_b": [{"bridge": "time_delay", "probe": "time_delay", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
    {
        "route_id": "siren",
        "route_family": "standard_siren",
        "determination": "GW170817 standard-siren route",
        "arxiv": [{"id": "1709.05895", "version_or_date": "sealed-spec current"}],
        "role": "headline",
        "include": True,
        "decisive_without_time_delay": True,
        "summary_only": True,
        "covariance_source_availability": "asymmetric posterior covariance to be unlocked by Phase B",
        "kernel": {
            "W_r": [
                {
                    "name": "near-local GW luminosity-distance response",
                    "type": "top_hat",
                    "z_min": 0.00,
                    "z_max": 0.02,
                    "z_eff": 0.01,
                    "normalization": "unit_area",
                    "probe": "siren",
                    "weight": 1.0,
                }
            ],
            "B_b": [{"bridge": "siren", "probe": "siren", "weight": 1.0, "basis": "unit_calibration"}],
            "distance_to_h0_sign": -1.0,
            "response": 1.0,
            "absorb_a0_into_H_closed": True,
        },
    },
]


def main() -> None:
    RESULTS.mkdir(parents=True, exist_ok=True)
    frozen = _load_frozen_xi()

    version_manifest = _version_manifest()
    version_path = RESULTS / "E4_ROUTE_VERSION_MANIFEST.json"
    _write_json(version_path, version_manifest)

    kernel = _kernel_freeze(frozen, version_path)
    kernel_path = RESULTS / "E4_KERNEL_FREEZE.json"
    _write_json(kernel_path, kernel)

    prediction = _predicted_route_table(frozen, version_path, kernel_path)
    prediction_path = RESULTS / "E4_PREDICTED_ROUTE_TABLE.json"
    _write_json(prediction_path, prediction)

    hashes = {
        "E4_ROUTE_VERSION_MANIFEST.json": _sha256(version_path),
        "E4_KERNEL_FREEZE.json": _sha256(kernel_path),
        "E4_PREDICTED_ROUTE_TABLE.json": _sha256(prediction_path),
    }
    receipt = {
        "schema_version": 1,
        "phase": "A_ordering_receipt_stub_no_values",
        "blinding_status": "blind",
        "contains_h0_values": False,
        "hashes": hashes,
        "next_step": "manager_commit_gate_before_any_E4_ROUTE_VALUE_MANIFEST_is_written",
    }
    receipt_path = RESULTS / "E4_ORDERING_RECEIPT_STUB.json"
    _write_json(receipt_path, receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True))


def _version_manifest() -> dict[str, Any]:
    return {
        "schema_version": 1,
        "phase": "A_version_manifest_no_values",
        "contract": "plan/E4_PREDICT_CONTRACT.md",
        "contains_h0_values": False,
        "blinding_status": "blind",
        "attestation": "results/E4/blind/E4_BLINDING_ATTESTATION.json",
        "routes": [{key: value for key, value in route.items() if key != "kernel"} for route in ROUTES],
    }


def _kernel_freeze(frozen: dict[str, Any], version_path: Path) -> dict[str, Any]:
    route_kernels = []
    for route in ROUTES:
        route_kernels.append(
            {
                "route_id": route["route_id"],
                "W_r": route["kernel"]["W_r"],
                "B_b": route["kernel"]["B_b"],
                "distance_to_h0_sign": route["kernel"]["distance_to_h0_sign"],
                "response": route["kernel"]["response"],
                "absorb_a0_into_H_closed": route["kernel"]["absorb_a0_into_H_closed"],
                "linear_basis_km_s_Mpc": hubble_route_kernel_basis(route["kernel"], h_unit=H_UNIT_KM_S_MPC),
            }
        )
    return {
        "schema_version": 1,
        "phase": "A_kernel_freeze_no_values",
        "contract": "plan/E4_PREDICT_CONTRACT.md",
        "input_version_manifest_sha256": _sha256(version_path),
        "contains_h0_values": False,
        "blinding_status": "blind",
        "kernel_status": "reimplemented_cleanly_from_plan_04_section_5",
        "H_closed_anchoring": {
            "mode": "free",
            "common_mode_handling": "route-common a0 is absorbed into H_closed(0); Phase-A offsets use the a1/a2 route-contrast terms",
            "h_unit_km_s_Mpc": H_UNIT_KM_S_MPC,
            "h_unit_note": "unit conversion scale only; not a route H0 value",
        },
        "sign_convention": {
            "positive_delta_H0": "route reads above H_closed(0)",
            "distance_response": "delta_H0/H_unit = - delta_distance/distance",
            "a2_to_delta_H0": "SN/stellar bridges have c_p=+1, so frozen negative a2 predicts positive local-ladder offsets; r_d/BAO has c_p=-1, so frozen negative a2 predicts negative early/inverse offsets",
        },
        "bridge_terms": {
            "Cepheid": {"probe": "SN", "c_p": 1.0, "basis": "unit_calibration", "active_routes": ["cepheid_sn"]},
            "TRGB": {"probe": "SN", "c_p": 1.0, "basis": "unit_calibration", "active_routes": ["trgb_sn", "jwst_trgb_sn"]},
            "JAGB": {"probe": "SN", "c_p": 1.0, "basis": "unit_calibration", "active_routes": ["jagb_sn"]},
            "r_d": {"probe": "BAO", "c_p": -1.0, "basis": "unit_calibration", "active_routes": ["cmb_bao", "inverse_ladder"]},
            "M_B": {"probe": "SN", "c_p": 1.0, "basis": "unit_calibration", "active_routes": [], "note": "declared shared SN zero-point bridge; not added as a second Phase-A bridge to avoid double counting the stellar-calibrator bridge"},
            "time_delay": {"probe": "time_delay", "c_p": 0.0, "basis": "unit_calibration", "active_routes": ["time_delay"]},
            "siren": {"probe": "siren", "c_p": 0.0, "basis": "unit_calibration", "active_routes": ["siren"]},
        },
        "primary_holonomy_loop": ["cmb_bao", "inverse_ladder", "cepheid_sn", "cmb_bao"],
        "frozen_xi": frozen,
        "route_kernels": route_kernels,
    }


def _predicted_route_table(frozen: dict[str, Any], version_path: Path, kernel_path: Path) -> dict[str, Any]:
    mean_params = {name: frozen["posterior"][name]["mean"] for name in ("a0", "a1", "a2")}
    variances = {name: frozen["posterior"][name]["sigma"] ** 2 for name in ("a0", "a1", "a2")}
    rows = []
    for route in ROUTES:
        basis = hubble_route_kernel_basis(route["kernel"], h_unit=H_UNIT_KM_S_MPC)
        delta = hubble_route_kernel(route["kernel"], mean_params, h_unit=H_UNIT_KM_S_MPC)
        sigma = float(np.sqrt(sum((basis[name] ** 2) * variances[name] for name in ("a0", "a1", "a2"))))
        rows.append(
            {
                "route_id": route["route_id"],
                "route_family": route["route_family"],
                "include": route["include"],
                "decisive_without_time_delay": route["decisive_without_time_delay"],
                "predicted_delta_H0_km_s_Mpc": delta,
                "predicted_sigma_from_frozen_xi": sigma,
                "predicted_sign": _sign(delta),
                "approx_amplitude_km_s_Mpc": round(delta, 2),
                "amplitude_band": _amplitude_band(delta),
                "linear_basis_km_s_Mpc": basis,
            }
        )
    included = [row for row in rows if row["include"]]
    ordering = []
    last_delta: float | None = None
    current_rank = 0
    for index, row in enumerate(sorted(included, key=lambda item: (-item["predicted_delta_H0_km_s_Mpc"], item["route_id"]))):
        delta = float(row["predicted_delta_H0_km_s_Mpc"])
        if last_delta is None or abs(delta - last_delta) > 1.0e-9:
            current_rank = index + 1
            last_delta = delta
        ordering.append(
            {
                "rank_high_to_low": current_rank,
                "route_id": row["route_id"],
                "predicted_delta_H0_km_s_Mpc": row["predicted_delta_H0_km_s_Mpc"],
            }
        )
    return {
        "schema_version": 1,
        "phase": "A_prediction_no_values",
        "contract": "plan/E4_PREDICT_CONTRACT.md",
        "contains_h0_values": False,
        "blinding_status": "blind",
        "input_hashes": {
            "E4_ROUTE_VERSION_MANIFEST.json": _sha256(version_path),
            "E4_KERNEL_FREEZE.json": _sha256(kernel_path),
        },
        "frozen_xi": frozen,
        "predictions": rows,
        "predicted_ordering_high_to_low": ordering,
        "ordering_note": "stellar-ladder routes are tied by construction because the sealed route structure gives no value-free basis for ranking Cepheid, TRGB, JWST-TRGB, and JAGB bridges separately",
        "manager_commit_gate": "STOP_AFTER_PHASE_A; do not write E4_ROUTE_VALUE_MANIFEST before manager commit.",
    }


def _load_frozen_xi() -> dict[str, Any]:
    e1 = json.loads((ROOT / "results" / "_summaries" / "E1B_C3_sbt.json").read_text(encoding="utf-8"))
    e2 = json.loads((ROOT / "results" / "_summaries" / "E2" / "summary.json").read_text(encoding="utf-8"))
    e1_post = e1["fit"]["posterior"]
    e2_post = e2["models"]["M2"]["posterior"]
    a0 = _precision_average([e1_post["a0"], e2_post["a0"]])
    a2 = _precision_average([e1_post["a2"], e2_post["a2"]])
    a1 = {"mean": float(e1_post["a1"]["mean"]), "sigma": float(e1_post["a1"]["sigma"]), "source": "E1B_only_E2_fixed_inactive"}
    coherence_rows = []
    with (ROOT / "results" / "xi_cosmo_coherence.csv").open("r", encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle):
            coherence_rows.append({key: row[key] for key in ("experiment", "run_id", "model", "a0", "a0_sigma", "a1", "a1_sigma", "a2", "a2_sigma", "aor_status")})
    return {
        "posterior": {"a0": a0, "a1": a1, "a2": a2},
        "sources": {
            "E1B": "results/_summaries/E1B_C3_sbt.json",
            "E2": "results/_summaries/E2/summary.json",
            "coherence": "results/xi_cosmo_coherence.csv",
        },
        "coherence_rows": coherence_rows,
        "combination": "precision_weighted_for_a0_a2; a1_from_E1B_with_E2_inactive",
    }


def _precision_average(items: list[dict[str, float]]) -> dict[str, float]:
    means = np.asarray([float(item["mean"]) for item in items], dtype=float)
    sigmas = np.asarray([float(item["sigma"]) for item in items], dtype=float)
    precision = 1.0 / np.square(sigmas)
    sigma = float(np.sqrt(1.0 / np.sum(precision)))
    mean = float(np.sum(precision * means) / np.sum(precision))
    return {"mean": mean, "sigma": sigma, "source": "precision_weighted_E1B_E2"}


def _sign(delta: float) -> str:
    if delta > 0.0:
        return "positive"
    if delta < 0.0:
        return "negative"
    return "zero"


def _amplitude_band(delta: float) -> str:
    value = abs(float(delta))
    if value >= 3.0:
        return "large"
    if value >= 1.0:
        return "moderate"
    if value >= 0.25:
        return "small"
    return "near_zero"


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
