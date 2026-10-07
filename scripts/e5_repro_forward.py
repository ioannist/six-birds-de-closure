#!/usr/bin/env python3
"""Run the E5-v2 physical-CCL reproduction substrate.

This script stops at G-E5-REPRO.  It does not build the Schur carrier or any
LOFO certificate.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import time
from pathlib import Path
from typing import Any, Mapping

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "E5_forward_repro"

THREAD_CAPS = {
    "OMP_NUM_THREADS": "1",
    "OPENBLAS_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
    "VECLIB_MAXIMUM_THREADS": "1",
    "CCL_NUM_THREADS": "1",
}

TARGETS = {
    "kids_legacy_shear": {
        "published_S8": 0.815,
        "published_sigma_minus": 0.021,
        "published_sigma_plus": 0.016,
        "reference": "KiDS-Legacy arXiv:2503.19441; plan/03 records S8=0.815^{+0.016}_{-0.021}",
    },
    "hsc_y3_origVSrecal": {
        "published_S8": 0.776,
        "published_sigma_minus": 0.033,
        "published_sigma_plus": 0.032,
        "reference": "HSC-Y3 Fourier own-published REPRO target, Dalal+23 arXiv:2304.00701 Table IV / HSC release: S8=0.776^{+0.032}_{-0.033}; ORIGINAL HSC n(z). DESI-recal S8≈0.805 is staging-only.",
    },
    "cmblensing_act_spt_planck": {
        "published_S8": None,
        "published_sigma_minus": None,
        "published_sigma_plus": None,
        "reference": "ACT+SPT+Planck CMB-lensing release; no scalar S8 target is locked in the E5 manifest",
    },
}

REFERENCE_PARAMS = {
    # KiDS official COSEBIs chain best-posterior row, but with pyccl NLA IA set
    # to zero because the release uses a mass-dependent IA module not equivalent
    # to CCL's single-amplitude NLA input.
    "kids_legacy_shear": {
        "omega_b": 0.024054728386330965,
        "omega_cdm": 0.15533896707470593,
        "h": 0.7576293916845687,
        "n_s": 1.0030959525314076,
        "sigma8": 0.8036589717533703,
        "m_nu": 0.06,
        "A_IA": 0.0,
    },
    "hsc_y3_origVSrecal": {
        "Omega_b": 0.049,
        "Omega_c": 0.251,
        "h": 0.70,
        "n_s": 0.965,
        "S8": 0.776,
        "m_nu": 0.06,
        "ia_model": "tatt",
        # Dalal+23 Table VI MAP values for the fiducial TATT model:
        # A1, eta1, A2, eta2, and b_ta. The reproduction target S8 is the
        # marginalized mode from Table IV, not the MAP.
        "A1": 0.07,
        "eta1": -2.4,
        "A2": 0.78,
        "eta2": -2.6,
        "b_ta": 0.38,
        "z_pivot_IA": 0.62,
        "nz_variant": "original",
    },
    "cmblensing_act_spt_planck": {
        "Omega_b": 0.049,
        "Omega_c": 0.265,
        "h": 0.67,
        "n_s": 0.965,
        "sigma8": 0.811,
        "m_nu": 0.06,
    },
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


def set_thread_caps() -> dict[str, str | None]:
    for key, value in THREAD_CAPS.items():
        os.environ[key] = value
    return {key: os.environ.get(key) for key in THREAD_CAPS}


def covariance_chi2(data: np.ndarray, theory: np.ndarray, covariance: np.ndarray) -> float:
    delta = data - theory
    return float(delta @ np.linalg.solve(covariance, delta))


def _s8_from_metadata(meta: dict[str, Any]) -> float:
    value = meta.get("S8")
    if value is None:
        raise ValueError("prediction metadata did not contain S8")
    return float(value)


def _s8_fit(reference_s8: float, amplitude: float, sigma_amplitude: float) -> tuple[float | None, float | None]:
    if amplitude <= 0.0:
        return None, None
    recovered = reference_s8 * float(np.sqrt(amplitude))
    sigma = 0.5 * reference_s8 * float(sigma_amplitude) / float(np.sqrt(amplitude))
    return recovered, sigma


def _within_one_sigma(target: dict[str, Any], recovered: float | None, recovered_sigma: float | None) -> bool | None:
    published = target["published_S8"]
    if published is None or recovered is None:
        return None
    sigma = target["published_sigma_plus"] if recovered >= published else target["published_sigma_minus"]
    return abs(recovered - published) <= float(sigma)


def evaluate_probe(probe_id: str) -> dict[str, Any]:
    from sbt_cosmo.probes.weaklensing import amplitude_fit, build_weak_lensing_probe

    params = REFERENCE_PARAMS[probe_id]
    probe = build_weak_lensing_probe({"probe_id": probe_id, "nz_variant": params.get("nz_variant", "original")})

    t0 = time.perf_counter()
    pred = probe.predict(params)
    seconds = time.perf_counter() - t0

    native_chi2 = pred.chi2()
    native_dof = int(pred.data.size)
    amp = amplitude_fit(pred.data, pred.prediction, pred.covariance)
    scaled_prediction = amp["amplitude"] * pred.prediction
    scaled_chi2 = covariance_chi2(pred.data, scaled_prediction, pred.covariance)
    scaled_dof = int(pred.data.size) - 1

    reference_s8 = _s8_from_metadata(pred.metadata)
    recovered_s8, recovered_s8_sigma = _s8_fit(reference_s8, amp["amplitude"], amp["sigma_amplitude"])
    target = TARGETS[probe_id]
    s8_pass = _within_one_sigma(target, recovered_s8, recovered_s8_sigma)
    # This is deliberately conservative for a reproduction substrate: a
    # forward curve with chi2/dof >= 2 is not accepted as tracing the survey's
    # published best-fit theory vector.
    theory_shape_pass = bool(scaled_chi2 / scaled_dof < 2.0)
    pass_gate = bool((s8_pass is not False) and theory_shape_pass)
    if s8_pass is None and probe_id != "cmblensing_act_spt_planck":
        pass_gate = False
    ia_model_comparison = _hsc_ia_model_comparison(probe_id, probe, params, pred, amp, scaled_chi2)

    return {
        "probe_id": probe_id,
        "target": target,
        "reference_parameters": params,
        "reference_S8": reference_s8,
        "recovered_S8_from_scalar_amplitude": recovered_s8,
        "recovered_S8_sigma_from_scalar_amplitude": recovered_s8_sigma,
        "within_published_1sigma": s8_pass,
        "native_chi2": native_chi2,
        "native_dof": native_dof,
        "native_chi2_per_dof": native_chi2 / native_dof,
        "scalar_amplitude": amp,
        "scaled_chi2": scaled_chi2,
        "scaled_dof": scaled_dof,
        "scaled_chi2_per_dof": scaled_chi2 / scaled_dof,
        "theory_shape_pass_chi2_per_dof_lt_2": theory_shape_pass,
        "seconds_per_eval": seconds,
        "prediction_shape": list(pred.prediction.shape),
        "data_shape": list(pred.data.shape),
        "metadata": pred.metadata,
        "ia_model_comparison": ia_model_comparison,
        "pass": pass_gate,
        "limitations": _limitations(probe_id),
    }


def _hsc_ia_model_comparison(
    probe_id: str,
    probe: Any,
    params: Mapping[str, Any],
    main_prediction: Any,
    main_amplitude: dict[str, float],
    main_scaled_chi2: float,
) -> dict[str, Any] | None:
    if probe_id != "hsc_y3_origVSrecal":
        return None
    from sbt_cosmo.probes.weaklensing import amplitude_fit

    variants = {
        "tatt_dalal23_table_vi_map": (params, main_prediction, main_amplitude, main_scaled_chi2),
        "nla_unit_baseline": (
            {
                **params,
                "ia_model": "nla",
                "A_IA": 1.0,
                "eta_IA": 0.0,
                "A1": 1.0,
                "eta1": 0.0,
                "A2": 0.0,
                "eta2": 0.0,
                "b_ta": 0.0,
            },
            None,
            None,
            None,
        ),
    }
    rows: dict[str, Any] = {}
    for name, (variant_params, prediction, amp, scaled_chi2) in variants.items():
        if prediction is None:
            prediction = probe.predict(variant_params)
            amp = amplitude_fit(prediction.data, prediction.prediction, prediction.covariance)
            scaled_chi2 = covariance_chi2(
                prediction.data,
                amp["amplitude"] * prediction.prediction,
                prediction.covariance,
            )
        assert amp is not None
        assert scaled_chi2 is not None
        recovered_s8, recovered_s8_sigma = _s8_fit(
            _s8_from_metadata(prediction.metadata),
            amp["amplitude"],
            amp["sigma_amplitude"],
        )
        rows[name] = {
            "reference_parameters": variant_params,
            "metadata": prediction.metadata,
            "recovered_S8_from_scalar_amplitude": recovered_s8,
            "recovered_S8_sigma_from_scalar_amplitude": recovered_s8_sigma,
            "native_chi2_per_dof": prediction.chi2() / int(prediction.data.size),
            "scaled_chi2_per_dof": scaled_chi2 / (int(prediction.data.size) - 1),
            "scalar_amplitude": amp,
        }
    return rows


def _limitations(probe_id: str) -> list[str]:
    if probe_id == "kids_legacy_shear":
        return [
            "Uses the official 2pt_stats COSEBIs root/normalization tables and pyccl shear C_ell.",
            "Does not reproduce the KiDS mass-dependent IA module; pyccl single-amplitude NLA is left at A_IA=0 for this substrate check.",
        ]
    if probe_id == "hsc_y3_origVSrecal":
        return [
            "Uses HSC Fourier SACC bandpower windows and ORIGINAL HSC n(z) for REPRO; DESI-recalibrated n(z) is staging-only.",
            "IA is wired through real pyccl nl_pt TATT for the REPRO baseline; NLA remains available as the IA staging comparison.",
            "Does not sample the full HSC nuisance posterior; only a scalar amplitude readout is fitted for the substrate check.",
        ]
    if probe_id == "cmblensing_act_spt_planck":
        return [
            "Uses the official ACT+SPT+Planck binning matrices with lens_only=True and no CMB correction matrices.",
            "No scalar S8 target is locked for this family; pass is based on finite physical curve and chi2/dof.",
        ]
    return []


def write_repro_csv(rows: list[dict[str, Any]]) -> str:
    path = RESULTS / "repro_growth.csv"
    fieldnames = [
        "probe_id",
        "published_target",
        "recovered",
        "recovered_sigma",
        "within_1sigma",
        "chi2_per_dof",
        "status",
        "reason",
    ]
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            status = "pass" if row["pass"] else "fail"
            if row["target"]["published_S8"] is None:
                target = "no locked scalar S8; CMB-lensing consistency by chi2/dof"
            else:
                target = row["target"]["published_S8"]
            writer.writerow(
                {
                    "probe_id": row["probe_id"],
                    "published_target": target,
                    "recovered": row["recovered_S8_from_scalar_amplitude"],
                    "recovered_sigma": row["recovered_S8_sigma_from_scalar_amplitude"],
                    "within_1sigma": row["within_published_1sigma"],
                    "chi2_per_dof": row["scaled_chi2_per_dof"],
                    "status": status,
                    "reason": "; ".join(row["limitations"]),
                }
            )
    return sha256_file(path)


def main() -> None:
    start = time.perf_counter()
    thread_caps = set_thread_caps()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)

    rows = [evaluate_probe(probe_id) for probe_id in TARGETS]
    repro_pass = bool(all(row["pass"] for row in rows))
    status = {
        "schema_version": 1,
        "design_version": "E5-minimal-physical-v2",
        "thread_caps": thread_caps,
        "G-E5-REPRO": {
            "pass": repro_pass,
            "status": "pass" if repro_pass else "failed_physical_forward_reproduction",
            "rule": "published S8 within quoted 1sigma where locked, plus scaled theory chi2/dof < 2; HSC REPRO uses original n(z), with DESI-recal n(z) reserved for staging",
        },
        "G-E5-NOSURR": {
            "pass": True,
            "status": "physical_ccl_no_surrogate_templates",
        },
        "families": rows,
        "runtime_seconds": float(time.perf_counter() - start),
        "load_average": os.getloadavg(),
        "bottom_line": (
            "physical forward model passed all three E5-v2 reproduction substrates"
            if repro_pass
            else "physical forward model implemented, but G-E5-REPRO is not earned for all three families"
        ),
    }
    report_hash = write_json(RESULTS / "E5_repro.json", status)
    csv_hash = write_repro_csv(rows)
    write_json(
        RESULTS / "manifests" / "E5_repro_forward_manifest.json",
        {
            "schema_version": 1,
            "design_version": "E5-minimal-physical-v2",
            "outputs": {
                "repro": {"path": "results/E5/E5_repro.json", "sha256": report_hash},
                "repro_csv": {"path": "results/E5/repro_growth.csv", "sha256": csv_hash},
            },
            "stopped_before_certificate": True,
        },
    )
    write_json(RUNS / "summary.json", {"G-E5-REPRO_pass": repro_pass, "results_sha256": report_hash})
    print(json.dumps(status, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
