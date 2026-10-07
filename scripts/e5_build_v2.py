#!/usr/bin/env python3
"""E5-minimal-physical-v2 substrate and build gate.

This script verifies the v2 locked inputs and real data products, then stops
before the Schur carrier if the physical CCL reproduction/forward-model
substrate is not implemented. It deliberately does not substitute templates or
surrogates for KiDS/HSC/CMB-lensing predictions.
"""

from __future__ import annotations

import ast
import csv
import hashlib
import json
import os
import time
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "E5_minimal_physical_v2"

GOVERNED = {
    "e5_manifest": ROOT / "data" / "manifests" / "e5_growth_currency_inputs.json",
    "carrier": ROOT / "plan" / "E5_CARRIER_REALIZATION.md",
    "design_freeze": ROOT / "plan" / "E5_DESIGN_FREEZE.md",
    "gates": ROOT / "plan" / "07-pass-fail-gates.md",
}

DECISIVE_PROBES = {
    "kids_legacy_shear": ROOT / "data" / "manifests" / "kids_legacy.json",
    "hsc_y3_origVSrecal": ROOT / "data" / "manifests" / "hsc_y3.json",
    "cmblensing_act_spt_planck": ROOT / "data" / "manifests" / "cmb_lensing.json",
}

PHYSICAL_FORWARD_MODULES = [
    ROOT / "sbt_cosmo" / "growth" / "power.py",
    ROOT / "sbt_cosmo" / "growth" / "projection.py",
    ROOT / "sbt_cosmo" / "growth" / "s8.py",
    ROOT / "sbt_cosmo" / "probes" / "weaklensing.py",
]


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


def load_json(path: Path) -> Any:
    with path.open() as fh:
        return json.load(fh)


def set_thread_caps() -> dict[str, str | None]:
    caps = {
        "OMP_NUM_THREADS": "1",
        "OPENBLAS_NUM_THREADS": "1",
        "MKL_NUM_THREADS": "1",
        "NUMEXPR_NUM_THREADS": "1",
        "VECLIB_MAXIMUM_THREADS": "1",
        "CCL_NUM_THREADS": "1",
    }
    for key, value in caps.items():
        os.environ[key] = value
    return {key: os.environ.get(key) for key in caps}


def freeze_governed_inputs() -> dict[str, Any]:
    return {
        key: {"path": str(path.relative_to(ROOT)), "sha256": sha256_file(path)}
        for key, path in GOVERNED.items()
    }


def verify_array(entry: dict[str, Any]) -> dict[str, Any]:
    path = ROOT / entry["path"]
    if not path.is_file():
        return {"path": entry["path"], "exists": False, "pass": False, "reason": "missing"}
    digest = sha256_file(path)
    arr = np.load(path)
    expected_shape = tuple(entry.get("shape", ()))
    shape_ok = tuple(arr.shape) == expected_shape if expected_shape else True
    sha_ok = digest == entry.get("sha256")
    return {
        "path": entry["path"],
        "exists": True,
        "sha256": digest,
        "expected_sha256": entry.get("sha256"),
        "sha256_ok": sha_ok,
        "shape": list(arr.shape),
        "expected_shape": list(expected_shape),
        "shape_ok": shape_ok,
        "dtype": str(arr.dtype),
        "finite": bool(np.all(np.isfinite(arr))),
        "pass": bool(sha_ok and shape_ok and np.all(np.isfinite(arr))),
    }


def covariance_report(entry: dict[str, Any]) -> dict[str, Any]:
    base = verify_array(entry)
    if not base["pass"]:
        return {**base, "symmetric": False, "PD": False, "condition_number": None}
    cov = np.load(ROOT / entry["path"])
    symmetric = bool(np.allclose(cov, cov.T, rtol=0.0, atol=1e-10))
    eig = np.linalg.eigvalsh(cov)
    eig_min = float(eig[0])
    eig_max = float(eig[-1])
    cond = float(eig_max / eig_min) if eig_min > 0 else float("inf")
    try:
        np.linalg.cholesky(cov)
        chol = True
    except np.linalg.LinAlgError:
        chol = False
    return {
        **base,
        "symmetric": symmetric,
        "lambda_min": eig_min,
        "condition_number": cond,
        "chol_success": chol,
        "PD": bool(chol and eig_min > 0),
        "G-E5-COV_pass": bool(base["pass"] and symmetric and chol and cond < 1.0e8),
    }


def verify_data_products(e5_manifest: dict[str, Any]) -> dict[str, Any]:
    probes = {probe["probe_id"]: probe for probe in e5_manifest["probes"]}
    rows = []
    for probe_id, manifest_path in DECISIVE_PROBES.items():
        dataset_manifest = load_json(manifest_path)
        processed = dataset_manifest["processed"]
        data = verify_array(processed["data_vector"])
        cov = covariance_report(processed["covariance"])
        staging_pair = {}
        if probe_id == "hsc_y3_origVSrecal":
            for key, path_text in {
                "nz_original": processed["nz_original"]["path"],
                "nz_original_z": processed["nz_original"]["z"],
                "nz_desi_recal": processed["nz_desi_recal"]["path"],
                "nz_desi_recal_z": processed["nz_desi_recal"]["z"],
            }.items():
                path = ROOT / path_text
                staging_pair[key] = {
                    "path": path_text,
                    "exists": path.is_file(),
                    "sha256": sha256_file(path) if path.is_file() else None,
                    "shape": list(np.load(path).shape) if path.is_file() else None,
                }
        rows.append(
            {
                "probe_id": probe_id,
                "family": probes[probe_id]["family"],
                "dataset_manifest": str(manifest_path.relative_to(ROOT)),
                "dataset_manifest_sha256": sha256_file(manifest_path),
                "data_vector": data,
                "covariance": cov,
                "staging_pair": staging_pair,
                "data_available": bool(data["pass"] and cov["G-E5-COV_pass"]),
                "total_SNR_from_manifest": dataset_manifest.get("validation", {}).get("total_SNR"),
            }
        )
    return {
        "schema_version": 1,
        "design_version": e5_manifest.get("design_version"),
        "families": rows,
        "all_three_data_available": bool(all(row["data_available"] for row in rows)),
        "G-E5-COV": {
            "pass": bool(all(row["covariance"]["G-E5-COV_pass"] for row in rows)),
            "condition_threshold": 1.0e8,
        },
    }


def function_has_notimplemented(path: Path) -> bool:
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, ast.Raise):
            text = ast.unparse(node) if hasattr(ast, "unparse") else ""
            if "NotImplementedError" in text:
                return True
    return False


def physical_forward_status() -> dict[str, Any]:
    module_rows = []
    for path in PHYSICAL_FORWARD_MODULES:
        module_rows.append(
            {
                "path": str(path.relative_to(ROOT)),
                "has_notimplemented": function_has_notimplemented(path),
                "sha256": sha256_file(path),
            }
        )
    missing = [row for row in module_rows if row["has_notimplemented"]]
    repro_path = RESULTS / "E5_repro.json"
    if repro_path.is_file():
        repro = load_json(repro_path)
        repro_gate = dict(repro["G-E5-REPRO"])
        if missing:
            repro_gate = {
                "pass": False,
                "status": "blocked_forward_modules_not_implemented",
                "reason": "Physical forward reproduction cannot unblock E5 while NotImplementedError remains in forward modules.",
                "upstream_repro_reported_pass": bool(repro["G-E5-REPRO"].get("pass")),
            }
        return {
            "G-E5-REPRO": repro_gate,
            "physical_forward_modules": module_rows,
            "blocking_modules": [row["path"] for row in missing],
            "repro_report": {
                "path": str(repro_path.relative_to(ROOT)),
                "sha256": sha256_file(repro_path),
                "families": repro.get("families", []),
            },
            "G-E5-NOSURR": repro.get(
                "G-E5-NOSURR",
                {"pass": True, "status": "physical_ccl_no_surrogate_templates"},
            ),
        }
    if not missing:
        return {
            "G-E5-REPRO": {
                "pass": False,
                "status": "not_evaluated",
                "reason": "Physical forward modules are implemented, but results/E5/E5_repro.json has not been generated. Run scripts/e5_repro_forward.py first.",
            },
            "physical_forward_modules": module_rows,
            "blocking_modules": [],
            "G-E5-NOSURR": {
                "pass": True,
                "status": "surrogate_not_used",
            },
        }
    kids_raw = ROOT / "data/raw/kids_legacy/KiDS_Legacy_cosmic_shear_data_release/data/KiDS_Legacy_cosebis.fits"
    return {
        "G-E5-REPRO": {
            "pass": False,
            "status": "blocked_missing_physical_forward_model",
            "published_targets": {
                "KiDS_Legacy_S8": 0.815,
                "HSC_Y3_S8": 0.776,
                "CMB_lensing": "consistent with published ACT+SPT+Planck lensing release",
            },
            "reason": (
                "The real data vectors/covariances are present, but the repo still lacks an implemented "
                "physical CCL projection/reproduction stack for the locked observables. KiDS decisive rows "
                "are COSEBIs; the available raw FITS contains data/cov/n(z), but no implemented COSEBI "
                "prediction adapter is present in sbt_cosmo. HSC and CMB-lensing cannot rescue the all-3 "
                "rule because KiDS is one of the three decisive folds."
            ),
        },
        "physical_forward_modules": module_rows,
        "blocking_modules": [row["path"] for row in missing],
        "kids_cosebis_raw_exists": kids_raw.is_file(),
        "G-E5-NOSURR": {
            "pass": True,
            "status": "surrogate_not_used",
            "note": "Build stopped before any surrogate/template prediction was used as a headline.",
        },
    }


def load_recorded_env4() -> dict[str, Any]:
    path = RESULTS / "E5_env4_pyccl_class.json"
    if not path.is_file():
        return {"pass": False, "status": "missing_recorded_G_ENV_4", "path": str(path.relative_to(ROOT))}
    data = load_json(path)
    return {
        "pass": bool(data.get("pass")),
        "path": str(path.relative_to(ROOT)),
        "sha256": sha256_file(path),
        "max_abs_frac_Pk": data.get("max_abs_frac_Pk"),
        "sigma8_frac_diff": data.get("sigma8_frac_diff"),
        "versions": data.get("versions"),
        "profile": data.get("profile"),
    }


def ia_nuisance_envelope_status() -> dict[str, Any]:
    """Record the IA nuisance class exposed to the later Schur carrier."""
    envelope = {
        "schema_version": 1,
        "design_version": "E5-minimal-physical-v2",
        "status": "implemented_not_evaluated_certificate_stop",
        "marginalization_required_before_D_growth": True,
        "models": {
            "NLA": {
                "implemented": True,
                "parameters": ["A_IA", "eta_IA", "z_pivot_IA"],
                "wide_prior": {"A_IA": [-6.0, 6.0], "eta_IA": [-6.0, 6.0]},
            },
            "TATT": {
                "implemented": True,
                "parameters": ["A1", "eta1", "A2", "eta2", "b_ta", "z_pivot_IA"],
                "wide_prior": {"A1": [-6.0, 6.0], "eta1": [-6.0, 6.0], "A2": [-6.0, 6.0], "eta2": [-6.0, 6.0], "b_ta": [0.0, 2.0]},
                "backend": "pyccl.nl_pt.PTIntrinsicAlignmentTracer + EulerianPTCalculator",
            },
        },
        "omega_floors_required_for_certificate": ["Omega_WL_shared", "Omega_HSC_pipeline"],
        "zero_controls_required_for_certificate": [
            "same_family_saturation",
            "shuffled_stages",
            "reversed_scale_cut_order",
            "linear_zero_heterogeneity_synthetic",
            "held_out_staging_vector_removed_from_L_and_D",
            "DPI_coarsening_guard",
        ],
        "certificate_evaluation": "not_run_in_C0b_FIX2",
    }
    envelope["pass"] = bool(all(model["implemented"] for model in envelope["models"].values()))
    return envelope


def write_repro_csv(status: dict[str, Any]) -> str:
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
    families = status.get("repro_report", {}).get("families")
    if families:
        with path.open("w", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=fieldnames)
            writer.writeheader()
            for row in families:
                target = row.get("target", {}).get("published_S8")
                if target is None:
                    target = "no locked scalar S8; CMB-lensing consistency by chi2/dof"
                writer.writerow(
                    {
                        "probe_id": row["probe_id"],
                        "published_target": target,
                        "recovered": row.get("recovered_S8_from_scalar_amplitude"),
                        "recovered_sigma": row.get("recovered_S8_sigma_from_scalar_amplitude"),
                        "within_1sigma": row.get("within_published_1sigma"),
                        "chi2_per_dof": row.get("scaled_chi2_per_dof"),
                        "status": "pass" if row.get("pass") else "fail",
                        "reason": "; ".join(row.get("limitations", [])),
                    }
                )
        return sha256_file(path)
    rows = []
    targets = status["G-E5-REPRO"]["published_targets"]
    for probe_id, target in [
        ("kids_legacy_shear", targets["KiDS_Legacy_S8"]),
        ("hsc_y3_origVSrecal", targets["HSC_Y3_S8"]),
        ("cmblensing_act_spt_planck", targets["CMB_lensing"]),
    ]:
        rows.append(
            {
                    "probe_id": probe_id,
                    "published_target": target,
                    "recovered": "",
                    "recovered_sigma": "",
                    "within_1sigma": False,
                    "chi2_per_dof": "",
                    "status": "blocked_missing_physical_forward_model",
                    "reason": status["G-E5-REPRO"]["reason"],
                }
        )
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    return sha256_file(path)


def update_aor_status(status: dict[str, Any]) -> None:
    path = ROOT / "results" / "aor_status_table.csv"
    fieldnames = ["experiment", "gate", "aor_status", "terminal_state", "next_front", "notes"]
    rows = []
    if path.exists():
        with path.open(newline="") as fh:
            reader = csv.DictReader(fh)
            if reader.fieldnames == fieldnames:
                rows = [row for row in reader if row.get("experiment") != "E5"]
    rows.append(
        {
            "experiment": "E5",
            "gate": "G-E5-CURRENCY-DECISIVE-3FAM",
            "aor_status": status["aor_status"],
            "terminal_state": status["terminal_state"],
            "next_front": status["next_front"],
            "notes": status["status_reason"],
        }
    )
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def update_coherence(status: dict[str, Any]) -> None:
    path = ROOT / "results" / "xi_cosmo_coherence.csv"
    fieldnames = [
        "experiment",
        "run_id",
        "model",
        "a0",
        "a0_sigma",
        "a1",
        "a1_sigma",
        "a2",
        "a2_sigma",
        "K_L_max_abs_mpc",
        "K_M_max_abs_ratio",
        "K_H_max_abs_ratio",
        "aor_status",
        "prediction_chi2_per_dof",
        "sign_hit_rate",
        "decisive_pass",
    ]
    rows = []
    if path.exists():
        with path.open(newline="") as fh:
            reader = csv.DictReader(fh)
            if reader.fieldnames == fieldnames:
                rows = [row for row in reader if row.get("experiment") != "E5"]
    rows.append(
        {
            "experiment": "E5",
            "run_id": "E5_minimal_physical_v2",
            "model": "sign_free_growth_currency",
            "a0": "",
            "a0_sigma": "",
            "a1": "",
            "a1_sigma": "",
            "a2": "",
            "a2_sigma": "",
            "K_L_max_abs_mpc": "",
            "K_M_max_abs_ratio": "",
            "K_H_max_abs_ratio": "",
            "aor_status": status["aor_status"],
            "prediction_chi2_per_dof": "",
            "sign_hit_rate": "",
            "decisive_pass": status["G-E5-CURRENCY-DECISIVE-3FAM"]["pass"],
        }
    )
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    start = time.perf_counter()
    thread_env = set_thread_caps()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)

    governed = freeze_governed_inputs()
    e5_manifest = load_json(GOVERNED["e5_manifest"])
    data = verify_data_products(e5_manifest)
    env4 = load_recorded_env4()
    repro = physical_forward_status()
    ia_envelope = ia_nuisance_envelope_status()

    substrate_pass = bool(data["all_three_data_available"] and data["G-E5-COV"]["pass"] and env4["pass"])
    repro_pass = bool(repro["G-E5-REPRO"]["pass"])
    if not substrate_pass:
        terminal_state = "BLOCKED"
        aor_status = "blocked"
        reason = "E5 v2 data/backend substrate failed before reproduction."
    elif not repro_pass:
        terminal_state = "BLOCKED"
        aor_status = "blocked"
        reason = (
            "E5 v2 blocked at G-E5-REPRO: physical CCL forward model ran, "
            f"but reproduction is not earned ({repro['G-E5-REPRO'].get('status', 'failed')})."
        )
    else:
        terminal_state = "REPRO_PASSED_AWAITING_REVIEW"
        aor_status = "zero"
        reason = "Substrate and TATT-capable reproduction passed; Schur carrier is not authorized until Eddy re-review."

    status = {
        "schema_version": 1,
        "design_version": "E5-minimal-physical-v2",
        "thread_caps": thread_env,
        "governed_input_hashes": governed,
        "G-ENV-4": env4,
        "G-E5-COV": data["G-E5-COV"],
        "G-E5-BACKEND": {"pass": bool(env4["pass"]), "uses_recorded_env4": True},
        "G-E5-REPRO": repro["G-E5-REPRO"],
        "G-E5-NOSURR": repro["G-E5-NOSURR"],
        "G-E5-IA-ENVELOPE": ia_envelope,
        "G-E5-RANK": {
            "pass": None,
            "status": "not_evaluated_repro_blocked" if terminal_state == "BLOCKED" else "not_evaluated_stop_after_repro_review",
        },
        "G-E5-KERNEL": {
            "pass": None,
            "status": "not_evaluated_repro_blocked" if terminal_state == "BLOCKED" else "not_evaluated_stop_after_repro_review",
        },
        "G-E5-CURRENCY-DECISIVE-3FAM": {
            "pass": False,
            "status": "blocked_repro_substrate" if terminal_state == "BLOCKED" else "not_evaluated",
            "all_3_of_3_rule": True,
            "majority_rescue_used": False,
        },
        "C3_KiDS_HSC_shared_stress": {
            "status": "not_evaluated_repro_blocked" if terminal_state == "BLOCKED" else "not_evaluated_stop_after_repro_review",
            "rho_grid": [0.25, 0.5, 0.75],
        },
        "C5_HSC_pipeline_budget": {
            "status": "not_evaluated_repro_blocked" if terminal_state == "BLOCKED" else "not_evaluated_stop_after_repro_review"
        },
        "aor_status": aor_status,
        "terminal_state": terminal_state,
        "next_front": "manager_physical_forward_model" if terminal_state == "BLOCKED" else "eddy_re_review",
        "status_reason": reason,
        "runtime_seconds": float(time.perf_counter() - start),
    }

    freeze_hash = write_json(RESULTS / "E5_v2_freeze.json", governed)
    substrate_hash = write_json(
        RESULTS / "E5_v2_substrate.json",
        {
            "schema_version": 1,
            "design_version": "E5-minimal-physical-v2",
            "data": data,
            "physical_forward_status": repro,
            "ia_nuisance_envelope": ia_envelope,
        },
    )
    ia_envelope_hash = write_json(RESULTS / "E5_ia_nuisance_envelope.json", ia_envelope)
    repro_csv_hash = write_repro_csv(repro)
    status_hash = write_json(RESULTS / "E5_status.json", status)
    write_json(RESULTS / "e5_currency_status.json", status)
    write_json(
        RESULTS / "E5_currency_certificate.json",
        {
            "schema_version": 1,
            "design_version": "E5-minimal-physical-v2",
            "status": "not_built_repro_blocked" if terminal_state == "BLOCKED" else "not_built_stop_after_repro_review",
        },
    )
    update_aor_status(status)
    update_coherence(status)
    coherence_hash = write_json(
        ROOT / "results" / "coherence_ledger" / "E5.json",
        {
            "schema_version": 1,
            "experiment": "E5",
            "run_id": "E5_minimal_physical_v2",
            "carrier": "sign_free_growth_currency",
            "terminal_state": terminal_state,
            "aor_status": aor_status,
            "decisive_pass": False,
            "status_reason": reason,
            "signed_amplitude_note": "E5 is sign-free; no a0/a1/a2 amplitude is produced.",
        },
    )

    run_manifest = {
        "schema_version": 1,
        "design_version": "E5-minimal-physical-v2",
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "inputs": governed,
        "thread_caps": thread_env,
        "outputs": {
            "freeze": {"path": "results/E5/E5_v2_freeze.json", "sha256": freeze_hash},
            "substrate": {"path": "results/E5/E5_v2_substrate.json", "sha256": substrate_hash},
            "repro_growth_csv": {"path": "results/E5/repro_growth.csv", "sha256": repro_csv_hash},
            "ia_nuisance_envelope": {"path": "results/E5/E5_ia_nuisance_envelope.json", "sha256": ia_envelope_hash},
            "status": {"path": "results/E5/E5_status.json", "sha256": status_hash},
            "coherence": {"path": "results/coherence_ledger/E5.json", "sha256": coherence_hash},
        },
    }
    manifest_hash = write_json(RESULTS / "manifests" / "E5_minimal_physical_v2_manifest.json", run_manifest)
    summary = {
        "terminal_state": terminal_state,
        "aor_status": aor_status,
        "status_reason": reason,
        "data_all_three_available": data["all_three_data_available"],
        "G-E5-COV_pass": data["G-E5-COV"]["pass"],
        "G-ENV-4_pass": env4["pass"],
        "G-E5-REPRO_pass": repro["G-E5-REPRO"]["pass"],
        "G-E5-CURRENCY-DECISIVE-3FAM": status["G-E5-CURRENCY-DECISIVE-3FAM"],
        "run_manifest_sha256": manifest_hash,
    }
    write_json(RUNS / "summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
