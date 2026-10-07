#!/usr/bin/env python3
"""E5 Phase 0: backend and real-data availability audit.

This script intentionally stops before the Schur carrier if fewer than three
decisive growth families have real published data vectors and covariances on
disk. It does not create surrogate rows or synthetic headline data.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results" / "E5"
RUNS = ROOT / "runs" / "E5" / "E5_phase0"
INPUT_MANIFEST = ROOT / "data" / "manifests" / "e5_growth_currency_inputs.json"

DATASET_MANIFESTS = {
    "des_y6_3x2pt": ROOT / "data" / "manifests" / "des_y6.json",
    "kids_legacy_shear": ROOT / "data" / "manifests" / "kids_legacy.json",
    "hsc_y3_origVSrecal": ROOT / "data" / "manifests" / "hsc_y3.json",
    "cmblensing_act_spt_planck": ROOT / "data" / "manifests" / "cmb_lensing.json",
    "desi_rsd_fsigma8": ROOT / "data" / "manifests" / "desi_rsd_fs.json",
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


def load_json(path: Path) -> Any:
    with path.open() as fh:
        return json.load(fh)


def _thread_env() -> dict[str, str | None]:
    for var in (
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "CCL_NUM_THREADS",
    ):
        os.environ.setdefault(var, "1")
    return {
        var: os.environ.get(var)
        for var in (
            "OMP_NUM_THREADS",
            "OPENBLAS_NUM_THREADS",
            "MKL_NUM_THREADS",
            "NUMEXPR_NUM_THREADS",
            "VECLIB_MAXIMUM_THREADS",
            "CCL_NUM_THREADS",
        )
    }


def run_env4() -> dict[str, Any]:
    import pyccl as ccl
    from classy import Class

    h = 0.67
    omega_b_frac = 0.049
    omega_c_frac = 0.265
    A_s = 2.1e-9
    n_s = 0.965
    k_h = np.logspace(-3, 0, 32)
    z_values = [0.0, 0.5, 1.0]

    t0 = time.perf_counter()
    cosmo_ccl = ccl.Cosmology(
        Omega_c=omega_c_frac,
        Omega_b=omega_b_frac,
        h=h,
        A_s=A_s,
        n_s=n_s,
        transfer_function="boltzmann_class",
        matter_power_spectrum="linear",
    )
    sigma8_ccl = float(ccl.sigma8(cosmo_ccl))

    cosmo_class = Class()
    cosmo_class.set(
        {
            "h": h,
            "omega_b": omega_b_frac * h * h,
            "omega_cdm": omega_c_frac * h * h,
            "A_s": A_s,
            "n_s": n_s,
            "output": "mPk",
            "P_k_max_1/Mpc": 1.0,
            "z_max_pk": max(z_values),
        }
    )
    cosmo_class.compute()
    sigma8_class = float(cosmo_class.sigma8())

    rows = []
    max_abs_frac = 0.0
    eval_count = 0
    eval_t0 = time.perf_counter()
    for z in z_values:
        a = 1.0 / (1.0 + z)
        for kh in k_h:
            k_mpc = float(kh * h)
            p_ccl = float(ccl.linear_matter_power(cosmo_ccl, k_mpc, a))
            p_class = float(cosmo_class.pk_lin(k_mpc, z))
            frac = p_ccl / p_class - 1.0
            max_abs_frac = max(max_abs_frac, abs(float(frac)))
            rows.append({"z": z, "k_h_Mpc": float(kh), "frac_diff": float(frac)})
            eval_count += 1
    eval_seconds = time.perf_counter() - eval_t0
    sigma8_frac = abs(sigma8_ccl / sigma8_class - 1.0)
    cosmo_class.struct_cleanup()
    cosmo_class.empty()

    versions = {
        "numpy": np.__version__,
        "pyccl": getattr(ccl, "__version__", "unknown"),
        "classy": getattr(__import__("classy"), "__version__", "unknown"),
        "E5_DESIGN_FREEZE_expected_pyccl": "3.1.2",
        "E5_DESIGN_FREEZE_expected_numpy": "1.26.4",
    }
    version_deviation = versions["pyccl"] != "3.1.2" or versions["numpy"] != "1.26.4"
    return {
        "gate_id": "G-ENV-4",
        "backend": "pyccl transfer_function=boltzmann_class vs standalone classy",
        "versions": versions,
        "version_deviation_from_E5_DESIGN_FREEZE": version_deviation,
        "fiducial": {
            "h": h,
            "Omega_b": omega_b_frac,
            "Omega_c": omega_c_frac,
            "A_s": A_s,
            "n_s": n_s,
        },
        "k_h_Mpc_range": [float(k_h[0]), float(k_h[-1])],
        "z_values": z_values,
        "max_abs_frac_Pk": max_abs_frac,
        "threshold_Pk": 0.01,
        "sigma8_pyccl": sigma8_ccl,
        "sigma8_classy": sigma8_class,
        "sigma8_frac_diff": sigma8_frac,
        "threshold_sigma8": 0.005,
        "pass": bool(max_abs_frac < 0.01 and sigma8_frac < 0.005),
        "profile": {
            "setup_plus_compute_seconds": float(time.perf_counter() - t0),
            "pk_eval_seconds": float(eval_seconds),
            "n_pk_evals": eval_count,
            "seconds_per_pk_eval": float(eval_seconds / max(eval_count, 1)),
        },
        "sample_differences": rows[:: max(1, len(rows) // 8)],
    }


def _path_info(path_text: str) -> dict[str, Any]:
    path = ROOT / path_text
    exists = path.exists()
    info: dict[str, Any] = {"path": path_text, "exists": exists}
    if exists and path.is_file():
        info.update({"bytes": path.stat().st_size, "sha256": sha256_file(path)})
    elif exists and path.is_dir():
        files = sorted(p for p in path.rglob("*") if p.is_file())
        info.update({"file_count": len(files), "bytes": int(sum(p.stat().st_size for p in files))})
    return info


def _url_reachable(url: str | None) -> dict[str, Any]:
    if not url or str(url).startswith("TODO"):
        return {"url": url, "reachable": False, "reason": "missing_or_todo_url"}
    req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "sbt-e5-phase0/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return {
                "url": url,
                "reachable": 200 <= resp.status < 400,
                "http_status": resp.status,
                "content_type": resp.headers.get("content-type"),
                "note": "Reachability only; this is not proof of a concrete data-vector/covariance download.",
            }
    except urllib.error.HTTPError as exc:
        if exc.code == 405:
            try:
                get_req = urllib.request.Request(url, method="GET", headers={"User-Agent": "sbt-e5-phase0/1.0"})
                with urllib.request.urlopen(get_req, timeout=10) as resp:
                    resp.read(256)
                    return {
                        "url": url,
                        "reachable": 200 <= resp.status < 400,
                        "http_status": resp.status,
                        "content_type": resp.headers.get("content-type"),
                        "note": "GET fallback used; not a concrete data-vector/covariance download.",
                    }
            except Exception as get_exc:  # noqa: BLE001 - provenance report wants the exact exception.
                return {"url": url, "reachable": False, "error": repr(get_exc)}
        return {"url": url, "reachable": False, "http_status": exc.code, "error": repr(exc)}
    except Exception as exc:  # noqa: BLE001 - provenance report wants the exact exception.
        return {"url": url, "reachable": False, "error": repr(exc)}


def data_availability(input_manifest: dict[str, Any]) -> dict[str, Any]:
    families = []
    decisive_available = 0
    for probe in input_manifest["probes"]:
        probe_id = probe["probe_id"]
        dataset_manifest_path = DATASET_MANIFESTS.get(probe_id)
        dataset_manifest = load_json(dataset_manifest_path) if dataset_manifest_path and dataset_manifest_path.exists() else None
        processed = dataset_manifest.get("processed", {}) if dataset_manifest else {}
        raw_files = dataset_manifest.get("raw_files", []) if dataset_manifest else []
        data_vector_path = processed.get("data_vector", {}).get("path")
        covariance_path = processed.get("covariance", {}).get("path")
        data_vector = _path_info(data_vector_path) if data_vector_path else {"exists": False, "reason": "no_path"}
        covariance = _path_info(covariance_path) if covariance_path else {"exists": False, "reason": "no_path"}
        raw_infos = [_path_info(r.get("path", "")) for r in raw_files if r.get("path")]
        fetch = _url_reachable(dataset_manifest.get("fetch_url") if dataset_manifest else None)
        concrete_download_pinned = bool(
            dataset_manifest
            and dataset_manifest.get("fetch_url")
            and "arxiv.org/abs" not in str(dataset_manifest.get("fetch_url"))
            and not str(dataset_manifest.get("fetch_url")).endswith("/")
        )
        real_pair_available = bool(data_vector.get("exists") and covariance.get("exists"))
        if probe["decisive"] and real_pair_available:
            decisive_available += 1
        status = "available" if real_pair_available else "blocked"
        if not probe["decisive"] and real_pair_available:
            status = "method_control_available"
        elif not probe["decisive"]:
            status = "method_control_blocked"
        families.append(
            {
                "probe_id": probe_id,
                "family": probe["family"],
                "role": probe["role"],
                "decisive": probe["decisive"],
                "source_arxiv": probe.get("source_arxiv"),
                "dataset_manifest": str(dataset_manifest_path.relative_to(ROOT)) if dataset_manifest_path else None,
                "dataset_manifest_sha256": sha256_file(dataset_manifest_path) if dataset_manifest_path and dataset_manifest_path.exists() else None,
                "e5_manifest_data_vector_field": probe.get("data_vector"),
                "e5_manifest_covariance_field": probe.get("covariance"),
                "processed_data_vector": data_vector,
                "processed_covariance": covariance,
                "raw_payloads": raw_infos,
                "fetch_url_probe": fetch,
                "concrete_download_path_pinned": concrete_download_pinned,
                "real_published_vector_and_covariance_available": real_pair_available,
                "aor_status": status,
                "blocked_reason": None
                if real_pair_available
                else (
                    "No real processed data_vector.npy + covariance.npy pair exists at the manifest paths. "
                    "The E5 input manifest still has TODO-on-fetch fields, and the dataset fetch_url is not a "
                    "verified concrete vector/covariance download."
                ),
            }
        )
    return {
        "schema_version": 1,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "decisive_families_required_min": 3,
        "decisive_families_available": decisive_available,
        "can_proceed_to_phase1": bool(decisive_available >= 3),
        "families": families,
    }


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
            "gate": "G-E5-CURRENCY-DECISIVE",
            "aor_status": status["aor_status"],
            "terminal_state": status["terminal_state"],
            "next_front": status["next_front"],
            "notes": status["status_reason"],
        }
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def append_xi_coherence(status: dict[str, Any]) -> None:
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
            "run_id": "E5_phase0",
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
            "decisive_pass": status["G-E5-CURRENCY-DECISIVE"]["pass"],
        }
    )
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    start = time.perf_counter()
    thread_env = _thread_env()
    RESULTS.mkdir(parents=True, exist_ok=True)
    RUNS.mkdir(parents=True, exist_ok=True)

    manifest = load_json(INPUT_MANIFEST)
    manifest_hash = sha256_file(INPUT_MANIFEST)
    freeze = {
        "schema_version": 1,
        "input_manifest": str(INPUT_MANIFEST.relative_to(ROOT)),
        "input_manifest_sha256": manifest_hash,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "note": "Manifest sha256 frozen before E5 backend/data availability scoring.",
    }
    freeze_hash = write_json(RESULTS / "E5_input_manifest_freeze.json", freeze)

    env4 = run_env4()
    env4_hash = write_json(RESULTS / "E5_env4_pyccl_class.json", env4)
    availability = data_availability(manifest)
    availability_hash = write_json(RESULTS / "E5_data_availability.json", availability)

    if not env4["pass"]:
        terminal_state = "BLOCKED"
        aor_status = "blocked"
        reason = "G-ENV-4 pyccl/Class agreement failed; no surrogate headline allowed."
    elif availability["decisive_families_available"] < availability["decisive_families_required_min"]:
        terminal_state = "BLOCKED"
        aor_status = "blocked"
        reason = (
            "AOR-blocked pending growth data: fewer than three decisive families have real "
            "published data_vector + covariance payloads at manifest paths."
        )
    else:
        terminal_state = "READY_FOR_PHASE1"
        aor_status = "zero"
        reason = "Phase 0 passed; enough decisive families are available for Schur carrier build."

    status = {
        "schema_version": 1,
        "phase": "E5_PHASE0_BACKEND_DATA",
        "G-ENV-4": env4,
        "G-E5-BACKEND": {
            "pass": bool(env4["pass"]),
            "version_deviation_from_E5_DESIGN_FREEZE": env4["version_deviation_from_E5_DESIGN_FREEZE"],
            "note": "Numerical G-ENV-4 agreement is separate from the recorded E5_DESIGN_FREEZE version deviation.",
        },
        "G-E5-NOSURR": {
            "pass": False,
            "status": "not_evaluated_no_decisive_data",
            "note": "No surrogate headline was built or reported.",
        },
        "G-E5-CURRENCY-DECISIVE": {
            "pass": False,
            "status": "blocked_pending_growth_data" if terminal_state == "BLOCKED" else "not_evaluated_phase0_only",
            "available_decisive_families": availability["decisive_families_available"],
            "required_decisive_families": availability["decisive_families_required_min"],
        },
        "aor_status": aor_status,
        "terminal_state": terminal_state,
        "next_front": "manager_data_provision" if terminal_state == "BLOCKED" else "E5_PHASE1",
        "status_reason": reason,
        "runtime_seconds": float(time.perf_counter() - start),
    }
    status_hash = write_json(RESULTS / "E5_status.json", status)
    write_json(RESULTS / "e5_currency_status.json", status)
    update_aor_status(status)
    append_xi_coherence(status)

    coherence = {
        "schema_version": 1,
        "experiment": "E5",
        "run_id": "E5_phase0",
        "carrier": "sign_free_growth_currency",
        "aor_status": aor_status,
        "terminal_state": terminal_state,
        "decisive_pass": False,
        "status_reason": reason,
        "signed_amplitude_note": "E5 is sign-free; no a0/a1/a2 amplitude is produced in Phase 0.",
    }
    coherence_hash = write_json(ROOT / "results" / "coherence_ledger" / "E5.json", coherence)

    run_manifest = {
        "schema_version": 1,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "inputs": {
            "e5_growth_currency_inputs": {"path": str(INPUT_MANIFEST.relative_to(ROOT)), "sha256": manifest_hash},
            "dataset_manifests": {
                probe: {"path": str(path.relative_to(ROOT)), "sha256": sha256_file(path)}
                for probe, path in DATASET_MANIFESTS.items()
                if path.exists()
            },
        },
        "thread_env": thread_env,
        "outputs": {
            "input_manifest_freeze": {"path": "results/E5/E5_input_manifest_freeze.json", "sha256": freeze_hash},
            "env4": {"path": "results/E5/E5_env4_pyccl_class.json", "sha256": env4_hash},
            "data_availability": {"path": "results/E5/E5_data_availability.json", "sha256": availability_hash},
            "status": {"path": "results/E5/E5_status.json", "sha256": status_hash},
            "coherence": {"path": "results/coherence_ledger/E5.json", "sha256": coherence_hash},
        },
    }
    run_manifest_hash = write_json(RESULTS / "manifests" / "E5_phase0_manifest.json", run_manifest)
    summary = {
        "terminal_state": terminal_state,
        "aor_status": aor_status,
        "G-ENV-4_pass": env4["pass"],
        "available_decisive_families": availability["decisive_families_available"],
        "required_decisive_families": availability["decisive_families_required_min"],
        "status_reason": reason,
        "run_manifest_sha256": run_manifest_hash,
    }
    write_json(RUNS / "summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
