"""Manifest-shape checks for provenance and future run manifests."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
DATASET_REQUIRED_KEYS = {
    "dataset",
    "release",
    "access",
    "fetch_url",
    "raw_files",
    "processed",
    "aor_status",
    "fallback",
    "fallback_invoked",
}
AOR_STATUSES = {
    "zero",
    "budgeted",
    "bridged",
    "hidden",
    "moduli",
    "selected",
    "probabilistic",
    "out_of_scope",
    "nonclaim",
    "blocked",
    "approved_other",
    "asymptotic_budgeted",
    "summable",
    "contractive",
    "eventual_zero",
}


def test_data_manifests_schema() -> None:
    """Tracked dataset manifests have required provenance fields."""
    non_dataset_manifests = {"r0_bridge_affinities.json", "e5_growth_currency_inputs.json", "e5sp_shadowprice_inputs.json"}
    manifests = [
        path
        for path in sorted((ROOT / "data" / "manifests").glob("*.json"))
        if path.name not in non_dataset_manifests
    ]
    assert manifests
    for path in manifests:
        data = json.loads(path.read_text(encoding="utf-8"))
        assert DATASET_REQUIRED_KEYS <= set(data), path
        assert data["aor_status"] in AOR_STATUSES, path
        if data["fallback_invoked"]:
            assert data["aor_status"] != "zero", path
            assert data.get("fallback_justification"), path
        else:
            assert data["aor_status"] == "zero" or data.get("fallback") is not None, path
        assert data["raw_files"], path
        assert data["processed"], path


def test_run_manifest_schema() -> None:
    """Produced run manifests expose provenance, seeds, datasets, and terminal state."""
    manifests = sorted((ROOT / "experiments").glob("E*/outputs/manifest.json"))
    if not manifests:
        pytest.skip("run artifacts not present")
    required = {
        "schema_version",
        "experiment",
        "package_version",
        "datasets",
        "seeds",
        "determinism",
        "runtime",
        "artifact_checksums_sha256",
        "terminal_state",
    }
    for path in manifests:
        data = json.loads(path.read_text(encoding="utf-8"))
        assert required <= set(data), path
        assert data["schema_version"] == 1, path
        assert {"numpy", "python", "sampler"} <= set(data["seeds"]), path
        if data["experiment"] == "E0":
            assert data["datasets"] == [], path
            assert data["terminal_state"] == "PASS", path
