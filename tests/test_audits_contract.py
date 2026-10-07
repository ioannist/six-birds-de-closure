"""Audit-control checks for E0 synthetic outputs."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
E0_OUTPUTS = ROOT / "experiments" / "E0_synthetic" / "outputs"


def _summary() -> dict:
    path = E0_OUTPUTS / "summary.json"
    if not path.exists():
        pytest.skip("E0 artifacts not present")
    return json.loads(path.read_text(encoding="utf-8"))


def test_e0_null_controls_are_recorded() -> None:
    """E0 records the matched null controls for route, distance, and holonomy."""
    summary = _summary()
    assert summary["gates"]["G-E0-1.2"]["value"] <= 1.0e-10
    assert summary["gates"]["G-E0-2.1"]["value"] <= 1.0e-6
    assert summary["gates"]["G-E0-2.5"]["value"] < 0.1
    assert summary["gates"]["G-E0-4.6"]["value"] <= 0.05


def test_e0_aor_has_no_unstatused_entries() -> None:
    """The E0 AOR ledger is complete under the closed status vocabulary."""
    path = E0_OUTPUTS / "aor_status.json"
    if not path.exists():
        pytest.skip("E0 artifacts not present")
    ledger = json.loads(path.read_text(encoding="utf-8"))
    assert ledger["unstatused"] == 0
    statuses = {entry["status"] for entry in ledger["entries"]}
    assert "unstatused" not in statuses
