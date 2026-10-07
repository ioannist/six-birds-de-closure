"""Naming conformance checks for G-REPO-16."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED_EXPERIMENT_DIRS = [
    "E0_synthetic",
    "E1_desi_dr2_repro",
    "E2_distance_duality",
    "E3_phantom_crossing",
    "E4_hubble_route_holonomy",
    "E5_growth_staging_s8",
    "E6_ide_accounting",
    "E7_modified_gravity",
    "E8_model_competition",
]


def test_experiment_dir_names() -> None:
    """Experiment directories match the locked E0-E8 slugs."""
    found = sorted(path.name for path in (ROOT / "experiments").iterdir() if path.is_dir())
    assert found == EXPECTED_EXPERIMENT_DIRS


def test_probe_and_route_tokens() -> None:
    """Probe and route tokens conform to the closed vocabulary."""
    from sbt_cosmo.hubble.routes import HUBBLE_ROUTE_IDS
    from sbt_cosmo.probes.base import PROBE_IDS

    assert PROBE_IDS == ("cmb", "bao", "sn", "wl", "rsd", "ladder")
    assert all(re.fullmatch(r"r[1-7]_[a-z0-9_]+", route) for route in HUBBLE_ROUTE_IDS)
