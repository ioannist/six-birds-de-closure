from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import numpy as np
import pytest


MODULE_PATH = Path(__file__).resolve().parents[1] / "scripts" / "de_window_carrier.py"
SPEC = importlib.util.spec_from_file_location("de_window_carrier", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
de_window = importlib.util.module_from_spec(SPEC)
sys.modules["de_window_carrier"] = de_window
SPEC.loader.exec_module(de_window)


def test_matter_era_growth_tracks_a_mode():
    cfg = de_window.CarrierConfig(a_max=2.0, n_eval=400)
    growth = de_window.solve_growth(0.0, cfg)
    expected = growth.a / cfg.a_init
    rel = np.max(np.abs(growth.growth / expected - 1.0))
    assert rel < 5.0e-4


def test_crunch_detection_for_negative_lambda():
    cfg = de_window.CarrierConfig(a_max=20.0, n_eval=200)
    growth = de_window.solve_growth(-1.0, cfg)
    assert growth.integration_sane
    assert growth.crunch_before_tmax


def test_rs_logic_requires_distinguishable_persistent_records():
    cfg = de_window.CarrierConfig(n_patches=8, heterogeneity_s=0.1, a_max=5.0, n_eval=500)
    growth = de_window.solve_growth(0.0, cfg)
    row = de_window.run_seed(0.0, 1100, cfg, growth)
    assert row["record_count_final"] >= 2
    assert row["distinguishable_records"]
    assert row["RS"]


def test_homogeneous_control_has_no_records():
    cfg = de_window.CarrierConfig(n_patches=8, heterogeneity_s=0.0, a_max=5.0, n_eval=300)
    rows = de_window.run_grid([0.0], [1100, 1101], cfg)
    assert all(row["record_count_final"] == 0 for row in rows)
    assert not any(row["RS"] for row in rows)


def test_turnaround_before_initial_grid_is_not_sane_expansion():
    cfg = de_window.CarrierConfig(a_init=0.1, a_max=1.0, n_eval=50)
    growth = de_window.solve_growth(-2000.0, cfg)
    assert not growth.integration_sane
    assert not de_window.run_seed(-2000.0, 1100, cfg, growth)["bare_admissible"]


def test_window_search_fails_on_carrier_without_records():
    cfg = de_window.CarrierConfig(heterogeneity_s=0.0, n_eval=50)
    with pytest.raises(ValueError, match="not record-bearing"):
        de_window.refine_positive_edge(cfg)


def test_grid_reuses_generator_of_seeds_at_each_lambda():
    cfg = de_window.CarrierConfig(n_eval=50)
    rows = de_window.run_grid([0.0, 0.01], (s for s in [1100, 1101]), cfg)
    assert len(rows) == 4
