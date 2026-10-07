from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import numpy as np


MODULE_PATH = Path(__file__).resolve().parents[1] / "scripts" / "de_dual_carrier.py"
SPEC = importlib.util.spec_from_file_location("de_dual_carrier", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
de_dual = importlib.util.module_from_spec(SPEC)
sys.modules["de_dual_carrier"] = de_dual
SPEC.loader.exec_module(de_dual)


def test_global_budget_kkt_stationarity():
    weights = np.array([1.2, 1.8, 2.4])
    curvatures = np.array([0.3, 0.4, 0.5])
    budget = 0.5 * float(np.sum(de_dual.unconstrained_x(weights, curvatures)))
    sol = de_dual.solve_global_budget(budget, weights, curvatures)
    assert sol["active"]
    assert sol["dual"] > 0.0
    assert sol["max_kkt_residual"] < 1.0e-10


def test_dual_matches_finite_difference_value():
    weights = np.array([1.3, 1.7, 2.1])
    curvatures = np.array([0.25, 0.35, 0.45])
    budget = 0.6 * float(np.sum(de_dual.unconstrained_x(weights, curvatures)))
    sol = de_dual.solve_global_budget(budget, weights, curvatures)
    fd = de_dual.finite_diff_dual(budget, budget * 1.0e-5, weights, curvatures)
    assert abs(sol["dual"] - fd) < 1.0e-7


def test_slack_budget_dual_collapses():
    weights = np.array([1.2, 1.8, 2.4])
    curvatures = np.array([0.3, 0.4, 0.5])
    budget = 1.2 * float(np.sum(de_dual.unconstrained_x(weights, curvatures)))
    sol = de_dual.solve_global_budget(budget, weights, curvatures)
    assert not sol["active"]
    assert sol["dual"] == 0.0


def test_local_budget_control_has_nonconstant_duals():
    cfg = de_dual.DualConfig(n_patches=8)
    weights, curvatures = de_dual.make_patch_params(cfg)
    rows = de_dual.local_budget_control(cfg, weights, curvatures)
    duals = np.array([row["local_dual"] for row in rows])
    assert np.std(duals) > 1.0e-2


def test_linear_vacuum_shift_screens_state_and_absorbs_multiplier():
    cfg = de_dual.DualConfig(n_patches=8)
    weights, curvatures = de_dual.make_patch_params(cfg)
    total = float(np.sum(de_dual.unconstrained_x(weights, curvatures)))
    budget = total * cfg.active_budget_fraction
    base = de_dual.solve_global_budget(budget, weights, curvatures)
    shifted = de_dual.solve_global_budget(budget, weights, curvatures, linear_offset=0.2)
    assert np.max(np.abs(shifted["x"] - base["x"])) < 1.0e-10
    assert abs((shifted["dual"] - base["dual"]) - 0.2) < 1.0e-10


def test_negative_shift_can_make_previously_binding_budget_slack():
    weights, curvatures = np.array([1.0, 2.0]), np.array([0.3, 0.4])
    budget = 0.5 * float(np.sum(de_dual.unconstrained_x(weights, curvatures)))
    sol = de_dual.solve_global_budget(budget, weights, curvatures, linear_offset=-2.5)
    assert sol["dual"] == 0.0
    assert not sol["active"]
    assert np.all(sol["x"] == 0.0)
    assert sol["max_kkt_residual"] == 0.0


def test_zero_budget_has_feasible_kkt_witness():
    sol = de_dual.solve_global_budget(0.0, np.array([1.0, 2.0]), np.array([0.3, 0.4]))
    assert np.all(sol["x"] == 0.0)
    assert sol["active"]
    assert sol["max_kkt_residual"] == 0.0
