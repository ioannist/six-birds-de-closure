from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import numpy as np


MODULE_PATH = Path(__file__).resolve().parents[1] / "scripts" / "de_measure_probe.py"
WINDOW_PATH = Path(__file__).resolve().parents[1] / "scripts" / "de_window_carrier.py"

WINDOW_SPEC = importlib.util.spec_from_file_location("de_window_carrier", WINDOW_PATH)
assert WINDOW_SPEC is not None and WINDOW_SPEC.loader is not None
de_window = importlib.util.module_from_spec(WINDOW_SPEC)
sys.modules["de_window_carrier"] = de_window
WINDOW_SPEC.loader.exec_module(de_window)

SPEC = importlib.util.spec_from_file_location("de_measure_probe", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
de_measure = importlib.util.module_from_spec(SPEC)
sys.modules["de_measure_probe"] = de_measure
SPEC.loader.exec_module(de_measure)


def test_weighted_quantile_respects_weights():
    values = np.array([0.0, 1.0, 2.0])
    weights = np.array([1.0, 1.0, 8.0])
    assert de_measure.weighted_quantile(values, weights, 0.50) > 1.0


def synthetic_measure_inputs():
    lambdas = np.geomspace(1.0e-5, 1.0, 50)
    return [
        {
            "lambda": float(lam),
            "rs_lambda_pass": True,
            "rs_pass_fraction": 1.0,
            "median_log10_R": float(np.log10(lam)),
            "median_R": float(lam),
            "median_a_lambda_over_a_rec": float(lam ** (-1.0 / 3.0)),
            "mean_N_rec": 10.0,
            "mean_f_coll": 0.5,
            "n_rs_seed_rows_with_positive_R": 3,
            "n_seeds": 3,
            "seed_samples": [{"log10_R": float(np.log10(lam)), "epoch_ratio": float(lam ** (-1 / 3)), "N_rec": 10.0, "f_coll": 0.5}] * 3,
        }
        for lam in lambdas
    ]


def test_flat_linear_can_collapse_when_top_edge_has_most_mass():
    measure = {
        "measure_id": "flat_linear",
        "description": "",
        "axis": "lambda",
        "record_weight": "none",
        "include_negative": False,
    }
    verdict = de_measure.evaluate_measure(synthetic_measure_inputs(), measure)
    assert verdict["collapses"]


def test_flat_log_keeps_broad_degeneracy_non_collapsing():
    measure = {
        "measure_id": "flat_log",
        "description": "",
        "axis": "log_lambda",
        "record_weight": "none",
        "include_negative": False,
    }
    verdict = de_measure.evaluate_measure(synthetic_measure_inputs(), measure)
    assert not verdict["collapses"]
    assert verdict["log10R_width90_decades"] > 4.0


def test_quantile_ignores_zero_mass_and_does_not_interpolate_atoms():
    assert de_measure.weighted_quantile(np.array([-100.0, 0.0, 10.0]), np.array([0.0, 1.0, 9.0]), 0.5) == 10.0


def test_record_weighting_conditions_within_each_seed():
    rows = synthetic_measure_inputs()
    for row in rows:
        row["n_seeds"] = 2
        row["seed_samples"] = [
            {"log10_R": -2.0, "epoch_ratio": 10.0, "N_rec": 1.0, "f_coll": 0.01},
            {"log10_R": 0.0, "epoch_ratio": 1.0, "N_rec": 99.0, "f_coll": 0.99},
        ]
    measure = {"measure_id": "records", "description": "", "axis": "lambda", "record_weight": "N_rec", "include_negative": False}
    verdict = de_measure.evaluate_measure(rows, measure)
    assert verdict["log10R_median"] == 0.0
    assert verdict["epoch_ratio_median"] == 1.0
    assert np.isclose(verdict["p_R_within_one_decade_top"], 0.99)
    collapse = de_measure.evaluate_measure(rows, {**measure, "record_weight": "f_coll"})
    assert collapse["log10R_width90_decades"] == verdict["log10R_width90_decades"]
