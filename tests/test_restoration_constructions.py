"""Analytic controls for additional restoration constructions."""
from __future__ import annotations

from pathlib import Path
from fractions import Fraction

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
import sys
sys.path.insert(0, str(ROOT / "scripts"))
import de_restoration_constructions as construction
import de_projected_sourcing as projected


def test_equality_solution_agrees_with_symmetric_closed_form():
    solution = construction.equality_allocation(6.0, np.zeros(2), np.ones(2), np.ones(2))
    np.testing.assert_allclose(solution["x"], [3, 3], atol=1e-12)
    assert solution["price"] == pytest.approx(-2.75)


def test_nonlinear_ledger_inverse_including_zero_coupling():
    x = np.array([0, 0.2, 1, 10])
    for kappa in [0.0, 0.3, 30.0]:
        rho = construction.density_from_ledger(x, kappa)
        np.testing.assert_allclose(construction.ledger_term(rho, kappa), x, atol=1e-13)


def test_projected_history_retains_ledger_and_matches_independent_price_solution():
    w, c, b = np.array([1.0, 1.5, 0.8]), np.array([0.3, 0.5, 0.4]), np.array([-2.0, 0.2, 0.1])
    states, prices = construction.allocation_history(1.0, b, w, c)
    shifted, shifted_prices = construction.allocation_history(1.0, b - 8, w, c)
    solution = construction.equality_allocation(1.0, b, w, c)
    np.testing.assert_allclose(states.sum(axis=1), 1.0, atol=1e-13)
    assert np.all(states >= 0)
    np.testing.assert_allclose(states[-1], solution["x"], atol=1e-11)
    np.testing.assert_allclose(states, shifted, atol=1e-12)
    np.testing.assert_allclose(shifted_prices - prices, -8, atol=1e-12)
    assert states[-1, 0] == 0  # lower-bound KKT case


def test_fixed_price_ablation_does_not_screen_the_feedback_shift():
    rho = np.array([0.2, 0.8])
    b, gradient = np.array([0.1, -0.1]), np.array([0.01, 0.03])
    original = construction.screened_potential(b, 0.4, 0.3, rho, gradient)
    fixed_price = construction.screened_potential(b + 1, 0.4, 0.3, rho, gradient)
    rebased_price = construction.screened_potential(b + 1, 1.4, 0.3, rho, gradient)
    np.testing.assert_allclose(fixed_price - original, 1 + 0.3 * rho)
    np.testing.assert_allclose(rebased_price, original, atol=1e-14)


def test_exact_mixture_bound_is_sharp_and_detects_a_false_control():
    def row(lam, seed, ratio):
        return {"lambda": str(lam), "seed": str(seed), "RS": "True",
                "lambda_to_matter_at_first_record": str(ratio)}
    rows = [row(1, 0, 1), row(1, 1, 2), row(2, 0, 20), row(2, 1, 30)]
    result = construction.exact_prior_obstruction(rows)
    assert result["sharp_upper_bound"] == "1"
    assert not result["probability_gate_impossible"]
    # Removing one high seed changes the sharp conditional bound, whereas
    # any reweighting of whole lambda nodes must mix the remaining fractions.
    rows[-1]["lambda_to_matter_at_first_record"] = "0.1"
    assert Fraction(construction.exact_prior_obstruction(rows)["sharp_upper_bound"]) == Fraction(1, 2)


def test_prior_obstruction_rejects_duplicate_samples():
    r = {"lambda": "1", "seed": "1", "RS": "True", "lambda_to_matter_at_first_record": "1"}
    with pytest.raises(ValueError, match="duplicate"):
        construction.exact_prior_obstruction([r, r])


def test_original_sourcing_force_projection_removes_the_exact_shift_direction():
    field = projected.initial_field()
    b = 0.15 * np.sin(0.9 * np.arange(8))
    force, prices = projected.projected_force(field, b, 0.3)
    other, shifted_prices = projected.projected_force(field, b + 10, 0.3)
    np.testing.assert_allclose(force, other, atol=1e-13)
    assert shifted_prices["ledger_price"] - prices["ledger_price"] == pytest.approx(10, abs=1e-12)
    assert shifted_prices["norm_price"] == pytest.approx(prices["norm_price"], abs=1e-12)
    assert prices["normal_residual"] < 1e-13


def test_projected_sourcing_preserves_both_constraints_over_time():
    history = projected.evolve(0.15 * np.sin(0.9 * np.arange(8)), tmax=2)
    np.testing.assert_allclose(history["norm2"], 1, atol=1e-10)
    np.testing.assert_allclose(history["ipr"], 17/108, atol=1e-10)
    assert history["min_gram_eigenvalue"] > 0


def test_norm_only_projection_does_not_remove_the_background_feedback():
    field = projected.initial_field()
    rho = np.abs(field)**2
    kappa = 0.3
    remaining = kappa * (rho - np.sum(rho**2)) * field
    assert np.linalg.norm(remaining) == pytest.approx(kappa * np.sqrt(35/11664), abs=1e-14)
    assert np.linalg.norm(remaining) > 0.01


def test_gauge_blindness_does_not_erase_coupling_or_inhomogeneous_forces():
    field = projected.initial_field()
    b = 0.15 * np.sin(0.9 * np.arange(8))
    original, _ = projected.projected_force(field, b, 0.3)
    coupled, _ = projected.projected_force(field, b, 0.4)
    inhomogeneous, _ = projected.projected_force(field, b + np.eye(8)[0], 0.3)
    assert np.linalg.norm(coupled - original) > 0.002
    assert np.linalg.norm(inhomogeneous - original) > 0.15
