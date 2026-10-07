"""Counterexamples and boundary cases found in the mathematical review."""
from __future__ import annotations

import math

import numpy as np
import pytest

from sbt_cosmo.audits.metrics import chi2_distance, kl_distance


def test_diagonal_covariance_agrees_with_full_covariance():
    residual = np.array([2.0, 3.0])
    variances = np.array([4.0, 9.0])
    assert chi2_distance(residual, np.zeros(2), variances) == 2.0
    assert chi2_distance(residual, np.zeros(2), np.diag(variances)) == 2.0
    assert chi2_distance(residual, np.zeros(2), 4.0) == 13.0 / 4.0


def test_kl_support_mismatch_is_infinite():
    assert math.isinf(kl_distance([1.0, 0.0], [0.0, 1.0]))
    assert kl_distance([0.0, 1.0], [0.0, 3.0]) == 0.0


def test_kl_rejects_zero_total_mass():
    with pytest.raises(ValueError):
        kl_distance([0.0, 0.0], [1.0, 1.0])


def test_kl_nonnegative_on_distinct_positive_distributions():
    assert kl_distance([1.0, 2.0, 3.0], [3.0, 2.0, 1.0]) > 0.0


def test_full_covariance_rejects_indefinite_matrix():
    with pytest.raises(np.linalg.LinAlgError):
        chi2_distance([1.0, 0.0], [0.0, 0.0], [[1.0, 2.0], [2.0, 1.0]])


def test_kl_tiny_positive_reference_mass_remains_finite():
    assert np.isclose(kl_distance([1.0, 0.0], [1e-300, 1e300]), 600 * math.log(10))
