"""Identifiability and correlated Gaussian predictive checks for R0."""
import importlib.util
import sys
from pathlib import Path

import numpy as np
import pytest
from scipy.stats import multivariate_normal

path = Path(__file__).resolve().parents[1] / "scripts/r0_hubble_power_exactness.py"
spec = importlib.util.spec_from_file_location("review_r0", path)
r0 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = r0
spec.loader.exec_module(r0)


def test_saturated_leave_one_out_is_not_identified():
    with pytest.raises(r0.UnidentifiedPrediction, match="not estimable"):
        r0.loo_pointwise_conditional(np.array([1.0, 2.0, 3.0]), np.eye(3), np.eye(3))


def test_correlated_intercept_leave_one_out_matches_exact_formula():
    y = np.array([1.0, 2.0, 3.0])
    C = 0.7 * np.eye(3) + 0.3 * np.ones((3, 3))
    scores = r0.loo_pointwise_conditional(y, C, np.ones((3, 1)))
    expected = [r0.logpdf_normal(y[i], np.mean(np.delete(y, i)), 1.5 * 0.7) for i in range(3)]
    np.testing.assert_allclose(scores, expected, rtol=1e-12)


def test_family_holdout_uses_joint_conditional_covariance():
    routes = [r0.RouteData(str(i), float(i + 1), 1.0, "b", "f", {}) for i in range(3)]
    C = 0.7 * np.eye(3) + 0.3 * np.ones((3, 3))
    score = r0.heldout_logpredict(routes[:1], routes[1:], C[:1, :1], C,
                                {str(i): i for i in range(3)}, "M_0")
    expected = multivariate_normal.logpdf([2.0, 3.0], mean=[1.0, 1.0], cov=[[1.4, 0.7], [0.7, 1.4]])
    assert np.isclose(score, expected, rtol=1e-12)
