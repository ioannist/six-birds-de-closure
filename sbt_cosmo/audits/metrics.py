"""Small deterministic audit metrics used by synthetic and real-data checks."""

from __future__ import annotations

import math
from typing import Any

import numpy as np


def chi2_distance(observed: Any, predicted: Any, covariance: Any) -> float:
    """Compute a chi-square distance under a covariance."""
    residual = np.asarray(observed, dtype=float) - np.asarray(predicted, dtype=float)
    if not np.all(np.isfinite(residual)):
        raise ValueError("residual must be finite.")
    cov = np.asarray(covariance, dtype=float)
    if cov.ndim == 0:
        if not np.isfinite(cov) or cov <= 0:
            raise ValueError("covariance variance must be finite and positive.")
        return float(np.sum(residual**2 / float(cov)))
    if cov.ndim == 1:
        if residual.shape != cov.shape:
            raise ValueError("diagonal covariance must match the residual vector.")
        if not np.all(np.isfinite(cov)) or np.any(cov <= 0):
            raise ValueError("diagonal covariance variances must be finite and positive.")
        return float(np.sum(residual**2 / cov))
    if residual.ndim != 1 or cov.shape != (residual.size, residual.size):
        raise ValueError("full covariance must be square and match the residual vector.")
    if not np.all(np.isfinite(cov)) or not np.allclose(cov, cov.T, rtol=1e-12, atol=1e-12):
        raise ValueError("covariance must be finite and symmetric.")
    # Symmetrize only within the declared floating-point symmetry tolerance.
    factor = np.linalg.cholesky(0.5 * (cov + cov.T))
    whitened = np.linalg.solve(factor, residual)
    return float(whitened @ whitened)


def l2_distance(left: Any, right: Any = None) -> float:
    """Return a Euclidean norm, optionally for a difference of two arrays."""
    values = np.asarray(left, dtype=float)
    if right is not None:
        values = values - np.asarray(right, dtype=float)
    return float(np.linalg.norm(values))


def rmse(observed: Any, predicted: Any) -> float:
    """Return the root mean square residual."""
    residual = np.asarray(observed, dtype=float) - np.asarray(predicted, dtype=float)
    return float(np.sqrt(np.mean(residual**2)))


def bic(chi2: float, n_observations: int, n_parameters: int) -> float:
    """Return the Gaussian BIC for a chi-square fit."""
    if n_observations <= 0:
        raise ValueError("n_observations must be positive.")
    return float(chi2 + n_parameters * math.log(n_observations))


def nonvac_metrics(staging_direction: Any, covariance: Any, covariance_marginalized: Any) -> dict[str, float | bool]:
    """Return G-E5-NONVAC norms for a staging direction."""
    t = np.asarray(staging_direction, dtype=float)
    cov = np.asarray(covariance, dtype=float)
    cov_marg = np.asarray(covariance_marginalized, dtype=float)
    pre2 = float(t @ np.linalg.solve(cov, t))
    post2 = float(t @ np.linalg.solve(cov_marg, t))
    pre = float(math.sqrt(max(pre2, 0.0)))
    post = float(math.sqrt(max(post2, 0.0)))
    retained = float(post / pre) if pre > 0.0 else 0.0
    return {
        "norm_pre": pre,
        "norm_post": post,
        "retained": retained,
        "NONVAC_pass": bool(post >= 2.0 and retained >= 0.25),
    }


def aic(chi2: float, n_parameters: int) -> float:
    """Return the Gaussian AIC for a chi-square fit."""
    return float(chi2 + 2 * n_parameters)


def kl_distance(left: Any, right: Any) -> float:
    """Compute D_KL(p || q) for finite nonnegative masses, including infinity."""
    p = np.asarray(left, dtype=float)
    q = np.asarray(right, dtype=float)
    if p.shape != q.shape or p.size == 0:
        raise ValueError("KL inputs must have the same nonempty shape.")
    if not np.all(np.isfinite(p)) or not np.all(np.isfinite(q)) or np.any(p < 0) or np.any(q < 0):
        raise ValueError("KL inputs must be finite and non-negative.")
    if np.max(p) <= 0 or np.max(q) <= 0:
        raise ValueError("KL inputs must have positive total mass.")
    if np.any((p > 0) & (q == 0)):
        return math.inf
    mask = p > 0
    # Normalize in scaled masses, but evaluate log probabilities directly
    # from the original masses so a tiny positive q cannot underflow to zero.
    p_scale, q_scale = float(np.max(p)), float(np.max(q))
    p_total, q_total = float(np.sum(p / p_scale)), float(np.sum(q / q_scale))
    p_normalized = (p[mask] / p_scale) / p_total
    log_p = np.log(p[mask]) - math.log(p_scale) - math.log(p_total)
    log_q = np.log(q[mask]) - math.log(q_scale) - math.log(q_total)
    return float(np.sum(p_normalized * (log_p - log_q)))
