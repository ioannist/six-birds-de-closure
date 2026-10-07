"""Finite stable-readout certificates for E0/E3 rewrite witnesses."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import numpy as np


def stable_readout_certificate(operator: Any, metric: Mapping[str, Any]) -> Mapping[str, Any]:
    """Return sampled density and spectral no-growing-mode diagnostics.

    The c_eff2 entry is a supplied proxy, not a P-adeq certificate. No Schur
    realization or ghost-absence theorem is established by this function.
    ``stable`` means no eigenvalue with positive real part; eigenvalues on the
    imaginary axis alone do not guarantee bounded evolution for Jordan blocks.
    """
    if not isinstance(operator, Mapping):
        raise TypeError("operator must provide finite witness arrays.")
    rho_eff = np.asarray(operator.get("rho_eff"), dtype=float)
    jacobian = np.asarray(operator.get("jacobian"), dtype=float)
    if rho_eff.size == 0:
        raise ValueError("rho_eff witness is empty.")
    if jacobian.ndim < 2 or jacobian.shape[-1] != jacobian.shape[-2]:
        raise ValueError("jacobian witness must contain square matrices.")
    eigvals = np.linalg.eigvals(jacobian.reshape((-1, jacobian.shape[-1], jacobian.shape[-1])))
    max_real = float(np.max(np.real(eigvals)))
    c_eff2 = np.asarray(metric.get("c_eff2", np.zeros_like(rho_eff)), dtype=float)
    return {
        "min_rho_eff": float(np.min(rho_eff)),
        "max_real_eigenvalue": max_real,
        "min_c_eff2_proxy": float(np.min(c_eff2)),
        "rho_eff_positive": bool(np.min(rho_eff) > 0.0),
        "stable": bool(max_real <= 0.0),
        "finite": bool(np.all(np.isfinite(rho_eff)) and np.all(np.isfinite(jacobian))),
        "eigenvalues": eigvals,
    }


def diagonal_stable_jacobian(z_grid: Any, *, primary: float, secondary: float) -> np.ndarray:
    """Return a stack of diagonal stable Jacobians on a redshift grid."""
    z = np.asarray(z_grid, dtype=float)
    if primary < 0.0 or secondary < 0.0:
        raise ValueError("decay rates must be non-negative.")
    scale = 1.0 + 0.1 * z
    matrices = np.zeros((z.size, 2, 2), dtype=float)
    matrices[:, 0, 0] = -primary * scale
    matrices[:, 1, 1] = -secondary
    return matrices
