"""Minimal FLRW background expansion helpers.

The production Boltzmann-backed backgrounds are deferred to C0b. These helpers
cover analytic LCDM/matter-only curves needed by E0's synthetic checks.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import numpy as np


def e_z(z: Any, parameters: Mapping[str, Any]) -> Any:
    """Return E(z)=H(z)/H0 for a configured LCDM, wCDM, or w0wa background."""
    z_arr = np.asarray(z, dtype=float)
    model = str(parameters.get("model", "lcdm")).lower()
    omega_m = float(parameters.get("omega_m", 1.0))
    omega_k = float(parameters.get("omega_k", 0.0))
    omega_de = float(parameters.get("omega_de", 1.0 - omega_m - omega_k))

    if model in {"matter", "einstein_de_sitter", "eds"}:
        values = np.sqrt((1.0 + z_arr) ** 3)
    elif model == "lcdm":
        values = np.sqrt(omega_m * (1.0 + z_arr) ** 3 + omega_k * (1.0 + z_arr) ** 2 + omega_de)
    else:
        raise NotImplementedError(f"Background model {model!r} is deferred to C0b.")
    if np.ndim(z) == 0:
        return float(values)
    return values


def hubble_rate(z: Any, parameters: Mapping[str, Any]) -> Any:
    """Return H(z) in km s^-1 Mpc^-1 for a configured background."""
    h0 = float(parameters.get("h0", parameters.get("H0", 70.0)))
    values = h0 * e_z(z, parameters)
    if np.ndim(z) == 0:
        return float(values)
    return values


def matter_inverse_hubble(z: Any, h_scale: float = 1.0) -> Any:
    """Return the dimensionless inverse-Hubble curve for a matter-only toy."""
    z_arr = np.asarray(z, dtype=float)
    values = 1.0 / (h_scale * (1.0 + z_arr) ** 1.5)
    if np.ndim(z) == 0:
        return float(values)
    return values


def heterogeneous_inverse_hubble_lens(
    z: Any,
    modes: Any,
    *,
    amplitude: float,
    response: float,
    exponent: float,
    z_max: float,
    h_scale: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return a deterministic heterogeneous inverse-Hubble lens.

    The function averages local matter-only inverse expansion rates over fixed
    route modes. It is a synthetic E0 generator, not a real-data cosmology.
    """
    z_arr = np.asarray(z, dtype=float)
    u = np.asarray(modes, dtype=float)
    if z_max <= 0:
        raise ValueError("z_max must be positive.")
    shape = np.power(np.clip(z_arr / z_max, 0.0, None), exponent)
    factors = 1.0 + response * amplitude * shape[:, None] * u[None, :]
    if np.any(factors <= 0.0):
        raise ValueError("heterogeneous local expansion factors must stay positive.")
    local_inv = matter_inverse_hubble(z_arr, h_scale=h_scale)[:, None] / factors
    effective_inv = np.mean(local_inv, axis=1)
    closure_proxy = effective_inv / matter_inverse_hubble(z_arr, h_scale=h_scale) - 1.0
    return effective_inv, closure_proxy, factors
