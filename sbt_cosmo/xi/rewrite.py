"""Least-audit-closed synthetic rewrite helpers."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import numpy as np

from sbt_cosmo.background.distances import luminosity_distance_from_inverse_hubble
from sbt_cosmo.background.flrw import heterogeneous_inverse_hubble_lens, matter_inverse_hubble


def apply_rewrite(xi_model: Any, state: Mapping[str, Any]) -> Any:
    """Apply the canonical rewrite map associated with Xi_cosmo."""
    if not hasattr(xi_model, "closure_proxy"):
        raise NotImplementedError("Real Xi_cosmo rewrites are deferred to C0b+.")
    z = np.asarray(state["z"], dtype=float)
    h_scale = float(state.get("h_scale", 1.0))
    inv = matter_inverse_hubble(z, h_scale=h_scale) * (1.0 + xi_model.closure_proxy(z))
    return {
        "z": z,
        "inverse_hubble": inv,
        "luminosity_distance": luminosity_distance_from_inverse_hubble(z, inv),
    }


def rewrite_inverse_hubble_lens(
    z_grid: Any,
    route_modes: Any,
    *,
    amplitude: float,
    response: float,
    exponent: float,
    z_max: float,
    h_scale: float = 1.0,
) -> dict[str, np.ndarray]:
    """Apply the E0 synthetic closure rewrite to a matter-only inverse-H curve."""
    inv, closure_proxy, factors = heterogeneous_inverse_hubble_lens(
        z_grid,
        route_modes,
        amplitude=amplitude,
        response=response,
        exponent=exponent,
        z_max=z_max,
        h_scale=h_scale,
    )
    return {
        "inverse_hubble": inv,
        "luminosity_distance": luminosity_distance_from_inverse_hubble(z_grid, inv),
        "closure_proxy": closure_proxy,
        "local_factors": factors,
        "variance_proxy": np.var(factors, axis=1),
    }


def p4_rho_eff(z_grid: Any, *, rho_min: float, curvature: float, crossing_z: float) -> np.ndarray:
    """Return a positive finite witness density with one w_eff crossing."""
    z = np.asarray(z_grid, dtype=float)
    if rho_min <= 0.0 or curvature <= 0.0:
        raise ValueError("rho_min and curvature must be positive.")
    return rho_min + curvature * (z - crossing_z) ** 2


def effective_w_readout(z_grid: Any, rho_eff: Any) -> Any:
    """Compute an effective w(z) readout from rho_eff(z)."""
    z = np.asarray(z_grid, dtype=float)
    rho = np.asarray(rho_eff, dtype=float)
    if z.ndim != 1 or rho.shape != z.shape:
        raise ValueError("z_grid and rho_eff must be one-dimensional arrays with equal shape.")
    if np.any(rho <= 0.0):
        raise ValueError("rho_eff must be strictly positive.")
    dlogrho_dz = np.gradient(np.log(rho), z, edge_order=2)
    return -1.0 + (1.0 + z) * dlogrho_dz / 3.0


def crossing_locations(z_grid: Any, values: Any, *, level: float = -1.0) -> np.ndarray:
    """Return linearly interpolated crossing locations of ``values == level``."""
    z = np.asarray(z_grid, dtype=float)
    y = np.asarray(values, dtype=float) - level
    locations: list[float] = []
    for left, right, z_left, z_right in zip(y[:-1], y[1:], z[:-1], z[1:]):
        if left == 0.0:
            locations.append(float(z_left))
        elif left * right < 0.0:
            frac = abs(left) / (abs(left) + abs(right))
            locations.append(float(z_left + frac * (z_right - z_left)))
    if y[-1] == 0.0:
        locations.append(float(z[-1]))
    return np.asarray(locations, dtype=float)
