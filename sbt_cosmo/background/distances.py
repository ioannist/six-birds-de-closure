"""Distance helpers for analytic backgrounds and E0 synthetic generators."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import numpy as np
from scipy.integrate import cumulative_trapezoid

from sbt_cosmo.background.flrw import e_z, matter_inverse_hubble


def cumulative_comoving_distance(z: Any, inverse_hubble: Any) -> np.ndarray:
    """Integrate an inverse-Hubble curve over a sorted redshift grid."""
    z_arr = np.asarray(z, dtype=float)
    inv = np.asarray(inverse_hubble, dtype=float)
    if z_arr.ndim != 1 or inv.shape != z_arr.shape:
        raise ValueError("z and inverse_hubble must be one-dimensional arrays with equal shape.")
    if np.any(np.diff(z_arr) < 0):
        raise ValueError("z grid must be sorted ascending.")
    return cumulative_trapezoid(inv, z_arr, initial=0.0)


def luminosity_distance_from_inverse_hubble(z: Any, inverse_hubble: Any) -> np.ndarray:
    """Return dimensionless D_L(z)=(1+z) integral dz/H(z)."""
    z_arr = np.asarray(z, dtype=float)
    return (1.0 + z_arr) * cumulative_comoving_distance(z_arr, inverse_hubble)


def lcdm_luminosity_distance(z: Any, h_scale: float, omega_m: float) -> np.ndarray:
    """Return flat-LCDM dimensionless luminosity distance for E0 fits."""
    z_arr = np.asarray(z, dtype=float)
    if not 0.0 <= omega_m <= 1.0:
        raise ValueError("omega_m must lie in [0, 1] for the flat-LCDM toy.")
    inv = 1.0 / (h_scale * np.sqrt(omega_m * (1.0 + z_arr) ** 3 + (1.0 - omega_m)))
    return luminosity_distance_from_inverse_hubble(z_arr, inv)


def matter_luminosity_distance(z: Any, h_scale: float = 1.0) -> np.ndarray:
    """Return matter-only dimensionless luminosity distance for E0 controls."""
    z_arr = np.asarray(z, dtype=float)
    return luminosity_distance_from_inverse_hubble(z_arr, matter_inverse_hubble(z_arr, h_scale=h_scale))


def comoving_distance(z: float, parameters: Mapping[str, Any]) -> float:
    """Return line-of-sight comoving distance D_C(z)."""
    grid = np.linspace(0.0, float(z), int(parameters.get("n_grid", 512)))
    inv = 1.0 / e_z(grid, parameters)
    return float(cumulative_comoving_distance(grid, inv)[-1])


def transverse_comoving_distance(z: float, parameters: Mapping[str, Any]) -> float:
    """Return transverse comoving distance D_M(z)."""
    omega_k = float(parameters.get("omega_k", 0.0))
    dc = comoving_distance(z, parameters)
    if abs(omega_k) > 1.0e-12:
        raise NotImplementedError("Curved transverse distances are deferred to C0b.")
    return dc


def angular_diameter_distance(z: float, parameters: Mapping[str, Any]) -> float:
    """Return angular-diameter distance D_A(z)."""
    return transverse_comoving_distance(z, parameters) / (1.0 + float(z))


def luminosity_distance(z: float, parameters: Mapping[str, Any]) -> float:
    """Return luminosity distance D_L(z)."""
    return (1.0 + float(z)) * transverse_comoving_distance(z, parameters)


def hubble_distance(z: float, parameters: Mapping[str, Any]) -> float:
    """Return Hubble distance D_H(z)=c/H(z)."""
    return 1.0 / e_z(float(z), parameters)


def sound_horizon(parameters: Mapping[str, Any]) -> float:
    """Return sound horizon r_d for the configured backend."""
    raise NotImplementedError("Sound-horizon calculation is deferred to C0b.")
