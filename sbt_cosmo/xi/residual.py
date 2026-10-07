"""Canonical Xi_cosmo residual definition.

This module is the only package location allowed to define the real-data
cosmological closure residual object.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

import numpy as np


@dataclass(frozen=True)
class XiCosmo:
    """Canonical low-rank Xi_cosmo residual configuration."""

    rank: int = 3
    parameter_names: tuple[str, ...] = ("a0", "a1", "a2")

    def evaluate(self, z: Any, ell: str | None, probe: str, parameters: Mapping[str, Any]) -> np.ndarray:
        """Evaluate Xi_cosmo(z, ell, probe) for configured parameters."""
        if self.rank != 3 or self.parameter_names != ("a0", "a1", "a2"):
            raise ValueError("E1-B implements the locked rank-3 Xi_cosmo ansatz only.")
        return evaluate_xi_cosmo(z, ell, probe, parameters)


def evaluate_xi_cosmo(z: Any, ell: str | None, probe: str, parameters: Mapping[str, Any]) -> np.ndarray:
    """Evaluate the canonical Xi_cosmo residual without constructing a model object."""
    del ell  # Geometry-only E1-B has inactive ell-dependence.
    z_array = np.asarray(z, dtype=float)
    a0 = float(parameters["a0"])
    a1 = float(parameters["a1"])
    a2 = float(parameters["a2"])
    return a0 * phi0(z_array) + a1 * phi1(z_array) * staging_weight(probe) + a2 * phi2(z_array) * calibration_weight(probe)


def xi_basis(z: Any) -> np.ndarray:
    """Return the locked E1-B basis columns [phi0, phi1, phi2]."""
    z_array = np.asarray(z, dtype=float)
    return np.column_stack((phi0(z_array), phi1(z_array), phi2(z_array)))


def phi0(z: Any) -> np.ndarray:
    """Constant-like repair basis phi0(z)=1."""
    return np.ones_like(np.asarray(z, dtype=float), dtype=float)


def phi1(z: Any) -> np.ndarray:
    """Staging basis phi1(z)=z/(1+z)."""
    z_array = np.asarray(z, dtype=float)
    return z_array / (1.0 + z_array)


def phi2(z: Any) -> np.ndarray:
    """Calibration/gluing basis phi2(z)=ln(1+z)."""
    return np.log1p(np.asarray(z, dtype=float))


def staging_weight(probe: str) -> float:
    """Return the fixed per-probe staging weight used in E1-B geometry."""
    normalized = _normalize_probe(probe)
    if normalized in {"sn", "bao"}:
        return 1.0
    if normalized == "cmb":
        return 0.0
    raise ValueError(f"unknown Xi_cosmo probe: {probe}")


def calibration_weight(probe: str) -> float:
    """Return the locked probe calibration weight c_p."""
    normalized = _normalize_probe(probe)
    if normalized == "sn":
        return 1.0
    if normalized == "bao":
        return -1.0
    if normalized == "cmb":
        return 0.0
    raise ValueError(f"unknown Xi_cosmo probe: {probe}")


def _normalize_probe(probe: str) -> str:
    key = probe.strip().lower()
    aliases = {
        "pantheon": "sn",
        "pantheon_plus": "sn",
        "supernova": "sn",
        "sne": "sn",
        "desi": "bao",
        "desi_dr2_bao": "bao",
        "planck": "cmb",
        "planck_2018_compressed": "cmb",
    }
    return aliases.get(key, key)


@dataclass(frozen=True)
class XiToy:
    """Synthetic E0 closure residual basis.

    XiToy is deliberately separate from the real-data ``XiCosmo`` object. E0
    uses it to make finite, reproducible witnesses for route mismatch, distance
    rewriting, and Hubble route matrices without claiming a real cosmological
    residual has been evaluated.
    """

    amplitude: float
    route_modes: tuple[float, ...]
    response: float = 1.0
    exponent: float = 0.5
    z_max: float = 1.5

    def normalized_modes(self) -> np.ndarray:
        """Return centered modes scaled to maximum absolute value one."""
        modes = np.asarray(self.route_modes, dtype=float)
        modes = modes - float(np.mean(modes))
        scale = float(np.max(np.abs(modes)))
        if scale == 0.0:
            return modes
        return modes / scale

    def basis(self, z: Any) -> np.ndarray:
        """Return the positive-redshift scalar basis used by the synthetic lens."""
        z_arr = np.asarray(z, dtype=float)
        return np.power(np.clip(z_arr / self.z_max, 0.0, None), self.exponent)

    def local_expansion_factors(self, z: Any) -> np.ndarray:
        """Return route-local multiplicative expansion factors."""
        modes = self.normalized_modes()
        return 1.0 + self.response * self.amplitude * self.basis(z)[:, None] * modes[None, :]

    def closure_proxy(self, z: Any) -> np.ndarray:
        """Return the synthetic inverse-Hubble closure proxy."""
        factors = self.local_expansion_factors(z)
        if np.any(factors <= 0.0):
            raise ValueError("XiToy local expansion factors must be positive.")
        return np.mean(1.0 / factors, axis=1) - 1.0

    def variance_proxy(self, z: Any) -> np.ndarray:
        """Return the route-factor variance proxy used as a Q-style diagnostic."""
        return np.var(self.local_expansion_factors(z), axis=1)
