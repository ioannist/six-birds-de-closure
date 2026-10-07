"""Readouts for late-time growth amplitudes."""

from __future__ import annotations

import math


def s8_readout(sigma8: float, omega_m: float) -> float:
    """Return S8 = sigma8 * sqrt(omega_m / 0.3)."""
    if sigma8 <= 0.0:
        raise ValueError("sigma8 must be positive")
    if omega_m <= 0.0:
        raise ValueError("omega_m must be positive")
    return float(sigma8) * math.sqrt(float(omega_m) / 0.3)
