"""Synthetic Hubble route-loop holonomy checks."""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

import numpy as np


def compute_hubble_holonomy(loop: Sequence[Any]) -> float:
    """Compute a route-loop holonomy discrepancy."""
    values = np.asarray(loop, dtype=float)
    if values.ndim != 1:
        raise ValueError("loop must be one-dimensional.")
    return float(abs(np.sum(values)))


def route_loop_holonomy(
    route_loading: Any,
    calibration_loading: Any,
    *,
    a0: float,
    a2: float,
    route_indices: Sequence[int],
    bridge_weights: Sequence[float],
    signs: Sequence[float],
) -> float:
    """Return the E0 synthetic holonomy around a declared route loop."""
    route = np.asarray(route_loading, dtype=float)
    calibration = np.asarray(calibration_loading, dtype=float)
    idx = np.asarray(route_indices, dtype=int)
    weights = np.asarray(bridge_weights, dtype=float)
    sign_arr = np.asarray(signs, dtype=float)
    if not (idx.size == weights.size == sign_arr.size):
        raise ValueError("route_indices, bridge_weights, and signs must have equal length.")
    bridge_offsets = a0 * route[idx] + a2 * calibration[idx] * weights
    return compute_hubble_holonomy(sign_arr * bridge_offsets)
