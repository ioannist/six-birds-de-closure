"""Deterministic Hubble route transport helpers."""

from __future__ import annotations

from typing import Any


def transport_posterior(posterior: Any, bridge: Any) -> Any:
    """Transport a Hubble posterior through a declared bridge."""
    offset = float(bridge.get("offset", 0.0)) if isinstance(bridge, dict) else float(bridge)
    if isinstance(posterior, dict):
        transported = dict(posterior)
        transported["mean"] = float(posterior["mean"]) + offset
        return transported
    return float(posterior) + offset


def synthetic_bridge_offset(route_loading: float, calibration_loading: float, *, a0: float, a2: float, stage_weight: float) -> float:
    """Return a synthetic bridge offset for the E0 route-loop witness."""
    return float(a0 * route_loading + a2 * calibration_loading * stage_weight)
