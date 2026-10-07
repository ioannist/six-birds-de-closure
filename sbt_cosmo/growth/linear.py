"""Linear-growth stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def growth_factor(z: float, parameters: Mapping[str, Any]) -> float:
    """Return normalized linear growth D(z)."""
    raise NotImplementedError("Growth calculations are deferred to C0b.")


def growth_rate(z: float, parameters: Mapping[str, Any]) -> float:
    """Return logarithmic growth rate f(z)."""
    raise NotImplementedError("Growth calculations are deferred to C0b.")


def sigma8_z(z: float, parameters: Mapping[str, Any]) -> float:
    """Return sigma8(z)."""
    raise NotImplementedError("Growth calculations are deferred to C0b.")


def fsigma8(z: float, parameters: Mapping[str, Any]) -> float:
    """Return f*sigma8(z)."""
    raise NotImplementedError("Growth calculations are deferred to C0b.")
