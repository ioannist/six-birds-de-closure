"""Route-mismatch audits for non-commuting coarse-graining routes."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Any

import numpy as np

from sbt_cosmo.audits.metrics import l2_distance


def compute_route_mismatch(route: Any, state: Any) -> float:
    """Compute RM_p for a route and state."""
    if not isinstance(route, Mapping):
        raise TypeError("route must provide 'dynamics' and 'packaging' callables.")
    dynamics = route.get("dynamics")
    packaging = route.get("packaging")
    metric = route.get("metric", l2_distance)
    if not isinstance(dynamics, Callable) or not isinstance(packaging, Callable):
        raise TypeError("route dynamics and packaging must be callable.")
    direct = packaging(dynamics(state))
    packaged = packaging(state)
    transported = dynamics(packaged)
    return float(metric(direct, transported))


def logistic_completion_mismatch(
    state: Any,
    *,
    dt: float,
    alpha: float,
    beta: float,
    completion: Any,
) -> dict[str, Any]:
    """Compute the Toy-1 mismatch for a scalar logistic step and mean lens.

    The microscopic route evolves every component before adding a fixed
    completion vector. The macroscopic route evolves the lensed mean and then
    applies the same completion. For a linear update (``beta=0``) these commute;
    the quadratic term exposes the Jensen defect.
    """
    x = np.asarray(state, dtype=float)
    c = np.asarray(completion, dtype=float)

    def step(values: np.ndarray) -> np.ndarray:
        return values + dt * (alpha * values - beta * values**2)

    micro_lens = np.full_like(c, float(np.mean(step(x)))) + c
    macro_scalar = float(np.mean(x))
    macro_lens = np.full_like(c, float(step(np.array([macro_scalar]))[0])) + c
    residual = micro_lens - macro_lens
    return {
        "rm": l2_distance(residual),
        "residual": residual,
        "micro_lens": micro_lens,
        "macro_lens": macro_lens,
        "variance": float(np.var(x)),
    }
