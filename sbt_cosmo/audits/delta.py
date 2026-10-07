"""Idempotence-defect audits for deterministic packaging maps."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Any

import numpy as np

from sbt_cosmo.audits.metrics import l2_distance


def compute_delta(packaging: Any, state: Any) -> float:
    """Compute the packaging idempotence defect delta_p."""
    if isinstance(packaging, Mapping):
        mapper = packaging.get("map")
        metric = packaging.get("metric", l2_distance)
    else:
        mapper = packaging
        metric = l2_distance
    if not isinstance(mapper, Callable):
        raise TypeError("packaging must be callable or provide a callable 'map'.")
    once = mapper(state)
    twice = mapper(once)
    return float(metric(twice, once))


def relative_delta(packaging: Any, state: Any) -> float:
    """Return delta_p normalized by the packaged-state norm."""
    if isinstance(packaging, Mapping):
        mapper = packaging.get("map")
    else:
        mapper = packaging
    if not isinstance(mapper, Callable):
        raise TypeError("packaging must be callable or provide a callable 'map'.")
    once = np.asarray(mapper(state), dtype=float)
    denom = max(float(np.linalg.norm(once)), np.finfo(float).eps)
    return compute_delta(packaging, state) / denom
