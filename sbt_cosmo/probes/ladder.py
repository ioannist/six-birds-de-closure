"""Local-H0 route likelihood wrapper stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_ladder_probe(config: Mapping[str, Any]) -> Any:
    """Build a Cepheid, TRGB, JAGB, time-delay, or siren route adapter."""
    raise NotImplementedError("Local-ladder probes are deferred to C0b.")
