"""Type-Ia supernova likelihood wrapper stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_sn_probe(config: Mapping[str, Any]) -> Any:
    """Build a supernova distance-modulus probe adapter."""
    raise NotImplementedError("SN probes are deferred to C0b.")
