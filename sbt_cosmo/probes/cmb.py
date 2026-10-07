"""CMB likelihood wrapper stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_cmb_probe(config: Mapping[str, Any]) -> Any:
    """Build a Planck, SPT, or ACT CMB probe adapter."""
    raise NotImplementedError("CMB probes are deferred to C0b.")
