"""BAO likelihood wrapper stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_bao_probe(config: Mapping[str, Any]) -> Any:
    """Build a BAO probe adapter for D_M/r_d, D_H/r_d, or D_V/r_d data."""
    raise NotImplementedError("BAO probes are deferred to C0b.")
