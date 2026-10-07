"""RSD likelihood wrapper stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_rsd_probe(config: Mapping[str, Any]) -> Any:
    """Build an RSD f*sigma8 probe adapter."""
    raise NotImplementedError("RSD probes are deferred to C0b.")
