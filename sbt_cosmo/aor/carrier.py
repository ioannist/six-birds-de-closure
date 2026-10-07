"""AOR carrier progression stubs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_aor_record(config: Mapping[str, Any]) -> Any:
    """Build an AOR progression record for a run."""
    raise NotImplementedError("AOR carrier records are deferred to experiment packets.")
