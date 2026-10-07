"""Thin backend-selection stubs for CLASS and CAMB."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def build_boltzmann_backend(name: str, config: Mapping[str, Any]) -> Any:
    """Build the selected Boltzmann backend object for one run."""
    raise NotImplementedError("Boltzmann backends are deferred to C0b.")
