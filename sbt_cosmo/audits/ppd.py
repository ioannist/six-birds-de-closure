"""Posterior-predictive audit stubs."""

from __future__ import annotations

from typing import Any


def compute_ppd(source_probe: Any, target_probe: Any, posterior: Any) -> float:
    """Compute a cross-probe posterior-predictive discrepancy."""
    raise NotImplementedError("PPD audits are deferred to C0b+.")
