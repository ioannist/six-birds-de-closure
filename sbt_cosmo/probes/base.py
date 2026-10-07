"""Base probe contracts and closed probe vocabulary."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any, Protocol

PROBE_IDS = ("cmb", "bao", "sn", "wl", "rsd", "ladder")


class Probe(Protocol):
    """Protocol shared by all probe likelihood adapters."""

    probe_id: str

    def data_vector(self) -> Any:
        """Return the observed data vector."""
        raise NotImplementedError("Probe data access is deferred to C0b.")

    def covariance(self) -> Any:
        """Return the probe covariance matrix."""
        raise NotImplementedError("Probe covariance access is deferred to C0b.")

    def model(self, theta: Mapping[str, Any]) -> Any:
        """Return the model prediction at parameters theta."""
        raise NotImplementedError("Probe forward models are deferred to C0b.")

    def loglike(self, theta: Mapping[str, Any]) -> float:
        """Return the log-likelihood at parameters theta."""
        raise NotImplementedError("Probe likelihoods are deferred to C0b.")


def validate_probe_id(probe_id: str) -> str:
    """Validate a probe ID against the closed vocabulary."""
    if probe_id not in PROBE_IDS:
        raise ValueError(f"Unknown probe_id {probe_id!r}; expected one of {PROBE_IDS}.")
    return probe_id
