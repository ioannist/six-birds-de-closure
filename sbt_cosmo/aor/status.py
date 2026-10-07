"""Canonical AOR status vocabulary."""

from __future__ import annotations

AOR_STATUSES = (
    "zero",
    "budgeted",
    "bridged",
    "hidden",
    "moduli",
    "selected",
    "probabilistic",
    "out_of_scope",
    "nonclaim",
    "blocked",
    "approved_other",
    "asymptotic_budgeted",
    "summable",
    "contractive",
    "eventual_zero",
)


def validate_aor_status(status: str) -> str:
    """Validate an AOR status against the closed registry enum."""
    if status not in AOR_STATUSES:
        raise ValueError(f"Unknown AOR status {status!r}.")
    return status
