"""Closed Hubble route vocabulary."""

from __future__ import annotations

HUBBLE_ROUTE_IDS = (
    "r1_cmb_to_bao",
    "r2_bao_to_sn",
    "r3_cepheid_to_sn",
    "r4_trgb_to_sn",
    "r5_jagb_to_sn",
    "r6_time_delay",
    "r7_standard_siren",
)


def validate_hubble_route_id(route_id: str) -> str:
    """Validate a Hubble route ID against the closed vocabulary."""
    if route_id not in HUBBLE_ROUTE_IDS:
        raise ValueError(f"Unknown route_id {route_id!r}; expected one of {HUBBLE_ROUTE_IDS}.")
    return route_id
