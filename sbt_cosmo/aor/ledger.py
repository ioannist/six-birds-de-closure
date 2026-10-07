"""AOR ledger writer."""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from typing import Any

from sbt_cosmo.aor.status import validate_aor_status
from sbt_cosmo.io.artifacts import write_json_artifact


def write_aor_ledger(entries: Mapping[str, Any], path: Path) -> None:
    """Write an AOR status ledger."""
    payload = dict(entries)
    for item in payload.get("entries", []):
        validate_aor_status(str(item["status"]))
    write_json_artifact(payload, path)


def count_unstatused(entries: Mapping[str, Any]) -> int:
    """Return the number of ledger entries missing a valid AOR status."""
    count = 0
    for item in entries.get("entries", []):
        try:
            validate_aor_status(str(item["status"]))
        except ValueError:
            count += 1
    return count
