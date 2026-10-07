"""Run-manifest writer."""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from typing import Any

from sbt_cosmo.io.artifacts import write_json_artifact


def write_run_manifest(manifest: Mapping[str, Any], path: Path) -> None:
    """Write a run manifest JSON file."""
    write_json_artifact(dict(manifest), path)
