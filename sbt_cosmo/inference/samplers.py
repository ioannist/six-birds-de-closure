"""Sampler wrappers, environment plumbing, and Cobaya output helpers."""

from __future__ import annotations

import json
import os
import subprocess
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

import numpy as np
import yaml


def build_seeded_generator(seed: int) -> Any:
    """Build a NumPy Generator from an explicit seed."""
    return np.random.default_rng(int(seed))


def prepare_planck_environment(metadata: Mapping[str, Any] | None = None) -> dict[str, str]:
    """Return process environment variables needed by native Planck clik."""
    env = os.environ.copy()
    packages_path = None
    pythonpath = None
    library_path = None
    if metadata:
        packages_path = metadata.get("resolved_cobaya_packages_path") or metadata.get("packages_path")
        pythonpath = metadata.get("pythonpath")
        library_path = metadata.get("ld_library_path")

    packages_path = packages_path or "/mnt/data-drive/sbt-de/data/raw/planck_2018/cobaya-packages"
    pythonpath = pythonpath or f"{packages_path}/code/planck/clik-main/lib/python/site-packages"
    library_path = library_path or f"{packages_path}/code/planck/clik-main/lib"

    env["COBAYA_PACKAGES_PATH"] = str(packages_path)
    env["PYTHONPATH"] = _prepend_path(str(pythonpath), env.get("PYTHONPATH"))
    env["LD_LIBRARY_PATH"] = _prepend_path(str(library_path), env.get("LD_LIBRARY_PATH"))
    env.setdefault("OMP_NUM_THREADS", "1")
    env.setdefault("SBT_MAX_CORES", "57")
    env.setdefault("PYTHONNOUSERSITE", "1")
    return env


def write_cobaya_yaml(info: Mapping[str, Any], path: Path) -> Path:
    """Write a Cobaya input dictionary as YAML and return the path."""
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = dict(info)
    if "evaluate" in payload.get("sampler", {}):
        payload["stop_at_error"] = True
    path.write_text(yaml.safe_dump(payload, sort_keys=False), encoding="utf-8")
    return path


def run_cobaya_subprocess(
    yaml_path: Path,
    *,
    packages_path: str | Path,
    env: Mapping[str, str] | None = None,
    extra_args: Sequence[str] = (),
    force: bool = True,
    resume: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Run cobaya-run as a subprocess and capture combined text output."""
    run_env = dict(env or os.environ)
    command = [
        "cobaya-run",
        "--packages-path",
        str(packages_path),
        "--no-mpi",
    ]
    if resume:
        command.append("--resume")
    elif force:
        command.append("--force")
    command.extend([str(yaml_path), *extra_args])
    return subprocess.run(
        command,
        check=False,
        cwd=Path(__file__).resolve().parents[2],
        env=run_env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def load_planck_metadata(report_path: Path | None = None) -> dict[str, Any]:
    """Load C-E1-data Planck package metadata from the committed report."""
    path = report_path or Path(__file__).resolve().parents[2] / "results" / "env" / "e1_data_report.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    return dict(report["datasets"]["PLANCK_2018"])


def find_chain_files(output_prefix: Path) -> list[Path]:
    """Return Cobaya text chain files for a given output prefix."""
    parent = output_prefix.parent
    stem = output_prefix.name
    return sorted(parent.glob(f"{stem}.*.txt"))


def load_minimum(path: Path) -> dict[str, float]:
    """Load a Cobaya minimum file into a dict of numeric columns."""
    values: dict[str, float] = {}
    if not path.exists():
        raise FileNotFoundError(path)
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        parts = stripped.split()
        if len(parts) == 2:
            try:
                values[parts[0]] = float(parts[1])
            except ValueError:
                continue
    return values


def _prepend_path(new_entry: str, existing: str | None) -> str:
    if not existing:
        return new_entry
    entries = existing.split(os.pathsep)
    if new_entry in entries:
        return existing
    return os.pathsep.join([new_entry, existing])
