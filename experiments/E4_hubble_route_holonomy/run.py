"""Thin E4 orchestrator skeleton."""

from __future__ import annotations

import argparse
from pathlib import Path

import yaml

from sbt_cosmo.hubble.route_matrix import build_route_matrix


def run(config_path: Path, outdir: Path) -> None:
    """Load config and defer route-matrix physics to C0b+."""
    with config_path.open("r", encoding="utf-8") as handle:
        config = yaml.safe_load(handle)
    outdir.mkdir(parents=True, exist_ok=True)
    build_route_matrix(config)


def main() -> None:
    """Parse runner arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("config.yaml"))
    parser.add_argument("--outdir", type=Path, default=Path("outputs"))
    args = parser.parse_args()
    run(args.config, args.outdir)


if __name__ == "__main__":
    main()
