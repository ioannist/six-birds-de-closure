"""Thin E5 orchestrator skeleton."""

from __future__ import annotations

import argparse
from pathlib import Path

import yaml

from sbt_cosmo.growth.s8 import s8_readout


def run(config_path: Path, outdir: Path) -> None:
    """Load config and defer growth/staging physics to C0b+."""
    with config_path.open("r", encoding="utf-8") as handle:
        yaml.safe_load(handle)
    outdir.mkdir(parents=True, exist_ok=True)
    s8_readout(sigma8=0.8, omega_m=0.3)


def main() -> None:
    """Parse runner arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("config.yaml"))
    parser.add_argument("--outdir", type=Path, default=Path("outputs"))
    args = parser.parse_args()
    run(args.config, args.outdir)


if __name__ == "__main__":
    main()
