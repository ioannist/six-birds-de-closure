"""Thin E8 orchestrator skeleton."""

from __future__ import annotations

import argparse
from pathlib import Path

import yaml

from sbt_cosmo.inference.evidence import compute_information_criteria


def run(config_path: Path, outdir: Path) -> None:
    """Load config and defer global model competition to C0b+."""
    with config_path.open("r", encoding="utf-8") as handle:
        yaml.safe_load(handle)
    outdir.mkdir(parents=True, exist_ok=True)
    compute_information_criteria(loglike=0.0, n_params=0, n_data=0)


def main() -> None:
    """Parse runner arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("config.yaml"))
    parser.add_argument("--outdir", type=Path, default=Path("outputs"))
    args = parser.parse_args()
    run(args.config, args.outdir)


if __name__ == "__main__":
    main()
