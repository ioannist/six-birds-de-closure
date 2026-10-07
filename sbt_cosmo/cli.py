"""Command-line entrypoint for config-driven experiment runners."""

from __future__ import annotations

import argparse
from pathlib import Path


def build_parser() -> argparse.ArgumentParser:
    """Create the top-level CLI parser."""
    parser = argparse.ArgumentParser(prog="sbt-cosmo")
    subparsers = parser.add_subparsers(dest="command", required=True)
    run = subparsers.add_parser("run", help="Run a configured experiment.")
    run.add_argument("--config", required=True, type=Path)
    run.add_argument("--outdir", required=True, type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    """Parse CLI arguments and dispatch to future orchestration code."""
    parser = build_parser()
    parser.parse_args(argv)
    raise NotImplementedError("Experiment execution is deferred to C0b+.")
