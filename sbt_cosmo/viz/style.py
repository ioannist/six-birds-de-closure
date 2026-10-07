"""Deterministic matplotlib style helpers."""

from __future__ import annotations


def apply_style() -> None:
    """Apply deterministic plotting style."""
    import matplotlib as mpl

    mpl.rcParams.update(
        {
            "figure.dpi": 120,
            "savefig.dpi": 120,
            "font.family": "DejaVu Sans",
            "font.size": 9,
            "axes.grid": True,
            "grid.alpha": 0.25,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "figure.autolayout": True,
        }
    )
