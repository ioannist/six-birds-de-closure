"""Residual diagnostic plotting helpers."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import numpy as np

from sbt_cosmo.viz.style import apply_style


def write_residual_plot(residuals: Any, path: Path) -> None:
    """Write a deterministic Xi_cosmo residual diagnostic plot."""
    import matplotlib.pyplot as plt

    apply_style()
    values = np.asarray(residuals, dtype=float)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig, ax = plt.subplots(figsize=(5.2, 3.2))
    ax.plot(values, marker="o", linewidth=1.2, markersize=3.0)
    ax.axhline(0.0, color="black", linewidth=0.8)
    ax.set_xlabel("index")
    ax.set_ylabel("residual")
    fig.savefig(path)
    plt.close(fig)
