"""Proposal covariance matrix helpers for Cobaya chains."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import numpy as np
import pandas as pd

from sbt_cosmo.inference.convergence import load_cobaya_chain

E1_PLANCK_LCDM_COVMAT_PARAMETERS = [
    "theta_s_100",
    "omega_b",
    "omega_cdm",
    "tau_reio",
    "logA",
    "n_s",
    "A_planck",
    "calib_100T",
    "calib_217T",
    "A_cib_217",
    "xi_sz_cib",
    "A_sz",
    "ksz_norm",
    "gal545_A_100",
    "gal545_A_143",
    "gal545_A_143_217",
    "gal545_A_217",
    "ps_A_100_100",
    "ps_A_143_143",
    "ps_A_143_217",
    "ps_A_217_217",
    "galf_TE_A_100",
    "galf_TE_A_100_143",
    "galf_TE_A_100_217",
    "galf_TE_A_143",
    "galf_TE_A_143_217",
    "galf_TE_A_217",
]


def write_covmat_from_cobaya_chains(
    chain_files: list[Path],
    output_path: Path,
    *,
    parameters: list[str] | None = None,
    ignore_rows: float = 0.3,
) -> dict[str, Any]:
    """Write a Cobaya-format weighted proposal covmat from text chains."""
    if not chain_files:
        raise FileNotFoundError("no chain files supplied")
    parameters = parameters or E1_PLANCK_LCDM_COVMAT_PARAMETERS
    frames = [_load_post_burnin(path, ignore_rows=ignore_rows) for path in chain_files]
    frame = pd.concat(frames, ignore_index=True)
    missing = [name for name in parameters if name not in frame.columns]
    if missing:
        raise ValueError(f"chain files are missing covmat parameters: {missing}")

    values = frame[parameters].to_numpy(dtype=np.float64)
    weights = frame["weight"].astype(float).clip(lower=1.0).to_numpy()
    if not np.isfinite(values).all():
        raise ValueError("non-finite covmat source values")

    covariance = _weighted_covariance(values, weights)
    covariance = 0.5 * (covariance + covariance.T)
    eigenvalues = np.linalg.eigvalsh(covariance)
    if float(np.min(eigenvalues)) <= 0.0:
        raise ValueError(f"covmat is not positive definite; min eigenvalue={float(np.min(eigenvalues))}")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8") as handle:
        handle.write("# " + " ".join(parameters) + "\n")
        np.savetxt(handle, covariance, fmt="%.18e")
    return {
        "path": str(output_path),
        "parameters": parameters,
        "shape": list(covariance.shape),
        "n_rows": int(frame.shape[0]),
        "weight_sum": float(weights.sum()),
        "min_eigenvalue": float(np.min(eigenvalues)),
        "max_eigenvalue": float(np.max(eigenvalues)),
        "condition_number": float(np.max(eigenvalues) / np.min(eigenvalues)),
        "diagonal": {name: float(covariance[index, index]) for index, name in enumerate(parameters)},
    }


def _load_post_burnin(path: Path, *, ignore_rows: float) -> pd.DataFrame:
    frame = load_cobaya_chain([path])
    drop = int(frame.shape[0] * float(ignore_rows))
    if drop >= frame.shape[0]:
        raise ValueError(f"ignore_rows={ignore_rows} drops all rows from {path}")
    return frame.iloc[drop:].reset_index(drop=True)


def _weighted_covariance(values: np.ndarray, weights: np.ndarray) -> np.ndarray:
    weight_sum = float(np.sum(weights))
    if weight_sum <= 1.0:
        raise ValueError("insufficient total chain weight for covariance")
    mean = np.average(values, axis=0, weights=weights)
    centered = values - mean
    return (centered * weights[:, None]).T @ centered / (weight_sum - 1.0)
