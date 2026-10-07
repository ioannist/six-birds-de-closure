"""MCMC chain loading and convergence diagnostics."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import arviz as az
import numpy as np
import pandas as pd


def load_cobaya_chain(chain_files: list[Path]) -> pd.DataFrame:
    """Load one or more Cobaya text chain files into a single data frame."""
    frames = []
    for path in chain_files:
        names = _column_names(path)
        frames.append(pd.read_csv(path, comment="#", sep=r"\s+", names=names, engine="python"))
    if not frames:
        raise FileNotFoundError("no Cobaya chain files found")
    return pd.concat(frames, ignore_index=True)


def convergence_summary(samples: Any) -> dict[str, float | int | None]:
    """Return R-hat and ESS summaries from a chain array or data frame."""
    if isinstance(samples, pd.DataFrame):
        numeric = samples.select_dtypes(include=[np.number])
        cols = [col for col in numeric.columns if col not in {"weight", "minuslogpost"}]
        array = numeric[cols].to_numpy(dtype=np.float64)
        names = cols
    else:
        array = np.asarray(samples, dtype=np.float64)
        if array.ndim == 1:
            array = array[:, None]
        names = [f"param_{index}" for index in range(array.shape[1])]

    if array.shape[0] < 8:
        return {"n_samples": int(array.shape[0]), "max_rhat_minus_one": None, "min_ess": None}

    split = 4
    usable = (array.shape[0] // split) * split
    reshaped = array[:usable].reshape(split, usable // split, array.shape[1])
    data = {name: reshaped[:, :, index] for index, name in enumerate(names)}
    inference_data = az.from_dict(posterior=data)
    rhat = az.rhat(inference_data).to_array().values.astype(float)
    ess = az.ess(inference_data).to_array().values.astype(float)
    finite_rhat = rhat[np.isfinite(rhat)]
    finite_ess = ess[np.isfinite(ess)]
    return {
        "n_samples": int(array.shape[0]),
        "max_rhat_minus_one": float(np.max(finite_rhat) - 1.0) if finite_rhat.size else None,
        "min_ess": float(np.min(finite_ess)) if finite_ess.size else None,
    }


def convergence_summary_from_chain_files(
    chain_files: list[Path],
    *,
    parameters: list[str],
) -> dict[str, float | int | None]:
    """Compute cross-chain R-hat/ESS from Cobaya chain files."""
    arrays: list[np.ndarray] = []
    total_weight = 0
    for path in chain_files:
        frame = load_cobaya_chain([path])
        missing = [name for name in parameters if name not in frame.columns]
        if missing:
            raise ValueError(f"{path} is missing sampled parameters: {missing}")
        weights = frame["weight"].astype(int).clip(lower=1).to_numpy()
        values = frame[parameters].to_numpy(dtype=np.float64)
        expanded = np.repeat(values, weights, axis=0)
        total_weight += int(weights.sum())
        if expanded.shape[0] >= 4:
            arrays.append(expanded)
    if len(arrays) < 2:
        return {
            "n_chains": len(arrays),
            "total_samples": total_weight,
            "max_rhat_minus_one": None,
            "min_ess": None,
        }
    n_draws = min(array.shape[0] for array in arrays)
    stacked = np.stack([array[:n_draws] for array in arrays], axis=0)
    data = {name: stacked[:, :, index] for index, name in enumerate(parameters)}
    inference_data = az.from_dict(posterior=data)
    rhat = az.rhat(inference_data).to_array().values.astype(float)
    ess = az.ess(inference_data).to_array().values.astype(float)
    finite_rhat = rhat[np.isfinite(rhat)]
    finite_ess = ess[np.isfinite(ess)]
    return {
        "n_chains": int(len(arrays)),
        "draws_per_chain_used": int(n_draws),
        "total_samples": int(total_weight),
        "max_rhat_minus_one": float(np.max(finite_rhat) - 1.0) if finite_rhat.size else None,
        "min_ess": float(np.min(finite_ess)) if finite_ess.size else None,
    }


def _column_names(path: Path) -> list[str]:
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        stripped = line.strip()
        if stripped.startswith("#") and "weight" in stripped and "minuslogpost" in stripped:
            return stripped.lstrip("#").split()
    raise ValueError(f"chain header with column names not found in {path}")
