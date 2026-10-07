"""Planck 2018 compressed CMB distance-prior likelihood."""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path
from typing import Any

import numpy as np
import yaml

from sbt_cosmo.theory.background_compressed import evaluate_background

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_CONFIG = ROOT / "configs" / "datasets" / "planck2018_compressed.yaml"


@lru_cache(maxsize=1)
def load_planck2018_compressed(path: str | None = None) -> dict[str, Any]:
    """Load the tracked Planck 2018 compressed-prior YAML."""
    config_path = Path(path) if path else DEFAULT_CONFIG
    payload = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    mean = np.asarray(payload["vector"]["mean"], dtype=np.float64)
    covariance = np.asarray(payload["vector"]["covariance"], dtype=np.float64)
    inv_covariance = np.linalg.inv(covariance)
    return {**payload, "mean_array": mean, "covariance_array": covariance, "inv_covariance_array": inv_covariance}


def planck2018_compressed_observable(
    *,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> np.ndarray:
    """Return the model vector (R, l_A, 100 omega_b)."""
    background = evaluate_background(
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    return np.asarray([background.R, background.l_A, 100.0 * float(omega_b)], dtype=np.float64)


def planck2018_compressed_chi2(
    *,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> float:
    """Return Gaussian chi-square for the Planck 2018 distance-prior vector."""
    prior = load_planck2018_compressed()
    delta = planck2018_compressed_observable(
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    ) - prior["mean_array"]
    return float(delta @ prior["inv_covariance_array"] @ delta)


def planck2018_compressed_logp(
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> float:
    """Cobaya external log-likelihood for compressed Planck 2018."""
    try:
        chi2 = planck2018_compressed_chi2(
            omega_b=omega_b,
            omega_cdm=omega_cdm,
            H0=H0,
            w0_fld=w0_fld,
            wa_fld=wa_fld,
        )
    except Exception:
        return -np.inf
    return -0.5 * chi2 if np.isfinite(chi2) else -np.inf

