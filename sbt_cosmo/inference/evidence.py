"""Evidence, likelihood-ratio, and information-criterion utilities."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Any

import numpy as np
from scipy import stats


def compute_information_criteria(loglike: float, n_params: int, n_data: int) -> Mapping[str, float]:
    """Compute AIC and BIC from a maximum log-likelihood."""
    loglike = float(loglike)
    n_params = int(n_params)
    n_data = int(n_data)
    if n_data <= 0:
        raise ValueError("n_data must be positive for BIC")
    return {
        "aic": float(2 * n_params - 2 * loglike),
        "bic": float(n_params * np.log(n_data) - 2 * loglike),
    }


def delta_chi2_to_sigma(delta_chi2: float, *, delta_k: int = 2) -> Mapping[str, float]:
    """Convert a nested-model chi-square improvement to Gaussian-equivalent sigma."""
    improvement = max(float(delta_chi2), 0.0)
    p_value = float(stats.chi2.sf(improvement, int(delta_k)))
    sigma = float(stats.norm.isf(p_value / 2.0)) if p_value > 0.0 else float("inf")
    return {"delta_chi2": improvement, "delta_k": int(delta_k), "p_value": p_value, "sigma": sigma}


def summarize_model_comparison(
    *,
    chi2_baseline: float,
    chi2_extended: float,
    n_baseline: int,
    n_extended: int,
    n_data: int,
) -> dict[str, float]:
    """Return chi-square, sigma, AIC, and BIC comparison summaries."""
    delta = float(chi2_baseline) - float(chi2_extended)
    sigma = delta_chi2_to_sigma(delta, delta_k=int(n_extended) - int(n_baseline))
    baseline_ic = compute_information_criteria(-0.5 * float(chi2_baseline), n_baseline, n_data)
    extended_ic = compute_information_criteria(-0.5 * float(chi2_extended), n_extended, n_data)
    return {
        "delta_chi2": delta,
        "sigma": sigma["sigma"],
        "p_value": sigma["p_value"],
        "delta_aic_baseline_minus_extended": baseline_ic["aic"] - extended_ic["aic"],
        "delta_bic_baseline_minus_extended": baseline_ic["bic"] - extended_ic["bic"],
    }


def run_dynesty_evidence(
    loglikelihood: Callable[[np.ndarray], float],
    prior_transform: Callable[[np.ndarray], np.ndarray],
    *,
    ndim: int,
    nlive: int,
    seed: int,
    dlogz: float = 0.5,
) -> dict[str, Any]:
    """Run a small dynesty evidence calculation for configured Python callables."""
    from dynesty import NestedSampler

    rng = np.random.default_rng(int(seed))
    sampler = NestedSampler(loglikelihood, prior_transform, int(ndim), nlive=int(nlive), rstate=rng)
    sampler.run_nested(dlogz=float(dlogz), print_progress=False)
    results = sampler.results
    return {
        "lnz": float(results.logz[-1]),
        "lnzerr": float(results.logzerr[-1]),
        "niter": int(results.niter),
        "nlive": int(nlive),
    }
