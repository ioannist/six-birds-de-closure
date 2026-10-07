"""Cobaya input builder for the E1 compressed-CMB reproduction track."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from copy import deepcopy
from pathlib import Path
from typing import Any


def build_compressed_cobaya_input(
    config: Mapping[str, Any],
    *,
    combination: str,
    model: str,
    sampler: str,
    output_prefix: str | Path,
    run_mode: str = "production",
    max_samples: int | None = None,
    covmat: str | Path | None = None,
) -> dict[str, Any]:
    """Build a Cobaya input dictionary for one compressed E1 run."""
    combo_key = combination.upper()
    model_key = model.lower()
    if combo_key not in config["combinations"]:
        raise KeyError(f"unknown E1 combination: {combination}")
    if model_key not in config["models"]:
        raise KeyError(f"unknown E1 model: {model}")

    combo = config["combinations"][combo_key]
    model_cfg = config["models"][model_key]
    return {
        "debug": bool(config.get("debug", False)),
        "output": str(output_prefix),
        "force": True,
        "stop_at_error": sampler.lower() not in {"mcmc", "minimize"},
        "likelihood": _likelihood_block(combo["datasets"]),
        "params": _parameter_block(config, model_cfg, combo["datasets"]),
        "sampler": _sampler_block(config, sampler, run_mode, max_samples=max_samples, covmat=covmat),
    }


def _likelihood_block(datasets: Sequence[str]) -> dict[str, Any]:
    likelihood: dict[str, Any] = {}
    for dataset in datasets:
        key = dataset.upper()
        if key == "PLANCK_2018_COMPRESSED":
            likelihood["e1_planck2018_compressed"] = {
                "external": 'import_module("sbt_cosmo.likelihoods.cmb_compressed").planck2018_compressed_logp'
            }
        elif key == "DESI_DR2_BAO":
            likelihood["e1_desi_dr2_bao_compressed"] = {
                "external": 'import_module("sbt_cosmo.likelihoods.bao_sn_gaussian").desi_dr2_bao_compressed_logp'
            }
        elif key == "PANTHEON_PLUS":
            likelihood["e1_pantheon_plus_compressed"] = {
                "external": 'import_module("sbt_cosmo.likelihoods.bao_sn_gaussian").pantheon_plus_compressed_logp'
            }
        elif key == "UNION3":
            likelihood["e1_union3_compressed"] = {
                "external": 'import_module("sbt_cosmo.likelihoods.bao_sn_gaussian").union3_compressed_logp'
            }
        elif key == "DES_SN5YR":
            likelihood["e1_des_sn5yr_compressed"] = {
                "external": 'import_module("sbt_cosmo.likelihoods.bao_sn_gaussian").des_sn5yr_compressed_logp'
            }
    return likelihood


def _parameter_block(config: Mapping[str, Any], model_cfg: Mapping[str, Any], datasets: Sequence[str]) -> dict[str, Any]:
    params = deepcopy(config["priors"]["cosmology"])
    params.update(deepcopy(model_cfg.get("fixed", {})))
    for name, prior in model_cfg.get("sampled", {}).items():
        params[name] = deepcopy(prior)
    if _has_supernova_dataset(datasets):
        params["sn_M"] = deepcopy(config["priors"]["supernova"]["sn_M"])
    return params


def _sampler_block(
    config: Mapping[str, Any],
    sampler: str,
    run_mode: str,
    *,
    max_samples: int | None,
    covmat: str | Path | None,
) -> dict[str, Any]:
    sampler_key = sampler.lower()
    mode = config["run_modes"].get(run_mode, {})
    sampler_cfg = deepcopy(config["samplers"][sampler_key])
    sampler_cfg.update(deepcopy(mode.get("sampler_overrides", {}).get(sampler_key, {})))
    seed_offset = int(mode.get("seed_offset", 0))
    if sampler_key in {"mcmc", "minimize"}:
        sampler_cfg["seed"] = int(config["seeds"]["sampler"]) + seed_offset
    if sampler_key == "mcmc" and max_samples is not None:
        sampler_cfg["max_samples"] = int(max_samples)
    if sampler_key == "mcmc" and covmat is not None:
        sampler_cfg["covmat"] = str(covmat)
    return {sampler_key: sampler_cfg}


def _has_supernova_dataset(datasets: Sequence[str]) -> bool:
    return bool({"PANTHEON_PLUS", "UNION3", "DES_SN5YR"} & {dataset.upper() for dataset in datasets})
