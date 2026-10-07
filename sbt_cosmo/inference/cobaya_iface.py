"""Cobaya input builders and E1 standard-likelihood wrappers."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from copy import deepcopy
from pathlib import Path
from typing import Any

import numpy as np

from sbt_cosmo.io.datasets import (
    ProbeData,
    load_des_sn5yr,
    load_desi_dr2_bao,
    load_pantheon_plus,
    load_union3,
)

LIGHT_SPEED_KM_S = 299792.458

_PROBE_CACHE: dict[str, ProbeData] = {}


def build_cobaya_input(
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
    """Build a Cobaya input dictionary for one E1 standard-model run."""
    combo_key = combination.upper()
    model_key = model.lower()
    if combo_key not in config["combinations"]:
        raise KeyError(f"unknown E1 combination: {combination}")
    if model_key not in config["models"]:
        raise KeyError(f"unknown E1 model: {model}")

    combo = config["combinations"][combo_key]
    model_cfg = config["models"][model_key]
    mode_cfg = config["run_modes"].get(run_mode, {})
    sampled_nuisance = bool(mode_cfg.get("sample_planck_nuisance", True))

    info: dict[str, Any] = {
        "debug": bool(config.get("debug", False)),
        "output": str(output_prefix),
        "force": True,
        "stop_at_error": _stop_at_error(sampler),
        "packages_path": str(_planck_packages_path(config)),
        "theory": _theory_block(config, model_key),
        "likelihood": _likelihood_block(combo["datasets"]),
        "params": _parameter_block(config, model_cfg, combo["datasets"], sampled_nuisance),
        "sampler": _sampler_block(config, sampler, run_mode, max_samples=max_samples, covmat=covmat),
    }
    return info


def desi_dr2_bao_logp(_self: Any) -> float:
    """External Gaussian log-likelihood for the DESI DR2 compressed BAO vector."""
    probe = _cached_probe("DESI_DR2_BAO")
    z = np.asarray(probe.bins["z"], dtype=np.float64)
    observables = list(probe.bins["observable"])
    angular = np.asarray(_self.provider.get_angular_diameter_distance(z), dtype=np.float64)
    hubble = np.asarray(_self.provider.get_Hubble(z, units="km/s/Mpc"), dtype=np.float64)
    sound_horizon = float(_self.provider.get_param("rs_drag"))

    transverse = (1.0 + z) * angular / sound_horizon
    radial = LIGHT_SPEED_KM_S / hubble / sound_horizon
    volume = (z * ((1.0 + z) * angular) ** 2 * LIGHT_SPEED_KM_S / hubble) ** (1.0 / 3.0)
    volume /= sound_horizon

    prediction = np.empty_like(probe.data_vector, dtype=np.float64)
    for index, observable in enumerate(observables):
        if observable == "DM_over_rs":
            prediction[index] = transverse[index]
        elif observable == "DH_over_rs":
            prediction[index] = radial[index]
        elif observable == "DV_over_rs":
            prediction[index] = volume[index]
        else:
            raise ValueError(f"unsupported DESI DR2 BAO observable: {observable}")
    return _gaussian_logp(probe, prediction)


def pantheon_plus_logp(sn_M: float = 0.0, _self: Any | None = None) -> float:
    """External Gaussian log-likelihood for Pantheon+ with a sampled offset."""
    return _sn_logp("PANTHEON_PLUS", sn_M=sn_M, _self=_self)


def union3_logp(sn_M: float = 0.0, _self: Any | None = None) -> float:
    """External Gaussian log-likelihood for Union3 with a sampled offset."""
    return _sn_logp("UNION3", sn_M=sn_M, _self=_self)


def des_sn5yr_logp(sn_M: float = 0.0, _self: Any | None = None) -> float:
    """External Gaussian log-likelihood for DES-SN5YR with a sampled offset."""
    return _sn_logp("DES_SN5YR", sn_M=sn_M, _self=_self)


def requested_distances_for_datasets(datasets: Sequence[str]) -> dict[str, Any]:
    """Return combined Cobaya theory requirements for the external probes."""
    z_angular: list[float] = []
    z_hubble: list[float] = []
    needs_rs_drag = False
    for dataset in datasets:
        key = dataset.upper()
        if key == "DESI_DR2_BAO":
            probe = _cached_probe(key)
            z = [float(value) for value in probe.bins["z"]]
            z_angular.extend(z)
            z_hubble.extend(z)
            needs_rs_drag = True
        elif key in {"PANTHEON_PLUS", "UNION3", "DES_SN5YR"}:
            probe = _cached_probe(key)
            z_angular.extend(_sn_redshifts(probe).tolist())

    requirements: dict[str, Any] = {}
    if z_angular:
        requirements["angular_diameter_distance"] = {"z": _unique_sorted(z_angular)}
    if z_hubble:
        requirements["Hubble"] = {"z": _unique_sorted(z_hubble)}
    if needs_rs_drag:
        requirements["rs_drag"] = None
    return requirements


def _theory_block(config: Mapping[str, Any], model: str) -> dict[str, Any]:
    class_settings = deepcopy(config["theory"]["class"])
    extra_args = class_settings.setdefault("extra_args", {})
    if model == "wcdm":
        extra_args.update({"Omega_Lambda": 0.0, "wa_fld": 0.0})
    elif model == "w0wa":
        extra_args.update({"Omega_Lambda": 0.0, "use_ppf": "yes"})
    return {"classy": class_settings}


def _stop_at_error(sampler: str) -> bool:
    """Use fatal theory errors only for single-point evaluations."""
    return sampler.lower() not in {"mcmc", "minimize"}


def _likelihood_block(datasets: Sequence[str]) -> dict[str, Any]:
    likelihood: dict[str, Any] = {}
    if "PLANCK_2018" in {dataset.upper() for dataset in datasets}:
        likelihood.update(
            {
                "planck_2018_highl_plik.TTTEEE": None,
                "planck_2018_lowl.TT": None,
                "planck_2018_lowl.EE": None,
                "planck_2018_lensing.native": None,
            }
        )

    for dataset in datasets:
        key = dataset.upper()
        if key == "DESI_DR2_BAO":
            likelihood["e1_desi_dr2_bao"] = {
                "external": 'import_module("sbt_cosmo.inference.cobaya_iface").desi_dr2_bao_logp',
                "requires": requested_distances_for_datasets([key]),
            }
        elif key == "PANTHEON_PLUS":
            likelihood["e1_pantheon_plus"] = {
                "external": 'import_module("sbt_cosmo.inference.cobaya_iface").pantheon_plus_logp',
                "requires": requested_distances_for_datasets([key]),
            }
        elif key == "UNION3":
            likelihood["e1_union3"] = {
                "external": 'import_module("sbt_cosmo.inference.cobaya_iface").union3_logp',
                "requires": requested_distances_for_datasets([key]),
            }
        elif key == "DES_SN5YR":
            likelihood["e1_des_sn5yr"] = {
                "external": 'import_module("sbt_cosmo.inference.cobaya_iface").des_sn5yr_logp',
                "requires": requested_distances_for_datasets([key]),
            }
    return likelihood


def _parameter_block(
    config: Mapping[str, Any],
    model_cfg: Mapping[str, Any],
    datasets: Sequence[str],
    sampled_nuisance: bool,
) -> dict[str, Any]:
    params: dict[str, Any] = deepcopy(config["priors"]["cosmology"])
    params["logA"]["drop"] = True
    params["A_s"] = {
        "value": "lambda logA: 1e-10*np.exp(logA)",
        "latex": "A_s",
    }

    for name, value in model_cfg.get("fixed", {}).items():
        params[name] = value
    for name, prior in model_cfg.get("sampled", {}).items():
        params[name] = deepcopy(prior)

    if "PLANCK_2018" in {dataset.upper() for dataset in datasets}:
        if sampled_nuisance:
            params.update(deepcopy(config["priors"]["planck_nuisance"]))
        else:
            params.update(deepcopy(config["fixed_planck_nuisance"]))

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


def _sn_logp(key: str, *, sn_M: float, _self: Any | None) -> float:
    if _self is None:
        raise ValueError("Cobaya external SN likelihood requires _self")
    probe = _cached_probe(key)
    redshifts = _sn_redshifts(probe)
    angular = np.asarray(_self.provider.get_angular_diameter_distance(redshifts), dtype=np.float64)
    luminosity_distance = (1.0 + redshifts) ** 2 * angular
    prediction = 5.0 * np.log10(luminosity_distance) + 25.0 + float(sn_M)
    return _gaussian_logp(probe, prediction)


def _gaussian_logp(probe: ProbeData, prediction: np.ndarray) -> float:
    residual = np.asarray(probe.data_vector, dtype=np.float64) - np.asarray(prediction, dtype=np.float64)
    solution = np.linalg.solve(np.asarray(probe.covariance, dtype=np.float64), residual)
    return float(-0.5 * residual @ solution)


def _cached_probe(key: str) -> ProbeData:
    normalized = key.upper()
    if normalized not in _PROBE_CACHE:
        if normalized == "DESI_DR2_BAO":
            _PROBE_CACHE[normalized] = load_desi_dr2_bao()
        elif normalized == "PANTHEON_PLUS":
            _PROBE_CACHE[normalized] = load_pantheon_plus()
        elif normalized == "UNION3":
            _PROBE_CACHE[normalized] = load_union3()
        elif normalized == "DES_SN5YR":
            _PROBE_CACHE[normalized] = load_des_sn5yr()
        else:
            raise KeyError(f"unsupported E1 probe: {key}")
    return _PROBE_CACHE[normalized]


def _sn_redshifts(probe: ProbeData) -> np.ndarray:
    bins = probe.bins
    redshifts = bins.get("z_cmb", bins.get("z_hd", bins.get("z")))
    if redshifts is None:
        raise ValueError(f"{probe.key} metadata does not contain redshift bins")
    return np.asarray(redshifts, dtype=np.float64)


def _has_supernova_dataset(datasets: Sequence[str]) -> bool:
    return any(dataset.upper() in {"PANTHEON_PLUS", "UNION3", "DES_SN5YR"} for dataset in datasets)


def _planck_packages_path(config: Mapping[str, Any]) -> Path:
    return Path(config["packages"]["cobaya"])


def _unique_sorted(values: Sequence[float]) -> list[float]:
    return sorted({float(value) for value in values})
