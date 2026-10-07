"""Physical matter-power wrappers around the locked CCL backend.

The E5 substrate uses pyccl/CLASS as the physical growth backend.  This
module keeps imports lazy so structural tests can run without importing CCL
and so thread caps can be set by the caller before the first backend import.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from functools import lru_cache
from typing import Any

import numpy as np


def matter_power_spectrum(k: Sequence[float], z: float, parameters: Mapping[str, Any]) -> np.ndarray:
    """Return the CCL-native matter power spectrum ``P(k,z)`` in ``Mpc^3``.

    The input wavenumbers are CCL-native ``1/Mpc`` values. No ``h`` rescaling
    is applied in this wrapper.

    Parameters are accepted in the conventions used across this repository:
    either physical densities (``omega_b``, ``omega_cdm`` / ``ombh2``,
    ``omch2``) plus ``h`` or fractional densities (``Omega_b``, ``Omega_c``),
    with normalization supplied as either ``sigma8`` or ``S8``.  The default
    nonlinear prescription is Halofit, matching the locked E5 substrate.
    """
    cosmo = build_ccl_cosmology(parameters)
    k_arr = np.asarray(k, dtype=np.float64)
    if np.any(k_arr <= 0.0):
        raise ValueError("k values must be positive")
    a = 1.0 / (1.0 + float(z))
    nonlinear = bool(parameters.get("nonlinear", True))
    ccl = _ccl()
    if nonlinear:
        return np.asarray(ccl.nonlin_matter_power(cosmo, k_arr, a), dtype=np.float64)
    return np.asarray(ccl.linear_matter_power(cosmo, k_arr, a), dtype=np.float64)


def growth_factor(z: float | Sequence[float], parameters: Mapping[str, Any]) -> np.ndarray:
    """Return the linear growth factor normalized to unity today."""
    ccl = _ccl()
    cosmo = build_ccl_cosmology(parameters)
    z_arr = np.asarray(z, dtype=np.float64)
    a = 1.0 / (1.0 + z_arr)
    return np.asarray(ccl.growth_factor(cosmo, a), dtype=np.float64)


def sigma8(parameters: Mapping[str, Any]) -> float:
    """Return ``sigma8`` from a CCL cosmology built from ``parameters``."""
    ccl = _ccl()
    return float(ccl.sigma8(build_ccl_cosmology(parameters)))


def build_ccl_cosmology(parameters: Mapping[str, Any]) -> Any:
    """Build a flat pyccl cosmology from repository parameter names."""
    values = _normalized_parameters(parameters)
    ccl = _ccl()
    return ccl.Cosmology(
        Omega_c=values["Omega_c"],
        Omega_b=values["Omega_b"],
        h=values["h"],
        n_s=values["n_s"],
        sigma8=values["sigma8"],
        Omega_k=values["Omega_k"],
        Neff=values["Neff"],
        m_nu=values["m_nu"],
        w0=values["w0"],
        wa=values["wa"],
        transfer_function=values["transfer_function"],
        matter_power_spectrum=values["matter_power_spectrum"],
        baryonic_effects=values["baryonic_effects"],
        extra_parameters={"camb": {"dark_energy_model": values["dark_energy_model"]}},
    )


def omega_m(parameters: Mapping[str, Any]) -> float:
    """Return ``Omega_m`` implied by the accepted parameter conventions."""
    values = _normalized_parameters(parameters)
    return float(values["Omega_b"] + values["Omega_c"] + values["Omega_nu"])


def _normalized_parameters(parameters: Mapping[str, Any]) -> dict[str, Any]:
    h = _first(parameters, "h", "h0")
    if h is None:
        H0 = _first(parameters, "H0", "hubble")
        h = float(H0) / 100.0 if H0 is not None else 0.67
    h = float(h)

    omega_b = _first(parameters, "omega_b", "ombh2")
    omega_c = _first(parameters, "omega_cdm", "omch2", "omega_c")
    Omega_b = _first(parameters, "Omega_b", "omega_b_fraction")
    Omega_c_input = _first(parameters, "Omega_c", "Omega_cdm", "omega_cdm_fraction")
    Omega_c = Omega_c_input
    if Omega_b is None:
        Omega_b = (float(omega_b) if omega_b is not None else 0.02237) / h**2
    if Omega_c is None:
        Omega_c = (float(omega_c) if omega_c is not None else 0.1200) / h**2

    m_nu = float(_first(parameters, "m_nu", "mnu", default=0.06))
    Omega_nu = m_nu / (93.14 * h**2)
    Omega_m_total = float(_first(parameters, "Omega_m", default=float(Omega_b) + float(Omega_c) + Omega_nu))
    if "Omega_m" in parameters and Omega_c_input is None:
        Omega_c = Omega_m_total - float(Omega_b) - Omega_nu

    sigma8_value = _first(parameters, "sigma8", "sigma_8")
    if sigma8_value is None:
        S8 = _first(parameters, "S8", "s8", "s_8_input")
        sigma8_value = (float(S8) / np.sqrt(Omega_m_total / 0.3)) if S8 is not None else 0.81

    baryonic_effects = parameters.get("baryonic_effects")
    if isinstance(baryonic_effects, (str, Mapping)):
        baryonic_effects = _baryonic_effects(baryonic_effects)

    w0 = float(_first(parameters, "w0", "w0_fld", "w", default=-1.0))
    wa = float(_first(parameters, "wa", "wa_fld", default=0.0))
    dark_energy_model = parameters.get("dark_energy_model")
    if dark_energy_model is None:
        dark_energy_model = "ppf" if (abs(wa) > 0.0 or w0 + wa >= -1.0 or w0 >= -1.0) else "fluid"

    return {
        "Omega_b": float(Omega_b),
        "Omega_c": float(Omega_c),
        "Omega_nu": float(Omega_nu),
        "h": h,
        "n_s": float(_first(parameters, "n_s", "ns", default=0.965)),
        "sigma8": float(sigma8_value),
        "Omega_k": float(_first(parameters, "Omega_k", "omega_k", default=0.0)),
        "Neff": float(_first(parameters, "Neff", "N_eff", default=3.044)),
        "m_nu": m_nu,
        "w0": w0,
        "wa": wa,
        "dark_energy_model": str(dark_energy_model),
        "transfer_function": str(parameters.get("transfer_function", "boltzmann_camb")),
        "matter_power_spectrum": str(parameters.get("matter_power_spectrum", parameters.get("nonlinear_model", "halofit"))),
        "baryonic_effects": baryonic_effects,
    }


def _first(parameters: Mapping[str, Any], *keys: str, default: Any = None) -> Any:
    for key in keys:
        if key in parameters and parameters[key] is not None:
            return parameters[key]
    return default


def _baryonic_effects(spec: str | Mapping[str, Any]) -> Any:
    params: Mapping[str, Any]
    if isinstance(spec, Mapping):
        raw_name = spec.get("model", spec.get("name", spec.get("type", "none")))
        params = spec
    else:
        raw_name = spec
        params = {}
    normalized = str(raw_name).lower().replace("_", "-")
    ccl = _ccl()
    if normalized in {"none", "off", "false", "0"}:
        return None
    if normalized in {"bcm", "vandaalen19", "van-daalen19"}:
        return ccl.BaryonsvanDaalen19(
            fbar=float(params.get("fbar", 0.7)),
            mass_def=str(params.get("mass_def", "500c")),
        )
    if normalized in {"schneider15", "baryons-schneider15"}:
        return ccl.BaryonsSchneider15(
            log10Mc=float(params.get("log10Mc", params.get("log10_Mc", 14.079181246047625))),
            eta_b=float(params.get("eta_b", 0.5)),
            k_s=float(params.get("k_s", 55.0)),
        )
    if normalized in {"bacco", "baccoemu", "baryons-baccoemu"}:
        return ccl.BaryonsBaccoemu(
            log10_M_c=float(params.get("log10_M_c", params.get("log10Mc", 14.174))),
            log10_eta=float(params.get("log10_eta", -0.3)),
            log10_beta=float(params.get("log10_beta", -0.22)),
            log10_M1_z0_cen=float(params.get("log10_M1_z0_cen", 10.674)),
            log10_theta_out=float(params.get("log10_theta_out", 0.25)),
            log10_theta_inn=float(params.get("log10_theta_inn", -0.86)),
            log10_M_inn=float(params.get("log10_M_inn", 13.574)),
            verbose=bool(params.get("verbose", False)),
        )
    raise ValueError(f"Unknown CCL baryonic effect {raw_name!r}")


@lru_cache(maxsize=1)
def _ccl() -> Any:
    import pyccl as ccl

    return ccl
