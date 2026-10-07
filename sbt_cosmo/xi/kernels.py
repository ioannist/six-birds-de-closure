"""Observable-correction kernels for the E1-B Xi_cosmo geometry test."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

import numpy as np

from sbt_cosmo.theory.background_compressed import LIGHT_SPEED_KM_S, evaluate_background
from sbt_cosmo.xi.residual import calibration_weight, evaluate_xi_cosmo, staging_weight


def luminosity_kernel(
    *,
    z: Any,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    parameters: Mapping[str, Any],
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> np.ndarray:
    """Return K_L[Xi](z) in Mpc for SN luminosity distances.

    E1-B uses H_tilde=H/H0, so the comoving perturbation is
    (c/H0) int Xi(z') / E(z') dz'. Xi amplitudes are dimensionless.
    """
    z_array = np.asarray(z, dtype=float)
    integral = _xi_integral(
        z_array,
        probe="SN",
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        parameters=parameters,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    return (1.0 + z_array) * (LIGHT_SPEED_KM_S / float(H0)) * integral


def transverse_bao_kernel(
    *,
    z: Any,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    r_drag: float,
    parameters: Mapping[str, Any],
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> np.ndarray:
    """Return K_M[Xi](z) for D_M/r_d BAO observables."""
    z_array = np.asarray(z, dtype=float)
    integral = _xi_integral(
        z_array,
        probe="BAO",
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        parameters=parameters,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    return (LIGHT_SPEED_KM_S / float(H0)) * integral / float(r_drag)


def radial_bao_kernel(
    *,
    z: Any,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    r_drag: float,
    parameters: Mapping[str, Any],
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> np.ndarray:
    """Return the radial BAO ratio perturbation implied by dK_M/dz."""
    z_array = np.asarray(z, dtype=float)
    background = evaluate_background(
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        z=tuple(z_array.tolist()),
    )
    xi = evaluate_xi_cosmo(z_array, None, "BAO", parameters)
    return (LIGHT_SPEED_KM_S / float(H0)) * xi / (background.H / float(H0)) / float(r_drag)


def corrected_luminosity_distance(
    *,
    z: Any,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    parameters: Mapping[str, Any],
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> tuple[np.ndarray, np.ndarray]:
    """Return FLRW-plus-Xi luminosity distance and K_L arrays."""
    z_array = np.asarray(z, dtype=float)
    background = evaluate_background(
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        z=tuple(z_array.tolist()),
    )
    kernel = luminosity_kernel(
        z=z_array,
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        parameters=parameters,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    return background.D_L + kernel, kernel


def corrected_bao_observables(
    *,
    z: Any,
    observables: list[str] | tuple[str, ...],
    omega_b: float,
    omega_cdm: float,
    H0: float,
    parameters: Mapping[str, Any],
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    """Return DESI-style BAO predictions with one shared Xi correction."""
    z_array = np.asarray(z, dtype=float)
    background = evaluate_background(
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        z=tuple(z_array.tolist()),
    )
    k_m = transverse_bao_kernel(
        z=z_array,
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        r_drag=background.r_drag,
        parameters=parameters,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    k_h = radial_bao_kernel(
        z=z_array,
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        r_drag=background.r_drag,
        parameters=parameters,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    dm_ratio = background.D_M / background.r_drag + k_m
    dh_ratio = background.D_H / background.r_drag + k_h
    dv_ratio = np.cbrt(np.maximum(z_array * (dm_ratio * background.r_drag) ** 2 * (dh_ratio * background.r_drag), 0.0)) / background.r_drag
    prediction = np.empty(z_array.shape, dtype=float)
    for index, observable in enumerate(observables):
        if observable == "DM_over_rs":
            prediction[index] = dm_ratio[index]
        elif observable == "DH_over_rs":
            prediction[index] = dh_ratio[index]
        elif observable == "DV_over_rs":
            prediction[index] = dv_ratio[index]
        else:
            raise ValueError(f"unsupported BAO observable: {observable}")
    return prediction, {"K_M": k_m, "K_H": k_h, "DM_over_rs": dm_ratio, "DH_over_rs": dh_ratio, "DV_over_rs": dv_ratio}


def hubble_route_kernel(
    route: Mapping[str, Any],
    parameters: Mapping[str, Any],
    *,
    h_unit: float = 70.0,
) -> float:
    """Return the frozen E4 Hubble-route offset K_{r,ell}[Xi] in km/s/Mpc.

    The E4-PREDICT contract freezes this deterministic linear readout before
    route values are unlocked.  The route mapping supplies the declared
    redshift response and bridge transports; this function only evaluates the
    locked low-rank basis against those physics-declared weights.

    Sign convention: positive ``delta_H0`` means the route reads a larger
    H0 than ``H_closed(0)``.  Distance-like bridge residuals enter with the
    local-ladder convention delta H0 / H0 ~= - delta D / D, hence the leading
    minus sign in the linear basis.
    """
    basis = hubble_route_kernel_basis(route, h_unit=h_unit)
    return float(sum(basis[name] * float(parameters.get(name, 0.0)) for name in ("a0", "a1", "a2")))


def hubble_route_kernel_basis(route: Mapping[str, Any], *, h_unit: float = 70.0) -> dict[str, float]:
    """Return linear coefficients mapping (a0, a1, a2) to K_{r,ell}.

    Preferred E4-PREDICT route definitions use:

    - ``W_r`` / ``distance_windows``: declared redshift response windows.
    - ``B_b`` / ``bridge_terms``: declared calibration bridge transports.

    The older scalar-weight schema is retained as a compatibility fallback for
    synthetic tests, but the blind E4 freeze uses the physics schema above.
    """
    if "distance_windows" in route or isinstance(route.get("W_r"), list):
        return _hubble_route_kernel_basis_physics(route, h_unit=h_unit)

    z_eff = float(route.get("z_eff", route.get("W_r", {}).get("z_eff")))
    response = float(route.get("response", 1.0))
    scale = -float(h_unit) * response
    return {
        "a0": float(scale * float(route.get("route_depth", 0.0))),
        "a1": float(scale * (z_eff / (1.0 + z_eff)) * float(route.get("staging_weight", 0.0))),
        "a2": float(scale * np.log1p(z_eff) * float(route.get("bridge_weight", 0.0)) * float(route.get("bridge_sign", 0.0))),
    }


def _hubble_route_kernel_basis_physics(route: Mapping[str, Any], *, h_unit: float) -> dict[str, float]:
    response = float(route.get("response", 1.0))
    distance_to_h0_sign = float(route.get("distance_to_h0_sign", -1.0))
    scale = float(h_unit) * response * distance_to_h0_sign
    coeffs = {"a0": 0.0, "a1": 0.0, "a2": 0.0}
    for window in _route_windows(route):
        weight = float(window.get("weight", 1.0))
        probe = str(window.get("probe", route.get("probe", "SN")))
        s_p, c_p = _probe_weights(probe)
        basis = _window_basis_averages(window)
        coeffs["a0"] += scale * weight * basis["phi0"]
        coeffs["a1"] += scale * weight * basis["phi1"] * s_p
        coeffs["a2"] += scale * weight * basis["phi2"] * c_p

    if bool(route.get("absorb_a0_into_H_closed", False)):
        coeffs["a0"] = 0.0

    for bridge in _bridge_terms(route):
        weight = float(bridge.get("weight", 1.0))
        probe = str(bridge.get("probe", bridge.get("c_p_probe", "SN")))
        _, c_p = _probe_weights(probe)
        coeffs["a2"] += scale * weight * _bridge_phi2(bridge) * c_p

    return {name: float(value) for name, value in coeffs.items()}


def _route_windows(route: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    windows = route.get("distance_windows")
    if windows is None:
        windows = route.get("W_r")
    if windows is None:
        return []
    if isinstance(windows, Mapping):
        return [windows]
    return list(windows)


def _bridge_terms(route: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    bridges = route.get("bridge_terms", route.get("B_b", []))
    if isinstance(bridges, Mapping):
        return [bridges]
    return list(bridges)


def _window_basis_averages(window: Mapping[str, Any]) -> dict[str, float]:
    kind = str(window.get("type", "top_hat")).lower()
    if kind in {"delta", "point"}:
        z_eff = float(window["z_eff"])
        return {
            "phi0": 1.0,
            "phi1": z_eff / (1.0 + z_eff),
            "phi2": float(np.log1p(z_eff)),
        }
    if kind != "top_hat":
        raise ValueError(f"unsupported Hubble-route W_r type: {kind}")

    z0 = float(window["z_min"])
    z1 = float(window["z_max"])
    if z1 < z0:
        z0, z1 = z1, z0
    width = z1 - z0
    if width <= 0.0:
        z_eff = float(window.get("z_eff", z0))
        return {
            "phi0": 1.0,
            "phi1": z_eff / (1.0 + z_eff),
            "phi2": float(np.log1p(z_eff)),
        }

    integral_phi0 = width
    integral_phi1 = (z1 - np.log1p(z1)) - (z0 - np.log1p(z0))
    y0 = 1.0 + z0
    y1 = 1.0 + z1
    integral_phi2 = (y1 * np.log(y1) - y1) - (y0 * np.log(y0) - y0)
    normalization = str(window.get("normalization", "unit_area")).lower()
    divisor = width if normalization in {"unit_area", "average"} else 1.0
    return {
        "phi0": float(integral_phi0 / divisor),
        "phi1": float(integral_phi1 / divisor),
        "phi2": float(integral_phi2 / divisor),
    }


def _bridge_phi2(bridge: Mapping[str, Any]) -> float:
    basis = str(bridge.get("basis", "unit_calibration")).lower()
    if basis == "unit_calibration":
        return 1.0
    if "z_eff" in bridge:
        return float(np.log1p(float(bridge["z_eff"])))
    raise ValueError(f"unsupported Hubble-route bridge basis: {basis}")


def _probe_weights(probe: str) -> tuple[float, float]:
    key = probe.strip().lower().replace("-", "_").replace(" ", "_")
    aliases = {
        "rd": "bao",
        "r_d": "bao",
        "bao_radial": "bao",
        "bao_transverse": "bao",
        "supernova": "sn",
        "sne": "sn",
    }
    normalized = aliases.get(key, key)
    if normalized in {"lensing", "time_delay", "strong_lens", "siren", "standard_siren", "gw"}:
        return 1.0, 0.0
    if normalized in {"none", "null"}:
        return 0.0, 0.0
    return float(staging_weight(normalized)), float(calibration_weight(normalized))


def _xi_integral(
    z: np.ndarray,
    *,
    probe: str,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    parameters: Mapping[str, Any],
    w0_fld: float,
    wa_fld: float,
) -> np.ndarray:
    if z.size == 0:
        return np.asarray([], dtype=float)
    z_max = float(np.max(z))
    if z_max == 0.0:
        return np.zeros_like(z, dtype=float)
    grid = np.unique(np.concatenate((np.linspace(0.0, z_max, 4097, dtype=float), z)))
    background = evaluate_background(
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        H0=H0,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        z=tuple(grid.tolist()),
    )
    xi = evaluate_xi_cosmo(grid, None, probe, parameters)
    integrand = xi / (background.H / float(H0))
    cumulative = np.concatenate(([0.0], np.cumsum(0.5 * (integrand[1:] + integrand[:-1]) * np.diff(grid))))
    return np.interp(z, grid, cumulative)


def apply_observable_kernel(kernel_id: str, xi_value: float, context: Mapping[str, Any]) -> Any:
    """Apply K_L, K_M, K_G, K_S, or K_{r,ell} to a Xi_cosmo value."""
    if kernel_id == "K_L":
        return luminosity_kernel(parameters={"a0": xi_value, "a1": 0.0, "a2": 0.0}, **context)
    if kernel_id == "K_M":
        return transverse_bao_kernel(parameters={"a0": xi_value, "a1": 0.0, "a2": 0.0}, **context)
    raise NotImplementedError(f"{kernel_id} is not active in E1-B geometry.")
