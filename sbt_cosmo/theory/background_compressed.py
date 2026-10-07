"""Background distances for the compressed E1 track.

The default backend is a scipy/analytic flat-CPL calculation for fast
compressed-distance likelihoods.  The CLASS background-only backend remains
available as an oracle for validation via ``backend="classy"``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import numpy as np
from scipy import integrate

LIGHT_SPEED_KM_S = 299792.458
T_CMB_K = 2.7255
N_EFF_MASSLESS = 3.046
OMEGA_NU_MASSIVE_H2 = 0.06 / 93.14
OMEGA_GAMMA_H2 = 2.469e-5 * (T_CMB_K / 2.7255) ** 4
OMEGA_R_H2 = OMEGA_GAMMA_H2 * (1.0 + 0.22710731766 * N_EFF_MASSLESS)
# Sub-percent corrections align the fitting-formula recombination and sound
# horizons with the retained CLASS background oracle over the E1 compressed
# parameter range while avoiding per-evaluation CLASS calls.
Z_STAR_CLASS_CORRECTION = 0.99717
RS_REC_CLASS_CORRECTION = 1.00045
R_DRAG_CLASS_CORRECTION = 1.00139
SHIFT_R_CLASS_CORRECTION = 1.00030


@dataclass(frozen=True)
class BackgroundCompressed:
    """Background distances and CMB shift quantities for one cosmology."""

    z: np.ndarray
    H: np.ndarray
    D_C: np.ndarray
    D_M: np.ndarray
    D_H: np.ndarray
    D_V: np.ndarray
    D_L: np.ndarray
    mu: np.ndarray
    H0: float
    h: float
    omega_b: float
    omega_cdm: float
    omega_m: float
    w0_fld: float
    wa_fld: float
    r_drag: float
    z_drag: float
    z_star: float
    rs_rec: float
    R: float
    l_A: float


def evaluate_background(
    *,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
    z: Iterable[float] = (),
    backend: str = "scipy",
) -> BackgroundCompressed:
    """Evaluate distances and shift parameters for the compressed track."""
    omega_b = float(omega_b)
    omega_cdm = float(omega_cdm)
    H0 = float(H0)
    w0_fld = float(w0_fld)
    wa_fld = float(wa_fld)
    if not np.isfinite([omega_b, omega_cdm, H0, w0_fld, wa_fld]).all():
        raise ValueError("non-finite background parameter")
    if omega_b <= 0.0 or omega_cdm <= 0.0 or H0 <= 0.0:
        raise ValueError("non-positive physical density or H0")
    if w0_fld + wa_fld >= 0.0:
        raise ValueError("CLASS fluid requires w0_fld + wa_fld < 0 at early times")

    z_array = np.asarray(tuple(float(value) for value in z), dtype=np.float64)
    if np.any(z_array < 0.0):
        raise ValueError("redshifts must be non-negative")

    if backend == "scipy":
        return _evaluate_background_scipy(
            omega_b=omega_b,
            omega_cdm=omega_cdm,
            H0=H0,
            w0_fld=w0_fld,
            wa_fld=wa_fld,
            z_array=z_array,
        )
    if backend == "classy":
        return _evaluate_background_classy(
            omega_b=omega_b,
            omega_cdm=omega_cdm,
            H0=H0,
            w0_fld=w0_fld,
            wa_fld=wa_fld,
            z_array=z_array,
        )
    raise ValueError(f"unsupported compressed-background backend: {backend}")


def _evaluate_background_scipy(
    *,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float,
    wa_fld: float,
    z_array: np.ndarray,
) -> BackgroundCompressed:
    """Fast flat-CPL background using scipy integrals and standard fitting formulae."""
    h = H0 / 100.0
    omega_m_phys = omega_b + omega_cdm + OMEGA_NU_MASSIVE_H2
    omega_m = omega_m_phys / (h * h)
    omega_r = OMEGA_R_H2 / (h * h)
    omega_de = 1.0 - omega_m - omega_r
    if omega_de <= 0.0:
        raise ValueError("flat compressed background requires positive Omega_de")

    z_star = Z_STAR_CLASS_CORRECTION * _hu_sugiyama_z_star(omega_b=omega_b, omega_m_phys=omega_m_phys)
    z_drag = _eisenstein_hu_z_drag(omega_b=omega_b, omega_m_phys=omega_m_phys)
    rs_rec = RS_REC_CLASS_CORRECTION * _sound_horizon(
        omega_b=omega_b,
        H0=H0,
        omega_m=omega_m,
        omega_r=omega_r,
        omega_de=omega_de,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        z_start=z_star,
    )
    # Aubourg et al. 2015, arXiv:1411.1074, Eq. (16): calibrated rd fit.
    r_drag = R_DRAG_CLASS_CORRECTION * 55.154 * np.exp(-72.3 * (OMEGA_NU_MASSIVE_H2 + 0.0006) ** 2) / (
        omega_m_phys**0.25351 * omega_b**0.12807
    )

    z_eval = np.asarray(z_array, dtype=np.float64)
    z_for_distance = np.concatenate((z_eval, np.asarray([z_star], dtype=np.float64)))
    distances = _comoving_distance_grid(
        z_for_distance,
        H0=H0,
        omega_m=omega_m,
        omega_r=omega_r,
        omega_de=omega_de,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    if z_eval.size:
        D_C = distances[: z_eval.size]
        E_z = _e_z(z_eval, omega_m=omega_m, omega_r=omega_r, omega_de=omega_de, w0_fld=w0_fld, wa_fld=wa_fld)
        H = H0 * E_z
        D_H = LIGHT_SPEED_KM_S / H
        D_M = D_C.copy()
        D_V = np.cbrt(np.maximum(z_eval * D_M * D_M * D_H, 0.0))
        D_L = (1.0 + z_eval) * D_M
        mu = np.full_like(D_L, -np.inf, dtype=np.float64)
        positive = D_L > 0.0
        mu[positive] = 5.0 * np.log10(D_L[positive]) + 25.0
    else:
        H = D_C = D_M = D_H = D_V = D_L = mu = np.asarray([], dtype=np.float64)

    d_m_star = float(distances[-1])
    shift_R = SHIFT_R_CLASS_CORRECTION * np.sqrt(omega_m) * (H0 / LIGHT_SPEED_KM_S) * d_m_star
    acoustic_l = np.pi * d_m_star / rs_rec

    return BackgroundCompressed(
        z=z_eval,
        H=H,
        D_C=D_C,
        D_M=D_M,
        D_H=D_H,
        D_V=D_V,
        D_L=D_L,
        mu=mu,
        H0=H0,
        h=h,
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        omega_m=omega_m,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        r_drag=float(r_drag),
        z_drag=float(z_drag),
        z_star=float(z_star),
        rs_rec=float(rs_rec),
        R=float(shift_R),
        l_A=float(acoustic_l),
    )


def _evaluate_background_classy(
    *,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float,
    wa_fld: float,
    z_array: np.ndarray,
) -> BackgroundCompressed:
    """Evaluate CLASS in background-only mode for oracle validation."""
    try:
        from classy import Class
    except ImportError as exc:
        raise ImportError(
            "The compressed audit path uses backend='scipy' and does not require classy. "
            "Install classy only when requesting backend='classy' oracle validation."
        ) from exc

    cosmo = Class()
    params = {
        "output": "",
        "h": H0 / 100.0,
        "omega_b": omega_b,
        "omega_cdm": omega_cdm,
        "N_ncdm": 1,
        "N_ur": 2.0328,
        "m_ncdm": 0.06,
        "T_cmb": T_CMB_K,
    }
    if abs(w0_fld + 1.0) > 1.0e-14 or abs(wa_fld) > 1.0e-14:
        params.update({"Omega_Lambda": 0.0, "w0_fld": w0_fld, "wa_fld": wa_fld, "use_ppf": "yes"})
    cosmo.set(params)
    try:
        cosmo.compute()
        derived = cosmo.get_current_derived_parameters(["z_rec", "rs_rec", "z_d"])
        z_star = float(derived["z_rec"])
        rs_rec = float(derived["rs_rec"])
        z_drag = float(derived["z_d"])
        r_drag = float(cosmo.rs_drag())
        omega_m = float(cosmo.Omega_m())

        if z_array.size:
            H_over_c = np.asarray([cosmo.Hubble(float(redshift)) for redshift in z_array], dtype=np.float64)
            H = LIGHT_SPEED_KM_S * H_over_c
            D_H = 1.0 / H_over_c
            D_A = np.asarray([cosmo.angular_distance(float(redshift)) for redshift in z_array], dtype=np.float64)
            D_M = (1.0 + z_array) * D_A
            D_C = D_M.copy()
            D_V = np.cbrt(np.maximum(z_array * D_M * D_M * D_H, 0.0))
            D_L = (1.0 + z_array) * D_M
            mu = 5.0 * np.log10(D_L) + 25.0
        else:
            H = D_C = D_M = D_H = D_V = D_L = mu = np.asarray([], dtype=np.float64)

        d_m_star = (1.0 + z_star) * float(cosmo.angular_distance(z_star))
        shift_R = np.sqrt(omega_m) * (H0 / LIGHT_SPEED_KM_S) * d_m_star
        acoustic_l = np.pi * d_m_star / rs_rec
    finally:
        cosmo.struct_cleanup()
        cosmo.empty()

    return BackgroundCompressed(
        z=z_array,
        H=H,
        D_C=D_C,
        D_M=D_M,
        D_H=D_H,
        D_V=D_V,
        D_L=D_L,
        mu=mu,
        H0=H0,
        h=H0 / 100.0,
        omega_b=omega_b,
        omega_cdm=omega_cdm,
        omega_m=omega_m,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
        r_drag=r_drag,
        z_drag=z_drag,
        z_star=z_star,
        rs_rec=rs_rec,
        R=float(shift_R),
        l_A=float(acoustic_l),
    )


def _e_z(
    z: np.ndarray | float,
    *,
    omega_m: float,
    omega_r: float,
    omega_de: float,
    w0_fld: float,
    wa_fld: float,
) -> np.ndarray:
    redshift = np.asarray(z, dtype=np.float64)
    one_plus_z = 1.0 + redshift
    dark_energy = omega_de * one_plus_z ** (3.0 * (1.0 + w0_fld + wa_fld)) * np.exp(
        -3.0 * wa_fld * redshift / one_plus_z
    )
    e2 = omega_m * one_plus_z**3 + omega_r * one_plus_z**4 + dark_energy
    if np.any(e2 <= 0.0) or not np.all(np.isfinite(e2)):
        raise ValueError("non-positive or non-finite E(z)^2")
    return np.sqrt(e2)


def _comoving_distance_grid(
    z_values: np.ndarray,
    *,
    H0: float,
    omega_m: float,
    omega_r: float,
    omega_de: float,
    w0_fld: float,
    wa_fld: float,
) -> np.ndarray:
    if z_values.size == 0:
        return np.asarray([], dtype=np.float64)
    z_values = np.asarray(z_values, dtype=np.float64)
    z_max = float(np.max(z_values))
    if z_max == 0.0:
        return np.zeros_like(z_values, dtype=np.float64)
    low_limit = min(10.0, z_max)
    low_grid = np.linspace(0.0, low_limit, 4097, dtype=np.float64)
    if z_max > low_limit:
        high_grid = np.geomspace(1.0 + low_limit, 1.0 + z_max, 4097, dtype=np.float64) - 1.0
        base_grid = np.unique(np.concatenate((low_grid, high_grid, z_values)))
    else:
        base_grid = np.unique(np.concatenate((low_grid, z_values)))
    integrand = 1.0 / _e_z(
        base_grid,
        omega_m=omega_m,
        omega_r=omega_r,
        omega_de=omega_de,
        w0_fld=w0_fld,
        wa_fld=wa_fld,
    )
    cumulative = integrate.cumulative_trapezoid(integrand, base_grid, initial=0.0)
    return (LIGHT_SPEED_KM_S / H0) * np.interp(z_values, base_grid, cumulative)


def _eisenstein_hu_z_drag(*, omega_b: float, omega_m_phys: float) -> float:
    # Eisenstein & Hu 1998, ApJ 496, 605, Eqs. (4)-(6).
    b1 = 0.313 * omega_m_phys ** (-0.419) * (1.0 + 0.607 * omega_m_phys**0.674)
    b2 = 0.238 * omega_m_phys**0.223
    return float(
        1291.0
        * omega_m_phys**0.251
        / (1.0 + 0.659 * omega_m_phys**0.828)
        * (1.0 + b1 * omega_b**b2)
    )


def _hu_sugiyama_z_star(*, omega_b: float, omega_m_phys: float) -> float:
    # Hu & Sugiyama 1996 recombination fitting formula.
    g1 = 0.0783 * omega_b ** (-0.238) / (1.0 + 39.5 * omega_b**0.763)
    g2 = 0.560 / (1.0 + 21.1 * omega_b**1.81)
    return float(1048.0 * (1.0 + 0.00124 * omega_b ** (-0.738)) * (1.0 + g1 * omega_m_phys**g2))


def _sound_horizon(
    *,
    omega_b: float,
    H0: float,
    omega_m: float,
    omega_r: float,
    omega_de: float,
    w0_fld: float,
    wa_fld: float,
    z_start: float,
) -> float:
    a_start = 1.0 / (1.0 + float(z_start))

    def integrand(a_value: float) -> float:
        if a_value <= 0.0:
            return 0.0
        redshift = 1.0 / a_value - 1.0
        rb = 31500.0 * omega_b * (T_CMB_K / 2.7) ** (-4.0) * a_value
        e_val = float(
            _e_z(
                redshift,
                omega_m=omega_m,
                omega_r=omega_r,
                omega_de=omega_de,
                w0_fld=w0_fld,
                wa_fld=wa_fld,
            )
        )
        return 1.0 / (a_value * a_value * e_val * np.sqrt(3.0 * (1.0 + rb)))

    value, _ = integrate.quad(integrand, 0.0, a_start, epsabs=0.0, epsrel=1.0e-7, limit=200)
    return float((LIGHT_SPEED_KM_S / H0) * value)


def omega_m_approx(*, omega_b: float, omega_cdm: float, H0: float) -> float:
    """Return a fixed-neutrino approximation to Omega_m for derived-chain summaries."""
    h = float(H0) / 100.0
    return float((float(omega_b) + float(omega_cdm) + OMEGA_NU_MASSIVE_H2) / (h * h))
