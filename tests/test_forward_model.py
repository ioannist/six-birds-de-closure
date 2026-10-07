"""Physical-forward smoke tests for the E5 CCL adapters."""

from __future__ import annotations

import os

import numpy as np

from sbt_cosmo.growth.power import build_ccl_cosmology, matter_power_spectrum, omega_m, sigma8
from sbt_cosmo.growth.projection import WeakLensingClEngine, limber_projection
from sbt_cosmo.growth.s8 import s8_readout
from sbt_cosmo.probes.weaklensing import amplitude_fit, build_weak_lensing_probe

for _key in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "CCL_NUM_THREADS",
):
    os.environ.setdefault(_key, "1")


FID = {"Omega_b": 0.049, "Omega_c": 0.265, "h": 0.67, "n_s": 0.965, "sigma8": 0.81, "m_nu": 0.06}


def test_s8_readout() -> None:
    assert np.isclose(s8_readout(0.8, 0.3), 0.8)


def test_matter_power_finite_positive() -> None:
    assert "1/Mpc" in (matter_power_spectrum.__doc__ or "")
    assert "(Mpc/h)^3" not in (matter_power_spectrum.__doc__ or "")
    pk = matter_power_spectrum([0.05, 0.1], 0.0, FID)
    assert pk.shape == (2,)
    assert np.all(np.isfinite(pk))
    assert np.all(pk > 0.0)
    assert np.isclose(sigma8(FID), 0.81, rtol=1e-10)
    assert omega_m(FID) > 0.31


def test_baryonic_effect_dictionary_is_physical_ccl() -> None:
    pk_dmo = matter_power_spectrum([0.5, 1.0], 0.2, {**FID, "baryonic_effects": "none"})
    pk_baryon = matter_power_spectrum(
        [0.5, 1.0],
        0.2,
        {
            **FID,
            "baryonic_effects": {"model": "schneider15", "log10Mc": 14.2, "eta_b": 0.6, "k_s": 55.0},
        },
    )
    assert pk_baryon.shape == pk_dmo.shape
    assert np.all(np.isfinite(pk_baryon))
    assert np.max(np.abs(pk_baryon - pk_dmo) / pk_dmo) > 1e-4


def test_limber_projection_toy_wl_shape() -> None:
    z = np.linspace(0.05, 2.0, 64)
    nz = z**2 * np.exp(-(z / 0.6) ** 1.5)
    ell = np.array([30.0, 100.0, 300.0])
    base = {
        "parameters": FID,
        "ell": ell,
        "tracer_1": {"type": "weak_lensing", "z": z, "nz": nz},
        "tracer_2": {"type": "weak_lensing", "z": z, "nz": nz},
    }
    cl = limber_projection(base)
    assert cl.shape == ell.shape
    assert np.all(np.isfinite(cl))
    cl_ia = limber_projection(
        {
            **base,
            "tracer_1": {"type": "weak_lensing", "z": z, "nz": nz, "ia_model": "nla", "A_IA": 1.0},
            "tracer_2": {"type": "weak_lensing", "z": z, "nz": nz, "ia_model": "nla", "A_IA": 1.0},
        }
    )
    assert cl_ia.shape == ell.shape
    assert np.all(np.isfinite(cl_ia))
    assert np.max(np.abs(cl_ia - cl) / np.maximum(np.abs(cl), 1e-30)) > 0.01


def test_tatt_projection_toy_wl_shape() -> None:
    z = np.linspace(0.05, 2.0, 64)
    nz = z**2 * np.exp(-(z / 0.6) ** 1.5)
    ell = np.array([30.0, 100.0, 300.0])
    cosmo = build_ccl_cosmology(FID)
    engine = WeakLensingClEngine(
        cosmo,
        [
            {
                "type": "weak_lensing",
                "z": z,
                "nz": nz,
                "ia_model": "tatt",
                "A1": 0.5,
                "eta1": 0.0,
                "A2": 0.4,
                "eta2": 0.0,
                "b_ta": 0.3,
            }
        ],
    )
    cl_tatt = engine.angular_cl(0, 0, ell)
    assert cl_tatt.shape == ell.shape
    assert np.all(np.isfinite(cl_tatt))


def test_probe_builders_and_amplitude_fit() -> None:
    assert build_weak_lensing_probe({"probe_id": "hsc_y3_origVSrecal"}).probe_id == "hsc_y3_origVSrecal"
    assert build_weak_lensing_probe({"probe_id": "cmblensing_act_spt_planck"}).probe_id == "cmblensing_act_spt_planck"
    assert build_weak_lensing_probe({"probe_id": "kids_legacy_shear"}).probe_id == "kids_legacy_shear"
    fit = amplitude_fit(np.array([2.0, 4.0]), np.array([1.0, 2.0]), np.eye(2))
    assert np.isclose(fit["amplitude"], 2.0)
    assert fit["chi2"] == 0.0
