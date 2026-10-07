"""DESI BAO and SN Gaussian likelihoods for the compressed E1 track."""

from __future__ import annotations

from functools import lru_cache

import numpy as np

from sbt_cosmo.io.datasets import (
    ProbeData,
    load_des_sn5yr,
    load_desi_dr2_bao,
    load_pantheon_plus,
    load_union3,
)
from sbt_cosmo.theory.background_compressed import evaluate_background


@lru_cache(maxsize=None)
def _probe(key: str) -> ProbeData:
    if key == "DESI_DR2_BAO":
        return load_desi_dr2_bao()
    if key == "PANTHEON_PLUS":
        return load_pantheon_plus()
    if key == "UNION3":
        return load_union3()
    if key == "DES_SN5YR":
        return load_des_sn5yr()
    raise KeyError(key)


@lru_cache(maxsize=8)
def _inverse_covariance(key: str) -> np.ndarray:
    return np.linalg.inv(np.asarray(_probe(key).covariance, dtype=np.float64))


def desi_dr2_bao_compressed_logp(
    omega_b: float,
    omega_cdm: float,
    H0: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> float:
    """Cobaya external log-likelihood for the DESI DR2 compressed BAO vector."""
    try:
        probe = _probe("DESI_DR2_BAO")
        z = np.asarray(probe.bins["z"], dtype=np.float64)
        observables = list(probe.bins["observable"])
        background = evaluate_background(
            omega_b=omega_b,
            omega_cdm=omega_cdm,
            H0=H0,
            w0_fld=w0_fld,
            wa_fld=wa_fld,
            z=tuple(z.tolist()),
        )
        prediction = np.empty_like(probe.data_vector, dtype=np.float64)
        for index, observable in enumerate(observables):
            if observable == "DM_over_rs":
                prediction[index] = background.D_M[index] / background.r_drag
            elif observable == "DH_over_rs":
                prediction[index] = background.D_H[index] / background.r_drag
            elif observable == "DV_over_rs":
                prediction[index] = background.D_V[index] / background.r_drag
            else:
                raise ValueError(f"unsupported DESI DR2 BAO observable: {observable}")
        chi2 = _chi2("DESI_DR2_BAO", prediction)
    except Exception:
        return -np.inf
    return -0.5 * chi2 if np.isfinite(chi2) else -np.inf


def pantheon_plus_compressed_logp(
    omega_b: float,
    omega_cdm: float,
    H0: float,
    sn_M: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> float:
    """Cobaya external log-likelihood for Pantheon+ distances."""
    return _sn_logp("PANTHEON_PLUS", omega_b=omega_b, omega_cdm=omega_cdm, H0=H0, sn_M=sn_M, w0_fld=w0_fld, wa_fld=wa_fld)


def union3_compressed_logp(
    omega_b: float,
    omega_cdm: float,
    H0: float,
    sn_M: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> float:
    """Cobaya external log-likelihood for Union3 distances."""
    return _sn_logp("UNION3", omega_b=omega_b, omega_cdm=omega_cdm, H0=H0, sn_M=sn_M, w0_fld=w0_fld, wa_fld=wa_fld)


def des_sn5yr_compressed_logp(
    omega_b: float,
    omega_cdm: float,
    H0: float,
    sn_M: float,
    w0_fld: float = -1.0,
    wa_fld: float = 0.0,
) -> float:
    """Cobaya external log-likelihood for DES-SN5YR distances."""
    return _sn_logp("DES_SN5YR", omega_b=omega_b, omega_cdm=omega_cdm, H0=H0, sn_M=sn_M, w0_fld=w0_fld, wa_fld=wa_fld)


def _sn_logp(
    key: str,
    *,
    omega_b: float,
    omega_cdm: float,
    H0: float,
    sn_M: float,
    w0_fld: float,
    wa_fld: float,
) -> float:
    try:
        probe = _probe(key)
        z = np.asarray(probe.bins.get("z_cmb", probe.bins.get("z_hd", probe.bins.get("z"))), dtype=np.float64)
        background = evaluate_background(
            omega_b=omega_b,
            omega_cdm=omega_cdm,
            H0=H0,
            w0_fld=w0_fld,
            wa_fld=wa_fld,
            z=tuple(z.tolist()),
        )
        chi2 = _chi2(key, background.mu + float(sn_M))
    except Exception:
        return -np.inf
    return -0.5 * chi2 if np.isfinite(chi2) else -np.inf


def _chi2(key: str, prediction: np.ndarray) -> float:
    probe = _probe(key)
    residual = np.asarray(probe.data_vector, dtype=np.float64) - np.asarray(prediction, dtype=np.float64)
    return float(residual @ _inverse_covariance(key) @ residual)

