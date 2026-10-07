"""Physical weak-lensing and CMB-lensing probe adapters for E5.

The adapters expose the native observable spaces used by the locked E5-v2
manifest: HSC-Y3 Fourier ``C_ell^EE``, KiDS-Legacy COSEBIs E-modes, and the
ACT+SPT+Planck CMB-lensing bandpowers. They are forward models, not fitted
templates; survey-specific limitations are reported by the reproduction
runner instead of being hidden by surrogate curves.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import Any

import numpy as np
from scipy.special import j0

from sbt_cosmo.growth.power import build_ccl_cosmology, omega_m
from sbt_cosmo.growth.projection import WeakLensingClEngine, angular_cl, build_tracer
from sbt_cosmo.growth.s8 import s8_readout

ROOT = Path(__file__).resolve().parents[2]


class ForwardModelUnavailable(RuntimeError):
    """Raised when a locked survey ingredient is unavailable."""


@dataclass(frozen=True)
class ProbePrediction:
    """Prediction plus the native data product it is meant to reproduce."""

    probe_id: str
    prediction: np.ndarray
    data: np.ndarray
    covariance: np.ndarray
    metadata: dict[str, Any]

    def chi2(self) -> float:
        """Return the native Gaussian chi-square."""
        delta = self.data - self.prediction
        return float(delta @ np.linalg.solve(self.covariance, delta))

    def chi2_per_dof(self, n_parameters: int = 0) -> float:
        """Return chi-square per degree of freedom."""
        dof = max(int(self.data.size) - int(n_parameters), 1)
        return self.chi2() / dof


class WeakLensingProbeAdapter:
    """Base class shared by concrete E5 weak-lensing adapters."""

    probe_id: str
    data_path: Path
    covariance_path: Path

    def data_vector(self) -> np.ndarray:
        """Return the tracked processed data vector."""
        return np.load(self.data_path)

    def covariance(self) -> np.ndarray:
        """Return the tracked processed covariance matrix."""
        return np.load(self.covariance_path)

    def model(self, theta: Mapping[str, Any]) -> np.ndarray:
        """Return the native observable prediction."""
        raise ForwardModelUnavailable(f"{type(self).__name__} does not define a native observable model")

    def predict(self, theta: Mapping[str, Any]) -> ProbePrediction:
        """Return prediction, data, covariance, and metadata."""
        return ProbePrediction(
            probe_id=self.probe_id,
            prediction=self.model(theta),
            data=self.data_vector(),
            covariance=self.covariance(),
            metadata=self.metadata(theta),
        )

    def loglike(self, theta: Mapping[str, Any]) -> float:
        """Return the native Gaussian log-likelihood."""
        return -0.5 * self.predict(theta).chi2()

    def metadata(self, theta: Mapping[str, Any]) -> dict[str, Any]:
        """Return basic cosmological readout metadata for a prediction."""
        om = omega_m(theta)
        sig8 = float(theta.get("sigma8", theta.get("sigma_8", 0.0)))
        if sig8 <= 0.0 and "S8" in theta:
            sig8 = float(theta["S8"]) / np.sqrt(om / 0.3)
        return {"omega_m": om, "sigma8": sig8, "S8": s8_readout(sig8, om) if sig8 > 0.0 else None}


@dataclass(frozen=True)
class HSCY3FourierProbe(WeakLensingProbeAdapter):
    """HSC-Y3 Fourier-space cosmic shear adapter."""

    nz_variant: str = "original"
    sacc_path: Path = ROOT / "data/raw/hsc_y3/hsc_y3_fourier_space_data_vector.sacc"
    data_path: Path = ROOT / "data/processed/hsc_y3/data_vector.npy"
    covariance_path: Path = ROOT / "data/processed/hsc_y3/covariance.npy"
    probe_id: str = "hsc_y3_origVSrecal"

    @cached_property
    def _sacc(self) -> dict[str, Any]:
        from astropy.io import fits

        with fits.open(self.sacc_path) as hdul:
            data = hdul["data:cl_ee"].data
            rows = [
                {
                    "tracer_0": str(row["tracer_0"]),
                    "tracer_1": str(row["tracer_1"]),
                    "ell": float(row["ell"]),
                    "window": int(row["window"]),
                    "window_ind": int(row["window_ind"]),
                }
                for row in data
            ]
            windows: dict[int, dict[str, np.ndarray]] = {}
            for hdu in hdul:
                if hdu.header.get("SACCCLSS") == "Bandpower" and "SACCNAME" in hdu.header:
                    windows[int(hdu.header["SACCNAME"])] = {
                        "ell": np.asarray(hdu.data["values"], dtype=np.float64),
                        "weights": np.asarray(hdu.data["weight"], dtype=np.float64),
                    }
        return {"rows": rows, "windows": windows}

    def _nz(self, theta: Mapping[str, Any]) -> tuple[np.ndarray, np.ndarray]:
        variant = str(theta.get("nz_variant", self.nz_variant)).lower()
        if variant in {"desi_recal", "desi-recal", "recal", "recalibrated"}:
            z = np.load(ROOT / "data/processed/hsc_y3_desi_recal/nz_recal_z.npy")
            nz = np.load(ROOT / "data/processed/hsc_y3_desi_recal/nz_recal.npy")
        elif variant == "original":
            z = np.load(ROOT / "data/processed/hsc_y3/nz_original_z.npy")
            nz = np.load(ROOT / "data/processed/hsc_y3/nz_original.npy")
        else:
            raise ValueError(f"Unknown HSC n(z) variant {variant!r}")
        dz = _as_vector(theta.get("dz", theta.get("photoz_dz", 0.0)), nz.shape[1])
        return z, np.column_stack([_shift_nz(z, nz[:, i], dz[i]) for i in range(nz.shape[1])])

    def model(self, theta: Mapping[str, Any]) -> np.ndarray:
        cosmo = build_ccl_cosmology(theta)
        z, nz = self._nz(theta)
        m = _as_vector(theta.get("m", theta.get("shear_m", 0.0)), nz.shape[1])
        tracer_configs = [{"type": "weak_lensing", "z": z, "nz": nz[:, i], **_ia_config_for_bin(theta, i, nz.shape[1])} for i in range(nz.shape[1])]
        engine = WeakLensingClEngine(cosmo, tracer_configs)
        pair_cache: dict[tuple[int, int, int], np.ndarray] = {}
        predicted: list[float] = []
        for row in self._sacc["rows"]:
            i = int(row["tracer_0"].split("_")[1])
            j = int(row["tracer_1"].split("_")[1])
            window_id = row["window"]
            key = (i, j, window_id)
            if key not in pair_cache:
                window = self._sacc["windows"][window_id]
                cl = engine.angular_cl(i, j, window["ell"])
                cl *= (1.0 + m[i]) * (1.0 + m[j])
                pair_cache[key] = cl @ window["weights"]
            predicted.append(float(pair_cache[key][row["window_ind"]]))
        return np.asarray(predicted, dtype=np.float64)

    def metadata(self, theta: Mapping[str, Any]) -> dict[str, Any]:
        meta = super().metadata(theta)
        meta.update(
            {
                "statistic": "cl_ee",
                "nz_variant": str(theta.get("nz_variant", self.nz_variant)),
                "ia": _ia_config(theta),
                "baryonic_effects": theta.get("baryonic_effects", None),
            }
        )
        return meta


@dataclass(frozen=True)
class CMBLensingProbe(WeakLensingProbeAdapter):
    """ACT+SPT+Planck CMB-lensing convergence bandpower adapter."""

    data_path: Path = ROOT / "data/processed/cmb_lensing/data_vector.npy"
    covariance_path: Path = ROOT / "data/processed/cmb_lensing/covariance.npy"
    probe_id: str = "cmblensing_act_spt_planck"

    @cached_property
    def _binning(self) -> dict[str, np.ndarray]:
        import sys
        import warnings

        package_root = ROOT / "data/raw/cmb_lensing/spt_act_likelihood"
        sys.path.insert(0, str(package_root))
        try:
            import act_dr6_spt_lenslike as apslike

            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                data = apslike.load_data("actplanckspt3g_baseline", lens_only=True, like_corrections=False)
        finally:
            try:
                sys.path.remove(str(package_root))
            except ValueError:
                pass
        return {
            "act": np.asarray(data["binmat_act"], dtype=np.float64),
            "planck": np.asarray(data["binmat_planck"], dtype=np.float64),
            "spt": np.asarray(data["binmat_spt"], dtype=np.float64),
        }

    def model(self, theta: Mapping[str, Any]) -> np.ndarray:
        cosmo = build_ccl_cosmology(theta)
        tracer = build_tracer(cosmo, {"type": "cmb_lensing", "z_source": theta.get("z_source", 1089.0)})
        ell = np.arange(0, 3102, dtype=np.float64)
        clkk = angular_cl(cosmo, tracer, tracer, ell)
        return np.concatenate(
            [
                self._binning["act"] @ clkk[: self._binning["act"].shape[1]],
                self._binning["planck"] @ clkk[: self._binning["planck"].shape[1]],
                self._binning["spt"] @ clkk[: self._binning["spt"].shape[1]],
            ]
        )

    def metadata(self, theta: Mapping[str, Any]) -> dict[str, Any]:
        meta = super().metadata(theta)
        meta.update({"statistic": "binned_C_L_kappakappa", "variant": "actplanckspt3g_baseline"})
        return meta


@dataclass(frozen=True)
class KiDSLegacyCOSEBIsProbe(WeakLensingProbeAdapter):
    """KiDS-Legacy COSEBIs adapter using official 2pt_stats filter tables."""

    data_path: Path = ROOT / "data/processed/kids_legacy/data_vector.npy"
    covariance_path: Path = ROOT / "data/processed/kids_legacy/covariance.npy"
    fits_path: Path = ROOT / "data/raw/kids_legacy/KiDS_Legacy_cosmic_shear_data_release/data/KiDS_Legacy_cosebis.fits"
    filter_root: Path = Path("/mnt/data-drive/sbt-de/src/2pt_stats/TLogsRootsAndNorms")
    theta_min_arcmin: float = 2.0
    theta_max_arcmin: float = 300.0
    n_modes: int = 6
    ell_min: float = 1.0
    ell_max: float = 1.0e5
    n_ell: int = 384
    probe_id: str = "kids_legacy_shear"

    @cached_property
    def _nz(self) -> tuple[np.ndarray, np.ndarray]:
        from astropy.io import fits

        with fits.open(self.fits_path) as hdul:
            table = hdul["NZ_SOURCE"].data
            z = np.asarray(table["Z_MID"], dtype=np.float64)
            nz = np.column_stack([np.asarray(table[f"BIN{i}"], dtype=np.float64) for i in range(1, 7)])
        return z, nz

    @cached_property
    def _wn(self) -> tuple[np.ndarray, np.ndarray]:
        root_file = self.filter_root / f"Root_{self.theta_min_arcmin:.2f}-{self.theta_max_arcmin:.2f}.table"
        norm_file = self.filter_root / f"Normalization_{self.theta_min_arcmin:.2f}-{self.theta_max_arcmin:.2f}.table"
        if not root_file.is_file() or not norm_file.is_file():
            raise ForwardModelUnavailable(
                "KiDS COSEBIs require the official 2pt_stats TLogsRootsAndNorms tables; "
                f"missing {root_file} or {norm_file}."
            )
        roots = _read_roots(root_file, self.n_modes)
        norms = _read_norms(norm_file, self.n_modes)
        ell = np.geomspace(self.ell_min, self.ell_max, self.n_ell)
        theta = np.geomspace(
            self.theta_min_arcmin * np.pi / (180.0 * 60.0),
            self.theta_max_arcmin * np.pi / (180.0 * 60.0),
            512,
        )
        log_theta = np.log(theta)
        zlog = np.log(theta / theta[0])
        bessel = j0(np.outer(ell, theta))
        wn = np.empty((self.n_modes, ell.size), dtype=np.float64)
        for mode in range(self.n_modes):
            t_n = np.full_like(theta, norms[mode])
            for root in roots[mode]:
                t_n *= zlog - root
            integrand = theta[None, :] ** 2 * t_n[None, :] * bessel
            wn[mode] = np.trapz(integrand, x=log_theta, axis=1)
        return ell, wn

    def model(self, theta: Mapping[str, Any]) -> np.ndarray:
        cosmo = build_ccl_cosmology(theta)
        z, nz = self._nz
        dz = _as_vector(theta.get("dz", theta.get("photoz_dz", 0.0)), nz.shape[1])
        nz = np.column_stack([_shift_nz(z, nz[:, i], dz[i]) for i in range(nz.shape[1])])
        m = _as_vector(theta.get("m", theta.get("shear_m", 0.0)), nz.shape[1])
        tracer_configs = [{"type": "weak_lensing", "z": z, "nz": nz[:, i], **_ia_config_for_bin(theta, i, nz.shape[1])} for i in range(nz.shape[1])]
        engine = WeakLensingClEngine(cosmo, tracer_configs)
        ell, wn = self._wn
        log_ell = np.log(ell)
        result: list[float] = []
        for i in range(nz.shape[1]):
            for j in range(i, nz.shape[1]):
                cl = engine.angular_cl(i, j, ell)
                cl *= (1.0 + m[i]) * (1.0 + m[j])
                for mode in range(self.n_modes):
                    integrand = ell**2 * wn[mode] * cl / (2.0 * np.pi)
                    result.append(float(np.trapz(integrand, x=log_ell)))
        return np.asarray(result, dtype=np.float64)

    def metadata(self, theta: Mapping[str, Any]) -> dict[str, Any]:
        meta = super().metadata(theta)
        meta.update(
            {
                "statistic": "COSEBIs_Emode",
                "theta_min_arcmin": self.theta_min_arcmin,
                "theta_max_arcmin": self.theta_max_arcmin,
                "n_modes": self.n_modes,
                "cosebis_path": "official maricool/2pt_stats TLogsRootsAndNorms tables",
            }
        )
        return meta


def build_weak_lensing_probe(config: Mapping[str, Any]) -> Any:
    """Build a KiDS, HSC, or CMB-lensing probe adapter."""
    probe_id = str(config.get("probe_id", config.get("id", config.get("family", "")))).lower()
    if probe_id in {"hsc_y3_origvsrecal", "hsc_y3", "wl_photoz_stage"}:
        return HSCY3FourierProbe(nz_variant=str(config.get("nz_variant", "original")))
    if probe_id in {"cmblensing_act_spt_planck", "cmb_lensing", "cmb_lensing_highz"}:
        return CMBLensingProbe()
    if probe_id in {"kids_legacy_shear", "kids_legacy", "wl_shear_cal"}:
        return KiDSLegacyCOSEBIsProbe()
    raise ValueError(f"Unknown weak-lensing probe config {probe_id!r}")


def amplitude_fit(data: np.ndarray, theory: np.ndarray, covariance: np.ndarray) -> dict[str, float]:
    """Best scalar amplitude ``A`` for ``data ~= A * theory`` under covariance."""
    data = np.asarray(data, dtype=np.float64)
    theory = np.asarray(theory, dtype=np.float64)
    covariance = np.asarray(covariance, dtype=np.float64)
    cinv_theory = np.linalg.solve(covariance, theory)
    denom = float(theory @ cinv_theory)
    if denom <= 0.0:
        raise ValueError("non-positive theory norm in amplitude fit")
    amplitude = float(theory @ np.linalg.solve(covariance, data) / denom)
    residual = data - amplitude * theory
    chi2 = float(residual @ np.linalg.solve(covariance, residual))
    sigma_amplitude = float(denom**-0.5)
    return {"amplitude": amplitude, "sigma_amplitude": sigma_amplitude, "chi2": chi2}


def _ia_config(theta: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "ia_model": str(theta.get("ia_model", theta.get("IA_model", "nla"))).lower(),
        "A_IA": float(theta.get("A_IA", theta.get("ia_A", theta.get("A1", 0.0)))),
        "eta_IA": float(theta.get("eta_IA", theta.get("ia_eta", theta.get("alpha1", 0.0)))),
        "z_pivot_IA": float(theta.get("z_pivot_IA", theta.get("z_piv", 0.62))),
        "A1": float(theta.get("A1", theta.get("A_IA", theta.get("ia_A", 0.0)))),
        "eta1": float(theta.get("eta1", theta.get("alpha1", theta.get("eta_IA", theta.get("ia_eta", 0.0))))),
        "A2": float(theta.get("A2", theta.get("A_2", 0.0))),
        "eta2": float(theta.get("eta2", theta.get("alpha2", 0.0))),
        "b_ta": float(theta.get("b_ta", theta.get("bias_ta", theta.get("bTA", 0.0)))),
    }


def _ia_config_for_bin(theta: Mapping[str, Any], index: int, n_bins: int) -> dict[str, Any]:
    cfg = _ia_config(theta)
    if "A_IA_bins" in theta or "ia_A_bins" in theta or "A1_bins" in theta:
        bins = _as_vector(theta.get("A_IA_bins", theta.get("ia_A_bins", theta.get("A1_bins"))), n_bins)
        cfg["A_IA"] = float(bins[index])
        cfg["A1"] = float(bins[index])
    if "eta_IA_bins" in theta or "eta1_bins" in theta:
        bins = _as_vector(theta.get("eta_IA_bins", theta.get("eta1_bins")), n_bins)
        cfg["eta_IA"] = float(bins[index])
        cfg["eta1"] = float(bins[index])
    return cfg


def _as_vector(value: Any, size: int) -> np.ndarray:
    arr = np.asarray(value, dtype=np.float64)
    if arr.ndim == 0:
        return np.full(size, float(arr), dtype=np.float64)
    if arr.shape != (size,):
        raise ValueError(f"expected scalar or length-{size} vector, got shape {arr.shape}")
    return arr


def _shift_nz(z: np.ndarray, nz: np.ndarray, dz: float) -> np.ndarray:
    shifted = np.interp(z - float(dz), z, nz, left=0.0, right=0.0)
    return np.clip(shifted, 0.0, None)


def _read_roots(path: Path, n_modes: int) -> list[np.ndarray]:
    rows: list[np.ndarray] = []
    with path.open() as fh:
        for line in fh:
            parts = [float(x) for x in line.split()]
            if not parts:
                continue
            mode = int(parts[0])
            if 1 <= mode <= n_modes:
                rows.append(np.asarray(parts[1 : mode + 2], dtype=np.float64))
            if len(rows) == n_modes:
                break
    if len(rows) != n_modes:
        raise ValueError(f"{path} did not contain {n_modes} COSEBIs root rows")
    return rows


def _read_norms(path: Path, n_modes: int) -> np.ndarray:
    values: list[float] = []
    with path.open() as fh:
        for line in fh:
            parts = [float(x) for x in line.split()]
            if len(parts) >= 2:
                values.append(parts[1])
            if len(values) == n_modes:
                break
    if len(values) != n_modes:
        raise ValueError(f"{path} did not contain {n_modes} COSEBIs normalization rows")
    return np.asarray(values, dtype=np.float64)
