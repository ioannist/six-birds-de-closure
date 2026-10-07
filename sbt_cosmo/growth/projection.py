"""Limber projections for weak-lensing and CMB-lensing observables."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from functools import cached_property
from typing import Any

import numpy as np

from sbt_cosmo.growth.power import build_ccl_cosmology


def limber_projection(config: Mapping[str, Any]) -> np.ndarray:
    """Project a configured pair of tracers into an angular power spectrum.

    Expected keys are ``parameters`` (or ``cosmology``), ``ell``, ``tracer_1``
    and ``tracer_2``.  Tracer configs support ``{"type": "weak_lensing",
    "z": ..., "nz": ...}`` and ``{"type": "cmb_lensing"}``.  If a
    ``window`` matrix is supplied, the projected spectrum is binned by
    ``window.T @ C_ell`` for SACC-style bandpower windows.
    """
    ell = np.asarray(config["ell"], dtype=np.float64)
    if ell.ndim != 1:
        raise ValueError("ell must be one-dimensional")
    cosmo = config.get("cosmology") or build_ccl_cosmology(config.get("parameters", {}))
    tracer_1 = build_tracer(cosmo, config["tracer_1"])
    tracer_2 = build_tracer(cosmo, config.get("tracer_2", config["tracer_1"]))
    cl = angular_cl(cosmo, tracer_1, tracer_2, ell)
    if "window" in config and config["window"] is not None:
        return apply_bandpower_window(cl, config["window"])
    return cl


def build_tracer(cosmo: Any, config: Mapping[str, Any]) -> Any:
    """Build a pyccl tracer from a small repository config dictionary."""
    tracer_type = str(config.get("type", "weak_lensing")).lower()
    ccl = _ccl()
    if tracer_type in {"weak_lensing", "wl", "shear"}:
        z = np.asarray(config["z"], dtype=np.float64)
        nz = np.asarray(config["nz"], dtype=np.float64)
        if z.shape != nz.shape:
            raise ValueError("weak-lensing z and nz arrays must have the same shape")
        ia_bias = _ia_bias(config, z)
        return ccl.WeakLensingTracer(
            cosmo,
            dndz=(z, np.clip(nz, 0.0, None)),
            ia_bias=ia_bias,
            use_A_ia=bool(config.get("use_A_ia", True)),
            n_samples=int(config.get("n_samples", 256)),
        )
    if tracer_type in {"cmb_lensing", "cmblensing", "cmbkappa"}:
        return ccl.CMBLensingTracer(
            cosmo,
            z_source=float(config.get("z_source", 1089.0)),
            n_samples=int(config.get("n_samples", 256)),
        )
    raise ValueError(f"Unknown tracer type {tracer_type!r}")


class WeakLensingClEngine:
    """Compute weak-lensing C_ell values with selectable NLA or TATT IA.

    ``WeakLensingTracer`` natively supports L-NLA.  For TATT, this class
    combines the shear-shear term with perturbation-theory GI, IG, and II
    terms from ``pyccl.nl_pt`` using IA-only projection kernels.
    """

    def __init__(self, cosmo: Any, tracer_configs: Sequence[Mapping[str, Any]]):
        self.cosmo = cosmo
        self.configs = [dict(config) for config in tracer_configs]
        self.models = [_ia_model(config) for config in self.configs]
        self._combined: list[Any | None] = [None] * len(self.configs)
        self._shear_only: list[Any | None] = [None] * len(self.configs)
        self._ia_only: list[Any | None] = [None] * len(self.configs)
        self._pt_ia: list[Any | None] = [None] * len(self.configs)
        self._pk_mi: dict[int, Any] = {}
        self._pk_ii: dict[tuple[int, int], Any] = {}

    def angular_cl(self, i: int, j: int, ell: Sequence[float]) -> np.ndarray:
        """Return the model C_ell for a tomographic pair."""
        if self.models[i] != self.models[j]:
            raise ValueError("mixed IA models in one C_ell pair are not supported")
        if self.models[i] == "tatt":
            return self._tatt_cl(i, j, ell)
        return angular_cl(self.cosmo, self._combined_tracer(i), self._combined_tracer(j), ell)

    def _combined_tracer(self, i: int) -> Any:
        if self._combined[i] is None:
            self._combined[i] = build_tracer(self.cosmo, self.configs[i])
        return self._combined[i]

    def _shear_tracer(self, i: int) -> Any:
        if self._shear_only[i] is None:
            config = {**self.configs[i], "ia_model": "none"}
            self._shear_only[i] = build_tracer(self.cosmo, config)
        return self._shear_only[i]

    def _ia_tracer(self, i: int) -> Any:
        if self._ia_only[i] is None:
            ccl = _ccl()
            z = np.asarray(self.configs[i]["z"], dtype=np.float64)
            nz = np.asarray(self.configs[i]["nz"], dtype=np.float64)
            self._ia_only[i] = ccl.WeakLensingTracer(
                self.cosmo,
                dndz=(z, np.clip(nz, 0.0, None)),
                has_shear=False,
                ia_bias=(z, np.ones_like(z)),
                use_A_ia=False,
                n_samples=int(self.configs[i].get("n_samples", 256)),
            )
        return self._ia_only[i]

    def _pt_ia_tracer(self, i: int) -> Any:
        if self._pt_ia[i] is None:
            nl_pt = _ccl().nl_pt
            z = np.asarray(self.configs[i]["z"], dtype=np.float64)
            c1, cdelta, c2 = _tatt_c_biases(self.cosmo, self.configs[i], z)
            self._pt_ia[i] = nl_pt.PTIntrinsicAlignmentTracer(
                c1=(z, c1),
                c2=(z, c2),
                cdelta=(z, cdelta),
            )
        return self._pt_ia[i]

    @cached_property
    def _pt_calculator(self) -> Any:
        nl_pt = _ccl().nl_pt
        return nl_pt.EulerianPTCalculator(with_IA=True, cosmo=self.cosmo)

    @cached_property
    def _pt_matter(self) -> Any:
        return _ccl().nl_pt.PTMatterTracer()

    def _matter_ia_pk(self, i: int) -> Any:
        if i not in self._pk_mi:
            self._pk_mi[i] = self._pt_calculator.get_biased_pk2d(
                self._pt_matter,
                tracer2=self._pt_ia_tracer(i),
            )
        return self._pk_mi[i]

    def _ia_ia_pk(self, i: int, j: int) -> Any:
        key = (min(i, j), max(i, j))
        if key not in self._pk_ii:
            self._pk_ii[key] = self._pt_calculator.get_biased_pk2d(
                self._pt_ia_tracer(key[0]),
                tracer2=self._pt_ia_tracer(key[1]),
            )
        return self._pk_ii[key]

    def _tatt_cl(self, i: int, j: int, ell: Sequence[float]) -> np.ndarray:
        ccl = _ccl()
        ell_arr = np.asarray(ell, dtype=np.float64)
        shear_i = self._shear_tracer(i)
        shear_j = self._shear_tracer(j)
        ia_i = self._ia_tracer(i)
        ia_j = self._ia_tracer(j)
        gg = angular_cl(self.cosmo, shear_i, shear_j, ell_arr)
        gi = _pt_angular_cl(ccl, self.cosmo, shear_i, ia_j, ell_arr, self._matter_ia_pk(j))
        ig = _pt_angular_cl(ccl, self.cosmo, ia_i, shear_j, ell_arr, self._matter_ia_pk(i))
        ii = _pt_angular_cl(ccl, self.cosmo, ia_i, ia_j, ell_arr, self._ia_ia_pk(i, j))
        return gg + gi + ig + ii


def angular_cl(cosmo: Any, tracer_1: Any, tracer_2: Any, ell: Sequence[float]) -> np.ndarray:
    """Return finite ``C_ell`` values, setting undefined low multipoles to zero."""
    ell_arr = np.asarray(ell, dtype=np.float64)
    cl = np.zeros_like(ell_arr, dtype=np.float64)
    mask = ell_arr >= 2.0
    if np.any(mask):
        cl[mask] = np.asarray(_ccl().angular_cl(cosmo, tracer_1, tracer_2, ell_arr[mask]), dtype=np.float64)
    if not np.all(np.isfinite(cl)):
        raise FloatingPointError("CCL angular_cl returned non-finite values")
    return cl


def _finite_angular_cl(values: Sequence[float]) -> np.ndarray:
    cl = np.asarray(values, dtype=np.float64)
    if not np.all(np.isfinite(cl)):
        raise FloatingPointError("CCL angular_cl returned non-finite values")
    return cl


def _pt_angular_cl(ccl: Any, cosmo: Any, tracer_1: Any, tracer_2: Any, ell: np.ndarray, pk2d: Any) -> np.ndarray:
    cl = np.zeros_like(ell, dtype=np.float64)
    mask = ell >= 2.0
    if np.any(mask):
        cl[mask] = _finite_angular_cl(ccl.angular_cl(cosmo, tracer_1, tracer_2, ell[mask], p_of_k_a=pk2d))
    return cl


def apply_bandpower_window(cl: Sequence[float], window: Any) -> np.ndarray:
    """Apply a bandpower window to a spectrum.

    ``window`` may be a two-dimensional array with shape ``(n_ell, n_band)`` or
    a mapping containing a ``weights`` field with that shape.
    """
    weights = np.asarray(window.get("weights") if isinstance(window, Mapping) else window, dtype=np.float64)
    cl_arr = np.asarray(cl, dtype=np.float64)
    if weights.ndim != 2:
        raise ValueError("bandpower window must be two-dimensional")
    if weights.shape[0] != cl_arr.shape[0]:
        raise ValueError(f"window has {weights.shape[0]} ell rows but spectrum has {cl_arr.shape[0]}")
    return cl_arr @ weights


def _ia_bias(config: Mapping[str, Any], z: np.ndarray) -> tuple[np.ndarray, np.ndarray] | None:
    model = _ia_model(config)
    if model in {"none", "off", "no_ia", "zero"}:
        return None
    if model == "tatt":
        raise ValueError("TATT IA must be evaluated with WeakLensingClEngine, not build_tracer")
    if model not in {"nla", "lnla", "linear_nla"}:
        raise ValueError(f"Unknown IA model {model!r}")
    amplitude = float(config.get("A_IA", config.get("ia_A", config.get("A1", 0.0))))
    if amplitude == 0.0:
        return None
    eta = float(config.get("eta_IA", config.get("ia_eta", config.get("alpha1", 0.0))))
    pivot = float(config.get("z_pivot_IA", config.get("z_piv", 0.62)))
    bias = amplitude * ((1.0 + z) / (1.0 + pivot)) ** eta
    return z, bias


def _ia_model(config: Mapping[str, Any]) -> str:
    model = str(config.get("ia_model", config.get("IA_model", "nla"))).lower()
    aliases = {
        "off": "none",
        "no_ia": "none",
        "zero": "none",
        "lnla": "nla",
        "linear_nla": "nla",
    }
    return aliases.get(model, model)


def _tatt_c_biases(cosmo: Any, config: Mapping[str, Any], z: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    nl_pt = _ccl().nl_pt
    pivot = float(config.get("z_pivot_IA", config.get("z_piv", 0.62)))
    a1 = float(config.get("A1", config.get("A_IA", config.get("ia_A", 0.0))))
    eta1 = float(config.get("eta1", config.get("alpha1", config.get("eta_IA", config.get("ia_eta", 0.0)))))
    a2 = float(config.get("A2", config.get("A_2", 0.0)))
    eta2 = float(config.get("eta2", config.get("alpha2", 0.0)))
    b_ta = float(config.get("b_ta", config.get("bias_ta", config.get("bTA", 0.0))))
    a1_z = a1 * ((1.0 + z) / (1.0 + pivot)) ** eta1
    a2_z = a2 * ((1.0 + z) / (1.0 + pivot)) ** eta2
    a1delta_z = b_ta * a1_z
    c1, cdelta, c2 = nl_pt.translate_IA_norm(
        cosmo,
        z=z,
        a1=a1_z,
        a1delta=a1delta_z,
        a2=a2_z,
        Om_m2_for_c2=bool(config.get("Om_m2_for_c2", False)),
        Om_m_fid=float(config.get("Om_m_fid", 0.3)),
    )
    return np.asarray(c1, dtype=np.float64), np.asarray(cdelta, dtype=np.float64), np.asarray(c2, dtype=np.float64)


def _ccl() -> Any:
    import pyccl as ccl

    return ccl
