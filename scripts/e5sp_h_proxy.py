#!/usr/bin/env python3
"""E5-SP Phase B: compute and freeze the H-proxy table only.

This script intentionally does not compute pi, Schur residuals, row-null
normalizers, carriers, model comparisons, bootstraps, LOFO, or controls.
"""

from __future__ import annotations

import csv
import hashlib
import os
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

for _key in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "CCL_NUM_THREADS",
):
    os.environ.setdefault(_key, "1")

import numpy as np

from sbt_cosmo.growth.power import build_ccl_cosmology
from sbt_cosmo.probes.weaklensing import build_weak_lensing_probe

RESULTS = ROOT / "results" / "E5SP"
H_TABLE = RESULTS / "H_proxy_table.csv"
H_SLACK = 0.05
N_POSTERIOR = int(os.environ.get("E5SP_H_NPOST", "64"))
CONTEXT_MODE = os.environ.get("E5SP_H_CONTEXT", "sample").lower()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_geometry_samples(n_samples: int) -> list[dict[str, float]]:
    path = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
    with path.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    data = np.loadtxt(path)
    cols = {name: i for i, name in enumerate(header)}
    weights = data[:, cols["weight"]] if "weight" in cols else np.ones(data.shape[0])
    weights = np.clip(weights.astype(np.float64), 0.0, None)
    weights = weights / weights.sum() if weights.sum() > 0.0 else np.full(data.shape[0], 1.0 / data.shape[0])
    if CONTEXT_MODE in {"mean", "posterior_mean"}:
        return [
            {
                "omega_b": float(np.sum(weights * data[:, cols["omega_b"]])),
                "omega_cdm": float(np.sum(weights * data[:, cols["omega_cdm"]])),
                "H0": float(np.sum(weights * data[:, cols["H0"]])),
                "w0_fld": float(np.sum(weights * data[:, cols["w0_fld"]])),
                "wa_fld": float(np.sum(weights * data[:, cols["wa_fld"]])),
                "n_s": 0.965,
                "sigma8": 0.811,
                "m_nu": 0.06,
            }
        ]
    rng = np.random.default_rng(20260602)
    replace = n_samples > data.shape[0]
    indices = rng.choice(data.shape[0], size=n_samples, replace=replace, p=weights)
    samples = []
    for idx in indices:
        row = data[idx]
        samples.append(
            {
                "omega_b": float(row[cols["omega_b"]]),
                "omega_cdm": float(row[cols["omega_cdm"]]),
                "H0": float(row[cols["H0"]]),
                "w0_fld": float(row[cols["w0_fld"]]),
                "wa_fld": float(row[cols["wa_fld"]]),
                "n_s": 0.965,
                "sigma8": 0.811,
                "m_nu": 0.06,
            }
        )
    return samples


def source_mean_z(z: np.ndarray, nz: np.ndarray) -> float:
    total = np.sum(nz, axis=1) if nz.ndim == 2 else nz
    denom = float(np.trapz(total, z))
    return float(np.trapz(z * total, z) / denom)


def hsc_z_eff() -> float:
    z = np.load(ROOT / "data/processed/hsc_y3/nz_original_z.npy")
    nz = np.load(ROOT / "data/processed/hsc_y3/nz_original.npy")
    return 0.5 * source_mean_z(z, nz)


def kids_z_eff() -> float:
    probe = build_weak_lensing_probe({"probe_id": "kids_legacy_shear"})
    z, nz = probe._nz  # noqa: SLF001 - Phase-B shell window construction.
    return 0.5 * source_mean_z(z, nz)


def normalized_weights(values: np.ndarray) -> np.ndarray:
    w = np.asarray(values, dtype=np.float64)
    w = np.clip(w, 0.0, None)
    if w.sum() == 0.0:
        return np.full(w.size, 1.0 / w.size)
    return w / w.sum()


def build_geometry_contexts(samples: list[dict[str, float]]) -> list[Any]:
    import pyccl as ccl

    contexts = []
    for sample in samples:
        contexts.append({"cosmo": build_ccl_cosmology(sample), "ccl": ccl})
    return contexts


def h_from_window(contexts: list[Any], z_eff: float, L_values: np.ndarray, weights: np.ndarray) -> tuple[float, float, float]:
    L = np.asarray(L_values, dtype=np.float64)
    w = normalized_weights(weights)
    h_vals = []
    hp_vals = []
    k_vals = []
    a = 1.0 / (1.0 + float(z_eff))
    for ctx in contexts:
        cosmo = ctx["cosmo"]
        ccl = ctx["ccl"]
        chi = float(ccl.comoving_radial_distance(cosmo, a))
        k = (L + 0.5) / chi
        p_lin = np.asarray(ccl.linear_matter_power(cosmo, k, a), dtype=np.float64)
        p_nl = np.asarray(ccl.nonlin_matter_power(cosmo, k, a), dtype=np.float64)
        ratio = np.clip(p_nl / p_lin, 0.0, np.inf)
        h_vals.append(float(np.sum(w * np.maximum(np.log(ratio), 0.0))))
        hp_vals.append(float(np.sum(w * np.maximum(ratio - 1.0, 0.0) ** 2)))
        k_vals.append(float(np.sum(w * k)))
    return float(np.mean(h_vals)), float(np.mean(hp_vals)), float(np.mean(k_vals))


def kids_shells(contexts: list[Any]) -> list[dict[str, Any]]:
    probe = build_weak_lensing_probe({"probe_id": "kids_legacy_shear"})
    ell, wn = probe._wn  # noqa: SLF001 - frozen COSEBIs filter support.
    z_eff = kids_z_eff()
    rows = []
    for lo, hi in [(1, 2), (3, 4), (5, 6)]:
        filt = np.mean(np.abs(wn[lo - 1 : hi]), axis=0)
        H, Hp, k_eff = h_from_window(contexts, z_eff, ell, filt)
        L_eff = float(np.sum(normalized_weights(filt) * ell))
        rows.append(row("KiDS-Legacy", f"COSEBIs-{lo}-{hi}", H, Hp, "COSEBIs_abs_Wn", z_eff, k_eff, float(lo), float(hi), L_eff))
    return rows


def hsc_shells(contexts: list[Any]) -> list[dict[str, Any]]:
    z_eff = hsc_z_eff()
    rows = []
    for lo, hi in [(300, 600), (600, 1000), (1000, 1500), (1500, 1800)]:
        ell = np.linspace(float(lo), float(hi), 64)
        H, Hp, k_eff = h_from_window(contexts, z_eff, ell, np.ones_like(ell))
        rows.append(row("HSC-Y3", f"ell-{lo}-{hi}", H, Hp, "uniform_ell_band", z_eff, k_eff, float(lo), float(hi), float(np.mean(ell))))
    return rows


def cmb_shells(contexts: list[Any]) -> list[dict[str, Any]]:
    L = np.load(ROOT / "data/processed/cmb_lensing/bin_centers_L.npy")
    ordered = np.sort(np.asarray(L, dtype=np.float64))
    groups = np.array_split(ordered, 3)
    rows = []
    for label, group in zip(["CMB-L-low", "CMB-L-mid", "CMB-L-high"], groups, strict=True):
        H, Hp, k_eff = h_from_window(contexts, 2.0, group, np.ones_like(group))
        rows.append(row("CMB-lensing", label, H, Hp, "equal_count_L_eff_tertile", 2.0, k_eff, float(np.min(group)), float(np.max(group)), float(np.mean(group))))
    return rows


def row(family: str, shell: str, H: float, H_prime: float, window: str, z_eff: float, k_eff: float, L_min: float, L_max: float, L_eff: float) -> dict[str, Any]:
    return {
        "family": family,
        "shell": shell,
        "H": H,
        "H_prime": H_prime,
        "window": window,
        "z_eff": z_eff,
        "k_eff": k_eff,
        "L_min": L_min,
        "L_max": L_max,
        "L_eff": L_eff,
        "slack_label": "slack" if H <= H_SLACK else "binding",
    }


def write_table(rows: list[dict[str, Any]]) -> None:
    RESULTS.mkdir(parents=True, exist_ok=True)
    with H_TABLE.open("w", newline="") as fh:
        writer = csv.DictWriter(
            fh,
            fieldnames=["family", "shell", "H", "H_prime", "window", "z_eff", "k_eff", "L_min", "L_max", "L_eff", "slack_label"],
        )
        writer.writeheader()
        for item in rows:
            writer.writerow(item)


def census(rows: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for item in rows:
        fam = item["family"]
        out.setdefault(fam, {"slack": 0, "binding": 0})
        out[fam][item["slack_label"]] += 1
    return out


def main() -> None:
    samples = read_geometry_samples(N_POSTERIOR)
    contexts = build_geometry_contexts(samples)
    rows = [*kids_shells(contexts), *hsc_shells(contexts), *cmb_shells(contexts)]
    write_table(rows)
    table_hash = sha256_file(H_TABLE)
    manifest_hash = sha256_file(ROOT / "data/manifests/e5sp_shadowprice_inputs.json")
    counts = census(rows)
    stop_gate = all(v["slack"] >= 1 and v["binding"] >= 1 for v in counts.values())
    print(
        {
            "H_proxy_table": str(H_TABLE.relative_to(ROOT)),
            "H_proxy_table_sha256": table_hash,
            "manifest_sha256": manifest_hash,
            "N_geometry_posterior": N_POSTERIOR,
            "geometry_context_mode": CONTEXT_MODE,
            "N_geometry_contexts_used": len(samples),
            "census": counts,
            "stop_gate_phase_C_allowed": stop_gate,
            "verdict": "HALT_FOR_OWNER_REVIEW" if stop_gate else "characterization-only / not-decisive",
        }
    )


if __name__ == "__main__":
    main()
