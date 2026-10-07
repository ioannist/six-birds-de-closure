#!/usr/bin/env python3
"""Path C0 full-shape H-support feasibility preflight.

This script computes only the heterogeneity proxy H for candidate galaxy
full-shape k-shells. It does not compute pi, Schur carriers, row nulls,
model comparisons, or any decisive certificate.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
from pathlib import Path
from typing import Any

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")
os.environ.setdefault("VECLIB_MAXIMUM_THREADS", "1")
os.environ.setdefault("CCL_NUM_THREADS", "1")

import numpy as np

from sbt_cosmo.growth.power import build_ccl_cosmology

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/E5SP/pathC0_feasibility"
CHAIN = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
PLAN_AGENT_PROVENANCE = ROOT / "results/provenance/decommissioned_plan_agent_sources.json"
H_SLACK = 0.05
H_STRONG = 0.30
K_SHELLS = [(0.01, 0.05), (0.05, 0.10), (0.10, 0.15), (0.15, 0.20), (0.20, 0.30)]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def provenance_sha256(entry: str) -> str:
    data = json.loads(PLAN_AGENT_PROVENANCE.read_text(encoding="utf-8"))
    return str(data["entries"][entry]["sha256"])


def posterior_mean_theta() -> dict[str, float]:
    with CHAIN.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    data = np.loadtxt(CHAIN, comments="#")
    cols = {name: i for i, name in enumerate(header)}
    weights = data[:, cols["weight"]] if "weight" in cols else np.ones(data.shape[0])
    weights = np.clip(weights.astype(np.float64), 0.0, None)
    weights = weights / weights.sum()
    return {
        "omega_b": float(np.sum(weights * data[:, cols["omega_b"]])),
        "omega_cdm": float(np.sum(weights * data[:, cols["omega_cdm"]])),
        "H0": float(np.sum(weights * data[:, cols["H0"]])),
        "w0_fld": float(np.sum(weights * data[:, cols["w0_fld"]])),
        "wa_fld": float(np.sum(weights * data[:, cols["wa_fld"]])),
        "sigma8": 0.811,
        "n_s": 0.965,
        "m_nu": 0.06,
    }


def candidates() -> list[dict[str, Any]]:
    return [
        {
            "family": "BOSS_DR12_full_shape",
            "tracer": "LOWZ_z0.38",
            "z_eff": 0.38,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.15, 0.20],
            "source": "BOSS DR12 Fourier-space analysis / Beutler et al. 2017, zeff={0.38,0.51,0.61}",
        },
        {
            "family": "BOSS_DR12_full_shape",
            "tracer": "CMASS_mid_z0.51",
            "z_eff": 0.51,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.15, 0.20],
            "source": "BOSS DR12 Fourier-space analysis / Beutler et al. 2017, zeff={0.38,0.51,0.61}",
        },
        {
            "family": "BOSS_DR12_full_shape",
            "tracer": "CMASS_high_z0.61",
            "z_eff": 0.61,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.15, 0.20],
            "source": "BOSS DR12 Fourier-space analysis / Beutler et al. 2017, zeff={0.38,0.51,0.61}",
        },
        {
            "family": "DESI_DR1_full_shape",
            "tracer": "BGS",
            "z_eff": 0.295,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.20],
            "source": "DESI 2024 V Full-Shape Table 1 / DESI DR1 full-shape public page",
        },
        {
            "family": "DESI_DR1_full_shape",
            "tracer": "LRG1",
            "z_eff": 0.510,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.20],
            "source": "DESI 2024 V Full-Shape Table 1 / DESI DR1 full-shape public page",
        },
        {
            "family": "DESI_DR1_full_shape",
            "tracer": "LRG2",
            "z_eff": 0.706,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.20],
            "source": "DESI 2024 V Full-Shape Table 1 / DESI DR1 full-shape public page",
        },
        {
            "family": "DESI_DR1_full_shape",
            "tracer": "LRG3",
            "z_eff": 0.930,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.20],
            "source": "DESI 2024 V Full-Shape Table 1 / DESI DR1 full-shape public page",
        },
        {
            "family": "DESI_DR1_full_shape",
            "tracer": "ELG2",
            "z_eff": 1.317,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.20],
            "source": "DESI 2024 V Full-Shape Table 1 / DESI DR1 full-shape public page",
        },
        {
            "family": "DESI_DR1_full_shape",
            "tracer": "QSO",
            "z_eff": 1.491,
            "realistic_kmax": 0.20,
            "kmax_sensitivity": [0.20],
            "source": "DESI 2024 V Full-Shape Table 1 / DESI DR1 full-shape public page",
        },
    ]


def normalized_weights(k: np.ndarray, mode: str) -> np.ndarray:
    if mode == "flat":
        w = np.ones_like(k)
    elif mode in {"k2", "k^2"}:
        w = k**2
    else:
        raise ValueError(f"unknown window mode {mode!r}")
    return w / np.sum(w)


def h_shell(ccl: Any, cosmo: Any, h: float, z_eff: float, k_min_hmpc: float, k_max_hmpc: float, window: str) -> tuple[float, float, float]:
    k_h = np.linspace(k_min_hmpc, k_max_hmpc, 192)
    weights = normalized_weights(k_h, window)
    k_mpc = k_h * h
    a = 1.0 / (1.0 + z_eff)
    p_lin = np.asarray(ccl.linear_matter_power(cosmo, k_mpc, a), dtype=np.float64)
    p_nl = np.asarray(ccl.nonlin_matter_power(cosmo, k_mpc, a), dtype=np.float64)
    ratio = np.clip(p_nl / p_lin, 0.0, np.inf)
    H = float(np.sum(weights * np.maximum(np.log(ratio), 0.0)))
    Hp = float(np.sum(weights * np.maximum(ratio - 1.0, 0.0) ** 2))
    k_eff = float(np.sum(weights * k_h))
    return H, Hp, k_eff


def point_h_curve(ccl: Any, cosmo: Any, h: float, z_eff: float) -> tuple[np.ndarray, np.ndarray]:
    k_h = np.linspace(0.005, 0.35, 512)
    k_mpc = k_h * h
    a = 1.0 / (1.0 + z_eff)
    p_lin = np.asarray(ccl.linear_matter_power(cosmo, k_mpc, a), dtype=np.float64)
    p_nl = np.asarray(ccl.nonlin_matter_power(cosmo, k_mpc, a), dtype=np.float64)
    H = np.maximum(np.log(np.clip(p_nl / p_lin, 1e-300, np.inf)), 0.0)
    return k_h, H


def crossing_k(k: np.ndarray, H: np.ndarray, threshold: float) -> float | None:
    above = H >= threshold
    if not np.any(above):
        return None
    first = int(np.argmax(above))
    if first == 0:
        return float(k[0])
    k0, k1 = k[first - 1], k[first]
    h0, h1 = H[first - 1], H[first]
    if h1 == h0:
        return float(k1)
    return float(k0 + (threshold - h0) * (k1 - k0) / (h1 - h0))


def label_for_h(H: float) -> str:
    if H <= H_SLACK:
        return "slack"
    if H >= H_STRONG:
        return "strong-binding"
    return "mild"


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    import pyccl as ccl

    window = os.environ.get("E5SP_PATHC0_WINDOW", "flat").lower()
    theta = posterior_mean_theta()
    h = theta["H0"] / 100.0
    cosmo = build_ccl_cosmology(theta)
    rows: list[dict[str, Any]] = []
    crossings: list[dict[str, Any]] = []
    for candidate in candidates():
        k_curve, h_curve = point_h_curve(ccl, cosmo, h, candidate["z_eff"])
        k_005 = crossing_k(k_curve, h_curve, H_SLACK)
        k_030 = crossing_k(k_curve, h_curve, H_STRONG)
        for k_min, k_max in K_SHELLS:
            H, Hp, k_eff = h_shell(ccl, cosmo, h, candidate["z_eff"], k_min, k_max, window)
            within_real_kmax = k_max <= candidate["realistic_kmax"] + 1e-12
            rows.append(
                {
                    "family": candidate["family"],
                    "tracer": candidate["tracer"],
                    "z_eff": f"{candidate['z_eff']:.6f}",
                    "k_min": f"{k_min:.6f}",
                    "k_max": f"{k_max:.6f}",
                    "k_eff": f"{k_eff:.6f}",
                    "H": f"{H:.12e}",
                    "H_prime": f"{Hp:.12e}",
                    "window": f"{window}_k_hmpc",
                    "label": label_for_h(H),
                    "within_realistic_kmax": within_real_kmax,
                    "source": candidate["source"],
                }
            )
        crossings.append(
            {
                "family": candidate["family"],
                "tracer": candidate["tracer"],
                "z_eff": f"{candidate['z_eff']:.6f}",
                "k_cross_H_0.05": "" if k_005 is None else f"{k_005:.6f}",
                "k_cross_H_0.30": "" if k_030 is None else f"{k_030:.6f}",
                "realistic_kmax": f"{candidate['realistic_kmax']:.6f}",
                "reaches_strong_by_realistic_kmax": bool(k_030 is not None and k_030 <= candidate["realistic_kmax"]),
                "source": candidate["source"],
            }
        )
    write_csv(OUT / "H_fullshape_feasibility.csv", rows)
    write_csv(OUT / "H_crossings.csv", crossings)

    verdicts: dict[str, dict[str, Any]] = {}
    for family in sorted({row["family"] for row in rows}):
        fam_rows = [row for row in rows if row["family"] == family and row["within_realistic_kmax"]]
        has_slack = any(row["label"] == "slack" for row in fam_rows)
        has_strong = any(row["label"] == "strong-binding" for row in fam_rows)
        has_mild = any(row["label"] == "mild" for row in fam_rows)
        if has_slack and has_strong:
            verdict = "PASS"
        elif has_slack and has_mild:
            verdict = "MILD-ONLY"
        else:
            verdict = "FAIL"
        verdicts[family] = {
            "verdict": verdict,
            "has_slack": has_slack,
            "has_mild": has_mild,
            "has_strong_binding": has_strong,
            "realistic_kmax_rule": "only shells with k_max <= realistic_kmax enter this verdict",
        }

    overall_passes = [family for family, item in verdicts.items() if item["verdict"] == "PASS"]
    summary = {
        "status": "Path C0 H-only feasibility / power preflight -- NOT pi, NOT decisive, NOT promotable",
        "geometry_context": "posterior_mean",
        "hard_coded_growth_params": {"sigma8": theta["sigma8"], "n_s": theta["n_s"], "m_nu": theta["m_nu"]},
        "window": f"{window}_over_k_hmpc",
        "thresholds": {"slack_H_le": H_SLACK, "strong_binding_H_ge": H_STRONG},
        "theta_posterior_mean": theta,
        "source_hashes": {
            "results/provenance/decommissioned_plan_agent_sources.json": sha256(PLAN_AGENT_PROVENANCE),
            "provenance:e5sp_pathc_ruling": provenance_sha256("e5sp_pathc_ruling"),
            "script": sha256(Path(__file__)),
        },
        "citations": {
            "BOSS_DR12": "Beutler et al. 2017 / BOSS DR12 Fourier-space analysis, effective redshifts 0.38, 0.51, 0.61.",
            "DESI_DR1": "DESI 2024 V Full-Shape Table 1 and DESI DR1 public full-shape page, effective redshifts BGS 0.295, LRG1 0.510, LRG2 0.706, LRG3/LRG+ELG 0.930, ELG2 1.317, QSO 1.491.",
        },
        "family_verdicts": verdicts,
        "overall_C0_H_verdict": "PASS" if overall_passes else "NO_FULLSHAPE_FAMILY_REACHES_STRONG_BINDING_WITHIN_ASSUMED_KMAX",
        "families_passing": overall_passes,
        "outputs": {
            "H_fullshape_feasibility_csv": str((OUT / "H_fullshape_feasibility.csv").relative_to(ROOT)),
            "H_crossings_csv": str((OUT / "H_crossings.csv").relative_to(ROOT)),
        },
    }
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
