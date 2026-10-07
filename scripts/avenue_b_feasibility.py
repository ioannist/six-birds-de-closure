#!/usr/bin/env python3
"""Avenue-B void/wall + ISW feasibility scan.

This runner computes only the H-proxy feasibility support. It does not compute
pi, Schur carriers, row-null normalizers, LOFO, model comparison, or controls.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
from pathlib import Path
from typing import Any

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

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/E5SP/avenueB_feasibility"
PLAN_AGENT_PROVENANCE = ROOT / "results/provenance/decommissioned_plan_agent_sources.json"
H_SLACK = 0.05
H_STRONG = 0.30
Z_EFF = 0.30
K_MIN = 0.01
K_MAX_RELIABLE = 0.20
N_K = 256
GROWTH_GAMMA = 0.55
SEED = 20260602


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def provenance_sha256(entry: str) -> str:
    data = json.loads(PLAN_AGENT_PROVENANCE.read_text(encoding="utf-8"))
    return str(data["entries"][entry]["sha256"])


def posterior_mean_geometry() -> dict[str, float]:
    path = ROOT / "runs/E1/E1C_C3_w0wa_dyn/chains/C3_w0wa_dyn.1.txt"
    with path.open() as fh:
        header = fh.readline().strip().lstrip("#").split()
    data = np.loadtxt(path)
    cols = {name: i for i, name in enumerate(header)}
    weights = data[:, cols["weight"]] if "weight" in cols else np.ones(data.shape[0])
    weights = np.clip(weights.astype(np.float64), 0.0, None)
    weights = weights / weights.sum() if weights.sum() > 0.0 else np.full(data.shape[0], 1.0 / data.shape[0])
    return {
        "omega_b": float(np.sum(weights * data[:, cols["omega_b"]])),
        "omega_cdm": float(np.sum(weights * data[:, cols["omega_cdm"]])),
        "H0": float(np.sum(weights * data[:, cols["H0"]])),
        "w0_fld": float(np.sum(weights * data[:, cols["w0_fld"]])),
        "wa_fld": float(np.sum(weights * data[:, cols["wa_fld"]])),
        "n_s": 0.965,
        "sigma8": 0.811,
        "m_nu": 0.06,
    }


def classify_h(value: float) -> str:
    if value <= H_SLACK:
        return "slack"
    if value >= H_STRONG:
        return "strong-binding"
    return "mild"


def env_growth_scale(delta: float) -> float:
    """Declared peak-background-style local growth proxy.

    The local fluctuation amplitude is rescaled as
    D_env/D = max(0.05, 1+delta)^gamma. This suppresses void growth and
    enhances wall growth without fitting to any target H threshold.
    """
    return float(max(0.05, 1.0 + delta) ** GROWTH_GAMMA)


def env_k_scale(delta: float) -> float:
    """Declared local length-scale compression proxy.

    Overdense regions are assigned a shorter local nonlinear length scale via
    k_env = k * max(0.05, 1+delta)^(1/3); voids are expanded accordingly.
    """
    return float(max(0.05, 1.0 + delta) ** (1.0 / 3.0))


def h_window(theta: dict[str, float], delta: float) -> tuple[float, float, float]:
    import pyccl as ccl

    scale_growth = env_growth_scale(delta)
    scale_k = env_k_scale(delta)
    local = dict(theta)
    local["sigma8"] = float(theta["sigma8"] * scale_growth)
    cosmo = build_ccl_cosmology(local)
    k = np.linspace(K_MIN, K_MAX_RELIABLE, N_K)
    k_env = k * scale_k
    a = 1.0 / (1.0 + Z_EFF)
    p_lin = np.asarray(ccl.linear_matter_power(cosmo, k_env, a), dtype=np.float64)
    p_nl = np.asarray(ccl.nonlin_matter_power(cosmo, k_env, a), dtype=np.float64)
    ratio = np.clip(p_nl / p_lin, 0.0, np.inf)
    weights = np.ones_like(k) / k.size
    H = float(np.sum(weights * np.maximum(np.log(ratio), 0.0)))
    Hp = float(np.sum(weights * np.maximum(ratio - 1.0, 0.0) ** 2))
    return H, Hp, float(np.sum(weights * k_env))


def density_rows() -> list[dict[str, Any]]:
    theta = posterior_mean_geometry()
    bins = [
        ("deep_void", -0.80),
        ("void", -0.50),
        ("underdense", -0.25),
        ("mean_density", 0.00),
        ("mild_wall", 0.50),
        ("wall", 1.00),
        ("dense_wall", 2.00),
    ]
    rows = []
    for label, delta in bins:
        H, Hp, k_eff = h_window(theta, delta)
        rows.append(
            {
                "density_environment": label,
                "delta": delta,
                "H": H,
                "H_prime": Hp,
                "k_eff": k_eff,
                "z_eff": Z_EFF,
                "k_min": K_MIN,
                "k_max": K_MAX_RELIABLE,
                "slack_mild_strong_label": classify_h(H),
                "growth_rescale": env_growth_scale(delta),
                "k_rescale": env_k_scale(delta),
                "proxy": "sigma8_env=sigma8*max(0.05,1+delta)^0.55; k_env=k*max(0.05,1+delta)^(1/3)",
            }
        )
    return rows


def write_csv(rows: list[dict[str, Any]]) -> Path:
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / "H_density_split.csv"
    with path.open("w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return path


def verdict_text(rows: list[dict[str, Any]], csv_path: Path) -> str:
    has_slack = any(row["slack_mild_strong_label"] == "slack" for row in rows)
    has_strong = any(row["slack_mild_strong_label"] == "strong-binding" for row in rows)
    if has_slack and has_strong:
        density_verdict = "PASS"
        density_reason = "the declared environment proxy spans slack to strong-binding within k<=0.2 at z_eff=0.30"
    elif has_slack:
        density_verdict = "MILD-ONLY"
        density_reason = "the declared environment proxy has a slack void regime but no strong-binding wall within k<=0.2"
    else:
        density_verdict = "FAIL"
        density_reason = "the declared environment proxy has no slack shell within k<=0.2"

    lines = [
        "# Avenue-B feasibility scan — NOT a detection",
        "",
        "Status: FEASIBILITY SCAN ONLY. No pi, Xi/Schur carrier, row-null normalizer, model comparison, LOFO, or controls were computed.",
        "",
        "## Density split",
        f"- Verdict: **{density_verdict}**.",
        f"- Reason: {density_reason}.",
        f"- Output table: `{csv_path.relative_to(ROOT)}`.",
        f"- H_slack={H_SLACK}; strong-binding threshold H>={H_STRONG}; z_eff={Z_EFF}; reliable k window=[{K_MIN},{K_MAX_RELIABLE}] h/Mpc proxy units.",
        "- Proxy: peak-background-style local growth rescaling `sigma8_env=sigma8*max(0.05,1+delta)^0.55` plus local scale compression/expansion `k_env=k*max(0.05,1+delta)^(1/3)`.",
        "- Disclosure: this is an approximate environment-conditioned nonlinearity proxy, not a public density-split data vector or covariance. It can de-risk support, not establish a closure observable.",
        "",
        "## ISW availability / signature",
        "- Public availability: feasible in principle via public Planck CMB temperature/lensing products and public LSS catalogues used in ISW cross-correlation work; this packet did not fetch or process ISW maps.",
        "- Signal-to-noise: existing ISW detections are low, typically a few sigma. Planck 2015 reported ISW-lensing bispectrum detection at about 3 sigma and similar combined LSS cross-correlation significance; RACS x Planck reports about 2.8 sigma.",
        "- ISW sources cited: Planck 2015 results XXI, arXiv:1502.01595; RACS x Planck ISW measurement, arXiv:2204.13436.",
        "- Closure distinguishability: ISW is on-target for late-time potential decay, but distinguishing a closure/late-time-potential-decay model from LambdaCDM requires a signed model for potential evolution and cross-correlation shape. With only few-sigma public ISW signals, this is feasible as a model-comparison follow-up, not a standalone decisive route.",
        "",
        "## Hashes",
        f"- `H_density_split.csv`: `{sha256(csv_path)}`",
        f"- `results/provenance/decommissioned_plan_agent_sources.json`: `{sha256(PLAN_AGENT_PROVENANCE)}`",
        f"- `provenance:de_avenues_map`: `{provenance_sha256('de_avenues_map')}`",
        f"- `results/E5SP/EMPIRICAL_BOUNDARY_RESULT.md`: `{sha256(ROOT / 'results/E5SP/EMPIRICAL_BOUNDARY_RESULT.md')}`",
        f"- script: `{sha256(Path(__file__))}`",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    rows = density_rows()
    csv_path = write_csv(rows)
    verdict_path = OUT / "verdict.md"
    verdict_path.write_text(verdict_text(rows, csv_path))
    print({"csv": str(csv_path.relative_to(ROOT)), "verdict": str(verdict_path.relative_to(ROOT)), "labels": {row["density_environment"]: row["slack_mild_strong_label"] for row in rows}})


if __name__ == "__main__":
    main()
