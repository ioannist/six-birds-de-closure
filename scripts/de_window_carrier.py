#!/usr/bin/env python3
"""Record-bearing lambda-window carrier.

This is a toy RUN-frame carrier in native units:
rho_m(a=1)=1 and 8*pi*G/3=1.  It intentionally does not contain any
observed cosmological value or matching target.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import os
import subprocess
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Iterable

import numpy as np
from scipy.integrate import solve_ivp


for _name in [
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
]:
    os.environ.setdefault(_name, "1")


REPO_ROOT = Path(__file__).resolve().parents[1]
OUTDIR = REPO_ROOT / "results" / "DE_window"
CONTROLDIR = OUTDIR / "controls"
SEEDS = list(range(1100, 1112))
LAMBDA_GRID = [
    -30.0,
    -10.0,
    -3.0,
    -1.0,
    -0.3,
    -0.1,
    -0.03,
    -0.01,
    -0.003,
    -0.001,
    -0.0003,
    -0.0001,
    -0.00003,
    -0.00001,
    0.0,
    0.00001,
    0.00003,
    0.0001,
    0.0003,
    0.001,
    0.003,
    0.01,
    0.03,
    0.1,
    0.3,
    1.0,
    3.0,
    10.0,
    30.0,
    100.0,
    300.0,
    1000.0,
]


@dataclass(frozen=True)
class CarrierConfig:
    n_patches: int = 64
    heterogeneity_s: float = 1.0e-3
    delta_c: float = 1.686
    a_init: float = 1.0e-3
    a_max: float = 20.0
    n_eval: int = 3000
    seed_pass_fraction: float = 0.8
    tag_probability: float = 0.5
    edge_factor_target: float = 3.0


@dataclass(frozen=True)
class GrowthSolution:
    """Growth on the expanding branch.

    Historical ``crunch_before_tmax`` means turnaround at or before ``a_max``.
    The declared toy rule erases records at that event. No contracting branch
    or elapsed-time crunch calculation is performed.
    """
    lam: float
    a: np.ndarray
    growth: np.ndarray
    crunch_before_tmax: bool
    integration_sane: bool
    reason: str


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_csv(path: Path, rows: list[dict[str, Any]], fieldnames: list[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if fieldnames is None:
        fieldnames = list(rows[0].keys()) if rows else []
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def h2_of_a(a: np.ndarray | float, lam: float) -> np.ndarray | float:
    return np.asarray(a) ** -3 + lam


def crunch_scale(lam: float) -> float | None:
    """Historical name for the turnaround scale H²=0, not the big-crunch epoch."""
    if lam >= 0:
        return None
    return (-1.0 / lam) ** (1.0 / 3.0)


def solve_growth(lam: float, cfg: CarrierConfig) -> GrowthSolution:
    a_turn = crunch_scale(lam)
    crunch_before_tmax = bool(a_turn is not None and a_turn <= cfg.a_max)
    if a_turn is not None:
        a_stop = min(cfg.a_max, a_turn * (1.0 - 1.0e-8))
    else:
        a_stop = cfg.a_max
    if a_stop <= cfg.a_init:
        return GrowthSolution(
            lam=lam,
            a=np.array([cfg.a_init]),
            growth=np.array([1.0]),
            crunch_before_tmax=crunch_before_tmax,
            integration_sane=False,
            reason="turnaround_before_initial_grid",
        )

    def rhs(a: float, y: np.ndarray) -> list[float]:
        h2 = a ** -3 + lam
        if h2 <= 0:
            return [0.0, 0.0]
        dlnh_da = -1.5 * a ** -4 / h2
        coeff = 3.0 / a + dlnh_da
        source = 1.5 * a ** -3 / (a * a * h2)
        return [float(y[1]), float(source * y[0] - coeff * y[1])]

    a_eval = np.geomspace(cfg.a_init, a_stop, cfg.n_eval)
    sol = solve_ivp(
        rhs,
        (cfg.a_init, a_stop),
        y0=[1.0, 1.0 / cfg.a_init],
        t_eval=a_eval,
        rtol=2.0e-8,
        atol=1.0e-10,
    )
    sane = bool(sol.success and np.all(np.isfinite(sol.y[0])) and np.all(sol.y[0] > 0))
    reason = "ok" if sane else f"solve_ivp_failed:{sol.message}"
    return GrowthSolution(
        lam=lam,
        a=sol.t if sol.t.size else a_eval[:1],
        growth=sol.y[0] if sol.y.size else np.array([1.0]),
        crunch_before_tmax=crunch_before_tmax,
        integration_sane=sane,
        reason=reason,
    )


def collapse_epoch(threshold_growth: float, growth: GrowthSolution) -> float | None:
    idx = np.flatnonzero(growth.growth >= threshold_growth)
    if idx.size == 0:
        return None
    j = int(idx[0])
    if j == 0:
        return float(growth.a[0])
    g0, g1 = float(growth.growth[j - 1]), float(growth.growth[j])
    a0, a1 = float(growth.a[j - 1]), float(growth.a[j])
    if g1 <= g0:
        return a1
    frac = (threshold_growth - g0) / (g1 - g0)
    return float(a0 + frac * (a1 - a0))


def run_seed(lam: float, seed: int, cfg: CarrierConfig, growth: GrowthSolution | None = None) -> dict[str, Any]:
    growth = growth if growth is not None else solve_growth(lam, cfg)
    rng = np.random.default_rng(seed)
    if cfg.heterogeneity_s == 0.0:
        amplitudes = np.zeros(cfg.n_patches)
    else:
        amplitudes = cfg.heterogeneity_s * np.abs(rng.normal(size=cfg.n_patches))
    tags = (rng.random(cfg.n_patches) < cfg.tag_probability).astype(int)

    collapse_as: list[float] = []
    collapse_tags: list[int] = []
    for amp, tag in zip(amplitudes, tags):
        if amp <= 0.0:
            continue
        epoch = collapse_epoch(cfg.delta_c / amp, growth)
        if epoch is not None:
            collapse_as.append(epoch)
            collapse_tags.append(int(tag))

    record_count_before_erasure = len(collapse_as)
    distinguishable_before_erasure = len(set(collapse_tags)) >= 2
    first_record_a = min(collapse_as) if collapse_as else math.nan
    records_persist = not growth.crunch_before_tmax
    record_count_final = record_count_before_erasure if records_persist else 0
    distinguishable_final = distinguishable_before_erasure if records_persist else False
    rs = bool(
        growth.integration_sane
        and not growth.crunch_before_tmax
        and record_count_final >= 2
        and distinguishable_final
        and records_persist
    )
    no_collapse = record_count_before_erasure == 0
    if growth.crunch_before_tmax:
        failure_mode = "crunch_erases_records"
    elif no_collapse or record_count_final < 2:
        failure_mode = "growth_shutoff_or_insufficient_growth"
    elif not distinguishable_final:
        failure_mode = "records_not_distinguishable"
    elif rs:
        failure_mode = "none"
    else:
        failure_mode = "other_rs_failure"
    rho_at_first = first_record_a ** -3 if math.isfinite(first_record_a) else math.nan
    if lam == 0.0 or not math.isfinite(first_record_a):
        ratio = 0.0 if lam == 0.0 and math.isfinite(first_record_a) else math.nan
        a_lam = math.nan
        epoch_ratio = math.nan
    else:
        a_lam = abs(lam) ** (-1.0 / 3.0)
        ratio = abs(lam) / rho_at_first
        epoch_ratio = a_lam / first_record_a
    return {
        "lambda": f"{lam:.12g}",
        "seed": seed,
        "n_patches": cfg.n_patches,
        "heterogeneity_s": f"{cfg.heterogeneity_s:.12g}",
        "delta_c": f"{cfg.delta_c:.12g}",
        "a_init": f"{cfg.a_init:.12g}",
        "a_max": f"{cfg.a_max:.12g}",
        "tag_probability": f"{cfg.tag_probability:.12g}",
        "bare_admissible": bool(growth.integration_sane),
        "integration_sane": bool(growth.integration_sane),
        "crunch_before_tmax": bool(growth.crunch_before_tmax),
        "records_persist": bool(records_persist),
        "record_count_before_erasure": record_count_before_erasure,
        "record_count_final": record_count_final,
        "distinct_tags_before_erasure": len(set(collapse_tags)),
        "distinct_tags_final": len(set(collapse_tags)) if distinguishable_final else min(len(set(collapse_tags)), 1),
        "distinguishable_records": bool(distinguishable_final),
        "RS": bool(rs),
        "first_record_a": f"{first_record_a:.12g}" if math.isfinite(first_record_a) else "",
        "a_lambda": f"{a_lam:.12g}" if math.isfinite(a_lam) else "",
        "lambda_to_matter_at_first_record": f"{ratio:.12g}" if math.isfinite(ratio) else "",
        "a_lambda_over_a_rec": f"{epoch_ratio:.12g}" if math.isfinite(epoch_ratio) else "",
        "failure_mode": failure_mode,
        "growth_solve_reason": growth.reason,
    }


def run_grid(lambdas: Iterable[float], seeds: Iterable[int], cfg: CarrierConfig) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seeds = tuple(seeds)
    for lam in lambdas:
        growth = solve_growth(lam, cfg)
        for seed in seeds:
            rows.append(run_seed(lam, seed, cfg, growth))
    return rows


def aggregate_by_lambda(rows: list[dict[str, Any]], cfg: CarrierConfig) -> list[dict[str, Any]]:
    grouped: dict[float, list[dict[str, Any]]] = {}
    for row in rows:
        grouped.setdefault(float(row["lambda"]), []).append(row)
    out: list[dict[str, Any]] = []
    for lam in sorted(grouped):
        group = grouped[lam]
        rs_values = [str(r["RS"]) == "True" or r["RS"] is True for r in group]
        bare_values = [str(r["bare_admissible"]) == "True" or r["bare_admissible"] is True for r in group]
        ratios = [float(r["lambda_to_matter_at_first_record"]) for r in group if r["lambda_to_matter_at_first_record"] != ""]
        a_ratios = [float(r["a_lambda_over_a_rec"]) for r in group if r["a_lambda_over_a_rec"] != ""]
        first_as = [float(r["first_record_a"]) for r in group if r["first_record_a"] != ""]
        pass_fraction = float(np.mean(rs_values))
        out.append(
            {
                "lambda": f"{lam:.12g}",
                "n_seeds": len(group),
                "rs_pass_count": int(np.sum(rs_values)),
                "rs_pass_fraction": f"{pass_fraction:.12g}",
                "rs_lambda_pass": bool(pass_fraction >= cfg.seed_pass_fraction),
                "bare_pass_count": int(np.sum(bare_values)),
                "bare_pass_fraction": f"{float(np.mean(bare_values)):.12g}",
                "median_first_record_a": f"{float(np.median(first_as)):.12g}" if first_as else "",
                "median_lambda_to_matter_at_first_record": f"{float(np.median(ratios)):.12g}" if ratios else "",
                "median_a_lambda_over_a_rec": f"{float(np.median(a_ratios)):.12g}" if a_ratios else "",
                "failure_modes": ";".join(sorted({str(r["failure_mode"]) for r in group})),
            }
        )
    return out


def lambda_passes(lam: float, cfg: CarrierConfig, seeds: Iterable[int] = SEEDS) -> bool:
    rows = run_grid([lam], seeds, cfg)
    agg = aggregate_by_lambda(rows, cfg)[0]
    return str(agg["rs_lambda_pass"]) == "True" or agg["rs_lambda_pass"] is True


def refine_negative_edge(cfg: CarrierConfig) -> dict[str, Any]:
    if not lambda_passes(0.0, cfg):
        raise ValueError("zero-lambda carrier is not record-bearing; no window can be bracketed by this search")
    inside = -1.0e-5
    while not lambda_passes(inside, cfg):
        inside /= 3.0
    outside = inside * 3.0
    while lambda_passes(outside, cfg):
        outside *= 3.0
    for _ in range(16):
        mid = -math.sqrt(abs(inside * outside))
        if lambda_passes(mid, cfg):
            inside = mid
        else:
            outside = mid
        if abs(outside / inside) <= cfg.edge_factor_target:
            break
    return {
        "edge": "negative_crunch",
        "inside_lambda": inside,
        "outside_lambda": outside,
        "factor_width": abs(outside / inside),
        "inside_passes": lambda_passes(inside, cfg),
        "outside_passes": lambda_passes(outside, cfg),
    }


def refine_positive_edge(cfg: CarrierConfig) -> dict[str, Any]:
    if not lambda_passes(0.0, cfg):
        raise ValueError("zero-lambda carrier is not record-bearing; no window can be bracketed by this search")
    inside = 1.0e-5
    while not lambda_passes(inside, cfg):
        inside /= 3.0
    outside = inside * 3.0
    while lambda_passes(outside, cfg):
        outside *= 3.0
        if outside > 1.0e6:
            raise RuntimeError("positive no-collapse edge was not bracketed")
    for _ in range(20):
        mid = math.sqrt(inside * outside)
        if lambda_passes(mid, cfg):
            inside = mid
        else:
            outside = mid
        if outside / inside <= cfg.edge_factor_target:
            break
    return {
        "edge": "positive_no_collapse",
        "inside_lambda": inside,
        "outside_lambda": outside,
        "factor_width": outside / inside,
        "inside_passes": lambda_passes(inside, cfg),
        "outside_passes": lambda_passes(outside, cfg),
    }


def summarize_readouts(rows: list[dict[str, Any]], agg: list[dict[str, Any]], edges: list[dict[str, Any]], cfg: CarrierConfig) -> dict[str, Any]:
    rs_lams = [float(r["lambda"]) for r in agg if str(r["rs_lambda_pass"]) == "True" or r["rs_lambda_pass"] is True]
    bare_lams = [float(r["lambda"]) for r in agg if float(r["bare_pass_fraction"]) > 0.0]
    strict = bool(set(rs_lams) < set(bare_lams))
    two_sided = any(e["edge"] == "negative_crunch" for e in edges) and any(e["edge"] == "positive_no_collapse" for e in edges)
    rs_seed_rows = [r for r in rows if str(r["RS"]) == "True" or r["RS"] is True]
    ratios = np.array([float(r["lambda_to_matter_at_first_record"]) for r in rs_seed_rows if r["lambda_to_matter_at_first_record"] != ""])
    epoch_ratios = np.array([float(r["a_lambda_over_a_rec"]) for r in rs_seed_rows if r["a_lambda_over_a_rec"] != ""])
    positive_ratios = ratios[ratios > 0]
    if positive_ratios.size:
        spread_decades = math.log10(float(np.max(positive_ratios) / np.min(positive_ratios)))
    else:
        spread_decades = math.nan
    edge_map = {e["edge"]: e for e in edges}
    neg_inside = abs(edge_map["negative_crunch"]["inside_lambda"])
    pos_inside = edge_map["positive_no_collapse"]["inside_lambda"]
    signed_width_decades = math.log10(pos_inside / neg_inside) if neg_inside > 0 else math.nan
    return {
        "config": {
            "n_patches": cfg.n_patches,
            "heterogeneity_s": cfg.heterogeneity_s,
            "delta_c": cfg.delta_c,
            "a_init": cfg.a_init,
            "a_max": cfg.a_max,
            "n_seeds": len(SEEDS),
            "seed_pass_fraction": cfg.seed_pass_fraction,
        },
        "strictness_rs_inside_bare": strict,
        "rs_lambda_values": rs_lams,
        "bare_lambda_values": bare_lams,
        "two_sided_edges_bracketed": two_sided,
        "negative_edge_inside_outside": {
            "inside": edge_map["negative_crunch"]["inside_lambda"],
            "outside": edge_map["negative_crunch"]["outside_lambda"],
            "factor_width": edge_map["negative_crunch"]["factor_width"],
        },
        "positive_edge_inside_outside": {
            "inside": edge_map["positive_no_collapse"]["inside_lambda"],
            "outside": edge_map["positive_no_collapse"]["outside_lambda"],
            "factor_width": edge_map["positive_no_collapse"]["factor_width"],
        },
        "window_width_signed_decades_inside_edges": signed_width_decades,
        "bare_admissibility_grid_width_decades": math.log10(max(abs(x) for x in bare_lams if x != 0) / min(abs(x) for x in bare_lams if x != 0)),
        "coincidence_ratio_min_positive": float(np.min(positive_ratios)) if positive_ratios.size else None,
        "coincidence_ratio_median": float(np.median(ratios)) if ratios.size else None,
        "coincidence_ratio_max": float(np.max(ratios)) if ratios.size else None,
        "coincidence_ratio_positive_spread_decades": spread_decades,
        "epoch_ratio_min": float(np.min(epoch_ratios)) if epoch_ratios.size else None,
        "epoch_ratio_median": float(np.median(epoch_ratios)) if epoch_ratios.size else None,
        "epoch_ratio_max": float(np.max(epoch_ratios)) if epoch_ratios.size else None,
        "coincidence_order_unity_bounded": bool(positive_ratios.size and spread_decades <= 2.0),
    }


def control_c1(cfg: CarrierConfig) -> dict[str, Any]:
    c_cfg = replace(cfg, heterogeneity_s=0.0)
    rows = run_grid([-1.0e-5, 0.0, 0.01, 0.1], SEEDS, c_cfg)
    write_csv(CONTROLDIR / "C1_homogeneous_control.csv", rows)
    rs_any = any(str(r["RS"]) == "True" or r["RS"] is True for r in rows)
    return {"control": "C1_homogeneous", "passes": not rs_any, "rs_any": rs_any, "rows": len(rows)}


def control_c2(cfg: CarrierConfig, edges: list[dict[str, Any]]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for edge in edges:
        for side in ["inside", "outside"]:
            lam = float(edge[f"{side}_lambda"])
            growth = solve_growth(lam, cfg)
            row = run_seed(lam, SEEDS[0], cfg, growth)
            row["edge"] = edge["edge"]
            row["side"] = side
            rows.append(row)
    write_csv(CONTROLDIR / "C2_edge_witnesses.csv", rows)
    neg_outside = [r for r in rows if r["edge"] == "negative_crunch" and r["side"] == "outside"][0]
    pos_outside = [r for r in rows if r["edge"] == "positive_no_collapse" and r["side"] == "outside"][0]
    return {
        "control": "C2_gate_can_fire",
        "passes": neg_outside["failure_mode"] == "crunch_erases_records"
        and pos_outside["failure_mode"] == "growth_shutoff_or_insufficient_growth",
        "negative_outside_failure": neg_outside["failure_mode"],
        "positive_outside_failure": pos_outside["failure_mode"],
    }


def control_c3(cfg: CarrierConfig, reference_rs_lams: list[float]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    summaries: list[dict[str, Any]] = []
    for prob in [0.45, 0.5, 0.55]:
        c_cfg = replace(cfg, tag_probability=prob)
        c_rows = run_grid(LAMBDA_GRID, SEEDS, c_cfg)
        c_agg = aggregate_by_lambda(c_rows, c_cfg)
        pass_lams = [float(r["lambda"]) for r in c_agg if str(r["rs_lambda_pass"]) == "True" or r["rs_lambda_pass"] is True]
        rows.extend(c_rows)
        summaries.append(
            {
                "tag_probability": prob,
                "rs_lambda_values": pass_lams,
                "same_as_reference": pass_lams == reference_rs_lams,
            }
        )
    write_csv(CONTROLDIR / "C3_tag_probability_sweep.csv", rows)
    write_json(CONTROLDIR / "C3_tag_probability_summary.json", {"rows": summaries})
    return {
        "control": "C3_record_irrelevant_tag_sweep",
        "passes": all(s["same_as_reference"] for s in summaries),
        "summaries": summaries,
    }


def quick_edges_for_config(cfg: CarrierConfig) -> dict[str, Any]:
    neg = refine_negative_edge(cfg)
    pos = refine_positive_edge(cfg)
    return {
        "n_patches": cfg.n_patches,
        "heterogeneity_s": cfg.heterogeneity_s,
        "delta_c": cfg.delta_c,
        "negative_inside": neg["inside_lambda"],
        "negative_outside": neg["outside_lambda"],
        "positive_inside": pos["inside_lambda"],
        "positive_outside": pos["outside_lambda"],
    }


def control_c4(cfg: CarrierConfig) -> dict[str, Any]:
    variants = []
    for n in [32, 64, 128]:
        variants.append(replace(cfg, n_patches=n))
    for dc in [1.2, 1.686, 2.0]:
        variants.append(replace(cfg, delta_c=dc))
    for mult in [1.0 / 3.0, 1.0, 3.0]:
        variants.append(replace(cfg, heterogeneity_s=cfg.heterogeneity_s * mult))
    dedup: dict[tuple[int, float, float], CarrierConfig] = {}
    for var in variants:
        dedup[(var.n_patches, var.delta_c, var.heterogeneity_s)] = var
    rows = [quick_edges_for_config(var) for var in dedup.values()]
    write_csv(CONTROLDIR / "C4_robustness_edges.csv", rows)
    monotone_s = sorted([r for r in rows if int(r["n_patches"]) == cfg.n_patches and float(r["delta_c"]) == cfg.delta_c], key=lambda r: float(r["heterogeneity_s"]))
    s_pos_edges = [float(r["positive_inside"]) for r in monotone_s]
    smooth_positive = all(x <= y for x, y in zip(s_pos_edges, s_pos_edges[1:]))
    return {
        "control": "C4_robustness",
        "passes": bool(smooth_positive and len(rows) >= 7),
        "variant_count": len(rows),
        "smooth_positive_edge_with_s": bool(smooth_positive),
    }


def run_validator() -> dict[str, Any]:
    completed = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts" / "de_window_validate.py"), "--results-dir", str(OUTDIR)],
        check=False,
        text=True,
        capture_output=True,
    )
    (CONTROLDIR / "C5_validator_stdout.txt").write_text(completed.stdout, encoding="utf-8")
    (CONTROLDIR / "C5_validator_stderr.txt").write_text(completed.stderr, encoding="utf-8")
    return {
        "control": "C5_verdict_rederivation",
        "passes": completed.returncode == 0,
        "returncode": completed.returncode,
    }


def write_verdict(summary: dict[str, Any], controls: list[dict[str, Any]]) -> None:
    coincidence = summary["coincidence_order_unity_bounded"]
    lines = [
        "# Record-bearing lambda-window carrier verdict",
        "",
        "Status: RUN-frame toy computation in carrier-native units only. This does not derive a lambda value and does not compare to external measured values.",
        "",
        "## Four readouts",
        f"1. Strictness: `{summary['strictness_rs_inside_bare']}`. RS is strictly inside the bare integration-admissible grid.",
        f"2. Two-sidedness: `{summary['two_sided_edges_bracketed']}`. Negative edge is crunch erasure; positive edge is no-collapse/growth shutoff.",
        f"3. Coincidence readout: order-unity-bounded across the whole RS window = `{coincidence}`.",
        f"   Positive-ratio spread: `{summary['coincidence_ratio_positive_spread_decades']:.6g}` decades; min/median/max = `{summary['coincidence_ratio_min_positive']}`, `{summary['coincidence_ratio_median']}`, `{summary['coincidence_ratio_max']}`.",
        f"   Epoch ratio min/median/max = `{summary['epoch_ratio_min']}`, `{summary['epoch_ratio_median']}`, `{summary['epoch_ratio_max']}`.",
        f"4. Window width: `{summary['window_width_signed_decades_inside_edges']:.6g}` signed-edge decades inside the refined RS brackets; bare grid width `{summary['bare_admissibility_grid_width_decades']:.6g}` decades.",
        "",
        "## Refined edge brackets",
        f"- Negative crunch edge: inside `{summary['negative_edge_inside_outside']['inside']}`, outside `{summary['negative_edge_inside_outside']['outside']}`, factor `{summary['negative_edge_inside_outside']['factor_width']}`.",
        f"- Positive no-collapse edge: inside `{summary['positive_edge_inside_outside']['inside']}`, outside `{summary['positive_edge_inside_outside']['outside']}`, factor `{summary['positive_edge_inside_outside']['factor_width']}`.",
        "",
        "## Controls",
    ]
    for control in controls:
        lines.append(f"- `{control['control']}`: pass=`{control['passes']}`.")
    lines.extend(
        [
            "",
            "## Honest grading",
            "The two-sided window shape is expected from the declared toy physics: negative lambda can crunch and erase records, while positive lambda can shut off growth. The computed content is the strictness, edge brackets, window width, coincidence-ratio spread, and can-fail controls.",
        ]
    )
    if coincidence:
        lines.append("The coincidence readout supports the record-bearing-window claim at toy enumeration strength.")
    else:
        lines.append("The coincidence readout is a clean negative for the strong claim as phrased across the entire RS window: near-zero lambda runs are record-bearing but have a small lambda-to-matter ratio at first record.")
    lines.append("")
    (OUTDIR / "VERDICT.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    cfg = CarrierConfig()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    CONTROLDIR.mkdir(parents=True, exist_ok=True)
    manifest_sources = [
        REPO_ROOT / "results" / "DE_DEMARCATION_RELANDING_2026-06-11.md",
        Path("../six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step54_f50_background_moduli_demarcation_artifacts/f50_background_moduli_step54.py").resolve(),
        Path("../six-birds-sm-qm-gr/paper/sections/sec_06_predictions.tex").resolve(),
    ]
    rows = run_grid(LAMBDA_GRID, SEEDS, cfg)
    agg = aggregate_by_lambda(rows, cfg)
    edges = [refine_negative_edge(cfg), refine_positive_edge(cfg)]
    summary = summarize_readouts(rows, agg, edges, cfg)

    write_csv(OUTDIR / "window_sweep.csv", rows)
    write_csv(OUTDIR / "lambda_summary.csv", agg)
    write_csv(OUTDIR / "edges.csv", [{k: (f"{v:.12g}" if isinstance(v, float) else v) for k, v in e.items()} for e in edges])
    write_json(OUTDIR / "coincidence_readout.json", summary)

    controls = [
        control_c1(cfg),
        control_c2(cfg, edges),
        control_c3(cfg, summary["rs_lambda_values"]),
        control_c4(cfg),
    ]
    controls.append(run_validator())
    write_verdict(summary, controls)
    write_json(CONTROLDIR / "controls_summary.json", {"controls": controls})

    provenance = {
        "carrier_units": "rho_m(a=1)=1; 8*pi*G/3=1",
        "lambda_grid": LAMBDA_GRID,
        "seeds": SEEDS,
        "config": summary["config"],
        "aggregate_rule": "rs_lambda_pass iff seed pass fraction >= 0.8",
        "sources": {str(path): sha256(path) for path in manifest_sources if path.exists()},
        "outputs": {
            "window_sweep.csv": sha256(OUTDIR / "window_sweep.csv"),
            "lambda_summary.csv": sha256(OUTDIR / "lambda_summary.csv"),
            "edges.csv": sha256(OUTDIR / "edges.csv"),
            "coincidence_readout.json": sha256(OUTDIR / "coincidence_readout.json"),
            "VERDICT.md": sha256(OUTDIR / "VERDICT.md"),
        },
    }
    write_json(OUTDIR / "run_manifest.json", provenance)

    all_controls_pass = all(bool(c["passes"]) for c in controls)
    print(
        json.dumps(
            {
                "outdir": str(OUTDIR.relative_to(REPO_ROOT)),
                "strictness": summary["strictness_rs_inside_bare"],
                "two_sided": summary["two_sided_edges_bracketed"],
                "coincidence_order_unity_bounded": summary["coincidence_order_unity_bounded"],
                "controls_pass": all_controls_pass,
            },
            sort_keys=True,
        )
    )
    return 0 if all_controls_pass else 2


if __name__ == "__main__":
    raise SystemExit(main())
