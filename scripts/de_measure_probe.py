#!/usr/bin/env python3
"""Record-measure probe for the frozen DE-window carrier.

This script extends the already-frozen Leg-A carrier outputs into a
measure-class audit. It writes only under results/DE_measure and does not
modify results/DE_window.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any

import numpy as np

from de_window_carrier import CarrierConfig, SEEDS, aggregate_by_lambda, refine_negative_edge, refine_positive_edge, run_grid


for _name in [
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
]:
    os.environ.setdefault(_name, "1")


REPO_ROOT = Path(__file__).resolve().parents[1]
OUTDIR = REPO_ROOT / "results" / "DE_measure"
ROBUSTNESS_DIR = OUTDIR / "robustness"

MIN_POSITIVE_LAMBDA = 1.0e-5
N_POSITIVE_GRID = 36
N_NEGATIVE_GRID = 8
TOP_DECADE_PROB_THRESHOLD = 0.8
WIDTH90_DECADES_THRESHOLD = 1.5


MEASURE_CLASSES = [
    {
        "measure_id": "M1_flat_lambda",
        "description": "flat d_lambda on the signed RS window",
        "axis": "lambda",
        "density": "flat",
        "record_weight": "none",
        "include_negative": True,
    },
    {
        "measure_id": "M2_flat_log_lambda",
        "description": "flat d_log_lambda on the positive RS window; negative sliver reported separately",
        "axis": "log_lambda",
        "density": "flat",
        "record_weight": "none",
        "include_negative": False,
    },
    {
        "measure_id": "M3_flat_lambda_times_N_rec",
        "description": "flat d_lambda weighted by distinguishable final record count",
        "axis": "lambda",
        "density": "flat",
        "record_weight": "N_rec",
        "include_negative": True,
    },
    {
        "measure_id": "M4_flat_lambda_times_f_coll",
        "description": "flat d_lambda weighted by collapsed-patch fraction",
        "axis": "lambda",
        "density": "flat",
        "record_weight": "f_coll",
        "include_negative": True,
    },
    {
        "measure_id": "M5_flat_log_lambda_times_N_rec",
        "description": "flat d_log_lambda weighted by distinguishable final record count",
        "axis": "log_lambda",
        "density": "flat",
        "record_weight": "N_rec",
        "include_negative": False,
    },
]


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


def weighted_quantile(values: np.ndarray, weights: np.ndarray, quantile: float) -> float:
    """Left inverse of the weighted empirical CDF; zero-mass atoms are ignored."""
    values = np.asarray(values, dtype=float)
    weights = np.asarray(weights, dtype=float)
    if values.ndim != 1 or values.shape != weights.shape or not 0.0 <= quantile <= 1.0:
        raise ValueError("equal vectors and a quantile in [0, 1] are required")
    if not np.all(np.isfinite(values)) or not np.all(np.isfinite(weights)) or np.any(weights < 0):
        raise ValueError("values must be finite and weights finite and nonnegative")
    positive = weights > 0
    values, weights = values[positive], weights[positive]
    if values.size == 0:
        return math.nan
    order = np.argsort(values)
    values = values[order]
    weights = weights[order]
    cdf = np.cumsum(weights)
    target = quantile * cdf[-1]
    return float(values[min(int(np.searchsorted(cdf, target, side="left")), values.size - 1)])


def interval_weights(axis_values: np.ndarray) -> np.ndarray:
    axis_values = np.asarray(axis_values, dtype=float)
    if axis_values.ndim != 1 or not np.all(np.isfinite(axis_values)) or np.any(np.diff(axis_values) <= 0):
        raise ValueError("quadrature nodes must be finite and strictly increasing")
    if axis_values.size < 2:
        return np.zeros_like(axis_values)
    weights = np.empty_like(axis_values)
    weights[0] = 0.5 * (axis_values[1] - axis_values[0])
    weights[-1] = 0.5 * (axis_values[-1] - axis_values[-2])
    if axis_values.size > 2:
        weights[1:-1] = 0.5 * (axis_values[2:] - axis_values[:-2])
    return np.maximum(weights, 0.0)


def dense_lambda_grid(negative_inside: float, positive_inside: float) -> list[float]:
    neg_abs = abs(float(negative_inside))
    negative = -np.geomspace(neg_abs, MIN_POSITIVE_LAMBDA, N_NEGATIVE_GRID)
    positive = np.geomspace(MIN_POSITIVE_LAMBDA, float(positive_inside), N_POSITIVE_GRID)
    grid = np.concatenate([negative, np.array([0.0]), positive])
    return sorted({float(f"{x:.12g}") for x in grid})


def truth(value: Any) -> bool:
    return value is True or str(value) == "True"


def enrich_rows(rows: list[dict[str, Any]], cfg: CarrierConfig, variant: str) -> list[dict[str, Any]]:
    enriched: list[dict[str, Any]] = []
    for row in rows:
        record_count = int(row["record_count_final"])
        distinguishable_count = record_count if truth(row["distinguishable_records"]) else 0
        out = dict(row)
        out["variant"] = variant
        out["N_rec_final"] = record_count
        out["N_rec_distinguishable"] = distinguishable_count
        out["f_coll"] = f"{record_count / cfg.n_patches:.12g}"
        enriched.append(out)
    return enriched


def aggregate_measure_inputs(rows: list[dict[str, Any]], cfg: CarrierConfig) -> list[dict[str, Any]]:
    grouped: dict[float, list[dict[str, Any]]] = {}
    for row in rows:
        grouped.setdefault(float(row["lambda"]), []).append(row)
    out: list[dict[str, Any]] = []
    for lam in sorted(grouped):
        group = grouped[lam]
        rs = np.array([truth(row["RS"]) for row in group], dtype=bool)
        rs_rows = [row for row, ok in zip(group, rs) if ok]
        ratios = np.array(
            [
                float(row["lambda_to_matter_at_first_record"])
                for row in rs_rows
                if str(row["lambda_to_matter_at_first_record"]) != "" and float(row["lambda_to_matter_at_first_record"]) > 0.0
            ],
            dtype=float,
        )
        epoch_ratios = np.array(
            [
                float(row["a_lambda_over_a_rec"])
                for row in rs_rows
                if str(row["a_lambda_over_a_rec"]) != "" and float(row["a_lambda_over_a_rec"]) > 0.0
            ],
            dtype=float,
        )
        n_rec = np.array([float(row["N_rec_distinguishable"]) for row in group], dtype=float)
        f_coll = np.array([float(row["f_coll"]) for row in group], dtype=float)
        out.append(
            {
                "lambda": lam,
                "rs_pass_fraction": float(np.mean(rs)),
                "rs_lambda_pass": bool(np.mean(rs) >= cfg.seed_pass_fraction),
                "median_log10_R": float(np.median(np.log10(ratios))) if ratios.size else math.nan,
                "median_R": float(np.median(ratios)) if ratios.size else math.nan,
                "median_a_lambda_over_a_rec": float(np.median(epoch_ratios)) if epoch_ratios.size else math.nan,
                "mean_N_rec": float(np.mean(n_rec)),
                "mean_f_coll": float(np.mean(f_coll)),
                "n_rs_seed_rows_with_positive_R": int(ratios.size),
                "n_seeds": len(group),
                "seed_samples": [
                    {
                        "log10_R": math.log10(float(row["lambda_to_matter_at_first_record"])),
                        "epoch_ratio": float(row["a_lambda_over_a_rec"]),
                        "N_rec": float(row["N_rec_distinguishable"]),
                        "f_coll": float(row["f_coll"]),
                    }
                    for row in rs_rows
                    if str(row["lambda_to_matter_at_first_record"]) != ""
                    and float(row["lambda_to_matter_at_first_record"]) > 0.0
                ],
            }
        )
    return out


def measure_axis_and_base_weights(inputs: list[dict[str, Any]], measure: dict[str, Any]) -> tuple[np.ndarray, np.ndarray, list[dict[str, Any]]]:
    selected = [
        row
        for row in inputs
        if row["rs_lambda_pass"]
        and math.isfinite(float(row["median_log10_R"]))
        and (measure["include_negative"] or float(row["lambda"]) > 0.0)
    ]
    if measure["axis"] == "log_lambda":
        selected = [row for row in selected if float(row["lambda"]) > 0.0]
        axis = np.log(np.array([float(row["lambda"]) for row in selected], dtype=float))
    else:
        axis = np.array([float(row["lambda"]) for row in selected], dtype=float)
    if not selected:
        return np.array([]), np.array([]), []
    order = np.argsort(axis)
    axis = axis[order]
    selected = [selected[int(i)] for i in order]
    weights = interval_weights(axis)
    # These are lambda quadrature masses. Seed selection and record weights
    # belong inside the joint pushforward, not on per-lambda seed medians.
    return axis, weights, selected


def evaluate_measure(inputs: list[dict[str, Any]], measure: dict[str, Any]) -> dict[str, Any]:
    _, weights, selected = measure_axis_and_base_weights(inputs, measure)
    if not selected or float(np.sum(weights)) <= 0.0:
        return {
            "measure_id": measure["measure_id"],
            "collapses": False,
            "status": "no_support",
        }
    samples = []
    for row, lambda_mass in zip(selected, weights):
        for sample in row["seed_samples"]:
            record_weight = 1.0 if measure["record_weight"] == "none" else sample[measure["record_weight"]]
            samples.append((row["lambda"], sample, lambda_mass * record_weight / row["n_seeds"]))
    samples = [sample for sample in samples if sample[2] > 0.0]
    if not samples:
        return {"measure_id": measure["measure_id"], "collapses": False, "status": "no_support"}
    log_r = np.array([sample[1]["log10_R"] for sample in samples], dtype=float)
    epoch = np.array([sample[1]["epoch_ratio"] for sample in samples], dtype=float)
    weights = np.array([sample[2] for sample in samples], dtype=float)
    top = float(np.max(log_r))
    p_top_decade = float(np.sum(weights[log_r >= top - 1.0]) / np.sum(weights))
    q05 = weighted_quantile(log_r, weights, 0.05)
    q50 = weighted_quantile(log_r, weights, 0.50)
    q95 = weighted_quantile(log_r, weights, 0.95)
    width90 = q95 - q05
    epoch_q05 = weighted_quantile(epoch, weights, 0.05)
    epoch_q50 = weighted_quantile(epoch, weights, 0.50)
    epoch_q95 = weighted_quantile(epoch, weights, 0.95)
    collapses = bool(p_top_decade >= TOP_DECADE_PROB_THRESHOLD and width90 <= WIDTH90_DECADES_THRESHOLD)
    top_lambdas = [sample[0] for sample in samples if sample[1]["log10_R"] >= top - 1.0]
    return {
        "measure_id": measure["measure_id"],
        "description": measure["description"],
        "collapses": collapses,
        "status": "collapsing" if collapses else "non_collapsing",
        "p_R_within_one_decade_top": p_top_decade,
        "log10R_q05": q05,
        "log10R_median": q50,
        "log10R_q95": q95,
        "log10R_width90_decades": width90,
        "top_log10R": top,
        "top_R": 10.0**top,
        "R_band_90": f"[{10.0**q05:.6g},{10.0**q95:.6g}]",
        "epoch_ratio_q05": epoch_q05,
        "epoch_ratio_median": epoch_q50,
        "epoch_ratio_q95": epoch_q95,
        "lambda_support_min": float(min(row["lambda"] for row in selected)),
        "lambda_support_max": float(max(row["lambda"] for row in selected)),
        "top_decade_lambda_min": float(min(top_lambdas)),
        "top_decade_lambda_max": float(max(top_lambdas)),
        "distribution": "joint lambda/seed quadrature conditioned on RS, weighted within each seed",
        "quantile_convention": "left inverse weighted empirical CDF",
        "structural_property": structural_property(measure, collapses),
    }


def structural_property(measure: dict[str, Any], collapses: bool) -> str:
    if measure["axis"] == "log_lambda" and not collapses:
        return "log prior preserves many decades of lower-edge candidates"
    if measure["axis"] == "lambda" and collapses and measure["record_weight"] == "none":
        return "non-singular linear prior density puts most continuous mass near the positive upper edge"
    if measure["axis"] == "lambda" and collapses:
        return "linear prior density near the upper edge; record abundance does not undo concentration"
    if measure["record_weight"] != "none" and not collapses:
        return "record abundance weighting is insufficient to overcome broad prior degeneracy"
    return "no collapsing structural property in this carrier"


def evaluate_all_measures(inputs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [evaluate_measure(inputs, measure) for measure in MEASURE_CLASSES]


def build_variant(name: str, cfg: CarrierConfig) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    neg = refine_negative_edge(cfg)
    pos = refine_positive_edge(cfg)
    grid = dense_lambda_grid(float(neg["inside_lambda"]), float(pos["inside_lambda"]))
    rows = enrich_rows(run_grid(grid, SEEDS, cfg), cfg, name)
    inputs = aggregate_measure_inputs(rows, cfg)
    verdicts = evaluate_all_measures(inputs)
    meta = {
        "variant": name,
        "n_patches": cfg.n_patches,
        "heterogeneity_s": cfg.heterogeneity_s,
        "delta_c": cfg.delta_c,
        "negative_inside": neg["inside_lambda"],
        "positive_inside": pos["inside_lambda"],
        "lambda_grid_count": len(grid),
    }
    return rows, verdicts, meta


def write_prereg(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# DE Measure Probe Preregistration",
        "",
        "Date: 2026-06-12.",
        "",
        "This probe reuses the frozen Leg-A record-bearing carrier and writes only to `results/DE_measure/`. It does not modify `results/DE_window/`.",
        "",
        "## Measure Classes",
        "- M1: flat `d_lambda` on the signed RS window.",
        "- M2: flat `d log(lambda)` on the positive RS window; the negative sliver is reported separately.",
        "- M3: flat `d_lambda * N_rec(lambda)`.",
        "- M4: flat `d_lambda * f_coll(lambda)`.",
        "- M5: flat `d log(lambda) * N_rec(lambda)`.",
        "- M6: not declared. No additional carrier-native measure was defensible without adding new content.",
        "",
        "## Collapse Criterion",
        f"A measure collapses the Leg-A degeneracy iff `P(log10 R >= max(log10 R)-1) >= {TOP_DECADE_PROB_THRESHOLD}` and the weighted 90% width of `log10 R` is <= `{WIDTH90_DECADES_THRESHOLD}` decades.",
        "This criterion is declared before evaluating the measure verdict table. It can fail: broad flat-log measures are expected not to collapse.",
        "",
        "## Grid and Aggregation",
        f"The positive side uses `{N_POSITIVE_GRID}` log-spaced lambda points from `{MIN_POSITIVE_LAMBDA}` to the refined positive RS inside edge. The negative sliver uses `{N_NEGATIVE_GRID}` log-spaced points from the refined negative inside edge to `-1e-5` plus zero for the raw observables. Continuous measure weights are trapezoid cell widths in either lambda or log-lambda.",
        "The distribution is the joint lambda/seed pushforward: each RS-passing seed receives its lambda quadrature mass divided by the number of seeds, multiplied by its own declared record weight. It is not a distribution of seed medians. Quantiles use the left inverse of the weighted empirical CDF. The zero-lambda node is excluded from log-R readouts.",
        "",
        "No observed cosmological values enter this probe. All quantities are carrier-native.",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_verdict(verdicts: list[dict[str, Any]], robustness: list[dict[str, Any]], validator: dict[str, Any]) -> None:
    collapsing = [row["measure_id"] for row in verdicts if row.get("collapses")]
    non_collapsing = [row["measure_id"] for row in verdicts if not row.get("collapses")]
    robust_by_measure: dict[str, list[bool]] = {}
    for row in robustness:
        robust_by_measure.setdefault(str(row["measure_id"]), []).append(bool(row["collapses"]))
    flips = [
        measure_id
        for measure_id, states in robust_by_measure.items()
        if len(set(states + [measure_id in collapsing])) > 1
    ]
    lines = [
        "# DE Measure Probe Verdict",
        "",
        "Status: conditional measure audit in carrier-native units only. This is not a derivation of a lambda value and not a comparison to external measured cosmology.",
        "",
        "## Main Verdict Table",
    ]
    for row in verdicts:
        lines.append(
            f"- `{row['measure_id']}`: collapses=`{row['collapses']}`, P_top_decade=`{row['p_R_within_one_decade_top']:.6g}`, width90=`{row['log10R_width90_decades']:.6g}` decades, median a_lambda/a_rec=`{row['epoch_ratio_median']:.6g}`."
        )
    lines.extend(
        [
            "",
            "## Can-fail Control",
            f"Collapsing classes: `{collapsing}`.",
            f"Non-collapsing classes: `{non_collapsing}`.",
            "The criterion is non-vacuous if at least one class collapses and at least one class does not.",
            "",
            "## Robustness",
        ]
    )
    for row in robustness:
        lines.append(
            f"- `{row['variant']}` `{row['measure_id']}`: collapses=`{row['collapses']}`, width90=`{row['log10R_width90_decades']:.6g}`."
        )
    if flips:
        lines.append("")
        lines.append(f"Robustness flips relative to the base verdict: `{flips}`.")
    lines.extend(
        [
            "",
            "## Validator",
            f"Validator match: `{validator['verdict_match']}`; mismatches: `{validator['mismatch_count']}`.",
            "",
            "## Honest Grade",
            "This is RECOGNITION + DEMARCATION only. The tables report joint lambda/seed distributions under the declared priors and RS condition. Record-count and collapse-fraction weights are proportional on RS-passing seeds and hence define the same normalized measure. The choice of prior remains supplied content; neither the finite carrier nor smoothness near zero alone fixes typicality.",
            "",
        ]
    )
    (OUTDIR / "VERDICT.md").write_text("\n".join(lines), encoding="utf-8")


def run_validator() -> dict[str, Any]:
    completed = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts" / "de_measure_validate.py"), "--results-dir", str(OUTDIR)],
        check=False,
        capture_output=True,
        text=True,
    )
    payload = {
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }
    try:
        parsed = json.loads(completed.stdout.strip().splitlines()[-1])
        payload.update(parsed)
    except Exception:
        payload.update({"verdict_match": False, "mismatch_count": -1})
    return payload


def main() -> int:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    ROBUSTNESS_DIR.mkdir(parents=True, exist_ok=True)
    write_prereg(OUTDIR / "PREREG.md")

    base_cfg = CarrierConfig()
    base_rows, base_verdicts, base_meta = build_variant("base", base_cfg)
    write_csv(OUTDIR / "record_observables.csv", base_rows)
    write_csv(OUTDIR / "measure_verdicts.csv", base_verdicts)
    epoch_rows = [
        {
            "measure_id": row["measure_id"],
            "epoch_ratio_q05": row["epoch_ratio_q05"],
            "epoch_ratio_median": row["epoch_ratio_median"],
            "epoch_ratio_q95": row["epoch_ratio_q95"],
            "p_R_within_one_decade_top": row["p_R_within_one_decade_top"],
            "log10R_width90_decades": row["log10R_width90_decades"],
        }
        for row in base_verdicts
    ]
    write_csv(OUTDIR / "epoch_typicality.csv", epoch_rows)

    robustness_rows: list[dict[str, Any]] = []
    robustness_meta: list[dict[str, Any]] = []
    variants = [
        ("N32", replace(base_cfg, n_patches=32)),
        ("N128", replace(base_cfg, n_patches=128)),
        ("delta_c_2p0", replace(base_cfg, delta_c=2.0)),
    ]
    for name, cfg in variants:
        rows, verdicts, meta = build_variant(name, cfg)
        write_csv(ROBUSTNESS_DIR / f"{name}_record_observables.csv", rows)
        write_csv(ROBUSTNESS_DIR / f"{name}_measure_verdicts.csv", verdicts)
        robustness_meta.append(meta)
        for verdict in verdicts:
            row = dict(verdict)
            row["variant"] = name
            robustness_rows.append(row)
    write_csv(OUTDIR / "robustness" / "measure_robustness.csv", robustness_rows)

    manifest = {
        "carrier_units": "rho_m(a=1)=1; 8*pi*G/3=1",
        "base_meta": base_meta,
        "robustness_meta": robustness_meta,
        "frozen_sources": {
            "results/DE_DEMARCATION_2026-06-12.md": sha256(REPO_ROOT / "results" / "DE_DEMARCATION_2026-06-12.md"),
            "results/DE_window/run_manifest.json": sha256(REPO_ROOT / "results" / "DE_window" / "run_manifest.json"),
            "results/DE_window/coincidence_readout.json": sha256(REPO_ROOT / "results" / "DE_window" / "coincidence_readout.json"),
        },
    }
    write_json(OUTDIR / "run_manifest.json", manifest)

    validator = run_validator()
    write_verdict(base_verdicts, robustness_rows, validator)
    # Re-run once after VERDICT.md exists so the manifest can stamp final outputs.
    manifest["outputs"] = {
        "PREREG.md": sha256(OUTDIR / "PREREG.md"),
        "record_observables.csv": sha256(OUTDIR / "record_observables.csv"),
        "measure_verdicts.csv": sha256(OUTDIR / "measure_verdicts.csv"),
        "epoch_typicality.csv": sha256(OUTDIR / "epoch_typicality.csv"),
        "VERDICT.md": sha256(OUTDIR / "VERDICT.md"),
    }
    write_json(OUTDIR / "run_manifest.json", manifest)

    print(
        json.dumps(
            {
                "outdir": str(OUTDIR.relative_to(REPO_ROOT)),
                "collapsing": [row["measure_id"] for row in base_verdicts if row["collapses"]],
                "non_collapsing": [row["measure_id"] for row in base_verdicts if not row["collapses"]],
                "validator_match": validator["verdict_match"],
            },
            sort_keys=True,
        )
    )
    return 0 if validator["verdict_match"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
