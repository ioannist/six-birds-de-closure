#!/usr/bin/env python3
"""Independent verdict re-derivation for the DE measure probe."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SEED_PASS_FRACTION = 0.8
TOP_DECADE_PROB_THRESHOLD = 0.8
WIDTH90_DECADES_THRESHOLD = 1.5


MEASURE_CLASSES = [
    ("M1_flat_lambda", "lambda", "none", True),
    ("M2_flat_log_lambda", "log_lambda", "none", False),
    ("M3_flat_lambda_times_N_rec", "lambda", "N_rec", True),
    ("M4_flat_lambda_times_f_coll", "lambda", "f_coll", True),
    ("M5_flat_log_lambda_times_N_rec", "log_lambda", "N_rec", False),
]


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def truth(value: Any) -> bool:
    return value is True or str(value) == "True"


def weighted_quantile(values: np.ndarray, weights: np.ndarray, quantile: float) -> float:
    pairs = sorted((float(v), float(w)) for v, w in zip(values, weights) if w > 0)
    total = math.fsum(w for _, w in pairs)
    if not pairs or not 0 <= quantile <= 1:
        return math.nan
    target = quantile * total
    cumulative = 0.0
    for value, weight in pairs:
        cumulative += weight
        if cumulative >= target:
            return value
    return pairs[-1][0]


def interval_weights(axis_values: np.ndarray) -> np.ndarray:
    if axis_values.size < 2:
        return np.zeros_like(axis_values)
    out = np.empty_like(axis_values)
    out[0] = 0.5 * (axis_values[1] - axis_values[0])
    out[-1] = 0.5 * (axis_values[-1] - axis_values[-2])
    if axis_values.size > 2:
        out[1:-1] = 0.5 * (axis_values[2:] - axis_values[:-2])
    return np.maximum(out, 0.0)


def aggregate_inputs(rows: list[dict[str, str]]) -> list[dict[str, Any]]:
    grouped: dict[float, list[dict[str, str]]] = {}
    for row in rows:
        grouped.setdefault(float(row["lambda"]), []).append(row)
    return [
        {
            "lambda": lam,
            "rs_lambda_pass": sum(truth(r["RS"]) for r in group) / len(group) >= SEED_PASS_FRACTION,
            "rows": group,
        }
        for lam, group in sorted(grouped.items())
    ]


def evaluate_measure(inputs: list[dict[str, Any]], measure_id: str, axis_name: str, record_weight: str, include_negative: bool) -> dict[str, Any]:
    selected = [
        row for row in inputs
        if row["rs_lambda_pass"] and row["lambda"] != 0.0
        and (include_negative or row["lambda"] > 0.0)
    ]
    axis = np.asarray([r["lambda"] for r in selected])
    if axis_name == "log_lambda":
        axis = np.log(axis)
    lambda_weights = interval_weights(axis)
    log_values, epoch_values, masses = [], [], []
    for item, mass in zip(selected, lambda_weights):
        for row in item["rows"]:
            if not truth(row["RS"]):
                continue
            if record_weight == "N_rec":
                weight = float(row["N_rec_distinguishable"])
            elif record_weight == "f_coll":
                weight = float(row["f_coll"])
            else:
                weight = 1.0
            if mass * weight <= 0:
                continue
            log_values.append(math.log10(float(row["lambda_to_matter_at_first_record"])))
            epoch_values.append(float(row["a_lambda_over_a_rec"]))
            masses.append(float(mass * weight / len(item["rows"])))
    if not masses:
        return {"measure_id": measure_id, "collapses": False, "status": "no_support"}
    log_r = np.asarray(log_values)
    epochs = np.asarray(epoch_values)
    weights = np.asarray(masses)
    top = float(np.max(log_r))
    p_top = float(np.sum(weights[log_r >= top - 1.0]) / np.sum(weights))
    q05 = weighted_quantile(log_r, weights, 0.05)
    q50 = weighted_quantile(log_r, weights, 0.50)
    q95 = weighted_quantile(log_r, weights, 0.95)
    width = q95 - q05
    return {
        "measure_id": measure_id,
        "collapses": bool(p_top >= TOP_DECADE_PROB_THRESHOLD and width <= WIDTH90_DECADES_THRESHOLD),
        "p_R_within_one_decade_top": p_top,
        "log10R_q05": q05,
        "log10R_median": q50,
        "log10R_q95": q95,
        "log10R_width90_decades": width,
        "epoch_ratio_median": weighted_quantile(epochs, weights, 0.50),
    }


def close(a: Any, b: Any, tol: float = 5.0e-9) -> bool:
    if isinstance(a, bool) or isinstance(b, bool):
        return bool(a) == bool(b)
    return math.isclose(float(a), float(b), rel_tol=tol, abs_tol=tol)


def derive(results_dir: Path) -> list[dict[str, Any]]:
    rows = read_csv(results_dir / "record_observables.csv")
    inputs = aggregate_inputs(rows)
    return [evaluate_measure(inputs, *measure) for measure in MEASURE_CLASSES]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results-dir", type=Path, default=Path("results/DE_measure"))
    args = parser.parse_args()
    derived = derive(args.results_dir)
    claimed_rows = read_csv(args.results_dir / "measure_verdicts.csv")
    claimed = {row["measure_id"]: row for row in claimed_rows}
    keys = [
        "collapses",
        "p_R_within_one_decade_top",
        "log10R_q05",
        "log10R_median",
        "log10R_q95",
        "log10R_width90_decades",
        "epoch_ratio_median",
    ]
    mismatches: dict[str, Any] = {}
    for row in derived:
        got = claimed[row["measure_id"]]
        for key in keys:
            if key == "collapses":
                ok = truth(got[key]) == bool(row[key])
            else:
                ok = close(got[key], row[key])
            if not ok:
                mismatches[f"{row['measure_id']}:{key}"] = {"claimed": got[key], "derived": row[key]}
    payload = {"derived": derived, "mismatches": mismatches, "verdict_match": not mismatches}
    (args.results_dir / "validator_rederived.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"verdict_match": not mismatches, "mismatch_count": len(mismatches)}, sort_keys=True))
    return 0 if not mismatches else 1


if __name__ == "__main__":
    raise SystemExit(main())
