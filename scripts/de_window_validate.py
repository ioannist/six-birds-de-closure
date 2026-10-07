#!/usr/bin/env python3
"""Independent verdict re-derivation for the DE window carrier."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SEED_PASS_FRACTION = 0.8


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def truth(value: Any) -> bool:
    return str(value) == "True" or value is True


def aggregate(rows: list[dict[str, str]]) -> list[dict[str, Any]]:
    grouped: dict[float, list[dict[str, str]]] = {}
    for row in rows:
        grouped.setdefault(float(row["lambda"]), []).append(row)
    out: list[dict[str, Any]] = []
    for lam in sorted(grouped):
        group = grouped[lam]
        rs = [truth(row["RS"]) for row in group]
        bare = [truth(row["bare_admissible"]) for row in group]
        first_as = [float(row["first_record_a"]) for row in group if row["first_record_a"]]
        ratios = [float(row["lambda_to_matter_at_first_record"]) for row in group if row["lambda_to_matter_at_first_record"]]
        epoch_ratios = [float(row["a_lambda_over_a_rec"]) for row in group if row["a_lambda_over_a_rec"]]
        pass_fraction = float(np.mean(rs))
        out.append(
            {
                "lambda": lam,
                "rs_lambda_pass": pass_fraction >= SEED_PASS_FRACTION,
                "rs_pass_fraction": pass_fraction,
                "bare_pass_fraction": float(np.mean(bare)),
                "median_first_record_a": float(np.median(first_as)) if first_as else None,
                "median_lambda_to_matter_at_first_record": float(np.median(ratios)) if ratios else None,
                "median_a_lambda_over_a_rec": float(np.median(epoch_ratios)) if epoch_ratios else None,
            }
        )
    return out


def derive(results_dir: Path) -> dict[str, Any]:
    rows = read_csv(results_dir / "window_sweep.csv")
    edge_rows = read_csv(results_dir / "edges.csv")
    agg = aggregate(rows)
    rs_lams = [row["lambda"] for row in agg if row["rs_lambda_pass"]]
    bare_lams = [row["lambda"] for row in agg if row["bare_pass_fraction"] > 0.0]
    rs_seed_rows = [row for row in rows if truth(row["RS"])]
    ratios = np.array([float(row["lambda_to_matter_at_first_record"]) for row in rs_seed_rows if row["lambda_to_matter_at_first_record"]])
    positive_ratios = ratios[ratios > 0]
    epoch_ratios = np.array([float(row["a_lambda_over_a_rec"]) for row in rs_seed_rows if row["a_lambda_over_a_rec"]])
    edge_map = {row["edge"]: row for row in edge_rows}
    neg_inside = abs(float(edge_map["negative_crunch"]["inside_lambda"]))
    pos_inside = float(edge_map["positive_no_collapse"]["inside_lambda"])
    positive_spread = (
        math.log10(float(np.max(positive_ratios) / np.min(positive_ratios)))
        if positive_ratios.size
        else math.nan
    )
    return {
        "strictness_rs_inside_bare": bool(set(rs_lams) < set(bare_lams)),
        "rs_lambda_values": rs_lams,
        "bare_lambda_values": bare_lams,
        "two_sided_edges_bracketed": "negative_crunch" in edge_map and "positive_no_collapse" in edge_map,
        "window_width_signed_decades_inside_edges": math.log10(pos_inside / neg_inside),
        "coincidence_ratio_min_positive": float(np.min(positive_ratios)) if positive_ratios.size else None,
        "coincidence_ratio_median": float(np.median(ratios)) if ratios.size else None,
        "coincidence_ratio_max": float(np.max(ratios)) if ratios.size else None,
        "coincidence_ratio_positive_spread_decades": positive_spread,
        "epoch_ratio_min": float(np.min(epoch_ratios)) if epoch_ratios.size else None,
        "epoch_ratio_median": float(np.median(epoch_ratios)) if epoch_ratios.size else None,
        "epoch_ratio_max": float(np.max(epoch_ratios)) if epoch_ratios.size else None,
        "coincidence_order_unity_bounded": bool(positive_ratios.size and positive_spread <= 2.0),
    }


def close(a: Any, b: Any, tol: float = 1.0e-9) -> bool:
    if a is None or b is None:
        return a is None and b is None
    if isinstance(a, bool) or isinstance(b, bool):
        return bool(a) == bool(b)
    if isinstance(a, list) or isinstance(b, list):
        return list(a) == list(b)
    return math.isclose(float(a), float(b), rel_tol=tol, abs_tol=tol)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results-dir", type=Path, default=Path("results/DE_window"))
    args = parser.parse_args()
    derived = derive(args.results_dir)
    claimed = json.loads((args.results_dir / "coincidence_readout.json").read_text(encoding="utf-8"))
    keys = [
        "strictness_rs_inside_bare",
        "rs_lambda_values",
        "bare_lambda_values",
        "two_sided_edges_bracketed",
        "window_width_signed_decades_inside_edges",
        "coincidence_ratio_min_positive",
        "coincidence_ratio_median",
        "coincidence_ratio_max",
        "coincidence_ratio_positive_spread_decades",
        "epoch_ratio_min",
        "epoch_ratio_median",
        "epoch_ratio_max",
        "coincidence_order_unity_bounded",
    ]
    mismatches = {
        key: {"claimed": claimed.get(key), "derived": derived.get(key)}
        for key in keys
        if not close(claimed.get(key), derived.get(key))
    }
    payload = {"derived": derived, "mismatches": mismatches, "verdict_match": not mismatches}
    (args.results_dir / "controls").mkdir(parents=True, exist_ok=True)
    (args.results_dir / "controls" / "C5_validator_rederived.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"verdict_match": not mismatches, "mismatch_count": len(mismatches)}, sort_keys=True))
    return 0 if not mismatches else 1


if __name__ == "__main__":
    raise SystemExit(main())
