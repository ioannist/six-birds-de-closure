#!/usr/bin/env python3
"""Independent verdict re-derivation for the DE dual carrier."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


TOL = 1.0e-8


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def truth(value: Any) -> bool:
    return str(value) == "True" or value is True


def fnum(value: Any) -> float:
    if value == "" or value is None:
        return math.nan
    return float(value)


def derive(results_dir: Path) -> dict[str, Any]:
    dual = read_csv(results_dir / "dual_sweep.csv")
    const = read_csv(results_dir / "constancy.csv")
    vacuum = read_csv(results_dir / "vacuum_shift.csv")
    local = read_csv(results_dir / "controls" / "local_budget_control.csv")
    slack = read_csv(results_dir / "controls" / "slack_collapse.csv")

    max_kkt = max(fnum(row["max_kkt_residual"]) for row in dual)
    max_fd = max(fnum(row["dual_fd_abs_error"]) for row in dual)
    gaps = np.array([fnum(row["stationarity_gap"]) for row in const])
    x_values = np.array([fnum(row["x_star"]) for row in const])
    local_duals = np.array([fnum(row["local_dual"]) for row in local])
    budget_rows = [row for row in vacuum if row["variant"] == "budget_dual_linear_offset"]
    source_rows = [row for row in vacuum if row["variant"] == "source_coupled_no_global_budget"]
    budget_invariant = max(fnum(row["max_abs_x_shift_from_base"]) for row in budget_rows) < 1.0e-10 and max(
        abs(fnum(row["dual_shift_minus_offset"])) for row in budget_rows
    ) < 1.0e-10
    source_moves = max(fnum(row["max_abs_x_shift_from_base"]) for row in source_rows) > 1.0e-3
    slack_collapse = all((not truth(row["active"])) and abs(fnum(row["dual_shadow_price"])) <= TOL for row in slack if fnum(row["budget_factor_to_unconstrained"]) > 1.0)
    return {
        "max_kkt_residual": max_kkt,
        "max_dual_finite_difference_error": max_fd,
        "global_dual_constant": bool(np.max(np.abs(gaps)) <= TOL),
        "heterogeneous_allocations": bool(np.std(x_values) > 1.0e-2),
        "local_budget_control_flips": bool(np.std(local_duals) > 1.0e-2),
        "vacuum_shift_state_screened_dual_absorbs_offset": bool(budget_invariant),
        "source_coupled_control_moves": bool(source_moves),
        "slack_collapse": bool(slack_collapse),
        "recognition_payoff_passes": bool(
            max_kkt <= TOL
            and max_fd <= 5.0e-7
            and np.max(np.abs(gaps)) <= TOL
            and np.std(x_values) > 1.0e-2
            and np.std(local_duals) > 1.0e-2
            and budget_invariant
            and source_moves
            and slack_collapse
        ),
    }


def close(a: Any, b: Any, tol: float = 1.0e-9) -> bool:
    if isinstance(a, bool) or isinstance(b, bool):
        return bool(a) == bool(b)
    return math.isclose(float(a), float(b), rel_tol=tol, abs_tol=tol)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results-dir", type=Path, default=Path("results/DE_dual"))
    args = parser.parse_args()
    derived = derive(args.results_dir)
    claimed = json.loads((args.results_dir / "verdict.json").read_text(encoding="utf-8"))
    keys = [
        "max_kkt_residual",
        "max_dual_finite_difference_error",
        "global_dual_constant",
        "heterogeneous_allocations",
        "local_budget_control_flips",
        "vacuum_shift_state_screened_dual_absorbs_offset",
        "source_coupled_control_moves",
        "slack_collapse",
        "recognition_payoff_passes",
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
