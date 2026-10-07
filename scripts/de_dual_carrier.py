#!/usr/bin/env python3
"""Lambda-slot-as-budget-dual recognition carrier.

Carrier-native finite optimization only.  The swept quantity is a global
closure budget B; the reported dual is the KKT shadow price of that budget.
No external measured value is used or compared.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import brentq


for _name in [
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
]:
    os.environ.setdefault(_name, "1")


REPO_ROOT = Path(__file__).resolve().parents[1]
OUTDIR = REPO_ROOT / "results" / "DE_dual"
CONTROLDIR = OUTDIR / "controls"


@dataclass(frozen=True)
class DualConfig:
    n_patches: int = 32
    weight_spread: float = 0.35
    curvature_spread: float = 0.22
    active_budget_fraction: float = 0.45
    slack_budget_factor: float = 1.35
    finite_diff_step_fraction: float = 2.5e-5
    tolerance: float = 1.0e-8
    seed: int = 26011


def fmt(value: Any) -> Any:
    if isinstance(value, (bool, int, np.integer)):
        return value
    if isinstance(value, (float, np.floating)):
        if not math.isfinite(float(value)):
            return ""
        return f"{float(value):.12e}"
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_csv(path: Path, rows: list[dict[str, Any]], fieldnames: list[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if fieldnames is None:
        fieldnames = list(rows[0].keys()) if rows else []
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: fmt(row.get(key, "")) for key in fieldnames})


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    def convert(obj: Any) -> Any:
        if isinstance(obj, dict):
            return {key: convert(value) for key, value in obj.items()}
        if isinstance(obj, list):
            return [convert(value) for value in obj]
        if isinstance(obj, (float, np.floating)):
            return fmt(obj)
        if isinstance(obj, (int, np.integer)):
            return int(obj)
        return obj

    path.write_text(json.dumps(convert(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def make_patch_params(cfg: DualConfig) -> tuple[np.ndarray, np.ndarray]:
    idx = np.arange(cfg.n_patches, dtype=float)
    weights = 1.15 + cfg.weight_spread * np.sin(0.37 * idx + 0.2) + 0.08 * np.cos(1.13 * idx)
    curvatures = 0.18 + cfg.curvature_spread * (0.55 + 0.45 * np.cos(0.29 * idx + 0.4))
    if np.any(weights <= 0.0) or np.any(curvatures <= 0.0):
        raise RuntimeError("patch parameters must be positive")
    return weights, curvatures


def utility(x: np.ndarray, weights: np.ndarray, curvatures: np.ndarray, linear_offset: float = 0.0) -> float:
    return float(np.sum(weights * np.log1p(x) - 0.5 * curvatures * x * x + linear_offset * x))


def derivative(x: np.ndarray, weights: np.ndarray, curvatures: np.ndarray, linear_offset: float = 0.0) -> np.ndarray:
    return weights / (1.0 + x) - curvatures * x + linear_offset


def x_from_dual(dual: float, weights: np.ndarray, curvatures: np.ndarray) -> np.ndarray:
    # The positive root of c*x^2 + (c+dual)*x + dual-w = 0.
    # Rationalize when c+dual >= 0 to avoid subtracting nearly equal roots.
    x = np.zeros_like(weights, dtype=float)
    interior = weights > dual
    c = curvatures[interior]
    w = weights[interior]
    b = c + dual
    root = np.hypot(c - dual, 2.0 * np.sqrt(c * w))
    positive_b = b >= 0.0
    values = np.empty_like(b)
    values[positive_b] = 2.0 * (w[positive_b] - dual) / (root[positive_b] + b[positive_b])
    values[~positive_b] = (root[~positive_b] - b[~positive_b]) / (2.0 * c[~positive_b])
    x[interior] = values
    return x


def unconstrained_x(weights: np.ndarray, curvatures: np.ndarray) -> np.ndarray:
    return x_from_dual(0.0, weights, curvatures)


def solve_global_budget(
    budget: float,
    weights: np.ndarray,
    curvatures: np.ndarray,
    linear_offset: float = 0.0,
) -> dict[str, Any]:
    weights = np.asarray(weights, dtype=float)
    curvatures = np.asarray(curvatures, dtype=float)
    if weights.ndim != 1 or weights.size == 0 or curvatures.shape != weights.shape:
        raise ValueError("weights and curvatures must be equal nonempty vectors")
    if not np.all(np.isfinite(weights)) or not np.all(np.isfinite(curvatures)) or np.any(weights <= 0) or np.any(curvatures <= 0):
        raise ValueError("weights and curvatures must be finite and positive")
    if not math.isfinite(budget) or budget < 0 or not math.isfinite(linear_offset):
        raise ValueError("budget must be finite and nonnegative; offset must be finite")
    x0 = x_from_dual(-linear_offset, weights, curvatures)
    unconstrained_sum = float(np.sum(x0))
    if budget == 0.0:
        x = np.zeros_like(weights)
        dual = max(0.0, float(np.max(weights)) + linear_offset)
        active = True
    elif budget >= unconstrained_sum:
        x = x0
        dual = 0.0
        active = budget == unconstrained_sum
    else:
        def excess(dual: float) -> float:
            return float(np.sum(x_from_dual(dual - linear_offset, weights, curvatures)) - budget)

        hi = max(1.0, float(np.max(weights)) + linear_offset)
        dual = float(brentq(excess, 0.0, hi, xtol=1.0e-13, rtol=1.0e-13, maxiter=200))
        x = x_from_dual(dual - linear_offset, weights, curvatures)
        active = True
    deriv = derivative(x, weights, curvatures, linear_offset)
    interior = x > 1.0e-10
    interior_residual = float(np.max(np.abs(deriv[interior] - dual))) if np.any(interior) else 0.0
    lower_bound_residual = float(np.max(np.maximum(deriv[~interior] - dual, 0.0))) if np.any(~interior) else 0.0
    stationarity_residual = max(interior_residual, lower_bound_residual)
    feasibility_residual = max(0.0, float(np.sum(x) - budget))
    complementarity_residual = float(abs(dual * (np.sum(x) - budget)))
    return {
        "budget": budget,
        "x": x,
        "dual": dual,
        "active": active,
        "objective": utility(x, weights, curvatures, linear_offset),
        "cost_value": -utility(x, weights, curvatures, linear_offset),
        "unconstrained_sum": unconstrained_sum,
        "stationarity_residual": stationarity_residual,
        "feasibility_residual": feasibility_residual,
        "complementarity_residual": complementarity_residual,
        "max_kkt_residual": max(stationarity_residual, feasibility_residual, complementarity_residual),
    }


def finite_diff_dual(
    budget: float,
    step: float,
    weights: np.ndarray,
    curvatures: np.ndarray,
) -> float:
    lo = solve_global_budget(budget - step, weights, curvatures)["cost_value"]
    hi = solve_global_budget(budget + step, weights, curvatures)["cost_value"]
    return -float((hi - lo) / (2.0 * step))


def dual_sweep(cfg: DualConfig, weights: np.ndarray, curvatures: np.ndarray) -> list[dict[str, Any]]:
    total = float(np.sum(unconstrained_x(weights, curvatures)))
    budgets = total * np.array([0.18, 0.28, 0.38, cfg.active_budget_fraction, 0.62, 0.82, 0.98, 1.02, 1.15, cfg.slack_budget_factor])
    rows: list[dict[str, Any]] = []
    for budget in budgets:
        sol = solve_global_budget(float(budget), weights, curvatures)
        step = max(1.0e-6, float(budget) * cfg.finite_diff_step_fraction)
        if budget - step <= 0.0:
            step = budget * 0.25
        fd = finite_diff_dual(float(budget), step, weights, curvatures)
        rows.append(
            {
                "budget": sol["budget"],
                "active": sol["active"],
                "dual_shadow_price": sol["dual"],
                "finite_diff_minus_dcost_dB": fd,
                "dual_fd_abs_error": abs(sol["dual"] - fd),
                "objective_value": sol["objective"],
                "cost_value": sol["cost_value"],
                "sum_x": float(np.sum(sol["x"])),
                "unconstrained_sum": sol["unconstrained_sum"],
                "stationarity_residual": sol["stationarity_residual"],
                "feasibility_residual": sol["feasibility_residual"],
                "complementarity_residual": sol["complementarity_residual"],
                "max_kkt_residual": sol["max_kkt_residual"],
            }
        )
    return rows


def constancy_rows(cfg: DualConfig, weights: np.ndarray, curvatures: np.ndarray) -> list[dict[str, Any]]:
    total = float(np.sum(unconstrained_x(weights, curvatures)))
    budget = total * cfg.active_budget_fraction
    sol = solve_global_budget(budget, weights, curvatures)
    deriv = derivative(sol["x"], weights, curvatures)
    rows = []
    for i, (weight, curvature, x, dval) in enumerate(zip(weights, curvatures, sol["x"], deriv)):
        rows.append(
            {
                "patch": i,
                "weight": float(weight),
                "curvature": float(curvature),
                "x_star": float(x),
                "local_marginal": float(dval),
                "global_dual": sol["dual"],
                "stationarity_gap": float(dval - sol["dual"]),
            }
        )
    return rows


def local_budget_control(cfg: DualConfig, weights: np.ndarray, curvatures: np.ndarray) -> list[dict[str, Any]]:
    total = float(np.sum(unconstrained_x(weights, curvatures)))
    budget = total * cfg.active_budget_fraction
    local_budget = budget / len(weights)
    rows = []
    for i, (weight, curvature) in enumerate(zip(weights, curvatures)):
        x = min(float(unconstrained_x(np.array([weight]), np.array([curvature]))[0]), local_budget)
        dual = max(0.0, float(derivative(np.array([x]), np.array([weight]), np.array([curvature]))[0]))
        rows.append(
            {
                "patch": i,
                "local_budget": local_budget,
                "x_star": x,
                "local_dual": dual,
            }
        )
    return rows


def vacuum_shift_rows(cfg: DualConfig, weights: np.ndarray, curvatures: np.ndarray) -> list[dict[str, Any]]:
    total = float(np.sum(unconstrained_x(weights, curvatures)))
    budget = total * cfg.active_budget_fraction
    base = solve_global_budget(budget, weights, curvatures)
    rows = []
    for offset in [-0.2, 0.0, 0.2]:
        shifted = solve_global_budget(budget, weights, curvatures, linear_offset=offset)
        dual_shift = float(shifted["dual"] - base["dual"])
        rows.append(
            {
                "variant": "budget_dual_linear_offset",
                "offset": offset,
                "budget": budget,
                "dual_shadow_price": shifted["dual"],
                "max_abs_x_shift_from_base": float(np.max(np.abs(shifted["x"] - base["x"]))),
                "dual_shift_from_base": dual_shift,
                "dual_shift_minus_offset": dual_shift - offset,
                "objective_shift_from_base": float(shifted["objective"] - base["objective"]),
            }
        )
    for source in [-0.2, 0.0, 0.2]:
        # Source-coupled control: no binding global budget; the same linear
        # offset is placed in the local stationarity equation itself.
        x = x_from_dual(-source, weights, curvatures)
        rows.append(
            {
                "variant": "source_coupled_no_global_budget",
                "offset": source,
                "budget": "",
                "dual_shadow_price": 0.0,
                "max_abs_x_shift_from_base": float(np.max(np.abs(x - unconstrained_x(weights, curvatures)))),
                "dual_shift_from_base": "",
                "dual_shift_minus_offset": "",
                "objective_shift_from_base": "",
            }
        )
    return rows


def slack_rows(cfg: DualConfig, weights: np.ndarray, curvatures: np.ndarray) -> list[dict[str, Any]]:
    total = float(np.sum(unconstrained_x(weights, curvatures)))
    rows = []
    for factor in [0.82, 0.98, 1.02, 1.15, cfg.slack_budget_factor]:
        sol = solve_global_budget(total * factor, weights, curvatures)
        rows.append(
            {
                "budget_factor_to_unconstrained": factor,
                "budget": sol["budget"],
                "sum_x": float(np.sum(sol["x"])),
                "active": sol["active"],
                "dual_shadow_price": sol["dual"],
                "max_kkt_residual": sol["max_kkt_residual"],
            }
        )
    return rows


def build_verdict_json(
    dual_rows: list[dict[str, Any]],
    const_rows: list[dict[str, Any]],
    local_rows: list[dict[str, Any]],
    vacuum_rows: list[dict[str, Any]],
    slack: list[dict[str, Any]],
    cfg: DualConfig,
) -> dict[str, Any]:
    active_dual_rows = [row for row in dual_rows if bool(row["active"])]
    max_kkt = max(float(row["max_kkt_residual"]) for row in dual_rows)
    max_fd = max(float(row["dual_fd_abs_error"]) for row in dual_rows)
    x_values = np.array([float(row["x_star"]) for row in const_rows])
    gaps = np.array([float(row["stationarity_gap"]) for row in const_rows])
    local_duals = np.array([float(row["local_dual"]) for row in local_rows])
    budget_shift_rows = [row for row in vacuum_rows if row["variant"] == "budget_dual_linear_offset"]
    source_rows = [row for row in vacuum_rows if row["variant"] == "source_coupled_no_global_budget"]
    budget_invariant = max(float(row["max_abs_x_shift_from_base"]) for row in budget_shift_rows) < 1.0e-10 and max(
        abs(float(row["dual_shift_minus_offset"])) for row in budget_shift_rows
    ) < 1.0e-10
    source_moves = max(float(row["max_abs_x_shift_from_base"]) for row in source_rows) > 1.0e-3
    slack_collapse = all((not bool(row["active"])) and abs(float(row["dual_shadow_price"])) <= cfg.tolerance for row in slack if float(row["budget_factor_to_unconstrained"]) > 1.0)
    return {
        "max_kkt_residual": max_kkt,
        "max_dual_finite_difference_error": max_fd,
        "global_dual_constant": bool(np.max(np.abs(gaps)) <= cfg.tolerance),
        "heterogeneous_allocations": bool(np.std(x_values) > 1.0e-2),
        "local_budget_control_flips": bool(np.std(local_duals) > 1.0e-2),
        "vacuum_shift_state_screened_dual_absorbs_offset": bool(budget_invariant),
        "source_coupled_control_moves": bool(source_moves),
        "slack_collapse": bool(slack_collapse),
        "recognition_payoff_passes": bool(
            max_kkt <= cfg.tolerance
            and max_fd <= 5.0e-7
            and np.max(np.abs(gaps)) <= cfg.tolerance
            and np.std(x_values) > 1.0e-2
            and np.std(local_duals) > 1.0e-2
            and budget_invariant
            and source_moves
            and slack_collapse
        ),
        "active_budget_count": len(active_dual_rows),
        "slack_budget_count": len(dual_rows) - len(active_dual_rows),
    }


def run_validator() -> dict[str, Any]:
    completed = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts" / "de_dual_validate.py"), "--results-dir", str(OUTDIR)],
        check=False,
        text=True,
        capture_output=True,
    )
    (CONTROLDIR / "C5_validator_stdout.txt").write_text(completed.stdout, encoding="utf-8")
    (CONTROLDIR / "C5_validator_stderr.txt").write_text(completed.stderr, encoding="utf-8")
    return {"control": "C5_verdict_rederivation", "passes": completed.returncode == 0, "returncode": completed.returncode}


def write_verdict(verdict: dict[str, Any], validator: dict[str, Any]) -> None:
    lines = [
        "# Lambda-slot budget-dual recognition verdict",
        "",
        "Status: RUN-frame toy recognition in carrier-native units only. The budget level is an external modulus of this carrier; no value law is claimed.",
        "",
        "## Computed payoffs",
        f"1. Spatial constancy: `{verdict['global_dual_constant']}`. Heterogeneous patches have different allocations while the active global-budget dual is one shared number.",
        f"2. Budget-set decoupling: `{verdict['vacuum_shift_state_screened_dual_absorbs_offset']}`. Linear in-layer offsets leave the selected state invariant on the binding budget surface, while the multiplier absorbs the offset.",
        f"   Source-coupled control moves: `{verdict['source_coupled_control_moves']}`.",
        f"3. Slack collapse: `{verdict['slack_collapse']}`. Budgets above the unconstrained optimum have zero shadow price.",
        f"4. Dual pairing: max KKT residual `{fmt(verdict['max_kkt_residual'])}`; max finite-difference dual error `{fmt(verdict['max_dual_finite_difference_error'])}`.",
        "",
        "## Controls",
        f"- Local-budget control flips constancy: `{verdict['local_budget_control_flips']}`.",
        f"- Heterogeneity contrast present: `{verdict['heterogeneous_allocations']}`.",
        f"- Validator re-derivation: `{validator['passes']}`.",
        "",
        "## Honest grading",
        "This is RECOGNITION at toy level: the constant slot form is recognized as the shadow price of one global closure budget, with vacuum-shift decoupling and slack collapse. It is not a derivation of the dual value, not a continuum gravity computation, and not a frame-transfer claim. The mainstream shadow is the Lagrange-multiplier reading of a constant background term; the carrier here only computes the finite optimization analogue.",
        "",
    ]
    (OUTDIR / "VERDICT.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    cfg = DualConfig()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    CONTROLDIR.mkdir(parents=True, exist_ok=True)
    weights, curvatures = make_patch_params(cfg)
    patch_rows = [
        {"patch": i, "weight": float(weight), "curvature": float(curvature)}
        for i, (weight, curvature) in enumerate(zip(weights, curvatures))
    ]
    dual_rows = dual_sweep(cfg, weights, curvatures)
    const_rows = constancy_rows(cfg, weights, curvatures)
    local_rows = local_budget_control(cfg, weights, curvatures)
    vacuum_rows = vacuum_shift_rows(cfg, weights, curvatures)
    slack = slack_rows(cfg, weights, curvatures)
    verdict = build_verdict_json(dual_rows, const_rows, local_rows, vacuum_rows, slack, cfg)

    write_csv(OUTDIR / "patch_parameters.csv", patch_rows)
    write_csv(OUTDIR / "dual_sweep.csv", dual_rows)
    write_csv(OUTDIR / "constancy.csv", const_rows)
    write_csv(OUTDIR / "vacuum_shift.csv", vacuum_rows)
    write_csv(CONTROLDIR / "local_budget_control.csv", local_rows)
    write_csv(CONTROLDIR / "slack_collapse.csv", slack)
    write_json(OUTDIR / "verdict.json", verdict)
    validator = run_validator()
    write_verdict(verdict, validator)
    controls = {
        "controls": [
            {"control": "local_budget_control", "passes": verdict["local_budget_control_flips"]},
            {"control": "source_coupled_control", "passes": verdict["source_coupled_control_moves"]},
            {"control": "slack_collapse", "passes": verdict["slack_collapse"]},
            validator,
        ]
    }
    write_json(CONTROLDIR / "controls_summary.json", controls)

    sources = [
        REPO_ROOT / "results" / "DE_DEMARCATION_RELANDING_2026-06-11.md",
        Path("../six-birds-sm-qm-gr/paper/sections/sec_05_result_qmgr.tex").resolve(),
        REPO_ROOT / "lean" / "SbtCosmo" / "Derivation" / "ClosurePrice.lean",
    ]
    write_json(
        OUTDIR / "run_manifest.json",
        {
            "carrier_units": "dimensionless finite closure-budget units",
            "config": cfg.__dict__,
            "sources": {str(path): sha256(path) for path in sources if path.exists()},
            "outputs": {
                "dual_sweep.csv": sha256(OUTDIR / "dual_sweep.csv"),
                "constancy.csv": sha256(OUTDIR / "constancy.csv"),
                "vacuum_shift.csv": sha256(OUTDIR / "vacuum_shift.csv"),
                "VERDICT.md": sha256(OUTDIR / "VERDICT.md"),
            },
        },
    )
    success = bool(verdict["recognition_payoff_passes"] and validator["passes"])
    print(
        json.dumps(
            {
                "outdir": str(OUTDIR.relative_to(REPO_ROOT)),
                "recognition_payoff_passes": success,
                "max_kkt_residual": fmt(verdict["max_kkt_residual"]),
                "max_fd_error": fmt(verdict["max_dual_finite_difference_error"]),
            },
            sort_keys=True,
        )
    )
    return 0 if success else 2


if __name__ == "__main__":
    raise SystemExit(main())
