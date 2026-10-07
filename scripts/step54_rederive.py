#!/usr/bin/env python3
"""Independent local re-derivation for vendored Step54 F50 reproduction."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SOURCE_STEP54 = (
    REPO_ROOT
    / "../six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step54_f50_background_moduli_demarcation_artifacts"
).resolve()
VENDORED_STEP54 = (
    REPO_ROOT
    / "external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step54_f50_background_moduli_demarcation_artifacts"
)
OUTDIR = REPO_ROOT / "results" / "DE_step54_repro"
RESIDUAL_COLUMNS = [
    "final_update_residual",
    "fixed_point_residual",
    "final_eigen_residual",
    "potential_sourcing_residual",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


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


def residual_pass(row: dict[str, str]) -> bool:
    tol = float(row["convergence_tol"])
    return math.isfinite(tol) and tol >= 0 and all(
        math.isfinite(float(row[col])) and 0 <= float(row[col]) <= tol
        for col in RESIDUAL_COLUMNS
    )


def derive_background(rows: list[dict[str, str]]) -> dict[str, Any]:
    pass_offsets = [float(row["background_offset"]) for row in rows if residual_pass(row)]
    fail_offsets = [float(row["background_offset"]) for row in rows if not residual_pass(row)]
    pass_count = len(pass_offsets)
    degeneracy = len(set(pass_offsets))
    if pass_count == 0:
        classification = "no_admissible_background_in_sweep"
        verdict = "BACKGROUND_SELECTION_BLOCKED_NO_ADMISSIBLE_SWEEP_POINT"
    elif degeneracy == 1:
        classification = "vacuum"
        verdict = "BACKGROUND_SINGLETON_VACUUM_ON_FINITE_SWEEP"
    elif pass_count == len(rows):
        classification = "moduli"
        verdict = "DECLARED_AUDIT_NONSELECTING_ON_FINITE_SWEEP"
    else:
        classification = "bounded_moduli"
        verdict = "DECLARED_AUDIT_NONSELECTING_ON_FINITE_SWEEP"
    return {
        "classification": classification,
        "verdict": verdict,
        "pass_offsets": pass_offsets,
        "fail_offsets": fail_offsets,
        "pass_count": pass_count,
        "fail_count": len(fail_offsets),
        "degeneracy": degeneracy,
        "total": len(rows),
        "singleton": degeneracy == 1,
        "evidence_scope": "recorded finite sweep under the frozen iteration count and tolerance",
        "background_independence_proved": False,
        "unrestricted_no_selector_proved": False,
        "continuum_bound_proved": False,
    }


def derive_kappa(rows: list[dict[str, str]]) -> dict[str, Any]:
    pass_values = [float(row["kappa"]) for row in rows if residual_pass(row)]
    fail_values = [float(row["kappa"]) for row in rows if not residual_pass(row)]
    return {
        "pass_values": pass_values,
        "fail_values": fail_values,
        "boundary_found": bool(pass_values and fail_values and min(fail_values) > max(pass_values)),
        "max_pass": max(pass_values) if pass_values else None,
        "min_fail": min(fail_values) if fail_values else None,
        "boundary_kind": "finite_budget_pass_fail_separation",
        "evidence_scope": "recorded finite sweep under the frozen iteration count and tolerance",
        "ground_state_nonexistence_proved": False,
        "runaway_proved": False,
        "linear_stability_boundary_proved": False,
    }


def compare_rows(
    ours: list[dict[str, str]],
    source: list[dict[str, str]],
    key: str,
    value_column: str,
) -> list[dict[str, Any]]:
    if len({row[key] for row in ours}) != len(ours) or len({row[key] for row in source}) != len(source):
        raise ValueError("duplicate comparison keys")
    if {row[key] for row in ours} != {row[key] for row in source}:
        raise ValueError("comparison case sets differ")
    source_by_key = {row[key]: row for row in source}
    rows: list[dict[str, Any]] = []
    for row in ours:
        src = source_by_key[row[key]]
        out: dict[str, Any] = {
            key: row[key],
            value_column: row[value_column],
            "ours_pass": residual_pass(row),
            "source_pass": residual_pass(src),
            "pass_match": residual_pass(row) == residual_pass(src),
            "value_match": float(row[value_column]) == float(src[value_column]),
        }
        for col in RESIDUAL_COLUMNS:
            ours_val = float(row[col])
            source_val = float(src[col])
            out[f"ours_{col}"] = f"{ours_val:.12g}"
            out[f"source_{col}"] = f"{source_val:.12g}"
            out[f"{col}_abs_delta"] = f"{abs(ours_val - source_val):.12g}"
        rows.append(out)
    return rows


def verdict_text(bg: dict[str, Any], kappa: dict[str, Any], comparison_ok: bool, validator_ok: bool) -> str:
    expected_bg = bg["pass_count"] == 15 and bg["fail_offsets"] == [-5.0, -3.0, 10.0] and bg["degeneracy"] == 15
    expected_kappa = kappa["pass_values"] == [0.0, 0.1, 0.3, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0] and kappa["fail_values"] == [15.0, 20.0, 30.0]
    reproduced = bool(expected_bg and expected_kappa and comparison_ok and validator_ok)
    lines = [
        "# Step54 Local Reproduction Verdict",
        "",
        f"Reproduced: `{reproduced}`.",
        "",
        "## Independent Re-Derivation",
        f"- Background pass count: `{bg['pass_count']}/{bg['total']}`.",
        f"- Background fails: `{bg['fail_offsets']}`.",
        f"- Background degeneracy: `{bg['degeneracy']}`.",
        f"- Classification: `{bg['classification']}`.",
        f"- Verdict: `{bg['verdict']}`.",
        f"- Kappa pass values: `{kappa['pass_values']}`.",
        f"- Kappa fail values: `{kappa['fail_values']}`.",
        f"- Kappa finite-budget pass/fail separation found: `{kappa['boundary_found']}`.",
        "",
        "## Comparison",
        f"- Regenerated-vs-source pass/residual comparison OK: `{comparison_ok}`.",
        f"- Vendored source validator OK: `{validator_ok}`.",
        "",
        "This is a local reproduction of the dependency-corpus finite sweep. It does not modify the source corpus and does not derive a physical cosmological value.",
        "A failed finite-budget residual audit proves neither absence of a fixed point nor runaway. The sweep alone does not certify a linear-stability boundary.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--vendored-dir", type=Path, default=VENDORED_STEP54)
    parser.add_argument("--source-dir", type=Path, default=SOURCE_STEP54)
    parser.add_argument("--outdir", type=Path, default=OUTDIR)
    parser.add_argument("--validator-returncode", type=int, default=0)
    args = parser.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)
    bg_rows = read_csv(args.vendored_dir / "background_sweep_step54.csv")
    k_rows = read_csv(args.vendored_dir / "kappa_sweep_step54.csv")
    src_bg = read_csv(args.source_dir / "background_sweep_step54.csv")
    src_k = read_csv(args.source_dir / "kappa_sweep_step54.csv")

    bg = derive_background(bg_rows)
    kappa = derive_kappa(k_rows)
    bg_comp = compare_rows(bg_rows, src_bg, "case_id", "background_offset")
    k_comp = compare_rows(k_rows, src_k, "case_id", "kappa")
    comparison_ok = all(row["pass_match"] and row["value_match"] for row in bg_comp + k_comp) and all(
        float(row[col]) <= 1.0e-10
        for row in bg_comp + k_comp
        for col in [f"{residual}_abs_delta" for residual in RESIDUAL_COLUMNS]
    )
    validator_ok = args.validator_returncode == 0

    write_csv(args.outdir / "background_comparison.csv", bg_comp)
    write_csv(args.outdir / "kappa_comparison.csv", k_comp)
    write_json(
        args.outdir / "self_check.json",
        {
            "background": bg,
            "kappa": kappa,
            "comparison_ok": comparison_ok,
            "validator_ok": validator_ok,
            "vendored_hashes": {
                "background_sweep_step54.csv": sha256(args.vendored_dir / "background_sweep_step54.csv"),
                "kappa_sweep_step54.csv": sha256(args.vendored_dir / "kappa_sweep_step54.csv"),
                "step54_schema.json": sha256(args.vendored_dir / "step54_schema.json"),
            },
            "source_hashes": {
                "background_sweep_step54.csv": sha256(args.source_dir / "background_sweep_step54.csv"),
                "kappa_sweep_step54.csv": sha256(args.source_dir / "kappa_sweep_step54.csv"),
                "step54_schema.json": sha256(args.source_dir / "step54_schema.json"),
            },
        },
    )
    (args.outdir / "VERDICT.md").write_text(
        verdict_text(bg, kappa, comparison_ok=comparison_ok, validator_ok=validator_ok),
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "background_pass_count": bg["pass_count"],
                "background_fail_offsets": bg["fail_offsets"],
                "background_degeneracy": bg["degeneracy"],
                "kappa_boundary_found": kappa["boundary_found"],
                "comparison_ok": comparison_ok,
                "validator_ok": validator_ok,
            },
            sort_keys=True,
        )
    )
    expected = (
        bg["pass_count"] == 15
        and bg["fail_offsets"] == [-5.0, -3.0, 10.0]
        and bg["degeneracy"] == 15
        and kappa["boundary_found"]
        and comparison_ok
        and validator_ok
    )
    return 0 if expected else 2


if __name__ == "__main__":
    raise SystemExit(main())
