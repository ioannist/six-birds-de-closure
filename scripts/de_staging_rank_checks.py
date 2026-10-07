#!/usr/bin/env python3
"""Recheck frozen B2 under finite-rank calibration without rewriting its tables.

This is a documented review amendment, not a retroactive preregistration.
The exchangeable level theorem is conditional; the real-data fitted anchor
does not automatically supply its premise.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from sbt_cosmo.audits.calibration import rank_calibration, upper_rank_pvalue
from scripts.de_audit_validate import derive, real_staging_score


def recompute() -> dict:
    directory = ROOT / "results/DE_audit"
    with (directory / "B2_calibration.csv").open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    with (directory / "B2_staging_audit.csv").open(newline="") as handle:
        real_rows = list(csv.DictReader(handle))
    null = [Fraction(row["staging_score"]) for row in rows if row["kind"] == "lcdm_null"]
    assert len(null) == 20
    calibration = rank_calibration(null)
    cutoff = max(null)
    assert calibration["null_threshold_p95"] == float(cutoff)
    real = real_staging_score(real_rows)
    legacy = derive(directory)
    assert real == legacy["b2_real_staging_score"]
    real_rank = upper_rank_pvalue(null, real)
    assert real_rank == Fraction(1, 21) < Fraction(1, 20)
    curves = []
    detects = {}
    for cls in ["sn_localized", "bao_localized"]:
        first = None
        amplitudes = sorted({Fraction(row["epsilon"]) for row in rows if row.get("class") == cls})
        for epsilon in amplitudes:
            scores = [Fraction(row["staging_score"]) for row in rows
                      if row.get("class") == cls and Fraction(row["epsilon"]) == epsilon]
            count = sum(score > cutoff for score in scores)
            rate = Fraction(count, len(scores))
            curves.append({"class": cls, "epsilon": str(epsilon), "trials": len(scores),
                           "rejections": count, "empirical_rate": str(rate)})
            if rate >= Fraction(4, 5) and first is None:
                first = epsilon
        detects[cls] = str(first)
    assert detects == {"sn_localized": "1/5", "bao_localized": "1/10"}

    # Exact rederivation of every omitted-array interpolation in the Lean control.
    omission_rows = []
    for i in range(21):
        scores = [Fraction(j) for j in range(21) if i != j]
        interpolated = Fraction(19, 20)*scores[-2] + Fraction(1, 20)*scores[-1]
        declared = Fraction(19)+Fraction(1, 20) if i < 19 else (
            Fraction(18)+Fraction(2, 20) if i == 19 else Fraction(18)+Fraction(1, 20))
        assert interpolated == declared
        assert abs(float(interpolated)-np.quantile(scores, 0.95)) < 1e-12
        conservative = max(scores)
        assert rank_calibration(scores)["null_threshold_p95"] == float(conservative)
        omission_rows.append({"future_index": i, "legacy_cutoff": str(interpolated),
                              "rank_cutoff": str(conservative),
                              "legacy_fires": i > interpolated, "rank_fires": i > conservative})
    legacy_rate = Fraction(sum(row["legacy_fires"] for row in omission_rows), 21)
    rank_rate = Fraction(sum(row["rank_fires"] for row in omission_rows), 21)
    assert legacy_rate == Fraction(2, 21) > Fraction(1, 20)
    assert rank_rate == Fraction(1, 21) < Fraction(1, 20)
    inputs = [directory / "B2_calibration.csv", directory / "B2_staging_audit.csv",
              directory / "B1_model_table.csv", Path(__file__),
              ROOT / "sbt_cosmo/audits/calibration.py", ROOT / "scripts/de_audit_validate.py",
              ROOT / "scripts/de_audit_run.py", ROOT / "scripts/de_audit_b2_fix.py",
              ROOT / "lean/SbtCosmo/Derivation/StagingAudit.lean"]
    return {
        "baseline_commit": "ecce4b3",
        "scope": "finite review amendment; no retroactive preregistration or population-level real-data significance",
        "calibration": calibration,
        "frozen_legacy_threshold": legacy["b2_null_threshold_p95"],
        "real_staging_score_recomputed_from_split_parameters": real,
        "real_rank_fraction": str(real_rank),
        "real_fires_under_rank_rule": real > float(cutoff),
        "empirical_detection_grid": detects,
        "empirical_injection_curves": curves,
        "omission_counterexample": {"legacy_rate": str(legacy_rate), "rank_rate": str(rank_rate),
                                   "exhaustive_rows": omission_rows},
        "bound_premise": "future and mock scores must be exchangeable under the complete fixed fitting/design procedure",
        "real_data_exchangeability_established": False,
        "frozen_artifacts_changed": False,
        "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=ROOT / "results/staging_rank_2026-10-02")
    args = parser.parse_args()
    receipt = recompute()
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir / "receipt.json").write_text(json.dumps(receipt, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"real_fires": receipt["real_fires_under_rank_rule"],
                      "threshold": receipt["calibration"]["null_threshold_p95"],
                      "empirical_detection_grid": receipt["empirical_detection_grid"]}))


if __name__ == "__main__":
    main()
