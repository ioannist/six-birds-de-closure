from __future__ import annotations

import csv
from fractions import Fraction
import itertools
import math
from pathlib import Path
import shutil

import numpy as np
import pytest

from sbt_cosmo.audits.calibration import rank_calibration, upper_rank_pvalue
from scripts import de_audit_run as run
from scripts import de_audit_b2_fix as localized
from scripts import de_audit_validate as validator


ROOT = Path(__file__).resolve().parents[1]


def test_rank_rule_exhaustive_small_vectors_including_ties() -> None:
    # Every vector has exchangeable omission under a uniform future index.
    # Enumeration tests the actual rejection count, independently of ceil logic.
    for size in range(2, 9):
        for values in itertools.combinations_with_replacement(range(3), size):
            for level in [Fraction(1, 20), Fraction(1, 4), Fraction(1, 2), Fraction(2, 3)]:
                rejected = 0
                for index, value in enumerate(values):
                    null = values[:index] + values[index + 1:]
                    cutoff = rank_calibration(null, level)["null_threshold_p95"]
                    decision = value > cutoff
                    assert decision == (upper_rank_pvalue(null, value) <= level)
                    rejected += decision
                assert Fraction(rejected, size) <= level


def test_interpolated_p95_has_exchangeable_counterexample() -> None:
    rejected_legacy = rejected_rank = 0
    for value in range(21):
        null = [other for other in range(21) if other != value]
        rejected_legacy += value > np.quantile(null, 0.95)
        rejected_rank += value > rank_calibration(null)["null_threshold_p95"]
    assert Fraction(int(rejected_legacy), 21) == Fraction(2, 21) > Fraction(1, 20)
    assert Fraction(rejected_rank, 21) == Fraction(1, 21) < Fraction(1, 20)


def test_resolution_ties_and_invalid_inputs() -> None:
    assert math.isinf(rank_calibration([0.0], 0.05)["null_threshold_p95"])
    assert upper_rank_pvalue([3.0] * 20, 3.0) == 1
    assert upper_rank_pvalue([3.0] * 20, 4.0) == Fraction(1, 21)
    for values in [[], [math.nan], [math.inf]]:
        with pytest.raises(ValueError):
            rank_calibration(values)
    for level in [0, 1, -0.1, math.nan, math.inf, True]:
        with pytest.raises(ValueError):
            rank_calibration([1.0, 2.0], level)


def test_original_and_localized_builders_use_rank_cutoff(monkeypatch) -> None:
    base = run.FitResult("lcdm", "joint", {"omega_b": 0.02, "omega_cdm": 0.12, "H0": 68}, 0, 0, 0, True, "")
    monkeypatch.setattr(run, "make_mock_block", lambda *args: object())
    monkeypatch.setattr(run, "split_blocks", lambda *args: {})
    monkeypatch.setattr(run, "fit_rewrite_splits", lambda *args, **kwargs: {})
    scores = iter(list(range(20)) + [100] * 80)
    monkeypatch.setattr(run, "staging_score", lambda *args: next(scores))
    rows, summary = run.b2_calibration(None, None, None, base)
    assert summary["null_threshold_p95"] == 19
    assert summary["null_calibration_method"] == "finite_rank_v1"
    assert summary["anti_vacuity_pass"]
    assert all(row["null_rank_index"] == 20 for row in rows)

    monkeypatch.setattr(localized, "make_mock_block", lambda *args: object())
    monkeypatch.setattr(localized, "inject_sn_tilt", lambda block, epsilon: block)
    monkeypatch.setattr(localized, "inject_bao_tilt", lambda block, epsilon: block)
    scores = iter(list(range(20)) + [100] * 200)
    monkeypatch.setattr(localized, "fit_score", lambda *args: (next(scores), "sn_high_z", {}))
    rows, summary = localized.calibration(None, None, None, base)
    assert summary["null_threshold_p95"] == 19
    assert summary["null_calibration_method"] == "finite_rank_v1"
    assert summary["epsilon_detect_sn_localized"] == 0.01


def test_validator_legacy_and_versioned_frozen_data(tmp_path) -> None:
    source = ROOT / "results/DE_audit"
    legacy = validator.derive(source)
    assert legacy["b2_real_structured_dependence_fires"]
    for filename in ["B1_model_table.csv", "B2_staging_audit.csv"]:
        shutil.copyfile(source / filename, tmp_path / filename)
    rows = validator.read_csv(source / "B2_calibration.csv")
    null = [float(row["staging_score"]) for row in rows if row["kind"] == "lcdm_null"]
    calibration = rank_calibration(null)
    for row in rows:
        row.update(calibration)
    with (tmp_path / "B2_calibration.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    repaired = validator.derive(tmp_path)
    assert repaired["b2_null_threshold_p95"] == max(null)
    assert repaired["b2_real_structured_dependence_fires"]
    assert repaired["b2_epsilon_detect_sn_localized"] == 0.2
    assert repaired["b2_epsilon_detect_bao_localized"] == 0.1
    assert repaired["b2_null_false_alarm_rate_empirical"] == 0


def test_validator_rejects_forged_real_score() -> None:
    rows = validator.read_csv(ROOT / "results/DE_audit/B2_staging_audit.csv")
    for row in rows:
        row["staging_score"] = "100"
    with pytest.raises(ValueError, match="raw split calculation"):
        validator.real_staging_score(rows)


def test_validator_rejects_forged_localization() -> None:
    rows = validator.read_csv(ROOT / "results/DE_audit/B2_staging_audit.csv")
    for row in rows:
        row["max_split"] = "bao_only"
    with pytest.raises(ValueError, match="driving split"):
        validator.real_staging_score(rows)


def test_common_estimate_shift_preserves_score_and_existing_rejection() -> None:
    fits = {
        "joint": run.FitResult("rewrite_power", "joint", {"m": 0}, 0, 0, 0, True, "", m_sigma=0.1),
        "split": run.FitResult("rewrite_power", "split", {"m": 1}, 0, 0, 0, True, "", m_sigma=0.1),
    }
    before = run.staging_score(fits)
    for fit in fits.values():
        fit.params["m"] += 10
    assert run.staging_score(fits) == before > 5


def test_exact_alpha_survives_metadata_roundtrip() -> None:
    summary = rank_calibration([0, 1], Fraction(1, 3))
    rows = [{key: str(value) for key, value in summary.items()}] * 2
    cutoff, metadata = validator.null_cutoff(rows, [0, 1])
    assert cutoff == 1
    assert metadata["b2_null_rank_index"] == 2
    assert metadata["b2_null_alpha_fraction"] == "1/3"
