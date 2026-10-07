#!/usr/bin/env python3
"""Re-derive the DE audit verdict from committed CSV artifacts."""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def fnum(value: Any) -> float:
    if value in ("", None):
        return math.nan
    return float(value)


def truth(value: Any) -> bool:
    return value is True or str(value) == "True"


def null_cutoff(rows: list[dict[str, str]], scores: list[float]) -> tuple[float, dict[str, Any]]:
    """Independent rederivation of legacy or versioned finite-rank calibration."""
    if not scores or not all(math.isfinite(value) for value in scores):
        raise ValueError("require finite, nonempty null calibration")
    methods = {row.get("null_calibration_method") or "empirical_quantile_legacy" for row in rows}
    if len(methods) != 1:
        raise ValueError("mixed null calibration protocols")
    method = methods.pop()
    if method == "empirical_quantile_legacy":
        # Frozen preregistered artifacts retain their original empirical rule.
        return float(np.quantile(scores, 0.95)), {}
    if method != "finite_rank_v1":
        raise ValueError(f"unknown null calibration protocol: {method}")
    levels = {Fraction(row["null_alpha_fraction"]) for row in rows}
    if len(levels) != 1:
        raise ValueError("mixed nominal levels")
    level = levels.pop()
    if not 0 < level < 1:
        raise ValueError("invalid nominal level")
    rank_fraction = (len(scores) + 1) * (1 - level)
    rank = -(-rank_fraction.numerator // rank_fraction.denominator)
    cutoff = sorted(scores)[rank - 1] if rank <= len(scores) else math.inf
    metadata = {
        "b2_null_calibration_method": method,
        "b2_null_alpha_nominal": float(level),
        "b2_null_alpha_fraction": str(level),
        "b2_null_rank_index": rank,
        "b2_null_n_realizations": len(scores),
        "b2_null_exchangeable_level_bound": float(Fraction(len(scores) + 1 - rank, len(scores) + 1)),
        "b2_null_level_scope": "conditional_on_exchangeable_scores_fixed_design",
    }
    for row in rows:
        for key, value in metadata.items():
            if not close(row.get(key.removeprefix("b2_")), value):
                raise ValueError(f"inconsistent calibration metadata: {key}")
    return cutoff, metadata


def real_staging_score(rows: list[dict[str, str]]) -> float:
    """Recompute from raw split parameters rather than a repeated score field."""
    fits = {row["split"]: row for row in rows if row["model"] == "rewrite_power"}
    if len(fits) != sum(row["model"] == "rewrite_power" for row in rows) or "joint" not in fits:
        raise ValueError("require distinct rewrite splits and one joint fit")

    def sigma(row: dict[str, str]) -> float:
        value = fnum(row["m_sigma"])
        # Match the original fitter's explicit unavailable/zero-sigma fallback.
        if not math.isfinite(value) or value == 0:
            return 1.0
        if value < 0:
            raise ValueError("negative shape uncertainty")
        return value

    joint = fits["joint"]
    joint_m, joint_sig = fnum(joint["m"]), sigma(joint)
    if not all(math.isfinite(fnum(row["m"])) for row in fits.values()):
        raise ValueError("nonfinite rewrite shape")
    components = {split: abs(fnum(row["m"]) - joint_m) /
                  math.sqrt(sigma(row)**2 + joint_sig**2 + 0.05**2)
                  for split, row in fits.items() if split != "joint"}
    score = max(components.values(), default=0.0)
    if not all(close(fnum(row["staging_score"]), score) for row in fits.values()):
        raise ValueError("reported real staging score differs from raw split calculation")
    for split, value in components.items():
        if "split_score" in fits[split] and not close(fnum(fits[split]["split_score"]), value):
            raise ValueError("reported split component differs from raw split calculation")
    if components:
        driver = max(components, key=components.get)
        if any(row.get("max_split") not in (None, "", driver) for row in fits.values()):
            raise ValueError("reported driving split differs from raw split calculation")
    return score


def derive(results_dir: Path) -> dict[str, Any]:
    model_rows = read_csv(results_dir / "B1_model_table.csv")
    calibration_rows = read_csv(results_dir / "B2_calibration.csv")
    audit_rows = read_csv(results_dir / "B2_staging_audit.csv")

    rewrite = next(row for row in model_rows if row["model"] == "rewrite_power")
    m_best = fnum(rewrite["m"])
    m_for_constant = fnum(rewrite.get("m_median", "nan"))
    if not math.isfinite(m_for_constant):
        m_for_constant = m_best
    m_sigma = fnum(rewrite["m_sigma"])
    constant_threshold = min(2.0 * m_sigma if math.isfinite(m_sigma) else math.inf, 0.25)
    constant_compatible = abs(m_for_constant) <= constant_threshold

    null_scores = [fnum(row["staging_score"]) for row in calibration_rows if row["kind"] == "lcdm_null"]
    inj_scores = [fnum(row["staging_score"]) for row in calibration_rows if row["kind"] in ("rewrite_injection", "probe_localized_injection")]
    threshold, calibration_metadata = null_cutoff(calibration_rows, null_scores)
    if any(row["kind"] == "probe_localized_injection" for row in calibration_rows):
        eps_by_class: dict[str, dict[float, float]] = {}
        for cls in ("sn_localized", "bao_localized"):
            eps_values = sorted({fnum(row["epsilon"]) for row in calibration_rows if row.get("class") == cls})
            eps_by_class[cls] = {}
            for eps in eps_values:
                scores = np.asarray(
                    [fnum(row["staging_score"]) for row in calibration_rows if row.get("class") == cls and fnum(row["epsilon"]) == eps]
                )
                eps_by_class[cls][eps] = float(np.mean(scores > threshold))
        det_sn = [eps for eps, tpr in eps_by_class.get("sn_localized", {}).items() if tpr >= 0.8]
        det_bao = [eps for eps, tpr in eps_by_class.get("bao_localized", {}).items() if tpr >= 0.8]
        epsilon_detect_sn = float(min(det_sn)) if det_sn else math.nan
        epsilon_detect_bao = float(min(det_bao)) if det_bao else math.nan
        true_positive = float(next(iter(eps_by_class.get("sn_localized", {math.nan: math.nan}).values())))
        anti_vacuity = bool(det_sn or det_bao)
    else:
        amps = sorted({fnum(row.get("injection_A", "nan")) for row in calibration_rows if row["kind"] == "rewrite_injection"})
        tpr_by_amp = {
            amp: float(
                np.mean(
                    np.asarray([fnum(row["staging_score"]) for row in calibration_rows if row["kind"] == "rewrite_injection" and fnum(row.get("injection_A", "nan")) == amp])
                    > threshold
                )
            )
            for amp in amps
            if math.isfinite(amp)
        }
        true_positive = float(tpr_by_amp[min(tpr_by_amp)] if tpr_by_amp else np.mean(np.asarray(inj_scores) > threshold))
        detected = [amp for amp, tpr in tpr_by_amp.items() if tpr >= 0.8]
        epsilon_detect_sn = float(min(detected)) if detected else math.nan
        epsilon_detect_bao = math.nan
        anti_vacuity = bool(detected)
    false_alarm = float(np.mean(np.asarray(null_scores) > threshold))
    real_score = real_staging_score(audit_rows)
    real_fires = bool(real_score > threshold and anti_vacuity)

    probe_localized = any(row["kind"] == "probe_localized_injection" for row in calibration_rows)
    if not anti_vacuity:
        bottom_line = "staging_audit_not_anti_vacuous_no_structured_claim"
    elif probe_localized and real_fires:
        bottom_line = "powered_probe_localized_dataset_tension_audit"
    elif constant_compatible and not real_fires:
        bottom_line = "rewrite_collapses_to_constant_or_no_calibrated_staging"
    elif real_fires:
        bottom_line = "calibrated_structured_audit_feature_present"
    else:
        bottom_line = "no_calibrated_structured_dependence"
    return {
        **calibration_metadata,
        "b1_rewrite_constant_compatible": bool(constant_compatible),
        "b1_rewrite_delta_aic_vs_lcdm": fnum(rewrite["delta_AIC_vs_lcdm"]),
        "b1_rewrite_m_best": m_best,
        "b1_rewrite_m_sigma": m_sigma,
        "b2_null_threshold_p95": threshold,
        "b2_rewrite_true_positive_rate": true_positive,
        "b2_epsilon_detect_sn_localized": epsilon_detect_sn,
        "b2_epsilon_detect_bao_localized": epsilon_detect_bao,
        "b2_null_false_alarm_rate_empirical": false_alarm,
        "b2_anti_vacuity_pass": bool(anti_vacuity),
        "b2_real_staging_score": float(real_score),
        "b2_real_structured_dependence_fires": real_fires,
        "overall_bottom_line": bottom_line,
    }


def close(a: Any, b: Any, tol: float = 1.0e-8) -> bool:
    if isinstance(a, bool) or isinstance(b, bool):
        return bool(a) == bool(b)
    if isinstance(a, str) or isinstance(b, str):
        return str(a) == str(b)
    af = float(a)
    bf = float(b)
    if math.isnan(af) and math.isnan(bf):
        return True
    return math.isclose(af, bf, rel_tol=tol, abs_tol=tol)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results-dir", type=Path, default=Path("results/DE_audit"))
    args = parser.parse_args()
    derived = derive(args.results_dir)
    claimed = json.loads((args.results_dir / "verdict.json").read_text(encoding="utf-8"))
    keys = [
        "b1_rewrite_constant_compatible",
        "b1_rewrite_delta_aic_vs_lcdm",
        "b1_rewrite_m_best",
        "b1_rewrite_m_sigma",
        "b2_null_threshold_p95",
        "b2_rewrite_true_positive_rate",
        "b2_epsilon_detect_sn_localized",
        "b2_epsilon_detect_bao_localized",
        "b2_anti_vacuity_pass",
        "b2_real_staging_score",
        "b2_real_structured_dependence_fires",
        "overall_bottom_line",
    ]
    keys.extend(key for key in derived if key.startswith("b2_null_") and key != "b2_null_false_alarm_rate_empirical" and key not in keys)
    mismatches = {
        key: {"claimed": claimed.get(key), "derived": derived.get(key)}
        for key in keys
        if not close(claimed.get(key), derived.get(key))
    }
    payload = {"derived": derived, "mismatches": mismatches, "verdict_match": not mismatches}
    try:
        (args.results_dir / "validator_rederived.json").write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    except PermissionError:
        # DEA artifacts may be locked read-only after generation to prevent a
        # stale worker from overwriting preregistered outputs. Validation still
        # reports the verdict in that state.
        pass
    print(json.dumps({"verdict_match": not mismatches, "mismatch_count": len(mismatches)}, sort_keys=True))
    return 0 if not mismatches else 1


if __name__ == "__main__":
    raise SystemExit(main())
