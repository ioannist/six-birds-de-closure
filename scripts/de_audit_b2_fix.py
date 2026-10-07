#!/usr/bin/env python3
"""Recalibrate DEA B2/B3 with probe-localized injection classes."""

from __future__ import annotations

import csv
import json
import math
import os
import sys
from dataclasses import replace
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from sbt_cosmo.audits.calibration import RANK_METADATA_FIELDS, rank_calibration

from scripts.de_audit_run import (  # noqa: E402
    INJECT_REALIZATIONS,
    NULL_REALIZATIONS,
    RESULTS,
    SEED,
    GaussianBlock,
    b2_real_and_b3,
    compress_sn_for_audit,
    fit_from_e1_summary,
    fit_rewrite_splits,
    load_blocks,
    make_mock_block,
    split_blocks,
    staging_score,
)


EPSILONS = (0.01, 0.02, 0.05, 0.10, 0.20)
BAO_Z_PIVOT = 0.80


def cap_threads() -> None:
    for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
        os.environ.setdefault(key, "1")


def clone_block(block: GaussianBlock, data: np.ndarray, name: str | None = None) -> GaussianBlock:
    return GaussianBlock(
        name=name or block.name,
        data=np.asarray(data, dtype=float),
        covariance=block.covariance,
        inv_covariance=block.inv_covariance,
        bins=block.bins,
        one_vector=block.one_vector,
    )


def inject_sn_tilt(block: GaussianBlock, epsilon: float) -> GaussianBlock:
    z = np.asarray(block.bins["z_cmb"], dtype=float)
    return clone_block(block, block.data + epsilon * (z / 0.5), "pantheon_plus_sn_localized_injection")


def inject_bao_tilt(block: GaussianBlock, epsilon: float) -> GaussianBlock:
    z = np.asarray(block.bins["z"], dtype=float)
    return clone_block(block, block.data * (1.0 + epsilon * (z - BAO_Z_PIVOT)), "desi_dr2_bao_localized_injection")


def split_scores(fits: dict[str, object]) -> dict[str, float]:
    joint = fits["joint"]
    joint_m = joint.params["m"]
    joint_sig = joint.m_sigma or 1.0
    out: dict[str, float] = {}
    for split, fit in fits.items():
        if split == "joint":
            continue
        sig = fit.m_sigma or 1.0
        out[split] = float(abs(fit.params["m"] - joint_m) / math.sqrt(sig * sig + joint_sig * joint_sig + 0.05**2))
    return out


def fit_score(planck: GaussianBlock, bao: GaussianBlock, sn: GaussianBlock, base_params: dict[str, float]) -> tuple[float, str, dict[str, float]]:
    fits = fit_rewrite_splits(split_blocks(planck, bao, sn), start={**base_params, "A": 0.70, "m": 0.0})
    scores = split_scores(fits)
    max_split = max(scores, key=scores.get)
    return float(scores[max_split]), max_split, scores


def calibration(planck: GaussianBlock, bao: GaussianBlock, sn: GaussianBlock, base) -> tuple[list[dict[str, object]], dict[str, object]]:
    rng = np.random.default_rng(SEED + 202)
    rows: list[dict[str, object]] = []
    base_params = {"omega_b": base.params["omega_b"], "omega_cdm": base.params["omega_cdm"], "H0": base.params["H0"]}
    null_scores: list[float] = []
    localized: dict[str, dict[float, list[float]]] = {
        "sn_localized": {eps: [] for eps in EPSILONS},
        "bao_localized": {eps: [] for eps in EPSILONS},
    }

    for realization in range(NULL_REALIZATIONS):
        mock_bao = make_mock_block(bao, "lcdm", base_params, rng, "desi_dr2_bao")
        mock_sn = make_mock_block(sn, "lcdm", base_params, rng, "pantheon_plus")
        score, max_split, scores = fit_score(planck, mock_bao, mock_sn, base.params)
        null_scores.append(score)
        rows.append(
            {
                "kind": "lcdm_null",
                "class": "null",
                "epsilon": 0.0,
                "realization": realization,
                "staging_score": score,
                "max_split": max_split,
                **{f"score_{key}": value for key, value in scores.items()},
            }
        )

    for cls in ("sn_localized", "bao_localized"):
        for eps in EPSILONS:
            for realization in range(INJECT_REALIZATIONS):
                mock_bao = make_mock_block(bao, "lcdm", base_params, rng, "desi_dr2_bao")
                mock_sn = make_mock_block(sn, "lcdm", base_params, rng, "pantheon_plus")
                if cls == "sn_localized":
                    mock_sn = inject_sn_tilt(mock_sn, eps)
                else:
                    mock_bao = inject_bao_tilt(mock_bao, eps)
                score, max_split, scores = fit_score(planck, mock_bao, mock_sn, base.params)
                localized[cls][eps].append(score)
                rows.append(
                    {
                        "kind": "probe_localized_injection",
                        "class": cls,
                        "epsilon": eps,
                        "realization": realization,
                        "staging_score": score,
                        "max_split": max_split,
                        **{f"score_{key}": value for key, value in scores.items()},
                    }
                )

    rank_summary = rank_calibration(null_scores)
    threshold = float(rank_summary["null_threshold_p95"])
    summary: dict[str, object] = {
        **rank_summary,
        "null_false_alarm_rate_empirical": float(np.mean(np.asarray(null_scores) > threshold)),
        "bao_z_pivot": BAO_Z_PIVOT,
    }
    for cls, by_eps in localized.items():
        detected = []
        for eps, scores in by_eps.items():
            tpr = float(np.mean(np.asarray(scores) > threshold))
            median = float(np.median(scores))
            summary[f"tpr_{cls}_eps_{eps:g}"] = tpr
            summary[f"median_score_{cls}_eps_{eps:g}"] = median
            if tpr >= 0.8:
                detected.append(eps)
        summary[f"epsilon_detect_{cls}"] = float(min(detected)) if detected else math.nan
    summary["anti_vacuity_pass"] = bool(
        math.isfinite(float(summary["epsilon_detect_sn_localized"]))
        or math.isfinite(float(summary["epsilon_detect_bao_localized"]))
    )
    for row in rows:
        row.update(summary)
    return rows, summary


def closest_equivalent(summary: dict[str, object], real_score: float, cls: str) -> float:
    candidates = []
    for eps in EPSILONS:
        median = float(summary[f"median_score_{cls}_eps_{eps:g}"])
        candidates.append((abs(median - real_score), eps))
    return float(min(candidates)[1])


def write_csv(path: Path, rows: list[dict[str, object]], fieldnames: list[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def update_verdict(summary: dict[str, object], real: dict[str, object]) -> None:
    path = RESULTS / "verdict.json"
    verdict = json.loads(path.read_text(encoding="utf-8"))
    real_score = float(real["real_staging_score"])
    fires = bool(real["real_structured_dependence_fires"])
    verdict.update(
        {
            **{f"b2_{key}": summary[key] for key in RANK_METADATA_FIELDS},
            "b2_null_threshold_p95": summary["null_threshold_p95"],
            "b2_real_staging_score": real_score,
            "b2_real_max_split": real["real_max_split"],
            "b2_real_structured_dependence_fires": fires,
            "b2_anti_vacuity_pass": summary["anti_vacuity_pass"],
            "b2_probe_localized_anti_vacuity_pass": summary["anti_vacuity_pass"],
            "b2_epsilon_detect_sn_localized": summary["epsilon_detect_sn_localized"],
            "b2_epsilon_detect_bao_localized": summary["epsilon_detect_bao_localized"],
            "b2_equivalent_epsilon_sn_localized": closest_equivalent(summary, real_score, "sn_localized"),
            "b2_equivalent_epsilon_bao_localized": closest_equivalent(summary, real_score, "bao_localized"),
            "overall_bottom_line": "powered_probe_localized_dataset_tension_audit" if fires else "no_powered_probe_localized_statement",
        }
    )
    path.write_text(json.dumps(verdict, indent=2, sort_keys=True, allow_nan=True) + "\n", encoding="utf-8")


def update_markdown() -> None:
    verdict = json.loads((RESULTS / "verdict.json").read_text(encoding="utf-8"))
    text = (RESULTS / "VERDICT.md").read_text(encoding="utf-8")
    amendment = f"""

## WP-DEA-FIX2 B2 Probe-Localized Calibration

- Conditional finite-rank staging threshold: {verdict['b2_null_threshold_p95']:.6g}.
- Real staging score: {verdict['b2_real_staging_score']:.6g}.
- Real max split: {verdict['b2_real_max_split']}.
- SN-localized epsilon_detect: {verdict['b2_epsilon_detect_sn_localized']}.
- BAO-localized epsilon_detect: {verdict['b2_epsilon_detect_bao_localized']}.
- Equivalent epsilon by median-score proximity: SN {verdict['b2_equivalent_epsilon_sn_localized']}, BAO {verdict['b2_equivalent_epsilon_bao_localized']}.
- Structured probe dependence fires: {verdict['b2_real_structured_dependence_fires']}.

The finite-rank level bound requires exchangeable scores under a fixed design;
the real-data fitted anchor does not establish that premise. Injection rates
are measured finite-grid rates.

Interpretation: if fired, this is a powered audit of structured probe dependence consistent with mild SN-vs-BAO dataset tension. It is not closure evidence and not a Lambda statement.
"""
    if "## WP-DEA-FIX2 B2 Probe-Localized Calibration" in text:
        text = text.split("## WP-DEA-FIX2 B2 Probe-Localized Calibration", 1)[0].rstrip() + amendment
    else:
        text = text.rstrip() + amendment
    (RESULTS / "VERDICT.md").write_text(text + "\n", encoding="utf-8")


def main() -> int:
    cap_threads()
    planck, bao, sn_full = load_blocks()
    sn = compress_sn_for_audit(sn_full)
    full_e1_n_data = int(planck.data.size + bao.data.size + sn_full.data.size)
    base = fit_from_e1_summary("lcdm", full_e1_n_data)
    rows, summary = calibration(planck, bao, sn, base)
    fieldnames = [
        "kind",
        "class",
        "epsilon",
        "realization",
        "staging_score",
        "max_split",
        "score_bao_only",
        "score_sn_only",
        "score_sn_low_z",
        "score_sn_high_z",
        "null_threshold_p95",
        "null_false_alarm_rate_empirical",
        *RANK_METADATA_FIELDS,
        "bao_z_pivot",
        "anti_vacuity_pass",
        "epsilon_detect_sn_localized",
        "epsilon_detect_bao_localized",
        *[f"tpr_sn_localized_eps_{eps:g}" for eps in EPSILONS],
        *[f"tpr_bao_localized_eps_{eps:g}" for eps in EPSILONS],
        *[f"median_score_sn_localized_eps_{eps:g}" for eps in EPSILONS],
        *[f"median_score_bao_localized_eps_{eps:g}" for eps in EPSILONS],
    ]
    write_csv(RESULTS / "B2_calibration.csv", rows, fieldnames)

    audit_rows, route_rows, real = b2_real_and_b3(planck, bao, sn, base, summary)
    # Attach split-level component scores and FIX2 status.
    rewrite_rows = [row for row in audit_rows if row["model"] == "rewrite_power"]
    scores = {row["split"]: row for row in rewrite_rows}
    real_scores = {
        split: float(row["staging_score"]) if split == "joint" else np.nan for split, row in scores.items()
    }
    real_fits = fit_rewrite_splits(split_blocks(planck, bao, sn), start={**base.params, "A": 0.70, "m": 0.0})
    components = split_scores(real_fits)
    max_split = max(components, key=components.get)
    fires = bool(float(real["real_staging_score"]) > float(summary["null_threshold_p95"]) and summary["anti_vacuity_pass"])
    for row in audit_rows:
        row["split_score"] = components.get(row["split"], math.nan)
        row["max_split"] = max_split
        row["structured_dependence_fires"] = fires
        row["fix2_status"] = "powered_probe_localized_dataset_tension_audit" if fires else "no_powered_probe_localized_statement"
    for row in route_rows:
        row["status"] = "powered_probe_localized_dataset_tension_audit" if fires else "no_powered_probe_localized_statement"
    real.update({"real_max_split": max_split, "real_structured_dependence_fires": fires})

    write_csv(
        RESULTS / "B2_staging_audit.csv",
        audit_rows,
        [
            "split",
            "model",
            "chi2",
            "n_data",
            "A",
            "m",
            "m_sigma",
            "omega_m",
            "A_lower_hit",
            "A_upper_hit",
            "m_lower_hit",
            "m_upper_hit",
            "converged",
            "split_score",
            "max_split",
            "staging_score",
            "null_threshold_p95",
            "structured_dependence_fires",
            "fix2_status",
        ],
    )
    write_csv(
        RESULTS / "B3_route_residuals.csv",
        route_rows,
        ["route_a", "route_b", "parameter", "unsigned_residual", "calibration_statistic", "null_threshold_p95", "status"],
    )
    update_verdict(summary, real)
    update_markdown()
    print(json.dumps(json.loads((RESULTS / "verdict.json").read_text(encoding="utf-8")), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
