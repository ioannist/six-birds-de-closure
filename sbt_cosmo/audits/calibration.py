"""Finite rank calibration for a scalar audit statistic.

The level bound requires exchangeability of the future score with the null
scores, including their fitting/design procedure. A real-data fitted anchor
does not automatically meet that premise. Rates measured on a fixed mock
grid are empirical rates, not certified population power.
"""
from __future__ import annotations

from fractions import Fraction
import math
from typing import Iterable


RANK_METADATA_FIELDS = [
    "null_calibration_method", "null_alpha_nominal", "null_alpha_fraction", "null_rank_index",
    "null_n_realizations", "null_exchangeable_level_bound", "null_level_scope",
]


def _scores(values: Iterable[float]) -> list[float]:
    scores = [float(value) for value in values]
    if not scores or not all(math.isfinite(value) for value in scores):
        raise ValueError("require nonempty finite null scores")
    return scores


def rank_calibration(null_scores: Iterable[float], alpha: float | Fraction = 0.05) -> dict:
    """Reject strictly above the k-th null order statistic.

    k=ceil((n+1)*(1-alpha)), with infinity if k>n. Inclusive upper ranks
    make ties conservative. The rank arithmetic uses exact fractions.
    """
    scores = sorted(_scores(null_scores))
    if isinstance(alpha, bool):
        raise ValueError("require 0<alpha<1")
    try:
        level = alpha if isinstance(alpha, Fraction) else Fraction(str(alpha))
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError("require 0<alpha<1") from exc
    if not 0 < level < 1:
        raise ValueError("require 0<alpha<1")
    n = len(scores)
    rank = math.ceil((n + 1) * (1 - level))
    cutoff = scores[rank - 1] if rank <= n else math.inf
    bound = Fraction(n + 1 - rank, n + 1)
    assert 0 <= bound <= level
    return {
        # Preserve the established field name; method metadata fixes its meaning.
        "null_threshold_p95": cutoff,
        "null_calibration_method": "finite_rank_v1",
        "null_alpha_nominal": float(level),
        "null_alpha_fraction": str(level),
        "null_rank_index": rank,
        "null_n_realizations": n,
        "null_exchangeable_level_bound": float(bound),
        "null_level_scope": "conditional_on_exchangeable_scores_fixed_design",
    }


def upper_rank_pvalue(null_scores: Iterable[float], score: float) -> Fraction:
    """Exact inclusive rank fraction; probabilistic validity is conditional."""
    scores = _scores(null_scores)
    score = float(score)
    if not math.isfinite(score):
        raise ValueError("require a finite audit score")
    return Fraction(1 + sum(value >= score for value in scores), len(scores) + 1)
