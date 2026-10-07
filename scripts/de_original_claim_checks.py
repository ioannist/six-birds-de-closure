#!/usr/bin/env python3
"""Check original chart and window obligations without changing frozen results.

Exact arithmetic applies to frozen-decimal crossing parameters and the finite
IID record law. Expansion-history and original ODE comparisons are floating
point checks, not interval certificates or physical stability proofs.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import platform
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import de_window_carrier as window
from sbt_cosmo.theory import background_compressed as bg


def iid_record_probability(n: int, p: Fraction, q: Fraction) -> Fraction:
    """Both tags occur among collapsed patches, for independent IID patches.

    p is collapse probability, q is the independent true-tag probability.
    This is a population law, not a probability estimate from 12 fixed seeds.
    """
    if not isinstance(n, int) or n < 0 or not 0 <= p <= 1 or not 0 <= q <= 1:
        raise ValueError("require integer n>=0 and probabilities in [0,1]")
    return 1 - (1 - p * q)**n - (1 - p * (1 - q))**n + (1 - p)**n


def enumerate_record_probability(n: int, p: Fraction, q: Fraction) -> Fraction:
    """Independent exact check by exhaustive disjoint patch outcomes."""
    masses = [1 - p, p * (1 - q), p * q]
    total = Fraction(0)
    for states in itertools.product(range(3), repeat=n):
        if 1 in states and 2 in states:
            mass = Fraction(1)
            for state in states:
                mass *= masses[state]
            total += mass
    return total


def recompute() -> dict:
    model_path = ROOT / "results/DE_audit/B1_model_table.csv"
    chart_path = ROOT / "results/DE_audit/B1b_chart_comparison.csv"
    with model_path.open(newline="") as handle:
        fit = next(row for row in csv.DictReader(handle) if row["model"] == "w0wa")
    with chart_path.open(newline="") as handle:
        frozen = list(csv.DictReader(handle))
    w0, wa = Fraction(fit["w0_fld"]), Fraction(fit["wa_fld"])
    crossing = -(1 + w0) / (1 + w0 + wa)
    assert Fraction(4388, 10000) < crossing < Fraction(4389, 10000)
    z = np.array([float(row["z"]) for row in frozen])
    matter = float(fit["omega_m"])
    radiation = bg.OMEGA_R_H2 / (float(fit["H0"]) / 100)**2
    amplitude = 1 - matter - radiation
    assert amplitude > 0
    f0, fa = float(w0), float(wa)
    density = amplitude * np.exp(3 * (1 + f0 + fa) * np.log1p(z) - 3 * fa * z / (1 + z))
    expansion = bg._e_z(z, omega_m=matter, omega_r=radiation, omega_de=amplitude,
                          w0_fld=f0, wa_fld=fa)**2
    additive = expansion - matter * (1 + z)**3 - radiation * (1 + z)**4
    fluid = f0 + fa * z / (1 + z)
    errors = {
        "same_history_max_error": float(np.max(np.abs(additive - density))),
        "frozen_density_max_error": float(np.max(np.abs(density - np.array([float(r["Delta_H_additive"]) for r in frozen])))),
        "frozen_fluid_max_error": float(np.max(np.abs(fluid - np.array([float(r["w_fluid"]) for r in frozen])))),
    }
    assert max(errors.values()) < 1e-12
    # Direct original-carrier counterexample: same realized amplitudes/growth,
    # two constant tag distributions versus the reference fair-tag realization.
    cfg = window.CarrierConfig()
    growth = window.solve_growth(0.0, cfg)
    tag_rows = []
    for q in [0.0, 0.5, 1.0]:
        tag_rows.append(window.run_seed(0.0, 1100, window.replace(cfg, tag_probability=q), growth))
    assert [row["RS"] for row in tag_rows] == [False, True, False]
    assert len({row["record_count_final"] for row in tag_rows}) == 1
    # With one fixed realized patch population, both tags collapse iff the
    # final increasing growth exceeds the larger of their two thresholds.
    # Reify sampled IEEE amplitudes exactly; delta_c is the declared decimal.
    thresholds = []
    for seed in window.SEEDS:
        rng = np.random.default_rng(seed)
        amplitudes = cfg.heterogeneity_s * np.abs(rng.normal(size=cfg.n_patches))
        tags = rng.random(cfg.n_patches) < cfg.tag_probability
        tag_maxima = [max(Fraction.from_float(float(x)) for x in amplitudes[tags == tag]) for tag in [False, True]]
        thresholds.append(max(Fraction(str(cfg.delta_c)) / maximum for maximum in tag_maxima))
    required = next(k for k in range(len(window.SEEDS) + 1)
                    if Fraction(k, len(window.SEEDS)) >= Fraction(str(cfg.seed_pass_fraction)))
    aggregate_threshold = sorted(thresholds)[required - 1]
    assert Fraction(3, 2) < aggregate_threshold < Fraction(str(cfg.a_max)) / Fraction(str(cfg.a_init))
    threshold_checks = 0
    for lam in [-0.00012, 0.0, 1.0, 3.0, 10.0]:
        solution = window.solve_growth(lam, cfg)
        assert solution.integration_sane and not solution.crunch_before_tmax
        assert np.all(np.diff(solution.growth) > 0)
        rows = [window.run_seed(lam, seed, cfg, solution) for seed in window.SEEDS]
        for threshold, row in zip(thresholds, rows):
            assert row["RS"] == (float(solution.growth[-1]) >= float(threshold))
            threshold_checks += 1
    law_checks = 0
    for n in range(6):
        for p, q in itertools.product([Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)], repeat=2):
            assert iid_record_probability(n, p, q) == enumerate_record_probability(n, p, q)
            law_checks += 1
    inputs = [model_path, chart_path, Path(__file__), ROOT / "scripts/de_window_carrier.py",
              ROOT / "sbt_cosmo/theory/background_compressed.py",
              ROOT / "lean/SbtCosmo/Derivation/CPLReadout.lean",
              ROOT / "lean/SbtCosmo/Derivation/WindowRecords.lean"]
    return {
        "scope": "exact decimal crossing and finite IID law; floating-point chart/ODE bridge checks",
        "software": {"python": platform.python_version(), "numpy": np.__version__},
        "sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
        "cpl": {"w0": str(w0), "wa": str(wa), "exact_crossing": str(crossing),
                "crossing_float": float(crossing), "amplitude": amplitude, "grid_points": len(z), **errors},
        "tag_counterexample": [{key: row[key] for key in ["lambda", "seed", "tag_probability", "record_count_final", "distinct_tags_final", "RS"]} for row in tag_rows],
        "window_threshold": {"required_seeds": required, "seed_thresholds_exact": [str(t) for t in thresholds],
                             "aggregate_threshold_exact": str(aggregate_threshold),
                             "aggregate_threshold_float": float(aggregate_threshold),
                             "vacuum_growth_limit": 1.5 - 0.5*(cfg.a_init/cfg.a_max)**2,
                             "matter_growth": cfg.a_max/cfg.a_init,
                             "original_carrier_threshold_checks": threshold_checks},
        "population_law_exact_enumeration_checks": law_checks,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path, default=ROOT / "results/original_claim_checks_2026-10-02")
    args = parser.parse_args()
    receipt = recompute()
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"crossing": receipt["cpl"]["crossing_float"], "tag_RS": [r["RS"] for r in receipt["tag_counterexample"]],
                      "exact_law_checks": receipt["population_law_exact_enumeration_checks"]}))
