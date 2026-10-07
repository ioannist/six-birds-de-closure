#!/usr/bin/env python3
"""Replay original seed-1100 count inputs; no solver or RNG is run.

The Lean kernel separately checks the rational count and gap certificates.
This script checks provenance and exercises false count/gap controls.
"""
from __future__ import annotations

import csv
from fractions import Fraction
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    population_path = ROOT / "results/window_population_2026-10-03/population.json"
    data = json.loads(population_path.read_text())
    population = next(p for p in data["populations"] if p["seed"] == 1100)
    amplitudes = list(map(Fraction, population["amplitudes_exact"]))
    tags = population["tags"]
    assert len(amplitudes) == len(tags) == 64
    delta = Fraction(843, 500)

    def collapsed(growth: int) -> list[int]:
        return [i for i, amp in enumerate(amplitudes) if delta <= amp * growth]

    def accepted(lower: int, upper: int, count: int) -> bool:
        return len(collapsed(lower)) == count and collapsed(lower) == collapsed(upper)

    assert accepted(17000, 26000, 58)
    assert not accepted(17000, 26000, 59)
    assert not accepted(17000, 27000, 58)
    assert tags[54] is False and tags[58] is True
    assert {54, 58} <= set(collapsed(17000))
    readout_path = ROOT / "results/DE_window/coincidence_readout.json"
    readout = json.loads(readout_path.read_text())
    outside = Fraction(readout["negative_edge_inside_outside"]["outside"])
    assert outside == Fraction(-1245155224975395, 4611686018427387904)
    witness_path = ROOT / "results/DE_window/controls/C2_edge_witnesses.csv"
    with witness_path.open(newline="") as source:
        witnesses = list(csv.DictReader(source))
    witness = next(row for row in witnesses if row["edge"] == "negative_crunch"
                   and row["side"] == "outside" and int(row["seed"]) == 1100)
    assert Fraction(float(witness["lambda"])) == Fraction(-0.00027)
    assert int(witness["record_count_before_erasure"]) == 58
    assert int(witness["record_count_final"]) == 0
    assert int(witness["distinct_tags_before_erasure"]) == 2
    assert witness["records_persist"] == "False"
    print(json.dumps({
        "population_source": str(population_path.relative_to(ROOT)),
        "witness_source": str(witness_path.relative_to(ROOT)),
        "full_precision_parameter_source": str(readout_path.relative_to(ROOT)),
        "rounded_csv_parameter": witness["lambda"],
        "outside_exact_binary_value": str(outside),
        "model_a0_exact_decimal": "1/1000",
        "model_delta_exact_decimal": str(delta),
        "lower_growth": 17000,
        "upper_growth": 26000,
        "collapsed_indices": collapsed(17000),
        "count": 58,
        "tag_witness_indices": [54, 58],
        "false_count_control_rejected": True,
        "false_gap_control_rejected": True,
        "original_solver_rerun": False,
        "floating_solver_error_certified": False,
        "distinct_tags_final_is_actual_final_set_cardinality": False,
        "historical_distinct_tags_final": witness["distinct_tags_final"],
    }, indent=2))


if __name__ == "__main__":
    main()
