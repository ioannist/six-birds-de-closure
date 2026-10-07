#!/usr/bin/env python3
"""Check every frozen amplitude/tag against the original run_seed sampler.

Capture its local arrays at return, without using the reifier's sampling code.
Collapse lookup is disabled and dummy growth is supplied solely to reach return;
no record verdict, ODE accuracy or growth-solver behavior is validated here.
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
from unittest.mock import patch

import numpy as np

import de_window_carrier as window

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    data = json.loads((ROOT / "results/window_population_2026-10-03/population.json").read_text())
    cfg = window.CarrierConfig()
    dummy = window.GrowthSolution(0.0, np.array([cfg.a_init, cfg.a_max]), np.ones(2),
                                  False, True, "population capture only")
    captured = {}

    def profile(frame, event, arg):
        if event == "return" and frame.f_code is window.run_seed.__code__:
            local = frame.f_locals
            captured[local["seed"]] = (
                [str(Fraction.from_float(float(x))) for x in local["amplitudes"]],
                [bool(x) for x in local["tags"]],
            )

    previous_profile = sys.getprofile()
    try:
        sys.setprofile(profile)
        with patch.object(window, "collapse_epoch", return_value=None):
            for seed in window.SEEDS:
                window.run_seed(0.0, seed, cfg, dummy)
    finally:
        sys.setprofile(previous_profile)
    assert [row["seed"] for row in data["populations"]] == window.SEEDS
    checked = 0
    for row in data["populations"]:
        amplitudes, tags = captured[row["seed"]]
        assert amplitudes == row["amplitudes_exact"], row["seed"]
        assert tags == row["tags"], row["seed"]
        checked += len(amplitudes)
    assert checked == 768
    first = data["populations"][0]
    altered_amplitudes = first["amplitudes_exact"].copy()
    altered_amplitudes[0] = str(Fraction(altered_amplitudes[0]) + 1)
    altered_tags = first["tags"].copy()
    altered_tags[0] = not altered_tags[0]
    assert captured[first["seed"]][0] != altered_amplitudes
    assert captured[first["seed"]][1] != altered_tags
    print("Original run_seed arrays match all 768 reified amplitudes/tags; amplitude/tag mutation controls detected.")


if __name__ == "__main__":
    main()
