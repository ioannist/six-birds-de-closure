"""Bounded log-likelihood timing probe for E1 Cobaya models.

This script does not run a sampler. It builds the requested Cobaya model,
warms one likelihood call, then times a fixed number of forced loglike
evaluations at tiny deterministic perturbations around the reference point.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

import yaml
from cobaya.model import get_model

from sbt_cosmo.inference.cobaya_iface import build_cobaya_input
from sbt_cosmo.inference.samplers import load_planck_metadata, prepare_planck_environment

from run import _reference_point

ROOT = Path(__file__).resolve().parents[2]


def probe(
    *,
    config_path: Path,
    cases: list[tuple[str, str]],
    repeat: int,
    warmup: int,
    omp_threads: int,
    out_path: Path | None,
) -> dict[str, Any]:
    """Run bounded timing probes and optionally write a JSON report."""
    planck_env = prepare_planck_environment(load_planck_metadata())
    os.environ.update(planck_env)
    os.environ["OMP_NUM_THREADS"] = str(int(omp_threads))
    for entry in planck_env["PYTHONPATH"].split(os.pathsep):
        if entry and entry not in sys.path:
            sys.path.insert(0, entry)
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    output_root = Path("runs/E1/timing_probe")
    output_root.mkdir(parents=True, exist_ok=True)

    results: dict[str, Any] = {
        "schema_version": 1,
        "omp_threads": int(omp_threads),
        "repeat": int(repeat),
        "warmup": int(warmup),
        "cases": {},
    }

    for combination, model in cases:
        label = f"{combination.upper()}_{model.lower()}"
        info = build_cobaya_input(
            config,
            combination=combination,
            model=model,
            sampler="minimize",
            output_prefix=output_root / label,
            run_mode="production",
        )
        info.pop("sampler", None)
        point = _reference_point(info["params"])
        model_obj = get_model(info)
        for index in range(warmup):
            model_obj.loglike(_perturbed_point(point, index), return_derived=False, cached=False)
        times: list[float] = []
        values: list[float] = []
        timed_points: list[dict[str, float]] = []
        for index in range(repeat):
            timed_point = _perturbed_point(point, warmup + index)
            start = time.perf_counter()
            value = float(model_obj.loglike(timed_point, return_derived=False, cached=False))
            times.append(time.perf_counter() - start)
            values.append(value)
            timed_points.append(timed_point)
        results["cases"][label] = {
            "combination": combination.upper(),
            "model": model.lower(),
            "loglike": values[-1],
            "times_seconds": times,
            "mean_seconds_per_loglike": sum(times) / len(times),
            "min_seconds_per_loglike": min(times),
            "max_seconds_per_loglike": max(times),
            "reference_point": point,
            "timed_points": timed_points,
        }

    if out_path:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(results, indent=2, sort_keys=True), encoding="utf-8")
    return results


def _parse_cases(raw: str) -> list[tuple[str, str]]:
    cases: list[tuple[str, str]] = []
    for item in raw.split(","):
        if not item:
            continue
        combination, model = item.split(":", 1)
        cases.append((combination, model))
    return cases


def _perturbed_point(point: dict[str, float], index: int) -> dict[str, float]:
    """Return a nearby point that is safely inside broad E1 priors."""
    trial = dict(point)
    direction = -1.0 if index % 2 else 1.0
    trial["omega_cdm"] = float(trial["omega_cdm"]) + direction * 1.0e-5 * (index + 1)
    trial["theta_s_100"] = float(trial["theta_s_100"]) + direction * 1.0e-6 * (index + 1)
    return trial


def main() -> None:
    """Parse arguments and print JSON timing results."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=ROOT / "configs" / "experiments" / "E1.yaml")
    parser.add_argument("--cases", default="C1:lcdm,C2:w0wa")
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--omp-threads", type=int, default=4)
    parser.add_argument("--out", type=Path, default=Path("runs/E1/timing_probe_omp4.json"))
    args = parser.parse_args()
    result = probe(
        config_path=args.config,
        cases=_parse_cases(args.cases),
        repeat=args.repeat,
        warmup=args.warmup,
        omp_threads=args.omp_threads,
        out_path=args.out,
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
