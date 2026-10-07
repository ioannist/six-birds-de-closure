"""Dynesty evidence driver for completed E1 standard-model configurations."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any

import numpy as np
import yaml
from scipy import stats

from sbt_cosmo.inference.cobaya_iface import build_cobaya_input
from sbt_cosmo.inference.evidence import run_dynesty_evidence


def run_evidence(
    *,
    config_path: Path,
    combination: str,
    model_name: str,
    output: Path,
    nlive: int | None,
    dlogz: float | None,
) -> dict[str, Any]:
    """Run dynesty evidence for one E1 combination/model."""
    _require_preexported_clik_library()
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    settings = config["samplers"]["dynesty"]
    live_points = int(nlive or settings["nlive"])
    stop_dlogz = float(dlogz or settings["dlogz"])
    info = build_cobaya_input(
        config,
        combination=combination,
        model=model_name,
        sampler="minimize",
        output_prefix=output.with_suffix("").as_posix(),
        run_mode="evidence",
    )
    names, transforms = _prior_transforms(info["params"])

    from cobaya.model import get_model

    cobaya_model = get_model(info, packages_path=config["packages"]["cobaya"], stop_at_error=True)

    def prior_transform(unit: np.ndarray) -> np.ndarray:
        return np.asarray([transform(float(value)) for transform, value in zip(transforms, unit)], dtype=np.float64)

    def loglikelihood(theta: np.ndarray) -> float:
        point = {name: float(value) for name, value in zip(names, theta)}
        loglikes = cobaya_model.loglikes(point, as_dict=True, cached=False)
        if isinstance(loglikes, tuple):
            loglikes = loglikes[0]
        return float(sum(loglikes.values()))

    result = run_dynesty_evidence(
        loglikelihood,
        prior_transform,
        ndim=len(names),
        nlive=live_points,
        seed=int(config["seeds"]["dynesty"]),
        dlogz=stop_dlogz,
    )
    payload = {
        "schema_version": 1,
        "combination": combination.upper(),
        "model": model_name.lower(),
        "sampler": "dynesty",
        "sampled_parameters": names,
        **result,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return payload


def _prior_transforms(params: dict[str, Any]) -> tuple[list[str], list[Any]]:
    names: list[str] = []
    transforms: list[Any] = []
    for name, spec in params.items():
        if not isinstance(spec, dict) or "prior" not in spec or "value" in spec:
            continue
        prior = spec["prior"]
        names.append(name)
        transforms.append(_transform_for_prior(prior))
    return names, transforms


def _transform_for_prior(prior: dict[str, Any]) -> Any:
    if {"min", "max"} <= set(prior):
        lower = float(prior["min"])
        width = float(prior["max"]) - lower
        return lambda unit, lower=lower, width=width: lower + width * unit
    if prior.get("dist") == "norm":
        loc = float(prior["loc"])
        scale = float(prior["scale"])
        return lambda unit, loc=loc, scale=scale: float(stats.norm.ppf(unit, loc=loc, scale=scale))
    if prior.get("dist") == "halfnorm":
        loc = float(prior.get("loc", 0.0))
        scale = float(prior["scale"])
        return lambda unit, loc=loc, scale=scale: float(loc + stats.halfnorm.ppf(unit, scale=scale))
    raise ValueError(f"unsupported prior for dynesty evidence: {prior}")


def _require_preexported_clik_library() -> None:
    library_path = os.environ.get("LD_LIBRARY_PATH", "")
    if "clik-main/lib" not in library_path:
        raise RuntimeError(
            "LD_LIBRARY_PATH must include the Planck clik lib directory before starting Python."
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("configs/experiments/E1.yaml"))
    parser.add_argument("--combination", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--nlive", type=int)
    parser.add_argument("--dlogz", type=float)
    args = parser.parse_args()
    result = run_evidence(
        config_path=args.config,
        combination=args.combination,
        model_name=args.model,
        output=args.output,
        nlive=args.nlive,
        dlogz=args.dlogz,
    )
    print(json.dumps({"output": str(args.output), "lnz": result["lnz"], "lnzerr": result["lnzerr"]}, indent=2))


if __name__ == "__main__":
    main()
