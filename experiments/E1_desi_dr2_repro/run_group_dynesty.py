"""Dynesty runner for the compressed-CMB E1 likelihood."""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Any

import numpy as np
import yaml
from dynesty import NestedSampler
from dynesty import utils as dyfunc
from scipy import stats

import sbt_cosmo
from sbt_cosmo.inference.cobaya_compressed import build_compressed_cobaya_input
from sbt_cosmo.io.checksums import sha256_file
from sbt_cosmo.likelihoods.bao_sn_gaussian import (
    des_sn5yr_compressed_logp,
    desi_dr2_bao_compressed_logp,
    pantheon_plus_compressed_logp,
    union3_compressed_logp,
)
from sbt_cosmo.likelihoods.cmb_compressed import planck2018_compressed_logp
from sbt_cosmo.theory.background_compressed import omega_m_approx

ROOT = Path(__file__).resolve().parents[2]


def run_dynesty_group(
    *,
    config_path: Path,
    outdir: Path,
    run_id: str,
    combination: str,
    model: str,
    nlive: int,
    dlogz: float,
    seed: int | None,
    max_equal_samples: int,
    pool_size: int = 1,
) -> dict[str, Any]:
    """Run static dynesty against the compressed E1 likelihood for one group."""
    started = time.monotonic()
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    combination = combination.upper()
    model = model.lower()
    outdir.mkdir(parents=True, exist_ok=True)
    for subdir in ("chains", "logs"):
        (outdir / subdir).mkdir(exist_ok=True)

    info = build_compressed_cobaya_input(
        config,
        combination=combination,
        model=model,
        sampler="mcmc",
        output_prefix=outdir / "chains" / f"{combination}_{model}_dyn_probe",
        run_mode="production",
    )
    names, transforms = _prior_transforms(info["params"])
    fixed = _fixed_parameters(info["params"])
    loglike = CompressedLogLikelihood(
        datasets=tuple(config["combinations"][combination]["datasets"]),
        names=tuple(names),
        fixed=fixed,
    )

    prior_transform = _PriorTransform(tuple(transforms))

    rng_seed = int(seed if seed is not None else config["seeds"]["sampler"] + 10000 + _combo_offset(combination, model))
    rng = np.random.default_rng(rng_seed)
    sampler_kwargs = dict(ndim=len(names), nlive=int(nlive), bound="multi", sample="rwalk", rstate=rng)
    if pool_size and int(pool_size) > 1:
        import dynesty.pool as dypool

        with dypool.Pool(int(pool_size), loglike, prior_transform) as pool:
            sampler = NestedSampler(
                pool.loglike, pool.prior_transform, pool=pool, queue_size=int(pool_size), **sampler_kwargs
            )
            sampler.run_nested(dlogz=float(dlogz), print_progress=False)
            results = sampler.results
    else:
        sampler = NestedSampler(loglike, prior_transform, **sampler_kwargs)
        sampler.run_nested(dlogz=float(dlogz), print_progress=False)
        results = sampler.results
    logz = float(results.logz[-1])
    logz_err = float(results.logzerr[-1])
    log_weights = np.asarray(results.logwt, dtype=np.float64)
    samples = np.asarray(results.samples, dtype=np.float64)
    logl = np.asarray(results.logl, dtype=np.float64)
    weights = np.exp(log_weights - logz)
    weights = weights / np.sum(weights)
    n_equal = min(int(max_equal_samples), max(1000, samples.shape[0]))
    equal_indices = rng.choice(samples.shape[0], size=n_equal, replace=True, p=weights)
    equal_samples = samples[equal_indices]
    equal_logl = logl[equal_indices]
    best_index = int(np.argmax(logl))
    best_sample = samples[best_index]
    best_point = {name: float(value) for name, value in zip(names, best_sample)}
    bestfit = {**fixed, **best_point}
    bestfit["Omega_m"] = omega_m_approx(
        omega_b=float(bestfit["omega_b"]),
        omega_cdm=float(bestfit["omega_cdm"]),
        H0=float(bestfit["H0"]),
    )
    chi2_map = float(-2.0 * logl[best_index])
    chain_path = outdir / "chains" / f"{combination}_{model}_dyn.1.txt"
    _write_equal_weight_chain(chain_path, names, equal_samples, equal_logl)
    neff = float(dyfunc.get_neff_from_logwt(log_weights))
    diagnostics = {
        "max_rhat_minus_one": None,
        "min_ess": neff,
        "logZ": logz,
        "logZ_err": logz_err,
        "converged": bool(logz_err < 0.3),
        "nlive": int(nlive),
        "dlogz": float(dlogz),
        "niter": int(results.niter),
        "ncall": int(np.sum(results.ncall)),
        "equal_weight_samples": int(n_equal),
    }
    wall = time.monotonic() - started
    summary = {
        "schema_version": 1,
        "experiment": "E1_compressed",
        "run_id": run_id,
        "mode": "production",
        "terminal_state": "RUN_COMPLETE" if diagnostics["converged"] else "RUN_COMPLETE_PARTIAL",
        "package_version": sbt_cosmo.__version__,
        "combination": combination,
        "model": model,
        "sampler": "dynesty",
        "datasets": config["combinations"][combination]["datasets"],
        "config": str(config_path),
        "seeds": {"dynesty": rng_seed},
        "clik_invoked": False,
        "spectra_invoked": False,
        "background_backend": "classy_background_only",
        "minimize": {
            "source": "dynesty_max_loglike_sample",
            "bestfit": bestfit,
            "chi2": chi2_map,
            "minusloglike": float(-logl[best_index]),
        },
        "mcmc": {
            "sampler": "dynesty",
            "chain_files": [str(chain_path)],
            "sampled_parameters": names,
            "diagnostics": diagnostics,
            "wall_clock_seconds": wall,
        },
        "logZ": logz,
        "logZ_err": logz_err,
        "scope": "compressed-CMB dynesty production group",
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    _write_manifest(config_path, outdir, summary)
    return summary


def _prior_transforms(params: dict[str, Any]) -> tuple[list[str], list[Any]]:
    names: list[str] = []
    transforms: list[Any] = []
    for name, spec in params.items():
        if not isinstance(spec, dict) or "prior" not in spec or "value" in spec:
            continue
        names.append(name)
        transforms.append(_transform_for_prior(spec["prior"]))
    return names, transforms


class CompressedLogLikelihood:
    """Pickle-safe direct compressed likelihood evaluator for dynesty."""

    def __init__(self, *, datasets: tuple[str, ...], names: tuple[str, ...], fixed: dict[str, float]) -> None:
        self.datasets = tuple(dataset.upper() for dataset in datasets)
        self.names = names
        self.fixed = dict(fixed)

    def __call__(self, theta: np.ndarray) -> float:
        point = {**self.fixed, **{name: float(value) for name, value in zip(self.names, theta)}}
        kwargs = {
            "omega_b": point["omega_b"],
            "omega_cdm": point["omega_cdm"],
            "H0": point["H0"],
            "w0_fld": point.get("w0_fld", -1.0),
            "wa_fld": point.get("wa_fld", 0.0),
        }
        total = 0.0
        try:
            for dataset in self.datasets:
                if dataset == "PLANCK_2018_COMPRESSED":
                    total += planck2018_compressed_logp(**kwargs)
                elif dataset == "DESI_DR2_BAO":
                    total += desi_dr2_bao_compressed_logp(**kwargs)
                elif dataset == "PANTHEON_PLUS":
                    total += pantheon_plus_compressed_logp(**kwargs, sn_M=point["sn_M"])
                elif dataset == "UNION3":
                    total += union3_compressed_logp(**kwargs, sn_M=point["sn_M"])
                elif dataset == "DES_SN5YR":
                    total += des_sn5yr_compressed_logp(**kwargs, sn_M=point["sn_M"])
        except Exception:
            return -np.inf
        return float(total) if np.isfinite(total) else -np.inf


def _fixed_parameters(params: dict[str, Any]) -> dict[str, float]:
    return {
        name: float(spec["value"])
        for name, spec in params.items()
        if isinstance(spec, dict) and "value" in spec
    }


class _UniformT:
    """Picklable uniform inverse-CDF (for dynesty pools)."""

    def __init__(self, lower: float, width: float) -> None:
        self.lower = lower
        self.width = width

    def __call__(self, unit: float) -> float:
        return self.lower + self.width * unit


class _NormT:
    """Picklable normal inverse-CDF."""

    def __init__(self, loc: float, scale: float) -> None:
        self.loc = loc
        self.scale = scale

    def __call__(self, unit: float) -> float:
        return float(stats.norm.ppf(unit, loc=self.loc, scale=self.scale))


class _HalfNormT:
    """Picklable half-normal inverse-CDF."""

    def __init__(self, loc: float, scale: float) -> None:
        self.loc = loc
        self.scale = scale

    def __call__(self, unit: float) -> float:
        return float(self.loc + stats.halfnorm.ppf(unit, scale=self.scale))


class _PriorTransform:
    """Picklable vector prior transform so dynesty can use a multiprocessing pool."""

    def __init__(self, transforms: tuple[Any, ...]) -> None:
        self.transforms = tuple(transforms)

    def __call__(self, unit: np.ndarray) -> np.ndarray:
        return np.asarray(
            [transform(float(value)) for transform, value in zip(self.transforms, unit)],
            dtype=np.float64,
        )


def _transform_for_prior(prior: dict[str, Any]) -> Any:
    if {"min", "max"} <= set(prior):
        lower = float(prior["min"])
        width = float(prior["max"]) - lower
        return _UniformT(lower, width)
    if prior.get("dist") == "norm":
        return _NormT(float(prior["loc"]), float(prior["scale"]))
    if prior.get("dist") == "halfnorm":
        return _HalfNormT(float(prior.get("loc", 0.0)), float(prior["scale"]))
    raise ValueError(f"unsupported prior for dynesty: {prior}")


def _write_equal_weight_chain(path: Path, names: list[str], samples: np.ndarray, logl: np.ndarray) -> None:
    columns = ["weight", "minuslogpost", *names, "Omega_m", "chi2"]
    lines = ["# " + " ".join(columns)]
    for sample, value in zip(samples, logl):
        point = {name: float(theta) for name, theta in zip(names, sample)}
        omega_m = omega_m_approx(
            omega_b=point["omega_b"],
            omega_cdm=point["omega_cdm"],
            H0=point["H0"],
        )
        chi2 = float(-2.0 * value)
        row = [1.0, float(-value), *[point[name] for name in names], omega_m, chi2]
        lines.append(" ".join(f"{item:.10e}" for item in row))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _combo_offset(combination: str, model: str) -> int:
    combo_number = int(combination[1:]) if combination.startswith("C") and combination[1:].isdigit() else 0
    model_offset = {"lcdm": 100, "wcdm": 200, "w0wa": 300}.get(model, 0)
    return combo_number * 1000 + model_offset


def _write_manifest(config_path: Path, outdir: Path, summary: dict[str, Any]) -> None:
    artifacts = {
        str(path.relative_to(outdir)): sha256_file(path)
        for path in sorted(outdir.rglob("*"))
        if path.is_file() and path.name != "manifest.json"
    }
    manifest = {
        "schema_version": 1,
        "experiment": "E1_compressed",
        "run_id": summary["run_id"],
        "sampler": "dynesty",
        "package_version": sbt_cosmo.__version__,
        "datasets": summary["datasets"],
        "config_sha256": sha256_file(config_path),
        "artifact_checksums_sha256": artifacts,
        "terminal_state": summary["terminal_state"],
    }
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("configs/experiments/E1_compressed.yaml"))
    parser.add_argument("--outdir", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--combination", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--nlive", type=int, default=800)
    parser.add_argument("--dlogz", type=float, default=0.1)
    parser.add_argument("--seed", type=int)
    parser.add_argument("--max-equal-samples", type=int, default=20000)
    parser.add_argument("--pool", type=int, default=1, help="multiprocessing pool size for likelihood evals")
    args = parser.parse_args()
    summary = run_dynesty_group(
        config_path=args.config,
        outdir=args.outdir,
        run_id=args.run_id,
        combination=args.combination,
        model=args.model,
        nlive=args.nlive,
        dlogz=args.dlogz,
        seed=args.seed,
        max_equal_samples=args.max_equal_samples,
        pool_size=args.pool,
    )
    print(
        json.dumps(
            {
                "summary": str(args.outdir / "summary.json"),
                "logZ": summary["logZ"],
                "logZ_err": summary["logZ_err"],
                "chi2": summary["minimize"]["chi2"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
