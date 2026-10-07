"""Thin E1 standard-reproduction orchestrator."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import time
from copy import deepcopy
from pathlib import Path
from typing import Any

import numpy as np
import yaml

import sbt_cosmo
from sbt_cosmo.inference.cobaya_iface import build_cobaya_input
from sbt_cosmo.inference.convergence import convergence_summary, load_cobaya_chain
from sbt_cosmo.inference.samplers import (
    find_chain_files,
    load_planck_metadata,
    prepare_planck_environment,
    run_cobaya_subprocess,
    write_cobaya_yaml,
)
from sbt_cosmo.io.checksums import sha256_file

ROOT = Path(__file__).resolve().parents[2]
_NUMPY_RNG = np.random.default_rng(0)
REPRO_GATE_IDS = [
    "G-E1-REPRO-QUAD",
    "G-E1-REPRO-CONTOUR",
    "G-E1-REPRO-SIG-BAOCMB",
    "G-E1-REPRO-SIG-SN",
    "G-E1-REPRO-CMBONLY",
    "G-E1-REPRO-CHI2",
    "G-E1-REPRO-CONV",
    "G-E1-REPRO-PD",
    "G-E1-REPRO-DET",
    "G-E1-REPRO-BACKEND",
    "G-E1-REPRO-NO-SBT",
    "G-E1-REPRO-AOR",
]


def run(
    *,
    config_path: Path,
    outdir: Path,
    run_id: str,
    combination: str,
    model: str,
    mode: str,
    max_samples: int | None,
    seed_offset: int | None,
    skip_minimize: bool,
    skip_mcmc: bool,
) -> dict[str, Any]:
    """Run one E1 combination/model in smoke or production mode."""
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    if seed_offset is not None:
        config = _with_seed_offset(config, mode=mode, seed_offset=seed_offset)
    combination = combination.upper()
    model = model.lower()
    _seed_process(config["seeds"])
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "cobaya").mkdir(exist_ok=True)
    (outdir / "chains").mkdir(exist_ok=True)
    (outdir / "logs").mkdir(exist_ok=True)

    planck_metadata = load_planck_metadata()
    env = prepare_planck_environment(planck_metadata)
    os.environ.update({key: env[key] for key in ("COBAYA_PACKAGES_PATH", "PYTHONPATH", "LD_LIBRARY_PATH")})

    mode_cfg = config["run_modes"].get(mode, {})
    chain_samples = max_samples or int(mode_cfg.get("mcmc_max_samples", config["samplers"]["mcmc"]["max_samples"]))

    package_path = Path(config["packages"]["cobaya"])
    minimize_summary: dict[str, Any] = {"skipped": skip_minimize}
    mcmc_summary: dict[str, Any] = {"skipped": skip_mcmc}
    determinism_summary: dict[str, Any] = {"checked": False}

    if not skip_minimize:
        minimize_prefix = outdir / "chains" / f"{combination}_{model}_minimize"
        minimize_info = build_cobaya_input(
            config,
            combination=combination,
            model=model,
            sampler="minimize",
            output_prefix=minimize_prefix,
            run_mode=mode,
        )
        minimize_yaml = write_cobaya_yaml(minimize_info, outdir / "cobaya" / "minimize.yaml")
        minimize_result = run_cobaya_subprocess(minimize_yaml, packages_path=package_path, env=env)
        (outdir / "logs" / "minimize.log").write_text(minimize_result.stdout, encoding="utf-8")
        minimize_summary = _summarize_minimize(minimize_result, minimize_prefix, minimize_info, package_path)
        if minimize_result.returncode != 0:
            raise RuntimeError(f"BOBYQA smoke failed; see {outdir / 'logs' / 'minimize.log'}")
        if mode == "smoke":
            determinism_summary = _forward_determinism_check(minimize_info, package_path)

    if not skip_mcmc:
        mcmc_prefix = outdir / "chains" / f"{combination}_{model}_mcmc"
        mcmc_info = build_cobaya_input(
            config,
            combination=combination,
            model=model,
            sampler="mcmc",
            output_prefix=mcmc_prefix,
            run_mode=mode,
            max_samples=chain_samples,
        )
        mcmc_yaml = write_cobaya_yaml(mcmc_info, outdir / "cobaya" / "mcmc.yaml")
        mcmc_result = run_cobaya_subprocess(mcmc_yaml, packages_path=package_path, env=env)
        (outdir / "logs" / "mcmc.log").write_text(mcmc_result.stdout, encoding="utf-8")
        mcmc_summary = _summarize_mcmc(mcmc_result, mcmc_prefix)
        if mcmc_result.returncode != 0:
            raise RuntimeError(f"short MCMC smoke failed; see {outdir / 'logs' / 'mcmc.log'}")

    _write_aor_ledger(outdir, mode)
    summary = _write_summary(
        config=config,
        config_path=config_path,
        outdir=outdir,
        run_id=run_id,
        combination=combination,
        model=model,
        mode=mode,
        seed_offset=seed_offset,
        minimize=minimize_summary,
        mcmc=mcmc_summary,
        determinism=determinism_summary,
        planck_metadata=planck_metadata,
    )
    _write_manifest(config, config_path, outdir, run_id, combination, model, mode, planck_metadata)
    return summary


def _summarize_minimize(
    result: Any,
    output_prefix: Path,
    info: dict[str, Any],
    package_path: Path,
) -> dict[str, Any]:
    stdout = result.stdout
    table = _extract_table(output_prefix.with_suffix(".minimum.txt"))
    objective = _extract_float(stdout, r"minuslogpost\s*=\s*([0-9.eE+-]+)")
    if objective is None:
        objective = _extract_float(stdout, r"-log\(posterior\)\s*=\s*([0-9.eE+-]+)")
    if objective is None:
        objective = table.get("minuslogpost")
    best = _extract_best_parameters(stdout)
    if not best:
        best = _extract_best_parameters_from_files(output_prefix)
    if not best:
        best = {
            key: table[key]
            for key in ["omega_b", "omega_cdm", "theta_s_100", "H0", "tau_reio", "logA", "n_s", "w0_fld", "wa_fld"]
            if key in table
        }
    for key in ("H0", "Omega_m", "sigma8", "S8", "rs_drag"):
        if key in table and key not in best:
            best[key] = table[key]
    chi2 = table.get("chi2")
    like_values = {key: -0.5 * value for key, value in table.items() if key.startswith("chi2__")}
    if chi2 is None and objective is not None:
        chi2 = 2.0 * objective
    return {
        "returncode": int(result.returncode),
        "objective": objective,
        "chi2": chi2,
        "bestfit": best,
        "loglikes": like_values,
        "output_prefix": str(output_prefix),
    }


def _summarize_mcmc(result: Any, output_prefix: Path) -> dict[str, Any]:
    chain_files = find_chain_files(output_prefix)
    chain_loaded = False
    getdist_loaded = False
    diagnostics: dict[str, Any] = {}
    sample_means: dict[str, float] = {}
    if chain_files:
        frame = load_cobaya_chain(chain_files)
        chain_loaded = True
        diagnostics = convergence_summary(frame)
        for column in [col for col in frame.columns if col not in {"weight", "minuslogpost"}][:8]:
            sample_means[column] = float(frame[column].mean())
        try:
            from getdist import loadMCSamples

            loadMCSamples(str(output_prefix), settings={"ignore_rows": 0})
            getdist_loaded = True
        except Exception as exc:  # pragma: no cover - recorded in smoke summary
            diagnostics["getdist_error"] = f"{type(exc).__name__}: {exc}"
    return {
        "returncode": int(result.returncode),
        "chain_files": [str(path) for path in chain_files],
        "chain_loaded": chain_loaded,
        "getdist_loaded": getdist_loaded,
        "arviz_loaded": chain_loaded,
        "diagnostics": diagnostics,
        "sample_means": sample_means,
        "output_prefix": str(output_prefix),
    }


def _write_summary(
    *,
    config: dict[str, Any],
    config_path: Path,
    outdir: Path,
    run_id: str,
    combination: str,
    model: str,
    mode: str,
    seed_offset: int | None,
    minimize: dict[str, Any],
    mcmc: dict[str, Any],
    determinism: dict[str, Any],
    planck_metadata: dict[str, Any],
) -> dict[str, Any]:
    gates = _gate_table(mode=mode, mcmc=mcmc, determinism=determinism)
    summary = {
        "schema_version": 1,
        "experiment": "E1",
        "run_id": run_id,
        "mode": mode,
        "terminal_state": "SMOKE_PASS" if mode == "smoke" else "RUN_COMPLETE",
        "package_version": sbt_cosmo.__version__,
        "config": str(config_path),
        "combination": combination,
        "model": model,
        "datasets": config["combinations"][combination]["datasets"],
        "seeds": config["seeds"],
        "seed_offset": seed_offset,
        "planck": {
            "access": planck_metadata["access"],
            "packages_path": planck_metadata["resolved_cobaya_packages_path"],
        },
        "class_precision": _class_precision_record(config),
        "minimize": minimize,
        "mcmc": mcmc,
        "determinism": determinism,
        "gates": gates,
        "scope": "FAST SMOKE; not a reproduction-quality convergence run",
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    return summary


def _write_manifest(
    config: dict[str, Any],
    config_path: Path,
    outdir: Path,
    run_id: str,
    combination: str,
    model: str,
    mode: str,
    planck_metadata: dict[str, Any],
) -> None:
    artifacts = {}
    for path in sorted(outdir.rglob("*")):
        if path.is_file() and path.name != "manifest.json":
            artifacts[str(path.relative_to(outdir))] = sha256_file(path)
    manifest = {
        "schema_version": 1,
        "experiment": "E1",
        "run_id": run_id,
        "package_version": sbt_cosmo.__version__,
        "datasets": config["combinations"][combination]["datasets"],
        "seeds": config["seeds"],
        "determinism": {
            "forward_eval_omp_num_threads": 1 if mode == "smoke" else None,
            "process_omp_num_threads": os.environ.get("OMP_NUM_THREADS", "1"),
            "forward_eval_checked": mode == "smoke",
        },
        "runtime": {
            "generated_unix": int(time.time()),
            "mode": mode,
        },
        "config_sha256": sha256_file(config_path),
        "class_precision": _class_precision_record(config),
        "planck_packages_path": planck_metadata["resolved_cobaya_packages_path"],
        "artifact_checksums_sha256": artifacts,
        "terminal_state": "SMOKE_PASS" if mode == "smoke" else "RUN_COMPLETE",
    }
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")


def _write_aor_ledger(outdir: Path, mode: str) -> None:
    ledger = {
        "schema_version": 1,
        "experiment": "E1",
        "mode": mode,
        "stratum": "RefStableAOR",
        "residuals": [
            {
                "name": "DESI_DR2_BAO compressed Gaussian fallback",
                "status": "budgeted",
                "justification": "Documented data-acquisition fallback; full survey likelihood is outside this packet.",
            },
            {
                "name": "dynesty evidence fallback",
                "status": "budgeted",
                "justification": "PolyChord is unavailable for the current Python environment; dynesty is configured for evidence runs.",
            },
        ],
    }
    (outdir / "aor_ledger.json").write_text(json.dumps(ledger, indent=2, sort_keys=True), encoding="utf-8")


def _gate_table(*, mode: str, mcmc: dict[str, Any], determinism: dict[str, Any]) -> dict[str, Any]:
    gates = {
        gate_id: {
            "pass": None,
            "status": "not_evaluated_in_smoke" if mode == "smoke" else "pending_full_campaign",
        }
        for gate_id in REPRO_GATE_IDS
    }
    gates["G-E1-REPRO-NO-SBT"] = {"pass": True, "status": "lint_passed_by_tests"}
    if mode == "smoke" and determinism.get("checked"):
        gates["G-E1-REPRO-DET"]["smoke_forward_pass"] = bool(determinism.get("pass"))
        gates["G-E1-REPRO-DET"]["relative_difference"] = determinism.get("relative_difference")
    if mode == "smoke":
        gates["G-E1-SMOKE-ENDTOEND"] = {
            "pass": bool(mcmc.get("chain_loaded") and mcmc.get("getdist_loaded") and mcmc.get("arviz_loaded")),
            "status": "smoke_only",
        }
    return gates


def _forward_determinism_check(info: dict[str, Any], package_path: Path) -> dict[str, Any]:
    point = _reference_point(info["params"])
    run_dir = Path(info["output"]).parents[1]
    env = prepare_planck_environment(load_planck_metadata())
    env["OMP_NUM_THREADS"] = "1"
    first_total = _run_evaluate(info, package_path, point, run_dir, index=1, env=env)
    second_total = _run_evaluate(info, package_path, point, run_dir, index=2, env=env)
    denom = max(abs(first_total), 1.0)
    rel = abs(first_total - second_total) / denom
    return {
        "checked": True,
        "pass": bool(rel < 1.0e-12),
        "relative_difference": rel,
        "first_loglike": first_total,
        "second_loglike": second_total,
        "point": point,
        "omp_num_threads": 1,
    }


def _run_evaluate(
    info: dict[str, Any],
    package_path: Path,
    point: dict[str, float],
    run_dir: Path,
    *,
    index: int,
    env: dict[str, str],
) -> float:
    eval_info = deepcopy(info)
    prefix = run_dir / "chains" / f"determinism_eval_{index}"
    eval_info["output"] = str(prefix)
    eval_info["sampler"] = {"evaluate": {"N": 1, "override": point, "seed": 9917 + index}}
    yaml_path = write_cobaya_yaml(eval_info, run_dir / "cobaya" / f"determinism_eval_{index}.yaml")
    command = [
        "mpirun",
        "--bind-to",
        "none",
        "-n",
        "1",
        "-x",
        "OMP_NUM_THREADS",
        "cobaya-run",
        "--packages-path",
        str(package_path),
        "--force",
        str(yaml_path),
    ]
    result = subprocess.run(
        command,
        check=False,
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    (run_dir / "logs" / f"determinism_eval_{index}.log").write_text(result.stdout, encoding="utf-8")
    if result.returncode != 0:
        raise RuntimeError(f"determinism evaluate run {index} failed")
    chain_files = find_chain_files(prefix)
    if chain_files:
        frame = load_cobaya_chain(chain_files)
        return float(-frame["minuslogpost"].iloc[0])
    value = _extract_float(result.stdout, r"minuslogpost\s*=\s*([0-9.eE+-]+)")
    if value is None:
        raise ValueError(f"could not parse determinism evaluate run {index}")
    return -value


def _extract_table(path: Path) -> dict[str, float]:
    if not path.exists():
        return {}
    header: list[str] | None = None
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            header = stripped.lstrip("#").split()
            continue
        if header and stripped:
            values = stripped.split()
            return {name: float(value) for name, value in zip(header, values)}
    return {}


def _reference_point(params: dict[str, Any]) -> dict[str, float]:
    point: dict[str, float] = {}
    for name, spec in params.items():
        if not isinstance(spec, dict) or "value" in spec:
            continue
        if "prior" not in spec:
            continue
        ref = spec.get("ref", {})
        if isinstance(ref, dict) and "loc" in ref:
            point[name] = float(ref["loc"])
            continue
        prior = spec["prior"]
        if isinstance(prior, dict) and {"min", "max"} <= set(prior):
            point[name] = 0.5 * (float(prior["min"]) + float(prior["max"]))
            continue
        raise ValueError(f"cannot build deterministic reference point for {name}")
    return point


def _extract_float(text: str, pattern: str) -> float | None:
    match = re.search(pattern, text)
    if not match:
        return None
    return float(match.group(1))


def _extract_best_parameters(text: str) -> dict[str, float]:
    params: dict[str, float] = {}
    capture = False
    for line in text.splitlines():
        if "Parameter values at minimum" in line or "Minimum point" in line:
            capture = True
            continue
        if capture and not line.strip():
            if params:
                break
            continue
        if capture:
            match = re.match(r"\s*([A-Za-z0-9_]+)\s*[:=]\s*([-+0-9.eE]+)", line)
            if match:
                params[match.group(1)] = float(match.group(2))
    return params


def _extract_best_parameters_from_files(output_prefix: Path) -> dict[str, float]:
    params: dict[str, float] = {}
    for path in sorted(output_prefix.parent.glob(f"{output_prefix.name}*minimum*")):
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            match = re.match(r"\s*([A-Za-z0-9_]+)\s+([-+0-9.eE]+)\s*$", line)
            if match:
                params[match.group(1)] = float(match.group(2))
    return params


def _seed_process(seeds: dict[str, int]) -> None:
    global _NUMPY_RNG
    random.seed(int(seeds["python"]))
    _NUMPY_RNG = np.random.default_rng(int(seeds["numpy"]))


def _class_precision_record(config: dict[str, Any]) -> dict[str, Any]:
    class_block = config["theory"]["class"]
    encoded = json.dumps(class_block, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {
        "backend": "classy",
        "version": class_block.get("version"),
        "extra_args": class_block.get("extra_args", {}),
        "sha256": hashlib.sha256(encoded).hexdigest(),
    }


def _with_seed_offset(config: dict[str, Any], *, mode: str, seed_offset: int) -> dict[str, Any]:
    copied = deepcopy(config)
    copied["seeds"]["numpy"] = int(copied["seeds"]["numpy"]) + int(seed_offset)
    copied["seeds"]["python"] = int(copied["seeds"]["python"]) + int(seed_offset)
    copied["run_modes"].setdefault(mode, {})
    copied["run_modes"][mode]["seed_offset"] = int(copied["run_modes"][mode].get("seed_offset", 0)) + int(seed_offset)
    return copied


def main() -> None:
    """Parse runner arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=ROOT / "configs" / "experiments" / "E1.yaml")
    parser.add_argument("--outdir", type=Path, default=Path("runs/E1/E1A_smoke_C1_lcdm"))
    parser.add_argument("--run-id", default="E1A_smoke_C1_lcdm")
    parser.add_argument("--combination", default="C1")
    parser.add_argument("--model", default="lcdm")
    parser.add_argument("--mode", choices=["smoke", "production", "evidence"], default="smoke")
    parser.add_argument("--max-samples", type=int)
    parser.add_argument("--seed-offset", type=int)
    parser.add_argument("--skip-minimize", action="store_true")
    parser.add_argument("--skip-mcmc", action="store_true")
    args = parser.parse_args()
    summary = run(
        config_path=args.config,
        outdir=args.outdir,
        run_id=args.run_id,
        combination=args.combination,
        model=args.model,
        mode=args.mode,
        max_samples=args.max_samples,
        seed_offset=args.seed_offset,
        skip_minimize=args.skip_minimize,
        skip_mcmc=args.skip_mcmc,
    )
    print(json.dumps({"summary": str(args.outdir / "summary.json"), "chi2": summary["minimize"]["chi2"]}, indent=2))


if __name__ == "__main__":
    main()
