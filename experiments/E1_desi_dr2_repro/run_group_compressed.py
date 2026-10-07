"""Compressed-CMB E1 group runner with independent single-rank chains."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import time
from copy import deepcopy
from pathlib import Path
from typing import Any

import yaml

import sbt_cosmo
from sbt_cosmo.inference.cobaya_compressed import build_compressed_cobaya_input
from sbt_cosmo.inference.convergence import convergence_summary_from_chain_files, load_cobaya_chain
from sbt_cosmo.inference.samplers import find_chain_files, write_cobaya_yaml
from sbt_cosmo.io.checksums import sha256_file
from sbt_cosmo.theory.background_compressed import omega_m_approx

from run import _reference_point, _summarize_minimize

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PACKAGES_PATH = Path("/mnt/data-drive/sbt-de/data/raw/planck_2018/cobaya-packages")


def run_group(
    *,
    config_path: Path,
    outdir: Path,
    run_id: str,
    combination: str,
    model: str,
    run_mode: str,
    chains: int,
    omp_threads: int,
    max_samples: int,
    covmat: Path | None,
    resume: bool,
    skip_mcmc: bool,
) -> dict[str, Any]:
    """Run one compressed E1 combination/model."""
    started = time.monotonic()
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    combination = combination.upper()
    model = model.lower()
    outdir.mkdir(parents=True, exist_ok=True)
    for subdir in ("chains", "cobaya", "logs"):
        (outdir / subdir).mkdir(exist_ok=True)
    env = os.environ.copy()
    env["OMP_NUM_THREADS"] = str(int(omp_threads))
    env.setdefault("PYTHONNOUSERSITE", "1")
    covmat_path = Path(covmat) if covmat is not None else None
    if covmat_path is not None and not _path_exists_from_root(covmat_path):
        raise FileNotFoundError(f"proposal covmat not found: {covmat_path}")

    minimize_prefix = outdir / "chains" / f"{combination}_{model}_minimize"
    minimize_summary, minimize_info = _run_minimize_once(
        config=config,
        combination=combination,
        model=model,
        run_mode=run_mode,
        outdir=outdir,
        output_prefix=minimize_prefix,
        env=env,
        resume=resume,
    )
    determinism_summary = _forward_determinism_check(minimize_info, outdir, env)
    mcmc_config = _with_map_refs(config, minimize_summary.get("bestfit", {}))
    mcmc_prefix = outdir / "chains" / f"{combination}_{model}_chain"

    sampled = _sampled_parameters(
        build_compressed_cobaya_input(
            mcmc_config,
            combination=combination,
            model=model,
            sampler="mcmc",
            output_prefix=outdir / "chains" / "parameter_probe",
            run_mode=run_mode,
            max_samples=max_samples,
            covmat=covmat_path,
        )["params"]
    )

    diagnostics: dict[str, Any] = {}

    def emit_summary(*, terminal_state: str, diagnostics: dict[str, Any], wall: float, total_samples: int) -> dict[str, Any]:
        summary = {
            "schema_version": 1,
            "experiment": "E1_compressed",
            "run_id": run_id,
            "mode": run_mode,
            "terminal_state": terminal_state,
            "package_version": sbt_cosmo.__version__,
            "combination": combination,
            "model": model,
            "datasets": config["combinations"][combination]["datasets"],
            "config": str(config_path),
            "seeds": config["seeds"],
            "clik_invoked": False,
            "spectra_invoked": False,
            "background_backend": "classy_background_only",
            "minimize": minimize_summary,
            "mcmc": {
                "coordination": "independent_single_rank_mpirun",
                "chains": chains,
                "omp_threads_per_chain": int(omp_threads),
                "cores_per_group": int(chains) * int(omp_threads),
                "max_samples_per_chain": int(max_samples),
                "Rminus1_stop": 0.01,
                "Rminus1_cl_stop": 0.2,
                "covmat": str(covmat_path) if covmat_path is not None else None,
                "chain_prefixes": diagnostics.get("chain_prefixes", []),
                "chain_files": diagnostics.get("chain_files", []),
                "sampled_parameters": sampled,
                "diagnostics": diagnostics,
                "wall_clock_seconds": wall,
                "seconds_per_sample": wall / total_samples if total_samples else None,
            },
            "determinism": determinism_summary,
            "scope": "compressed-CMB validation; not the full E1 campaign" if run_mode == "validation" else "compressed-CMB production group",
        }
        (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
        _write_manifest(config_path, outdir, summary)
        return summary

    if skip_mcmc:
        return emit_summary(
            terminal_state="MINIMIZE_ONLY_PASS",
            diagnostics={"skipped": True, "reason": "skip_mcmc"},
            wall=time.monotonic() - started,
            total_samples=0,
        )

    mcmc_result = _run_independent_mcmc(
        config=mcmc_config,
        combination=combination,
        model=model,
        run_mode=run_mode,
        outdir=outdir,
        output_prefix_base=mcmc_prefix,
        env=env,
        chains=chains,
        omp_threads=omp_threads,
        max_samples=max_samples,
        resume=resume,
        covmat=covmat_path,
    )
    chain_files = [Path(path) for path in mcmc_result["chain_files"]]
    diagnostics = (
        convergence_summary_from_chain_files(chain_files, parameters=sampled)
        if len(chain_files) >= 2
        else {"n_chains": len(chain_files), "total_samples": 0, "max_rhat_minus_one": None, "min_ess": None}
    )
    all_chains_ok = mcmc_result["returncode"] == 0
    diagnostics.update(
        {
            "returncode": mcmc_result["returncode"],
            "stop_reason": "max_samples_then_rhat" if all_chains_ok else "max_samples_then_rhat_partial",
            "chain_files": [str(path) for path in chain_files],
            "chain_prefixes": mcmc_result["chain_prefixes"],
            "logs": mcmc_result["logs"],
            "failed_chains": mcmc_result["failed_chains"],
            "chain_results": mcmc_result["chain_results"],
        }
    )
    if not all_chains_ok:
        diagnostics["error_excerpt"] = mcmc_result["error_excerpt"]
        if len(chain_files) < 2:
            summary = emit_summary(
                terminal_state="GROUP_FAILED_PARTIAL",
                diagnostics=diagnostics,
                wall=time.monotonic() - started,
                total_samples=int(diagnostics.get("total_samples") or 0),
            )
            raise RuntimeError(f"fewer than two compressed chains survived: {summary['run_id']}")

    return emit_summary(
        terminal_state=(
            "VALIDATION_PASS" if run_mode == "validation" and all_chains_ok
            else "VALIDATION_PARTIAL" if run_mode == "validation"
            else "RUN_COMPLETE" if all_chains_ok
            else "RUN_COMPLETE_PARTIAL"
        ),
        diagnostics=diagnostics,
        wall=time.monotonic() - started,
        total_samples=int(diagnostics.get("total_samples") or 0),
    )


def _run_minimize_once(
    *,
    config: dict[str, Any],
    combination: str,
    model: str,
    run_mode: str,
    outdir: Path,
    output_prefix: Path,
    env: dict[str, str],
    resume: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    info = build_compressed_cobaya_input(
        config,
        combination=combination,
        model=model,
        sampler="minimize",
        output_prefix=output_prefix,
        run_mode=run_mode,
    )
    minimum_file = output_prefix.with_suffix(".minimum.txt")
    if resume and minimum_file.exists():
        return _summarize_minimize(subprocess.CompletedProcess([], 0, stdout=""), output_prefix, info, DEFAULT_PACKAGES_PATH), info
    yaml_path = write_cobaya_yaml(info, outdir / "cobaya" / "minimize.yaml")
    _clear_stale_locks(outdir=outdir, output_prefix=output_prefix, yaml_path=yaml_path)
    log_path = outdir / "logs" / "minimize.log"
    command = _cobaya_command(yaml_path=yaml_path, output_prefix=output_prefix, chains=1, force=True, resume=False)
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log_path.write_text(result.stdout, encoding="utf-8")
    summary = _summarize_minimize(result, output_prefix, info, DEFAULT_PACKAGES_PATH)
    if result.returncode != 0:
        raise RuntimeError(f"compressed minimize failed; see {log_path}")
    return summary, info


def _forward_determinism_check(info: dict[str, Any], outdir: Path, env: dict[str, str]) -> dict[str, Any]:
    point = _reference_point(info["params"])
    run_env = dict(env)
    run_env["OMP_NUM_THREADS"] = "1"
    first = _run_evaluate(info, outdir, point, index=1, env=run_env)
    second = _run_evaluate(info, outdir, point, index=2, env=run_env)
    denom = max(abs(first), 1.0)
    relative_difference = abs(first - second) / denom
    return {
        "checked": True,
        "pass": bool(relative_difference < 1.0e-12),
        "relative_difference": relative_difference,
        "first_loglike": first,
        "second_loglike": second,
        "point": point,
        "forward_eval_omp_num_threads": 1,
        "chain_bitwise_determinism_claimed": False,
    }


def _run_evaluate(info: dict[str, Any], outdir: Path, point: dict[str, float], *, index: int, env: dict[str, str]) -> float:
    eval_info = deepcopy(info)
    prefix = outdir / "chains" / f"determinism_eval_{index}"
    eval_info["output"] = str(prefix)
    eval_info["sampler"] = {"evaluate": {"N": 1, "override": point, "seed": 9917 + index}}
    yaml_path = write_cobaya_yaml(eval_info, outdir / "cobaya" / f"determinism_eval_{index}.yaml")
    command = _cobaya_command(yaml_path=yaml_path, output_prefix=prefix, chains=1, force=True, resume=False)
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (outdir / "logs" / f"determinism_eval_{index}.log").write_text(result.stdout, encoding="utf-8")
    if result.returncode != 0:
        raise RuntimeError(f"compressed determinism evaluate run {index} failed")
    value = _extract_float(result.stdout, r"minuslogpost\\s*=\\s*([0-9.eE+-]+)")
    if value is None:
        value = _extract_float(result.stdout, r"-log\\(posterior\\)\\s*=\\s*([0-9.eE+-]+)")
    if value is None:
        chain_files = find_chain_files(prefix)
        if chain_files:
            frame = load_cobaya_chain(chain_files)
            value = float(frame["minuslogpost"].iloc[0])
    if value is None:
        raise ValueError(f"could not parse compressed determinism evaluate run {index}")
    return -value


def _run_independent_mcmc(
    *,
    config: dict[str, Any],
    combination: str,
    model: str,
    run_mode: str,
    outdir: Path,
    output_prefix_base: Path,
    env: dict[str, str],
    chains: int,
    omp_threads: int,
    max_samples: int,
    resume: bool,
    covmat: Path | None,
) -> dict[str, Any]:
    processes: list[dict[str, Any]] = []
    for chain_index in range(1, int(chains) + 1):
        output_prefix = output_prefix_base.with_name(f"{output_prefix_base.name}{chain_index}")
        info = build_compressed_cobaya_input(
            config,
            combination=combination,
            model=model,
            sampler="mcmc",
            output_prefix=output_prefix,
            run_mode=run_mode,
            max_samples=max_samples,
            covmat=covmat,
        )
        sampler_cfg = info["sampler"]["mcmc"]
        sampler_cfg["Rminus1_stop"] = 0.01
        sampler_cfg["Rminus1_cl_stop"] = 0.2
        sampler_cfg["max_samples"] = int(max_samples)
        sampler_cfg["seed"] = int(sampler_cfg.get("seed", config["seeds"]["sampler"])) + chain_index
        log_path = outdir / "logs" / f"mcmc_chain{chain_index}.log"
        can_resume = resume and output_prefix.with_suffix(".updated.yaml").exists()
        if can_resume:
            info["force"] = False
            info["resume"] = True
        yaml_path = write_cobaya_yaml(info, outdir / "cobaya" / f"mcmc_chain{chain_index}.yaml")
        command = _cobaya_command(yaml_path=yaml_path, output_prefix=output_prefix, chains=1, force=not can_resume, resume=can_resume)
        log_handle = log_path.open("w", encoding="utf-8")
        process = subprocess.Popen(command, cwd=ROOT, env=env, text=True, stdout=log_handle, stderr=subprocess.STDOUT)
        processes.append({"chain_index": chain_index, "process": process, "log_handle": log_handle, "log": log_path, "prefix": output_prefix, "command": command})

    chain_results: list[dict[str, Any]] = []
    for item in processes:
        returncode = int(item["process"].wait())
        item["log_handle"].close()
        chain_files = find_chain_files(item["prefix"])
        chain_results.append(
            {
                "chain_index": item["chain_index"],
                "returncode": returncode,
                "command": item["command"],
                "log": str(item["log"]),
                "prefix": str(item["prefix"]),
                "chain_files": [str(path) for path in chain_files],
                "error_excerpt": _extract_failure_excerpt(item["log"]) if returncode != 0 else "",
            }
        )
    failed_chains = [entry["chain_index"] for entry in chain_results if entry["returncode"] != 0]
    return {
        "returncode": 0 if not failed_chains else 1,
        "chain_results": chain_results,
        "chain_prefixes": [entry["prefix"] for entry in chain_results],
        "chain_files": [path for entry in chain_results for path in entry["chain_files"]],
        "logs": [entry["log"] for entry in chain_results],
        "failed_chains": failed_chains,
        "error_excerpt": "\n\n".join(entry["error_excerpt"] for entry in chain_results if entry["error_excerpt"]),
    }


def _cobaya_command(*, yaml_path: Path, output_prefix: Path, chains: int, force: bool, resume: bool) -> list[str]:
    command = [
        "mpirun",
        "--bind-to",
        "none",
        "-n",
        str(int(chains)),
        "-x",
        "OMP_NUM_THREADS",
        "cobaya-run",
        "--packages-path",
        str(DEFAULT_PACKAGES_PATH),
        "--output",
        str(output_prefix),
    ]
    if resume:
        command.append("--resume")
    elif force:
        command.append("--force")
    command.append(str(yaml_path))
    return command


def _sampled_parameters(params: dict[str, Any]) -> list[str]:
    return [name for name, spec in params.items() if isinstance(spec, dict) and "prior" in spec and "value" not in spec]


def _with_map_refs(config: dict[str, Any], bestfit: dict[str, float]) -> dict[str, Any]:
    copied = deepcopy(config)
    for block_name in ("cosmology",):
        for name, spec in copied.get("priors", {}).get(block_name, {}).items():
            if name in bestfit and isinstance(spec, dict) and "prior" in spec:
                scale = float(spec.get("proposal", 0.01))
                spec["ref"] = {"dist": "norm", "loc": float(bestfit[name]), "scale": scale}
    for model_cfg in copied.get("models", {}).values():
        for name, spec in model_cfg.get("sampled", {}).items():
            if name in bestfit and isinstance(spec, dict) and "prior" in spec:
                scale = float(spec.get("proposal", 0.05))
                spec["ref"] = {"dist": "norm", "loc": float(bestfit[name]), "scale": scale}
    return copied


def _path_exists_from_root(path: Path) -> bool:
    return path.exists() if path.is_absolute() else (ROOT / path).exists()


def _clear_stale_locks(*, outdir: Path, output_prefix: Path, yaml_path: Path) -> None:
    for lock in [
        yaml_path.with_name(yaml_path.name + ".locked"),
        *output_prefix.parent.glob(f"{output_prefix.name}*.locked"),
        *(outdir / "cobaya").glob("*.locked"),
    ]:
        if lock.exists():
            lock.unlink()


def _extract_failure_excerpt(log_path: Path, *, max_lines: int = 24) -> str:
    if not log_path.exists():
        return "<log file missing>"
    lines = log_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    patterns = ("Traceback", "ERROR", "Error", "exception", "Segmentation fault", "signal 11")
    selected = [line for line in lines if any(pattern in line for pattern in patterns)]
    if not selected:
        selected = lines[-max_lines:]
    return "\n".join(selected[-max_lines:])


def _extract_float(text: str, pattern: str) -> float | None:
    import re

    match = re.search(pattern, text)
    return float(match.group(1)) if match else None


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
    parser.add_argument("--run-mode", choices=["production", "validation"], default="production")
    parser.add_argument("--chains", type=int, default=4)
    parser.add_argument("--omp-threads", type=int, default=1)
    parser.add_argument("--max-samples", type=int, default=3000)
    parser.add_argument("--covmat", type=Path)
    parser.add_argument("--skip-mcmc", action="store_true")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    summary = run_group(
        config_path=args.config,
        outdir=args.outdir,
        run_id=args.run_id,
        combination=args.combination,
        model=args.model,
        run_mode=args.run_mode,
        chains=args.chains,
        omp_threads=args.omp_threads,
        max_samples=args.max_samples,
        covmat=args.covmat,
        resume=args.resume,
        skip_mcmc=args.skip_mcmc,
    )
    print(json.dumps({"summary": str(args.outdir / "summary.json"), "diagnostics": summary["mcmc"]["diagnostics"]}, indent=2))


if __name__ == "__main__":
    main()
