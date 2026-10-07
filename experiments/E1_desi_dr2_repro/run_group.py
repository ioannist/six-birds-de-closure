"""Group runner: one minimization plus independent single-rank MCMC chains."""

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
from sbt_cosmo.inference.cobaya_iface import build_cobaya_input
from sbt_cosmo.inference.convergence import convergence_summary_from_chain_files
from sbt_cosmo.inference.samplers import find_chain_files, load_planck_metadata, prepare_planck_environment, write_cobaya_yaml
from sbt_cosmo.io.checksums import sha256_file

from run import _class_precision_record, _forward_determinism_check, _summarize_minimize

ROOT = Path(__file__).resolve().parents[2]


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
    rminus1_stop: float,
    rminus1_cl_stop: float,
    max_samples: int,
    covmat: Path | None,
    resume: bool,
    skip_mcmc: bool,
) -> dict[str, Any]:
    """Run one E1 combination/model as a group of independent chains."""
    started = time.monotonic()
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    combination = combination.upper()
    model = model.lower()
    outdir.mkdir(parents=True, exist_ok=True)
    for subdir in ("chains", "cobaya", "logs"):
        (outdir / subdir).mkdir(exist_ok=True)

    planck_metadata = load_planck_metadata()
    env = prepare_planck_environment(planck_metadata)
    env["OMP_NUM_THREADS"] = str(int(omp_threads))
    package_path = Path(config["packages"]["cobaya"])
    covmat_path = Path(covmat) if covmat is not None else None
    if covmat_path is not None and not covmat_path.exists():
        raise FileNotFoundError(f"proposal covmat not found: {covmat_path}")

    minimize_prefix = outdir / "chains" / f"{combination}_{model}_minimize"
    minimize_summary, minimize_info = _run_minimize_once(
        config=config,
        config_path=config_path,
        combination=combination,
        model=model,
        run_mode=run_mode,
        outdir=outdir,
        output_prefix=minimize_prefix,
        package_path=package_path,
        env=env,
        resume=resume,
    )
    determinism_summary = _forward_determinism_check(minimize_info, package_path)
    mcmc_config = _with_map_refs(config, minimize_summary.get("bestfit", {}))

    sampled = _sampled_parameters(
        build_cobaya_input(
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
    mcmc_prefix = outdir / "chains" / f"{combination}_{model}_chain"

    def emit_summary(*, terminal_state: str, diagnostics: dict[str, Any], wall: float, total_samples: int) -> dict[str, Any]:
        summary = {
            "schema_version": 1,
            "experiment": "E1",
            "run_id": run_id,
            "mode": run_mode,
            "terminal_state": terminal_state,
            "package_version": sbt_cosmo.__version__,
            "combination": combination,
            "model": model,
            "datasets": config["combinations"][combination]["datasets"],
            "config": str(config_path),
            "seeds": config["seeds"],
            "planck": {"packages_path": planck_metadata["resolved_cobaya_packages_path"]},
            "class_precision": _class_precision_record(config),
            "minimize": minimize_summary,
            "mcmc": {
                "coordinated": False,
                "coordination": "independent_single_rank_mpirun",
                "rminus1_stop": rminus1_stop,
                "rminus1_cl_stop": rminus1_cl_stop,
                "chains": chains,
                "omp_threads_per_chain": int(omp_threads),
                "cores_per_group": int(chains) * int(omp_threads),
                "covmat": str(covmat_path) if covmat_path is not None else None,
                "shared_prefix": None,
                "chain_prefixes": diagnostics.get("chain_prefixes", []),
                "chain_files": diagnostics.get("chain_files", []),
                "sampled_parameters": sampled,
                "diagnostics": diagnostics,
                "wall_clock_seconds": wall,
                "seconds_per_sample": wall / total_samples if total_samples else None,
            },
            "determinism": {
                **determinism_summary,
                "forward_eval_omp_num_threads": 1,
                "chain_omp_num_threads": int(omp_threads),
                "chain_bitwise_determinism_claimed": False,
                "chain_validation": "statistical_Rhat_ESS",
            },
            "scope": "VALIDATION; not a reproduction-quality campaign" if run_mode == "validation" else "production group",
        }
        (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
        _write_manifest(config_path, outdir, summary)
        _write_status(outdir, "failed_partial" if "FAILED" in terminal_state else "complete", summary)
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
        package_path=package_path,
        env=env,
        chains=chains,
        omp_threads=omp_threads,
        max_samples=max_samples,
        rminus1_stop=rminus1_stop,
        rminus1_cl_stop=rminus1_cl_stop,
        resume=resume,
        covmat=covmat_path,
    )
    chain_files = [Path(path) for path in mcmc_result["chain_files"]]
    if len(chain_files) >= 2:
        diagnostics = convergence_summary_from_chain_files(chain_files, parameters=sampled)
    else:
        diagnostics = {"n_chains": len(chain_files), "total_samples": 0, "max_rhat_minus_one": None, "min_ess": None}
    all_chains_ok = mcmc_result["returncode"] == 0
    diagnostics.update(
        {
            "returncode": mcmc_result["returncode"],
            "stop_reason": "max_samples_then_rhat" if all_chains_ok else "max_samples_then_rhat_partial",
            "chain_files": [str(path) for path in chain_files],
            "chain_prefixes": mcmc_result["chain_prefixes"],
            "logs": mcmc_result["logs"],
            "chain_results": mcmc_result["chain_results"],
            "failed_chains": mcmc_result["failed_chains"],
            "surviving_chains": len(chain_files),
        }
    )
    if not all_chains_ok:
        diagnostics["error_excerpt"] = mcmc_result["error_excerpt"]
        if len(chain_files) < 2:
            wall = time.monotonic() - started
            total_samples = int(diagnostics.get("total_samples") or 0)
            emit_summary(
                terminal_state="GROUP_FAILED_PARTIAL",
                diagnostics=diagnostics,
                wall=wall,
                total_samples=total_samples,
            )
            raise RuntimeError(f"fewer than two MCMC chains survived for {combination} {model}")

    wall = time.monotonic() - started
    total_samples = int(diagnostics.get("total_samples") or 0)
    return emit_summary(
        terminal_state=(
            "VALIDATION_PASS" if run_mode == "validation" and all_chains_ok
            else "VALIDATION_PARTIAL" if run_mode == "validation"
            else "RUN_COMPLETE" if all_chains_ok
            else "RUN_COMPLETE_PARTIAL"
        ),
        diagnostics=diagnostics,
        wall=wall,
        total_samples=total_samples,
    )


def _run_minimize_once(
    *,
    config: dict[str, Any],
    config_path: Path,
    combination: str,
    model: str,
    run_mode: str,
    outdir: Path,
    output_prefix: Path,
    package_path: Path,
    env: dict[str, str],
    resume: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    minimum_file = output_prefix.with_suffix(".minimum.txt")
    info = build_cobaya_input(
        config,
        combination=combination,
        model=model,
        sampler="minimize",
        output_prefix=output_prefix,
        run_mode=run_mode,
    )
    if resume and minimum_file.exists():
        return _summarize_minimize(subprocess.CompletedProcess([], 0, stdout=""), output_prefix, info, package_path), info
    yaml_path = write_cobaya_yaml(info, outdir / "cobaya" / "minimize.yaml")
    log_path = outdir / "logs" / "minimize.log"
    _clear_stale_locks(outdir=outdir, output_prefix=output_prefix, yaml_path=yaml_path)
    command = _mpi_cobaya_command(
        yaml_path=yaml_path,
        output_prefix=output_prefix,
        package_path=package_path,
        chains=1,
        omp_threads=int(env.get("OMP_NUM_THREADS", "1")),
        force=True,
        resume=False,
    )
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log_path.write_text(result.stdout, encoding="utf-8")
    summary = _summarize_minimize(result, output_prefix, info, package_path)
    summary["covmat_from_minimize"] = str(output_prefix.with_suffix(".covmat")) if output_prefix.with_suffix(".covmat").exists() else None
    if result.returncode != 0:
        raise RuntimeError(f"group minimize failed; see {log_path}")
    return summary, info


def _clear_stale_locks(*, outdir: Path, output_prefix: Path, yaml_path: Path) -> None:
    lock_candidates = [
        yaml_path.with_name(yaml_path.name + ".locked"),
        *output_prefix.parent.glob(f"{output_prefix.name}*.locked"),
        *(outdir / "cobaya").glob("*.locked"),
    ]
    for lock in lock_candidates:
        if lock.exists():
            lock.unlink()


def _run_independent_mcmc(
    *,
    config: dict[str, Any],
    combination: str,
    model: str,
    run_mode: str,
    outdir: Path,
    output_prefix_base: Path,
    package_path: Path,
    env: dict[str, str],
    chains: int,
    omp_threads: int,
    max_samples: int,
    rminus1_stop: float,
    rminus1_cl_stop: float,
    resume: bool,
    covmat: Path | None,
) -> dict[str, Any]:
    processes: list[dict[str, Any]] = []
    for chain_index in range(1, int(chains) + 1):
        output_prefix = output_prefix_base.with_name(f"{output_prefix_base.name}{chain_index}")
        info = build_cobaya_input(
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
        sampler_cfg["Rminus1_stop"] = 0.0
        sampler_cfg["Rminus1_cl_stop"] = 0.0
        sampler_cfg["max_samples"] = int(max_samples)
        sampler_cfg["seed"] = int(sampler_cfg.get("seed", config["seeds"]["sampler"])) + chain_index
        yaml_path = write_cobaya_yaml(info, outdir / "cobaya" / f"mcmc_chain{chain_index}.yaml")
        log_path = outdir / "logs" / f"mcmc_chain{chain_index}.log"
        can_resume = resume and output_prefix.with_suffix(".updated.yaml").exists()
        command = _mpi_cobaya_command(
            yaml_path=yaml_path,
            output_prefix=output_prefix,
            package_path=package_path,
            chains=1,
            omp_threads=omp_threads,
            force=not can_resume,
            resume=can_resume,
        )
        log_handle = log_path.open("w", encoding="utf-8")
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            env=env,
            text=True,
            stdout=log_handle,
            stderr=subprocess.STDOUT,
        )
        processes.append(
            {
                "chain_index": chain_index,
                "process": process,
                "log_handle": log_handle,
                "command": command,
                "log": log_path,
                "prefix": output_prefix,
            }
        )

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
    chain_files = [
        path
        for entry in chain_results
        for path in entry["chain_files"]
    ]
    return {
        "returncode": 0 if not failed_chains else 1,
        "chain_results": chain_results,
        "chain_prefixes": [entry["prefix"] for entry in chain_results],
        "chain_files": chain_files,
        "logs": [entry["log"] for entry in chain_results],
        "failed_chains": failed_chains,
        "error_excerpt": "\n\n".join(entry["error_excerpt"] for entry in chain_results if entry["error_excerpt"]),
    }


def _extract_failure_excerpt(log_path: Path, *, max_lines: int = 24) -> str:
    if not log_path.exists():
        return "<log file missing>"
    lines = log_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    patterns = ("CosmoComputationError", "Traceback", "ERROR", "Error", "exception", "condition", "Segmentation fault", "signal 11")
    selected = [line for line in lines if any(pattern in line for pattern in patterns)]
    if not selected:
        selected = lines[-max_lines:]
    return "\n".join(selected[-max_lines:])


def _sampled_parameters(params: dict[str, Any]) -> list[str]:
    return [name for name, spec in params.items() if isinstance(spec, dict) and "prior" in spec and "value" not in spec]


def _with_map_refs(config: dict[str, Any], bestfit: dict[str, float]) -> dict[str, Any]:
    copied = deepcopy(config)
    for block_name in ("cosmology", "planck_nuisance"):
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


def _mpi_cobaya_command(
    *,
    yaml_path: Path,
    output_prefix: Path,
    package_path: Path,
    chains: int,
    omp_threads: int,
    force: bool,
    resume: bool,
) -> list[str]:
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
        str(package_path),
        "--output",
        str(output_prefix),
    ]
    if resume:
        command.append("--resume")
    elif force:
        command.append("--force")
    command.append(str(yaml_path))
    return command


def _write_manifest(config_path: Path, outdir: Path, summary: dict[str, Any]) -> None:
    artifacts = {
        str(path.relative_to(outdir)): sha256_file(path)
        for path in sorted(outdir.rglob("*"))
        if path.is_file() and path.name != "manifest.json"
    }
    manifest = {
        "schema_version": 1,
        "experiment": "E1",
        "run_id": summary["run_id"],
        "package_version": sbt_cosmo.__version__,
        "datasets": summary["datasets"],
        "seeds": summary["seeds"],
        "determinism": {
            "forward_eval_omp_num_threads": summary["determinism"]["forward_eval_omp_num_threads"],
            "chain_omp_num_threads": summary["determinism"]["chain_omp_num_threads"],
            "chain_bitwise_determinism_claimed": summary["determinism"]["chain_bitwise_determinism_claimed"],
            "coordination": summary["mcmc"]["coordination"],
        },
        "runtime": {
            "generated_unix": int(time.time()),
            "mode": summary["mode"],
        },
        "config_sha256": sha256_file(config_path),
        "class_precision": summary["class_precision"],
        "artifact_checksums_sha256": artifacts,
        "terminal_state": summary["terminal_state"],
    }
    (outdir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8")


def _write_status(outdir: Path, state: str, summary: dict[str, Any]) -> None:
    status = {
        "state": state,
        "run_id": summary["run_id"],
        "combination": summary["combination"],
        "model": summary["model"],
        "terminal_state": summary["terminal_state"],
        "diagnostics": summary["mcmc"]["diagnostics"],
    }
    (outdir / "status.json").write_text(json.dumps(status, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("configs/experiments/E1.yaml"))
    parser.add_argument("--outdir", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--combination", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--run-mode", choices=["production", "validation"], default="production")
    parser.add_argument("--chains", type=int, default=4)
    parser.add_argument("--omp-threads", type=int, default=4)
    parser.add_argument("--rminus1-stop", type=float, default=0.01)
    parser.add_argument("--rminus1-cl-stop", type=float, default=0.2)
    parser.add_argument("--max-samples", type=int, default=40000)
    parser.add_argument("--covmat", type=Path, default=Path("configs/covmats/e1_planck_lcdm.covmat"))
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
        rminus1_stop=args.rminus1_stop,
        rminus1_cl_stop=args.rminus1_cl_stop,
        max_samples=args.max_samples,
        covmat=args.covmat,
        resume=args.resume,
        skip_mcmc=args.skip_mcmc,
    )
    print(json.dumps({"summary": str(args.outdir / "summary.json"), "diagnostics": summary["mcmc"]["diagnostics"]}, indent=2))


if __name__ == "__main__":
    main()
