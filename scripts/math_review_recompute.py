#!/usr/bin/env python3
"""Recompute review receipts from frozen inputs, without rewriting old results.

Run with the repository's sbt-de Python. The optional sibling-source check
executes Step26 in memory only. No paper or external repository is written.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
from pathlib import Path

import numpy as np
import scipy

import de_audit_validate as audit
import de_dual_carrier as dual
import de_measure_probe as measure
import de_measure_validate as measure_validator
import de_window_validate as window
import step54_rederive as step54
import r0_hubble_power_exactness as r0
from de_ground_state_checks import align_ray

ROOT = Path(__file__).resolve().parents[1]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def recompute(outdir: Path, check_sibling: bool) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    receipt = {
        "scope": "finite floating-point recomputation; not an interval certificate",
        "software": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
        "measures": {},
    }
    paths = [ROOT / "results/DE_measure/record_observables.csv"] + sorted(
        (ROOT / "results/DE_measure/robustness").glob("*_record_observables.csv")
    )
    keys = ["collapses", "p_R_within_one_decade_top", "log10R_q05", "log10R_median",
            "log10R_q95", "log10R_width90_decades", "epoch_ratio_median"]
    for path in paths:
        rows = measure_validator.read_csv(path)
        verdicts = measure.evaluate_all_measures(measure.aggregate_measure_inputs(rows, measure.CarrierConfig()))
        rederived = [measure_validator.evaluate_measure(measure_validator.aggregate_inputs(rows), *cls)
                     for cls in measure_validator.MEASURE_CLASSES]
        for left, right in zip(verdicts, rederived):
            if not all(measure_validator.close(left[k], right[k]) for k in keys):
                raise AssertionError((left, right))
        name = "base" if path.parent.name == "DE_measure" else path.name.split("_record")[0]
        measure.write_csv(outdir / f"{name}_measure_verdicts.csv", verdicts)
        receipt["measures"][name] = {"input": str(path.relative_to(ROOT)), "sha256": digest(path),
                                     "validator_match": True, "verdicts": verdicts}

    cfg = dual.DualConfig()
    weights, curvatures = dual.make_patch_params(cfg)
    sweep = dual.dual_sweep(cfg, weights, curvatures)
    measure.write_csv(outdir / "dual_sweep.csv", sweep)
    receipt["dual"] = {"max_kkt_residual": max(r["max_kkt_residual"] for r in sweep),
                       "max_dual_fd_error": max(r["dual_fd_abs_error"] for r in sweep)}
    if receipt["dual"]["max_kkt_residual"] > 1e-8 or receipt["dual"]["max_dual_fd_error"] > 5e-7:
        raise AssertionError(receipt["dual"])

    receipt["window"] = window.derive(ROOT / "results/DE_window")
    receipt["audit"] = audit.derive(ROOT / "results/DE_audit")
    for name, checker, filename in [("window", window, "coincidence_readout.json"),
                                      ("audit", audit, "verdict.json")]:
        claimed = json.loads((ROOT / "results" / ("DE_" + name) / filename).read_text())
        required = set(receipt[name]) - {"b2_null_false_alarm_rate_empirical"}
        if not required <= set(claimed):
            raise AssertionError((name, "missing claimed fields", sorted(required - set(claimed))))
        mismatches = [k for k, value in receipt[name].items() if k in claimed and not checker.close(value, claimed[k])]
        receipt[name + "_additional_derived_fields"] = [k for k in receipt[name] if k not in claimed]
        receipt[name + "_mismatches"] = mismatches
        if mismatches:
            raise AssertionError((name, mismatches))

    bgpath = step54.VENDORED_STEP54 / "background_sweep_step54.csv"
    kpath = step54.VENDORED_STEP54 / "kappa_sweep_step54.csv"
    receipt["step54"] = {"background": step54.derive_background(step54.read_csv(bgpath)),
                         "kappa": step54.derive_kappa(step54.read_csv(kpath)),
                         "background_csv_sha256": digest(bgpath), "kappa_csv_sha256": digest(kpath)}
    routes = r0.load_external_routes()
    covariance, assumptions = r0.build_covariance(routes)
    scores = r0.score_all(routes, covariance)
    r0.add_deltas(scores)
    neff = r0.effective_n(covariance)
    lofo = r0.leave_one_family_out(routes, covariance)
    stress = r0.covariance_stress(routes)
    receipt["r0"] = {"scores": scores, "covariance_assumptions": assumptions,
                     "power_gate": r0.power_gate(routes, scores, neff, lofo, stress)}
    if check_sibling:
        source = (ROOT.parent / "six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/"
                  "step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py")
        spec = importlib.util.spec_from_file_location("review_step26", source)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        psi, background, _ = module.load_initial_field()
        kinetic = module.kinetic_operator(len(psi))
        states, summaries = [], []
        for offset in [0.0, 0.1]:
            _, summary, state = module.run_case("review", psi, background + offset, 0.3, 0.5, kinetic, 60)
            states.append(np.asarray(state["psi_re"]) + 1j * np.asarray(state["psi_im"]))
            summaries.append(summary)
        v0 = background + 0.3 * module.stress_energy_density(psi, background)
        v1 = background + 0.1 + 0.3 * module.stress_energy_density(psi, background + 0.1)
        receipt["step26_source_check"] = {
            "source_sha256": digest(source),
            "potential_increment_range": float(np.ptp(v1 - v0)),
            "phase_aligned_state_difference": float(np.linalg.norm(align_ray(states[1], states[0]) - states[0])),
            "phase_distance_helper": "local corrected align_ray; frozen source has the opposite phase sign",
            "summaries": summaries,
        }
        if not all(s["converged"] for s in summaries) or np.ptp(v1 - v0) <= 0:
            raise AssertionError(receipt["step26_source_check"])
    # Match the tracked text format so byte hashes survive a fresh Git checkout.
    for generated_csv in outdir.glob("*.csv"):
        generated_csv.write_bytes(generated_csv.read_bytes().replace(b"\r\n", b"\n"))
    sources = sorted((ROOT / "lean/SbtCosmo").rglob("*.lean")) + [
        Path(__file__).resolve(), ROOT / "scripts/de_measure_probe.py", ROOT / "scripts/de_measure_validate.py",
        ROOT / "scripts/de_dual_carrier.py", ROOT / "scripts/step54_rederive.py",
        ROOT / "scripts/de_ground_state_checks.py",
        ROOT / "scripts/de_window_carrier.py", ROOT / "scripts/de_window_validate.py",
        ROOT / "scripts/de_audit_validate.py", ROOT / "sbt_cosmo/audits/metrics.py",
        ROOT / "sbt_cosmo/xi/stability.py",
        ROOT / "scripts/r0_hubble_power_exactness.py", ROOT / "results/E4/E4_ROUTE_VALUE_MANIFEST.json",
        ROOT / "lean/lean-toolchain", ROOT / "lean/lake-manifest.json",
    ]
    receipt["source_hashes"] = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    (outdir / "recomputation.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=ROOT / "results/math_review_2026-10-01")
    parser.add_argument("--check-sibling", action="store_true")
    args = parser.parse_args()
    receipt = recompute(args.outdir, args.check_sibling)
    print(json.dumps({"measure_variants": list(receipt["measures"]), "dual": receipt["dual"],
                      "window_match": not receipt["window_mismatches"], "audit_match": not receipt["audit_mismatches"]}))


if __name__ == "__main__":
    main()
