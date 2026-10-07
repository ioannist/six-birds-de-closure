"""Aggregate E1 standard-run summaries and evaluate reproduction gates."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np
import yaml

from sbt_cosmo.inference.convergence import load_cobaya_chain
from sbt_cosmo.inference.evidence import delta_chi2_to_sigma

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_REFERENCE_PATH = ROOT / "configs" / "references" / "desi_dr2_published.yaml"
REQUIRED_COMBINATIONS = ("C1", "C2", "C3", "C4", "C5")
REQUIRED_MODELS = ("lcdm", "wcdm", "w0wa")
TRACK_RUN_GLOBS = {"full": "E1A_*", "compressed": "E1C_*"}
W0_ALIASES = ("w0_fld", "w0")
WA_ALIASES = ("wa_fld", "wa")


def aggregate_campaign(
    run_root: Path,
    output: Path,
    reference_path: Path = DEFAULT_REFERENCE_PATH,
    *,
    run_glob: str = TRACK_RUN_GLOBS["full"],
    track: str = "full",
    prefer_dynesty: bool = False,
) -> dict[str, Any]:
    """Aggregate completed per-run summaries into a full E1-A gate summary."""
    runs = _load_run_summaries(run_root, run_glob)
    table = _best_runs_by_combo_model(runs, prefer_dynesty=prefer_dynesty)
    significances = _significance_table(table)
    evidence = _evidence_table(table)
    reference = _load_reference(reference_path)
    gates = _evaluate_gates(table, significances, reference, evidence)
    summary = {
        "schema_version": 1,
        "experiment": "E1",
        "run_id": output.parent.name,
        "track": track,
        "run_glob": run_glob,
        "prefer_dynesty": prefer_dynesty,
        "terminal_state": "PASS" if all(gate["pass"] is True for gate in gates.values()) else "BLOCKED",
        "reference": {
            "path": str(reference_path),
            "aor_status": reference.get("aor_status"),
            "schema_version": reference.get("schema_version"),
        },
        "runs": table,
        "significances": significances,
        "evidence": evidence,
        "gates": gates,
        "scope": _scope_for_track(track),
    }
    if track == "compressed":
        summary["aor_status"] = "budgeted"
        summary["caveat"] = (
            "Compressed-CMB track substitutes Planck distance priors for the full Planck clik/C_l likelihood; "
            "tight reproduction gates should be interpreted with that sanctioned budgeted substitution."
        )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    return summary


def _load_run_summaries(run_root: Path, run_glob: str = TRACK_RUN_GLOBS["full"]) -> list[dict[str, Any]]:
    summaries: list[dict[str, Any]] = []
    for path in sorted(run_root.glob(f"{run_glob}/summary.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("mode") != "production":
            continue
        summaries.append(data)
    return summaries


def _scope_for_track(track: str) -> str:
    if track == "compressed":
        return "Compressed-CMB E1 reproduction aggregate from completed production summaries"
    return "Full E1-A reproduction aggregate from completed long-run summaries"


def _best_runs_by_combo_model(summaries: list[dict[str, Any]], *, prefer_dynesty: bool = False) -> dict[str, Any]:
    table: dict[str, Any] = {}
    for summary in summaries:
        combo = summary["combination"]
        model = summary["model"]
        mcmc = summary.get("mcmc", {})
        diagnostics = mcmc.get("diagnostics", {})
        entry = {
            "run_id": summary["run_id"],
            "sampler": summary.get("sampler", mcmc.get("sampler", "mcmc")),
            "chi2": summary.get("minimize", {}).get("chi2"),
            "bestfit": summary.get("minimize", {}).get("bestfit", {}),
            "diagnostics": diagnostics,
            "determinism": summary.get("determinism", {}),
            "chain_files": mcmc.get("chain_files", []),
            "logZ": summary.get("logZ", diagnostics.get("logZ")),
            "logZ_err": summary.get("logZ_err", diagnostics.get("logZ_err")),
        }
        current = table.get(combo, {}).get(model)
        if _prefer_run_entry(entry, current, prefer_dynesty=prefer_dynesty):
            table.setdefault(combo, {})[model] = entry
    return table


def _prefer_run_entry(entry: dict[str, Any], current: dict[str, Any] | None, *, prefer_dynesty: bool) -> bool:
    if current is None:
        return True
    if prefer_dynesty:
        entry_is_dynesty = entry.get("sampler") == "dynesty"
        current_is_dynesty = current.get("sampler") == "dynesty"
        if entry_is_dynesty != current_is_dynesty:
            return entry_is_dynesty
    return entry["chi2"] is not None and entry["chi2"] < current.get("chi2", float("inf"))


def _significance_table(table: dict[str, Any]) -> dict[str, Any]:
    results: dict[str, Any] = {}
    for combo in ("C2", "C3", "C4", "C5"):
        lcdm = table.get(combo, {}).get("lcdm", {})
        w0wa = table.get(combo, {}).get("w0wa", {})
        if lcdm.get("chi2") is None or w0wa.get("chi2") is None:
            results[combo] = {"status": "missing_inputs"}
            continue
        results[combo] = {
            "status": "computed",
            **delta_chi2_to_sigma(float(lcdm["chi2"]) - float(w0wa["chi2"]), delta_k=2),
        }
    return results


def _evidence_table(table: dict[str, Any]) -> dict[str, Any]:
    evidence: dict[str, Any] = {}
    for combo in ("C2", "C3", "C4", "C5"):
        lcdm = table.get(combo, {}).get("lcdm", {})
        w0wa = table.get(combo, {}).get("w0wa", {})
        lcdm_logz = lcdm.get("logZ")
        w0wa_logz = w0wa.get("logZ")
        if lcdm_logz is None or w0wa_logz is None:
            evidence[combo] = {"status": "missing_inputs"}
            continue
        evidence[combo] = {
            "status": "computed",
            "lnZ_lcdm": float(lcdm_logz),
            "lnZ_w0wa": float(w0wa_logz),
            "lnB_w0wa_minus_lcdm": float(w0wa_logz) - float(lcdm_logz),
            "lnZ_err_lcdm": lcdm.get("logZ_err"),
            "lnZ_err_w0wa": w0wa.get("logZ_err"),
        }
    return evidence


def _load_reference(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"E1 published reference table not found: {path}")
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or "references" not in data:
        raise ValueError(f"invalid E1 published reference table: {path}")
    return data


def _evaluate_gates(
    table: dict[str, Any],
    significances: dict[str, Any],
    reference: dict[str, Any],
    evidence: dict[str, Any],
) -> dict[str, Any]:
    missing = _missing_runs(table)
    c1_lcdm = table.get("C1", {}).get("lcdm", {})
    h0 = c1_lcdm.get("bestfit", {}).get("H0")
    c1_ref = _reference_for(reference, "C1")
    h0_ref = c1_ref.get("H0_mean", 67.4)
    h0_sigma = c1_ref.get("H0_sigma", 0.5)
    conv_ok = _convergence_ok(table)
    quad_values = {
        combo: table.get(combo, {}).get("w0wa", {}).get("bestfit", {})
        for combo in ("C2", "C3", "C4", "C5")
    }
    quad_pass = all(
        "w0_fld" in value and "wa_fld" in value and float(value["w0_fld"]) > -1.0 and float(value["wa_fld"]) < 0.0
        for value in quad_values.values()
    )
    gates = {
        "G-E1-REPRO-QUAD": {
            "pass": bool(quad_pass),
            "value": quad_values,
            "status": "computed" if all(value for value in quad_values.values()) else "missing_inputs",
        },
        "G-E1-REPRO-CONTOUR": {
            **_contour_gate(table, reference),
        },
        "G-E1-REPRO-CMBONLY": {
            "pass": bool(h0 is not None and abs(float(h0) - float(h0_ref)) <= float(h0_sigma)),
            "value": {
                "H0": h0,
                "published_H0_mean": h0_ref,
                "published_H0_sigma": h0_sigma,
                "delta": None if h0 is None else float(h0) - float(h0_ref),
                "citation": c1_ref.get("citations", {}).get("H0_mean"),
            },
            "status": "computed" if h0 is not None else "missing_inputs",
        },
        "G-E1-REPRO-SIG-BAOCMB": {
            **_sig_baocmb_gate(significances, reference, evidence),
        },
        "G-E1-REPRO-SIG-SN": {
            **_sig_sn_gate(significances, reference, evidence),
        },
        "G-E1-REPRO-CONV": {
            "pass": conv_ok,
            "status": "computed" if not missing else "missing_inputs",
        },
        "G-E1-REPRO-CHI2": {
            **_chi2_gate(table, reference),
        },
        "G-E1-REPRO-PD": {
            "pass": None,
            "status": "delegated_to_data_integrity_report",
        },
        "G-E1-REPRO-DET": {
            "pass": all(
                entry.get("determinism", {}).get("pass") is True
                for combo_models in table.values()
                for entry in combo_models.values()
            ),
            "status": "computed" if table else "missing_inputs",
        },
        "G-E1-REPRO-BACKEND": {
            "pass": None,
            "status": "requires_camb_control_runs",
        },
        "G-E1-REPRO-NO-SBT": {
            "pass": True,
            "status": "lint_enforced_by_tests",
        },
        "G-E1-REPRO-AOR": {
            "pass": not missing,
            "missing": missing,
            "status": "computed" if not missing else "missing_inputs",
        },
    }
    return gates


def _reference_for(reference: dict[str, Any], combo: str) -> dict[str, Any]:
    entry = reference.get("references", {}).get(combo, {})
    return entry if isinstance(entry, dict) else {}


def _contour_gate(table: dict[str, Any], reference: dict[str, Any]) -> dict[str, Any]:
    comparisons: dict[str, Any] = {}
    missing: list[str] = []
    passed: list[bool] = []
    for combo in ("C2", "C3", "C4", "C5"):
        ref = _reference_for(reference, combo)
        entry = table.get(combo, {}).get("w0wa")
        if not ref or entry is None:
            missing.append(combo)
            continue
        stats = _w0wa_stats(entry)
        if stats is None:
            missing.append(combo)
            comparisons[combo] = {"status": "missing_chain_statistics"}
            continue
        combo_result: dict[str, Any] = {"status": "computed", "parameters": {}}
        combo_pass = True
        for logical_name, published_name in (("w0", "w0"), ("wa", "wa")):
            published_mean = float(ref[f"{published_name}_mean"])
            published_sigma = float(ref[f"{published_name}_sigma"])
            recovered = stats[logical_name]
            mean_delta_fraction = _relative_delta(float(recovered["mean"]), published_mean)
            sigma_delta_fraction = _relative_delta(float(recovered["sigma"]), published_sigma)
            param_pass = mean_delta_fraction <= 0.05 and sigma_delta_fraction <= 0.15
            combo_pass = combo_pass and param_pass
            combo_result["parameters"][logical_name] = {
                "recovered_mean": float(recovered["mean"]),
                "published_mean": published_mean,
                "mean_delta_fraction": mean_delta_fraction,
                "mean_tolerance_fraction": 0.05,
                "recovered_sigma": float(recovered["sigma"]),
                "published_sigma": published_sigma,
                "sigma_delta_fraction": sigma_delta_fraction,
                "sigma_tolerance_fraction": 0.15,
                "pass": bool(param_pass),
                "stat_source": recovered.get("source"),
                "mean_citation": ref.get("citations", {}).get(f"{published_name}_mean"),
                "sigma_citation": ref.get("citations", {}).get(f"{published_name}_sigma"),
            }
        comparisons[combo] = combo_result
        passed.append(bool(combo_pass))
    return {
        "pass": bool(len(passed) == 4 and all(passed)),
        "value": comparisons,
        "missing": missing,
        "status": "computed" if not missing else "missing_inputs",
    }


def _chi2_gate(table: dict[str, Any], reference: dict[str, Any]) -> dict[str, Any]:
    comparisons: dict[str, Any] = {}
    compared = 0
    failed = False
    for combo in ("C2", "C3", "C4", "C5"):
        ref = _reference_for(reference, combo)
        ref_chi2 = ref.get("chi2")
        if ref_chi2 is None:
            comparisons[combo] = {
                "status": "reference_unavailable",
                "note": ref.get("chi2_note", "published total chi2 unavailable"),
                "delta_chi2_map": ref.get("delta_chi2_map"),
                "sigma_dynamical_de": ref.get("sigma_dynamical_de"),
                "citation": ref.get("citations", {}).get("chi2"),
            }
            continue
        compared += 1
        entry = table.get(combo, {}).get("w0wa", {})
        recovered_chi2 = entry.get("chi2")
        if recovered_chi2 is None:
            comparisons[combo] = {"status": "missing_inputs", "published_chi2": ref_chi2}
            failed = True
            continue
        delta_fraction = _relative_delta(float(recovered_chi2), float(ref_chi2))
        pass_combo = delta_fraction <= 0.05
        failed = failed or not pass_combo
        comparisons[combo] = {
            "status": "computed",
            "recovered_chi2": float(recovered_chi2),
            "published_chi2": float(ref_chi2),
            "delta_fraction": delta_fraction,
            "tolerance_fraction": 0.05,
            "pass": bool(pass_combo),
            "citation": ref.get("citations", {}).get("chi2"),
        }
    if compared == 0:
        return {"pass": True, "value": comparisons, "status": "reference_unavailable"}
    return {"pass": not failed, "value": comparisons, "status": "computed"}


def _sig_baocmb_gate(significances: dict[str, Any], reference: dict[str, Any], evidence: dict[str, Any]) -> dict[str, Any]:
    combo = "C2"
    ref = _reference_for(reference, combo)
    computed = significances.get(combo, {})
    evidence_entry = evidence.get(combo, {})
    sigma = computed.get("sigma")
    published_sigma = ref.get("sigma_dynamical_de")
    status = computed.get("status", "missing_inputs")
    value = {
        "computed": computed,
        "evidence": evidence_entry,
        "published_sigma": published_sigma,
        "tolerance_sigma": 0.4,
        "citation": ref.get("citations", {}).get("sigma_dynamical_de"),
    }
    if sigma is None or published_sigma is None:
        return {"pass": False, "value": value, "status": status if sigma is None else "missing_reference"}
    delta = abs(float(sigma) - float(published_sigma))
    value["delta_sigma"] = delta
    ln_b = evidence_entry.get("lnB_w0wa_minus_lcdm")
    ln_b_ok = None if ln_b is None else float(ln_b) > 0.0
    value["lnB_positive"] = ln_b_ok
    pass_gate = delta <= 0.4 and (ln_b_ok is not False)
    return {"pass": bool(pass_gate), "value": value, "status": "computed"}


def _sig_sn_gate(significances: dict[str, Any], reference: dict[str, Any], evidence: dict[str, Any]) -> dict[str, Any]:
    comparisons: dict[str, Any] = {}
    recovered: list[float] = []
    missing: list[str] = []
    ln_b_values: list[float] = []
    for combo in ("C3", "C4", "C5"):
        ref = _reference_for(reference, combo)
        computed = significances.get(combo, {})
        evidence_entry = evidence.get(combo, {})
        sigma = computed.get("sigma")
        published_sigma = ref.get("sigma_dynamical_de")
        if sigma is None or published_sigma is None:
            missing.append(combo)
            comparisons[combo] = {
                "status": computed.get("status", "missing_inputs"),
                "computed": computed,
                "published_sigma": published_sigma,
                "evidence": evidence_entry,
            }
            continue
        sigma_value = float(sigma)
        ln_b = evidence_entry.get("lnB_w0wa_minus_lcdm")
        if ln_b is not None:
            ln_b_values.append(float(ln_b))
        recovered.append(sigma_value)
        comparisons[combo] = {
            "status": "computed",
            "computed_sigma": sigma_value,
            "published_sigma": float(published_sigma),
            "delta_sigma": sigma_value - float(published_sigma),
            "published_band": [2.8, 4.2],
            "hard_fail_band": [2.5, 4.5],
            "inside_published_band": 2.8 <= sigma_value <= 4.2,
            "inside_hard_fail_band": 2.5 <= sigma_value <= 4.5,
            "evidence": evidence_entry,
            "lnB_positive": None if ln_b is None else float(ln_b) > 0.0,
            "citation": ref.get("citations", {}).get("sigma_dynamical_de"),
        }
    spread = max(recovered) - min(recovered) if recovered else None
    spread_collapse_minimum = 0.5
    spread_ok = spread is not None and spread >= spread_collapse_minimum
    pass_gate = (
        len(recovered) == 3
        and all(item["inside_published_band"] for item in comparisons.values() if item.get("status") == "computed")
        and all(item.get("lnB_positive") is not False for item in comparisons.values() if item.get("status") == "computed")
        and spread_ok
    )
    return {
        "pass": bool(pass_gate),
        "value": {
            "comparisons": comparisons,
            "recovered_sigmas": recovered,
            "recovered_spread": spread,
            "spread_collapse_minimum": spread_collapse_minimum,
            "spread_ok": spread_ok,
            "lnB_values": ln_b_values,
        },
        "missing": missing,
        "status": "computed" if not missing else "missing_inputs",
    }


def _w0wa_stats(entry: dict[str, Any]) -> dict[str, Any] | None:
    diagnostics = entry.get("diagnostics", {})
    parameter_stats = diagnostics.get("parameter_stats") or diagnostics.get("posterior_stats") or entry.get("summary_stats")
    if isinstance(parameter_stats, dict):
        from_summary = {
            "w0": _stat_from_summary(parameter_stats, W0_ALIASES),
            "wa": _stat_from_summary(parameter_stats, WA_ALIASES),
        }
        if from_summary["w0"] is not None and from_summary["wa"] is not None:
            return {
                "w0": {**from_summary["w0"], "source": "summary_parameter_stats"},
                "wa": {**from_summary["wa"], "source": "summary_parameter_stats"},
            }

    chain_files = _existing_chain_paths(entry.get("chain_files", []))
    if not chain_files:
        return None
    frame = load_cobaya_chain(chain_files)
    w0_col = _first_existing_column(frame.columns, W0_ALIASES)
    wa_col = _first_existing_column(frame.columns, WA_ALIASES)
    if w0_col is None or wa_col is None:
        return None
    return {
        "w0": {**_weighted_mean_sigma(frame, w0_col), "source": "chain_files", "column": w0_col},
        "wa": {**_weighted_mean_sigma(frame, wa_col), "source": "chain_files", "column": wa_col},
    }


def _stat_from_summary(parameter_stats: dict[str, Any], aliases: tuple[str, ...]) -> dict[str, float] | None:
    for alias in aliases:
        stat = parameter_stats.get(alias)
        if not isinstance(stat, dict):
            continue
        mean = stat.get("mean")
        sigma = stat.get("sigma", stat.get("std", stat.get("sd")))
        if mean is not None and sigma is not None:
            return {"mean": float(mean), "sigma": float(sigma)}
    return None


def _existing_chain_paths(chain_files: list[str]) -> list[Path]:
    paths: list[Path] = []
    for item in chain_files:
        path = Path(item)
        if not path.is_absolute():
            path = ROOT / path
        if path.exists():
            paths.append(path)
    return paths


def _first_existing_column(columns: Any, aliases: tuple[str, ...]) -> str | None:
    names = set(columns)
    for alias in aliases:
        if alias in names:
            return alias
    return None


def _weighted_mean_sigma(frame: Any, column: str) -> dict[str, float]:
    values = frame[column].to_numpy(dtype=np.float64)
    if "weight" in frame:
        weights = frame["weight"].to_numpy(dtype=np.float64)
    else:
        weights = np.ones_like(values)
    weight_sum = float(np.sum(weights))
    if weight_sum <= 0.0:
        raise ValueError(f"non-positive total chain weight for {column}")
    mean = float(np.sum(weights * values) / weight_sum)
    variance = float(np.sum(weights * (values - mean) ** 2) / weight_sum)
    return {"mean": mean, "sigma": math.sqrt(max(variance, 0.0))}


def _relative_delta(recovered: float, published: float) -> float:
    return abs(recovered - published) / max(abs(published), 1.0e-12)


def _missing_runs(table: dict[str, Any]) -> list[str]:
    missing: list[str] = []
    for combo in REQUIRED_COMBINATIONS:
        for model in REQUIRED_MODELS:
            if model not in table.get(combo, {}):
                missing.append(f"{combo}:{model}")
    return missing


def _convergence_ok(table: dict[str, Any]) -> bool:
    for combo_models in table.values():
        for entry in combo_models.values():
            diagnostics = entry.get("diagnostics", {})
            if entry.get("sampler") == "dynesty":
                logz_err = diagnostics.get("logZ_err", entry.get("logZ_err"))
                converged = diagnostics.get("converged")
                if converged is True or (logz_err is not None and float(logz_err) < 0.3):
                    continue
                return False
            rhat = diagnostics.get("max_rhat_minus_one")
            ess = diagnostics.get("min_ess")
            if rhat is None or ess is None or float(rhat) >= 0.01 or float(ess) <= 400.0:
                return False
    return bool(table)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-root", type=Path, default=Path("runs/E1"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--reference", type=Path, default=DEFAULT_REFERENCE_PATH)
    parser.add_argument("--track", choices=tuple(TRACK_RUN_GLOBS), default="full")
    parser.add_argument("--run-glob", default=None)
    parser.add_argument("--prefer-dynesty", action="store_true")
    args = parser.parse_args()
    run_glob = args.run_glob or TRACK_RUN_GLOBS[args.track]
    output = args.output or _default_output_for_track(args.track)
    summary = aggregate_campaign(
        args.run_root,
        output,
        args.reference,
        run_glob=run_glob,
        track=args.track,
        prefer_dynesty=args.prefer_dynesty,
    )
    print(
        json.dumps(
            {
                "output": str(output),
                "track": summary["track"],
                "run_glob": summary["run_glob"],
                "prefer_dynesty": summary["prefer_dynesty"],
                "terminal_state": summary["terminal_state"],
            },
            indent=2,
        )
    )


def _default_output_for_track(track: str) -> Path:
    if track == "compressed":
        return Path("runs/E1/E1C_full/summary.json")
    return Path("runs/E1/E1A_full/summary.json")


if __name__ == "__main__":
    main()
