#!/usr/bin/env python3
"""Additional constructions; frozen experiments and the paper are untouched.

The equality-ledger allocation is a new carrier. Its nonlinear background
term reproduces Step26's coefficient, not Step26's entire update law. The
prior obstruction is exact arithmetic on the frozen decimal samples, not an
interval certificate for the upstream growth ODE.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import platform

import numpy as np
import scipy
from scipy.optimize import brentq

import de_dual_carrier as dual
import de_projected_sourcing as projected

ROOT = Path(__file__).resolve().parents[1]
OUTDIR = ROOT / "results/restoration_2026-10-01"


def exact_prior_obstruction(rows: list[dict[str, str]], mode: str = "none") -> dict:
    """Sharp mixture bound with the original full-support maximum retained."""
    if mode not in {"none", "N_rec", "f_coll"}:
        raise ValueError("unknown within-seed weighting")
    groups = {}
    seen = set()
    for row in rows:
        key = (Fraction(row["lambda"]), int(row["seed"]))
        if key in seen:
            raise ValueError("duplicate lambda/seed")
        seen.add(key)
        groups.setdefault(key[0], []).append(row)
    retained = []
    for lam, group in sorted(groups.items()):
        admitted = [r for r in group if r["RS"] == "True"]
        if not lam or Fraction(len(admitted), len(group)) < Fraction(4, 5):
            continue
        samples = []
        for row in admitted:
            ratio = Fraction(row["lambda_to_matter_at_first_record"])
            weight = (Fraction(1) if mode == "none" else
                      Fraction(row["N_rec_distinguishable"] if mode == "N_rec" else row["f_coll"]))
            if ratio <= 0 or weight <= 0:
                raise ValueError("nonpositive admitted ratio or weight")
            samples.append((ratio, weight))
        retained.append((lam, samples, len(group)))
    if not retained:
        raise ValueError("empty admitted support")
    top = max(ratio for _, samples, _ in retained for ratio, _ in samples)
    counts = []
    for lam, samples, total_seeds in retained:
        numerator = sum((weight for ratio, weight in samples if 10 * ratio >= top), Fraction(0))
        denominator = sum((weight for _, weight in samples), Fraction(0))
        counts.append({"lambda": str(lam), "top_mass": str(numerator),
                       "admitted_mass": str(denominator), "seed_count": total_seeds,
                       "conditional_top_fraction": str(numerator / denominator)})
    best = max(counts, key=lambda r: Fraction(r["conditional_top_fraction"]))
    bound = Fraction(best["conditional_top_fraction"])
    margin = min(abs(10 * ratio - top) for _, samples, _ in retained for ratio, _ in samples)
    return {"mode": mode, "top_R_exact": str(top), "threshold_R_exact": str(top / 10),
            "classification_margin_exact": str(margin), "groups": counts,
            "sharp_upper_bound": str(bound), "upper_bound_float": float(bound),
            "probability_gate_impossible": bound < Fraction(4, 5),
            "scope": "any nonnegative lambda weights for this fixed band; strictly positive priors retain the band"}


def ledger_term(density: np.ndarray, kappa: float) -> np.ndarray:
    return density + 0.5 * kappa * density**2


def density_from_ledger(x: np.ndarray, kappa: float) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    if not np.isfinite(kappa) or kappa < 0 or not np.all(np.isfinite(x)) or np.any(x < 0):
        raise ValueError("nonnegative finite ledger amounts and kappa are required")
    return 2.0 * x / (1.0 + np.sqrt(1.0 + 2.0 * kappa * x))


def allocation_from_price(price: float, background: np.ndarray,
                          weights: np.ndarray, curvatures: np.ndarray) -> np.ndarray:
    d = price - background
    interior = weights > d
    x = np.zeros_like(weights)
    c, w, d = curvatures[interior], weights[interior], d[interior]
    b = c + d
    root = np.hypot(c - d, 2.0 * np.sqrt(c * w))
    pos = b >= 0
    values = np.empty_like(b)
    values[pos] = 2.0 * (w[pos] - d[pos]) / (root[pos] + b[pos])
    values[~pos] = (root[~pos] - b[~pos]) / (2.0 * c[~pos])
    x[interior] = values
    return x


def equality_allocation(budget: float, background: np.ndarray,
                        weights: np.ndarray, curvatures: np.ndarray) -> dict:
    background, weights, curvatures = (np.asarray(a, dtype=float) for a in (background, weights, curvatures))
    if weights.ndim != 1 or not weights.size or background.shape != weights.shape or curvatures.shape != weights.shape:
        raise ValueError("equal nonempty vectors are required")
    if not all(np.all(np.isfinite(a)) for a in (background, weights, curvatures)) or np.any(weights <= 0) or np.any(curvatures <= 0):
        raise ValueError("finite inputs and positive weights/curvatures are required")
    if not np.isfinite(budget) or budget <= 0:
        raise ValueError("the equality budget must be positive and finite")
    lo = float(np.min(background - curvatures * budget) - 1.0)
    hi = float(np.max(background + weights))
    price = float(brentq(lambda p: allocation_from_price(p, background, weights, curvatures).sum() - budget,
                        lo, hi, xtol=1e-13, rtol=1e-13))
    x = allocation_from_price(price, background, weights, curvatures)
    residual = weights / (1 + x) - curvatures * x + background - price
    stationarity = np.where(x > 1e-10, np.abs(residual), np.maximum(residual, 0))
    return {"x": x, "price": price, "kkt_residual": float(max(np.max(stationarity), abs(x.sum() - budget)))}


def project_simplex(vector: np.ndarray, budget: float) -> tuple[np.ndarray, float]:
    """Euclidean projection; water level shifts with a common input offset."""
    vector = np.asarray(vector, dtype=float)
    if vector.ndim != 1 or not vector.size or not np.all(np.isfinite(vector)) or not np.isfinite(budget) or budget <= 0:
        raise ValueError("a finite nonempty vector and positive finite budget are required")
    ordered = np.sort(vector)[::-1]
    levels = (np.cumsum(ordered) - budget) / np.arange(1, vector.size + 1)
    active = np.flatnonzero(ordered > levels)
    level = float(levels[active[-1]])
    return np.maximum(vector - level, 0.0), level


def allocation_history(budget: float, background: np.ndarray, weights: np.ndarray,
                       curvatures: np.ndarray, steps: int = 300) -> tuple[np.ndarray, np.ndarray]:
    """Projected gradient ascent on the equality ledger, in ledger coordinates."""
    # Validate the same optimization problem; the solver result is not used by
    # this iterative method, whose initial allocation is uniform.
    equality_allocation(budget, background, weights, curvatures)
    x = np.full(len(weights), budget / len(weights))
    rate = 1.0 / float(np.max(weights + curvatures))
    states, prices = [x.copy()], []
    for _ in range(steps):
        gradient = weights / (1 + x) - curvatures * x + background
        x, level = project_simplex(x + rate * gradient, budget)
        states.append(x.copy())
        prices.append(level / rate)
    return np.array(states), np.array(prices)


def screened_potential(background: np.ndarray, price: float, kappa: float,
                       density: np.ndarray, gradient_energy: np.ndarray) -> np.ndarray:
    return background + kappa * (gradient_energy + background * density) - price * (1 + kappa * density)


def run_constructions(outdir: Path, check_sibling: bool = False) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    receipt = {"baseline_commit": "2a8a33a", "software": {"python": platform.python_version(),
               "numpy": np.__version__, "scipy": scipy.__version__}, "prior_obstructions": {}}
    paths = [ROOT / "results/DE_measure/record_observables.csv", *sorted((ROOT / "results/DE_measure/robustness").glob('*_record_observables.csv'))]
    for path in paths:
        with path.open(newline="") as f:
            rows = list(csv.DictReader(f))
        result = {mode: exact_prior_obstruction(rows, mode) for mode in ["none", "N_rec", "f_coll"]}
        result["input_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        receipt["prior_obstructions"][str(path.relative_to(ROOT))] = result
    base = receipt["prior_obstructions"]["results/DE_measure/record_observables.csv"]["none"]
    count_pairs = [(Fraction(g["top_mass"]), Fraction(g["admitted_mass"])) for g in base["groups"]]
    # Audit the exact external-data premise of the Lean theorem.
    expected = [(0, 12)] * 40 + [(2, 12), (4, 12), (7, 12), (8, 11)]
    if count_pairs != expected or base["sharp_upper_bound"] != "8/11":
        raise AssertionError("the frozen CSV no longer matches the reified Lean counts")
    receipt["base_count_premise_matches_lean"] = True

    cfg = dual.DualConfig(n_patches=8)
    weights, curvatures = dual.make_patch_params(cfg)
    budget = float(cfg.active_budget_fraction * dual.unconstrained_x(weights, curvatures).sum())
    background = 0.15 * np.sin(0.9 * np.arange(cfg.n_patches))
    kappa = 0.3
    reference = equality_allocation(budget, background, weights, curvatures)
    states, prices = allocation_history(budget, background, weights, curvatures)
    rho = density_from_ledger(reference["x"], kappa)
    gradient = ((np.roll(np.sqrt(rho), -1) - np.roll(np.sqrt(rho), 1)) / 2)**2
    potential = screened_potential(background, reference["price"], kappa, rho, gradient)
    comparisons = []
    for shift in [-8.0, -5.0, -3.0, 0.0, 0.1, 1.0, 10.0]:
        new = equality_allocation(budget, background + shift, weights, curvatures)
        newstates, newprices = allocation_history(budget, background + shift, weights, curvatures)
        newrho = density_from_ledger(new["x"], kappa)
        newgradient = ((np.roll(np.sqrt(newrho), -1) - np.roll(np.sqrt(newrho), 1)) / 2)**2
        newpotential = screened_potential(background + shift, new["price"], kappa, newrho, newgradient)
        comparisons.append({"shift": shift, "price": new["price"], "kkt_residual": new["kkt_residual"],
                            "state_difference": float(np.max(np.abs(newrho - rho))),
                            "price_shift_error": abs(new["price"] - reference["price"] - shift),
                            "history_difference": float(np.max(np.abs(newstates - states))),
                            "history_price_shift_error": float(np.max(np.abs(newprices - prices - shift))),
                            "screened_potential_difference": float(np.max(np.abs(newpotential - potential)))})
    all_errors = [value for row in comparisons for key, value in row.items() if key not in {"shift", "price"}]
    if max(all_errors) > 1e-9:
        raise AssertionError(comparisons)
    free0 = allocation_from_price(0.0, background, weights, curvatures)
    free1 = allocation_from_price(0.0, background + 1, weights, curvatures)
    control = float(np.linalg.norm(density_from_ledger(free1, kappa) - density_from_ledger(free0, kappa)))
    if control <= 0.1:
        raise AssertionError("removing the ledger did not discriminate the construction")
    receipt["gauge_ledger"] = {"scope": "new finite equality-ledger allocation; not unchanged Step26 or continuum gravity",
          "n_patches": cfg.n_patches, "kappa": kappa, "budget": budget,
          "background": background.tolist(), "weights": weights.tolist(), "curvatures": curvatures.tolist(),
          "reference_density": rho.tolist(), "reference_price": reference["price"],
          "ledger_residual": float(abs(ledger_term(rho, kappa).sum() - budget)),
          "iterative_optimizer_error": float(np.max(np.abs(states[-1] - reference["x"]))),
          "unconstrained_control_state_difference": control, "shift_comparisons": comparisons,
          "price_sign": "equality multiplier may have either sign; absolute sign is gauge dependent"}
    receipt["projected_sourcing"] = projected.construction_check()
    if check_sibling:
        path = ROOT.parent / ("six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/"
                              "step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py")
        spec = importlib.util.spec_from_file_location("restoration_step26_source", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        field = projected.initial_field()
        source_potential = background + kappa * module.stress_energy_density(field, background)
        source_force = module.kinetic_operator(8) @ field + source_potential * field
        error = float(np.max(np.abs(source_force - projected.sourcing_force(field, background, kappa))))
        if error > 1e-14:
            raise AssertionError("the local force does not match Step26")
        receipt["step26_local_force_check"] = {"source_path": str(path),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "local_force_difference": error,
            "scope": "source formula at the constructed initial field; update law intentionally differs"}
    files = [Path(__file__).resolve(), ROOT / "scripts/de_dual_carrier.py",
             ROOT / "scripts/de_projected_sourcing.py",
             ROOT / "lean/SbtCosmo/Derivation/GaugeClosure.lean", ROOT / "lean/SbtCosmo/Derivation/PriorObstruction.lean"]
    receipt["source_hashes"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (outdir / "construction_receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=OUTDIR)
    parser.add_argument("--check-sibling", action="store_true")
    args = parser.parse_args()
    result = run_constructions(args.outdir, args.check_sibling)
    print(json.dumps({"base_prior_bound": "8/11", "new_ledger_max_shift_error": max(
        r["screened_potential_difference"] for r in result["gauge_ledger"]["shift_comparisons"])}))
