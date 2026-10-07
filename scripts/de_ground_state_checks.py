#!/usr/bin/env python3
"""Native finite-budget reruns and an independent ground-map/Jacobian audit.

Numerical witnesses are approximate, not interval certificates. All-background
existence is proved mathematically in math/GROUND_STATE_PROOFS_2026-10-02.md;
the exact constant-background sector is constructed in Lean.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import numpy as np

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
STEPS = ROOT / "external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps"
SOURCE = STEPS / "step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py"
PIN = "391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd"
OFFSETS = [-8, -5, -3, -2, -1, -.5, -.2, -.1, 0, .1, .2, .5, 1, 2, 3, 5, 8, 10]
KAPPAS = [0, .1, .3, .5, 1, 2, 3, 5, 10, 15, 20, 30]
RESIDUALS = ["final_update_residual", "fixed_point_residual", "final_eigen_residual",
             "potential_sourcing_residual"]


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def import_native():
    require(digest(SOURCE) == PIN, "Step26 pin changed")
    spec = importlib.util.spec_from_file_location("ground_review_step26", SOURCE)
    require(spec is not None and spec.loader is not None, "cannot load pinned source")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def operators(n):
    require(n == 8, "the native matrix bridge is scoped to eight sites")
    kinetic, gradient = np.eye(n), np.zeros((n, n))
    for i in range(n):
        kinetic[i, (i-1) % n] = kinetic[i, (i+1) % n] = -.5
        gradient[i, (i+1) % n], gradient[i, (i-1) % n] = .5, -.5
    return kinetic, gradient


def potential(background, kappa, psi, gradient):
    return background + kappa * (np.abs(gradient @ psi)**2 + background*np.abs(psi)**2)


def align_ray(candidate, reference):
    """Rotate candidate to minimize Euclidean distance to reference.

    With numpy's conjugate-first vdot convention the overlap phase multiplies
    candidate without conjugation. At zero overlap any phase has equal distance.
    """
    overlap = np.vdot(candidate, reference)
    return candidate.copy() if abs(overlap) == 0 else candidate*(overlap/abs(overlap))


def ground_map(kinetic, gradient, background, kappa, psi):
    h = kinetic + np.diag(potential(background, kappa, psi, gradient))
    values, vectors = np.linalg.eigh(h)
    ground = vectors[:, 0]
    ground *= 1 if ground.sum() > 0 else -1
    require(np.all(ground > 0), "positive ground representative lost numerically")
    return ground, values, vectors, h


def solve(kinetic, gradient, background, kappa, initial, cap=6000):
    # Real positive cone: phase alignment is unnecessary. This is a declared
    # solver choice, not the frozen complex initialization or a universal budget.
    psi = np.asarray(initial, dtype=float).copy()
    psi /= np.linalg.norm(psi)
    for iteration in range(cap):
        ground, values, vectors, h = ground_map(kinetic, gradient, background, kappa, psi)
        gap = np.linalg.norm(ground-psi)
        if gap < 5e-13:
            return psi, iteration, float(gap)
        psi = .8*psi + .2*ground
        psi /= np.linalg.norm(psi)
    raise RuntimeError(f"declared continuation failed: kappa={kappa}, gap={gap}")


def jacobians(kinetic, gradient, background, kappa, psi):
    ground, values, vectors, h = ground_map(kinetic, gradient, background, kappa, psi)
    # Unit-sphere tangent in the real slice. Imaginary projective tangent modes
    # have zero first-order sourcing at a real field, hence zero map derivative.
    _, _, vh = np.linalg.svd(psi.reshape(1, -1), full_matrices=True)
    basis = vh[1:].T
    resolvent = (vectors[:, 1:] / (values[1:]-values[0])) @ vectors[:, 1:].T
    source_derivative = 2*kappa*(np.diag(gradient@psi)@gradient + np.diag(background*psi))
    analytic = -basis.T @ resolvent @ np.diag(ground) @ source_derivative @ basis
    finite = np.empty_like(analytic)
    eps = 1e-6
    for i in range(basis.shape[1]):
        plus, minus = psi+eps*basis[:, i], psi-eps*basis[:, i]
        plus /= np.linalg.norm(plus)
        minus /= np.linalg.norm(minus)
        fp = ground_map(kinetic, gradient, background, kappa, plus)[0]
        fm = ground_map(kinetic, gradient, background, kappa, minus)[0]
        finite[:, i] = basis.T @ (fp-fm)/(2*eps)
    error = float(np.max(np.abs(analytic-finite)))
    require(error < 2e-7, f"analytic/FD Jacobian discrepancy {error}")
    eigenvalues = np.linalg.eigvals(analytic)
    complex_projective_eigenvalues = np.concatenate((eigenvalues, np.zeros(7)))
    leading = complex_projective_eigenvalues[np.argmax(np.abs(complex_projective_eigenvalues))]
    eigen_residual = np.linalg.norm(h@psi-values[0]*psi)
    return {
        "analytic_fd_max_error": error, "map_residual": float(np.linalg.norm(ground-psi)),
        "eigen_residual": float(eigen_residual), "spectral_gap": float(values[1]-values[0]),
        "raw_map_radius": float(abs(leading)), "leading_real": float(leading.real),
        "leading_imag": float(leading.imag),
        "raw_map_stable_diagnostic": bool(abs(leading) < 1-1e-6),
        "relaxed_radius_mix_0_2": float(np.max(np.abs(.8+.2*complex_projective_eigenvalues))),
        "relaxed_radius_mix_0_5": float(np.max(np.abs(.5+.5*complex_projective_eigenvalues))),
        "psi": psi.tolist(),
    }


def recompute():
    native = import_native()
    frozen, background, _ = native.load_initial_field()
    kinetic, gradient = operators(len(frozen))
    require(np.array_equal(kinetic, native.kinetic_operator(8)), "kinetic bridge")
    rng = np.random.default_rng(261026)
    bridge_errors = []
    for _ in range(24):
        psi = rng.normal(size=8)+1j*rng.normal(size=8)
        psi /= np.linalg.norm(psi)
        bridge_errors.append(float(np.max(np.abs(gradient@psi-native.periodic_gradient(psi)))))
        for kappa in (-3., .3, 30.):
            bridge_errors.append(float(np.max(np.abs(
                potential(background, kappa, psi, gradient)-
                (background+kappa*native.stress_energy_density(psi, background))))))
    require(max(bridge_errors) < 1e-13, "independent native potential bridge")

    legacy = []
    for iterations in (60, 120):
        for offset in OFFSETS:
            _, summary, _ = native.run_case("review", frozen, background+offset, .3, .5,
                                            kinetic, iterations)
            legacy.append({"sweep": "background", "parameter": offset, "iterations": iterations,
                           "converged": bool(summary["converged"]),
                           **{name: summary[name] for name in RESIDUALS}})
    for kappa in KAPPAS:
        _, summary, _ = native.run_case("review", frozen, background, kappa, .5, kinetic, 60)
        legacy.append({"sweep": "kappa", "parameter": kappa, "iterations": 60,
                       "converged": bool(summary["converged"]),
                       **{name: summary[name] for name in RESIDUALS}})
    legacy60 = [r for r in legacy if r["sweep"] == "background" and r["iterations"] == 60]
    legacy120 = [r for r in legacy if r["sweep"] == "background" and r["iterations"] == 120]
    require([r["parameter"] for r in legacy60 if not r["converged"]] == [-5, -3, 10], "legacy 60")
    require(all(r["converged"] for r in legacy120), "legacy 120")

    uniform = np.ones(8)/np.sqrt(8)
    continuation = []
    for sweep, params in (("background", OFFSETS), ("kappa", KAPPAS)):
        psi = uniform.copy()
        for parameter in params:
            b = background+parameter if sweep == "background" else background
            k = .3 if sweep == "background" else parameter
            psi, iterations, gap = solve(kinetic, gradient, b, k, psi)
            row = jacobians(kinetic, gradient, b, k, psi)
            require(row["eigen_residual"] < 1e-10, "continuation eigen residual")
            continuation.append({"sweep": sweep, "parameter": parameter, "kappa": k,
                                 "iterations": iterations, **row})

    # The source uses vdot(candidate, reference), but multiplies by the
    # conjugate phase. An identical ray with reference i*uniform gets -i*uniform.
    aligned = native.phase_align(uniform.astype(complex), 1j*uniform)
    wrong_gap = float(np.linalg.norm(aligned-1j*uniform))
    require(abs(wrong_gap-2) < 1e-14, "phase-sign counterexample")
    corrected = align_ray(uniform.astype(complex), 1j*uniform)
    require(np.linalg.norm(corrected-1j*uniform) < 1e-14, "corrected phase control")
    phase_counterexample = {
        "same_ray": True, "native_aligned_gap": wrong_gap,
        "corrected_aligned_gap": float(np.linalg.norm(corrected-1j*uniform)),
        "candidate": "uniform", "reference": "i*uniform",
        "wrong_source_multiplier": "exp(-i arg(vdot(candidate,reference)))",
        "correct_multiplier": "vdot(candidate,reference)/abs(vdot(candidate,reference))",
        "pinned_source_edited": False,
    }

    # Ground/eigen control exercises the actual matrix, not only diagonal data.
    uniform_controls = []
    for b in (-20., 0., 20.):
        for k in (-30., 0., .3, 30.):
            _, values, _, h = ground_map(kinetic, gradient, np.full(8, b), k, uniform)
            expected = b+k*b/8
            residual = float(np.linalg.norm(h@uniform-expected*uniform))
            require(residual < 1e-13 and abs(values[0]-expected) < 1e-12, "constant sector bridge")
            uniform_controls.append({"background": b, "kappa": k, "eigen_residual": residual})
    return {
        "scope": "finite floating reruns and derivative diagnostics; written Brouwer proof is separate",
        "source_sha256": {str(SOURCE.relative_to(ROOT)): digest(SOURCE)},
        "numpy_version": np.__version__, "native_bridge_max_error": max(bridge_errors),
        "legacy": legacy, "continuation": continuation, "uniform_controls": uniform_controls,
        "phase_sign_counterexample": phase_counterexample,
        "summary": {
            "background_60_passes": sum(r["converged"] for r in legacy60),
            "background_120_passes": sum(r["converged"] for r in legacy120),
            "approximate_ground_points": len(continuation),
            "background_raw_map_unstable_offsets": [r["parameter"] for r in continuation
                if r["sweep"] == "background" and not r["raw_map_stable_diagnostic"]],
            "kappa_raw_map_unstable_samples": [r["parameter"] for r in continuation
                if r["sweep"] == "kappa" and not r["raw_map_stable_diagnostic"]],
            "max_analytic_fd_error": max(r["analytic_fd_max_error"] for r in continuation),
            "interval_certified": False,
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=ROOT / "results/ground_state_2026-10-02")
    args = parser.parse_args()
    receipt = recompute()
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir/"receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps(receipt["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
