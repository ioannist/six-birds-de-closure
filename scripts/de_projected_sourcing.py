#!/usr/bin/env python3
"""Original Step26 local force with an additional global density ledger.

The new constraint preserves norm and inverse participation ratio. Projection
changes the update law; this is explicitly an extension, not a replay of the
original lowest-eigenvector iteration. No convergence theorem is asserted.
"""
from __future__ import annotations

from fractions import Fraction
import numpy as np
from scipy.integrate import solve_ivp


def initial_field() -> np.ndarray:
    densities = np.arange(1, 9, dtype=float) / 36
    return np.sqrt(densities) * np.exp(0.17j * np.arange(8))


def kinetic_operator(n: int) -> np.ndarray:
    lap = np.diag(np.full(n, 2.0))
    for i in range(n):
        lap[i, (i - 1) % n] = -1
        lap[i, (i + 1) % n] = -1
    return 0.5 * lap


def realify(psi: np.ndarray) -> np.ndarray:
    return np.concatenate([psi.real, psi.imag])


def sourcing_force(psi: np.ndarray, background: np.ndarray, kappa: float) -> np.ndarray:
    rho = np.abs(psi)**2
    grad = (np.roll(psi, -1) - np.roll(psi, 1)) / 2
    potential = background + kappa * (np.abs(grad)**2 + background * rho)
    return kinetic_operator(len(psi)) @ psi + potential * psi


def projected_force(psi: np.ndarray, background: np.ndarray, kappa: float) -> tuple[np.ndarray, dict]:
    if psi.ndim != 1 or not psi.size or background.shape != psi.shape:
        raise ValueError("matching nonempty field/background vectors are required")
    if not np.all(np.isfinite(psi)) or not np.all(np.isfinite(background)) or not np.isfinite(kappa) or kappa <= 0:
        raise ValueError("finite inputs and positive kappa are required")
    rho = np.abs(psi)**2
    force = sourcing_force(psi, background, kappa)
    # Both gradients are retained: norm² and sum rho². Their span is also
    # that of norm² and Q_kappa = norm² + kappa/2 * sum rho².
    normals = np.column_stack([realify(psi), realify(rho * psi)])
    gram = normals.T @ normals
    eigenvalues = np.linalg.eigvalsh(gram)
    if eigenvalues[0] <= 0:
        raise ValueError("singular constraint normals")
    coeff = np.linalg.solve(gram, normals.T @ realify(force))
    tangent = realify(force) - normals @ coeff
    price = float(coeff[1] / kappa)
    norm_price = float(coeff[0] - price)
    return tangent, {"ledger_price": price, "norm_price": norm_price,
                     "gram_min_eigenvalue": float(eigenvalues[0]),
                     "normal_residual": float(np.linalg.norm(normals.T @ tangent))}


def evolve(background: np.ndarray, kappa: float = 0.3, tmax: float = 20.0) -> dict:
    psi0 = initial_field()
    if background.shape != psi0.shape or not np.isfinite(tmax) or tmax <= 0:
        raise ValueError("eight background sites and positive finite time are required")
    def rhs(_time, state):
        psi = state[:8] + 1j * state[8:]
        tangent, _ = projected_force(psi, background, kappa)
        return -tangent
    solution = solve_ivp(rhs, (0, tmax), realify(psi0), t_eval=np.linspace(0, tmax, 201),
                         rtol=1e-10, atol=1e-12)
    if not solution.success:
        raise RuntimeError(solution.message)
    fields = solution.y[:8].T + 1j * solution.y[8:].T
    audits = [projected_force(field, background, kappa) for field in fields]
    return {"fields": fields, "ledger_prices": np.array([r[1]["ledger_price"] for r in audits]),
            "norm_prices": np.array([r[1]["norm_price"] for r in audits]),
            "norm2": np.sum(np.abs(fields)**2, axis=1),
            "ipr": np.sum(np.abs(fields)**4, axis=1),
            "min_gram_eigenvalue": min(r[1]["gram_min_eigenvalue"] for r in audits),
            "max_normal_residual": max(r[1]["normal_residual"] for r in audits),
            "final_tangent_force": float(np.linalg.norm(audits[-1][0]))}


def construction_check() -> dict:
    background = 0.15 * np.sin(0.9 * np.arange(8))
    reference = evolve(background)
    comparisons = []
    for shift in [-8.0, 0.1, 10.0]:
        other = evolve(background + shift)
        comparisons.append({"shift": shift,
           "field_history_difference": float(np.max(np.abs(other["fields"] - reference["fields"]))),
           "ledger_price_shift_error": float(np.max(np.abs(other["ledger_prices"] - reference["ledger_prices"] - shift))),
           "norm_price_difference": float(np.max(np.abs(other["norm_prices"] - reference["norm_prices"]))),
           "norm2_drift": float(np.max(np.abs(other["norm2"] - 1))),
           "ipr_drift": float(np.max(np.abs(other["ipr"] - 17/108)))})
    max_error = max(v for r in comparisons for k, v in r.items() if k != "shift")
    if max_error > 1e-7:
        raise AssertionError(comparisons)
    # With only norm projection, the remaining shift force has exact squared
    # norm kappa² * (sum rho³ - (sum rho²)²) = kappa² * 35/11664.
    field = initial_field()
    rho = np.abs(field)**2
    remaining = 0.3 * (rho - float(np.sum(rho**2))) * field
    ablation = float(np.linalg.norm(remaining))
    if ablation < 0.01:
        raise AssertionError("the additional ledger was not needed by the control")
    base_force, _ = projected_force(field, background, 0.3)
    coupled_force, _ = projected_force(field, background, 0.4)
    inhomogeneous_force, _ = projected_force(field, background + np.eye(8)[0], 0.3)
    coupling_difference = float(np.linalg.norm(coupled_force - base_force))
    inhomogeneous_difference = float(np.linalg.norm(inhomogeneous_force - base_force))
    if min(coupling_difference, inhomogeneous_difference) <= 1e-4:
        raise AssertionError("the force controls did not discriminate the gauge direction")
    return {"scope": "projected extension retaining the original kinetic and local sourcing force",
            "initial_norm2": 1, "initial_ipr_exact": "17/108", "kappa": 0.3, "tmax": 20,
            "noncritical_ipr": all(Fraction(17, 108) != Fraction(1, m) for m in range(1, 9)),
            "norm_only_control_shift_difference": ablation,
            "norm_only_control_variance_exact": "35/11664",
            "coupling_control_force_difference": coupling_difference,
            "inhomogeneous_background_control_force_difference": inhomogeneous_difference,
            "reference_final_tangent_force": reference["final_tangent_force"],
            "min_gram_eigenvalue_sampled": reference["min_gram_eigenvalue"],
            "max_normal_residual": reference["max_normal_residual"], "comparisons": comparisons,
            "convergence_theorem": False, "numerical_interval_certificate": False}
