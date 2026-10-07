from pathlib import Path
import sys

import numpy as np

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import de_ground_state_checks as checks
import step54_rederive as step54


def test_native_phase_sign_counterexample_and_corrected_return():
    native = checks.import_native()
    u = np.ones(8, dtype=complex)/np.sqrt(8)
    assert abs(np.linalg.norm(native.phase_align(u, 1j*u)-1j*u)-2) < 1e-14
    np.testing.assert_allclose(checks.align_ray(u, 1j*u), 1j*u, rtol=0, atol=1e-14)


def test_corrected_phase_alignment_minimizes_distance_and_respects_rays():
    a = np.array([1+2j, -1j, 3], dtype=complex)
    b = np.array([-1j, 2+1j, 1], dtype=complex)
    a /= np.linalg.norm(a)
    b /= np.linalg.norm(b)
    aligned = checks.align_ray(a, b)
    overlap = np.vdot(aligned, b)
    assert overlap.real > 0 and abs(overlap.imag) < 1e-14
    assert abs(np.linalg.norm(aligned-b)**2-(2-2*abs(np.vdot(a, b)))) < 1e-14
    phase = np.exp(.73j)
    np.testing.assert_allclose(checks.align_ray(phase*a, b), aligned, atol=1e-14, rtol=0)
    np.testing.assert_allclose(checks.align_ray(a, phase*b), phase*aligned, atol=1e-14, rtol=0)
    orthogonal = np.array([0, 1], dtype=complex)
    np.testing.assert_array_equal(checks.align_ray(np.array([1, 0]), orthogonal), [1, 0])


def test_analytic_derivative_checks_actual_ground_selector():
    kinetic, gradient = checks.operators(8)
    background = np.array([.35, .32, .25, .18, .15, .18, .25, .32])
    psi, _, _ = checks.solve(kinetic, gradient, background, 10., np.ones(8)/np.sqrt(8))
    receipt = checks.jacobians(kinetic, gradient, background, 10., psi)
    assert receipt["analytic_fd_max_error"] < 2e-7
    assert receipt["map_residual"] < 1e-12 and receipt["eigen_residual"] < 1e-10
    assert receipt["raw_map_radius"] > 1
    assert receipt["relaxed_radius_mix_0_2"] < 1


def test_frozen_budget_separation_is_not_nonexistence_or_runaway():
    path = step54.VENDORED_STEP54 / "kappa_sweep_step54.csv"
    receipt = step54.derive_kappa(step54.read_csv(path))
    assert receipt["boundary_found"]
    assert receipt["max_pass"] == 10 and receipt["min_fail"] == 15
    assert receipt["boundary_kind"] == "finite_budget_pass_fail_separation"
    assert not receipt["ground_state_nonexistence_proved"]
    assert not receipt["runaway_proved"]
    assert not receipt["linear_stability_boundary_proved"]
