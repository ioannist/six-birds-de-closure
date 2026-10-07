"""Reproduce-without-rerun gate checks for committed experiment artifacts."""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
E0_OUTPUTS = ROOT / "experiments" / "E0_synthetic" / "outputs"
E1_SCAN_PATHS = [
    ROOT / "configs" / "experiments" / "E1.yaml",
    ROOT / "sbt_cosmo" / "inference",
    ROOT / "experiments" / "E1_desi_dr2_repro",
]
E1_REPRO_SUMMARY = ROOT / "runs" / "E1" / "E1A_full" / "summary.json"
FORBIDDEN_E1_PATTERNS = {
    "Xi name": re.compile(r"(?:Xi_cosmo|Ξ_cosmo)"),
    "a0-a2 coefficients": re.compile(r"(?:\ba[0-2]\b|a[₀₁₂])"),
    "rewrite token": re.compile(r"R\[[^\]]*\]"),
    "K-family": re.compile(r"(?:\bK_[LMGS]\b|K_L/K_M/K_G/K_S)"),
    "Delta marker": re.compile(r"(?:Delta_SBT|Δ_SBT)"),
    "route-index H0": re.compile(r"(?:H0\^\{\(r,l\)\}|H₀\^\{\(r,ℓ\)\})"),
    "fraktur h": re.compile(r"𝔥_γ"),
}


def _summary() -> dict:
    path = E0_OUTPUTS / "summary.json"
    if not path.exists():
        pytest.skip("E0 artifacts not present")
    return json.loads(path.read_text(encoding="utf-8"))


def test_e0_all_gates_pass() -> None:
    """Every pre-registered E0 gate recorded in summary.json passes."""
    summary = _summary()
    assert summary["experiment"] == "E0"
    assert summary["terminal_state"] == "PASS"
    failures = {gate_id: gate for gate_id, gate in summary["gates"].items() if not gate["pass"]}
    assert failures == {}


def test_e0_headline_gate_values() -> None:
    """Load-bearing E0 values satisfy the locked thresholds."""
    summary = _summary()
    headline = summary["headline"]
    assert 0.4 <= headline["apparent_omega_lambda"] <= 0.75
    assert headline["homogeneous_control_omega_lambda"] < 0.1
    assert headline["rewrite_oos_ratio"] >= 10.0
    assert headline["min_rho_eff"] > 0.0
    assert headline["max_real_eigenvalue"] <= 1.0e-10
    assert headline["hubble_bic_null_minus_sbt"] >= 10.0
    assert headline["hubble_bic_nuisance_minus_sbt"] >= 6.0


def test_e0_expected_artifacts_exist() -> None:
    """E0 emits the five committed figures and five committed tables."""
    expected = [
        E0_OUTPUTS / "tables" / "toy1_rm_vs_beta.csv",
        E0_OUTPUTS / "tables" / "toy2_Q_summary.csv",
        E0_OUTPUTS / "tables" / "toy2_fit_summary.csv",
        E0_OUTPUTS / "tables" / "toy3_weff_crossing.csv",
        E0_OUTPUTS / "tables" / "toy4_route_recovery.csv",
        E0_OUTPUTS / "figures" / "fig_toy1_rm_vs_beta.png",
        E0_OUTPUTS / "figures" / "fig_toy2_Q_vs_time.png",
        E0_OUTPUTS / "figures" / "fig_toy2_distance_fit.png",
        E0_OUTPUTS / "figures" / "fig_toy3_weff.png",
        E0_OUTPUTS / "figures" / "fig_toy4_route_matrix.png",
    ]
    missing = [path.relative_to(ROOT).as_posix() for path in expected if not path.exists() or path.stat().st_size == 0]
    assert missing == []


def scan_e1_no_sbt(paths: list[Path] | None = None) -> list[str]:
    """Return forbidden-symbol violations for the standard E1-A code path."""
    violations: list[str] = []
    for path in paths or E1_SCAN_PATHS:
        for file_path in _scan_files(path):
            text = file_path.read_text(encoding="utf-8", errors="ignore")
            for name, pattern in FORBIDDEN_E1_PATTERNS.items():
                match = pattern.search(text)
                if match:
                    rel = file_path.relative_to(ROOT) if file_path.is_relative_to(ROOT) else file_path
                    violations.append(f"{rel}: {name}: {match.group(0)}")
    return violations


def assert_e1b_allowed(summary_path: Path = E1_REPRO_SUMMARY) -> None:
    """Refuse E1-B scoring until every E1-A reproduction gate passed."""
    if not summary_path.exists():
        raise AssertionError(f"E1-A summary missing: {summary_path}")
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    gates = summary.get("gates", {})
    failures = {
        gate_id: gate
        for gate_id, gate in gates.items()
        if gate_id.startswith("G-E1-REPRO-") and gate.get("pass") is not True
    }
    missing = [gate_id for gate_id in gates if gate_id.startswith("G-E1-REPRO-") and "pass" not in gates[gate_id]]
    if failures or missing:
        raise AssertionError({"failures": failures, "missing": missing})


def test_e1_no_sbt_lint_passes_real_code_path() -> None:
    """E1-A config and runner path contain no forbidden project-extension symbols."""
    assert scan_e1_no_sbt() == []


def test_e1_no_sbt_lint_catches_planted_symbol(tmp_path: Path) -> None:
    """The E1-A lint fails when a forbidden symbol is planted."""
    planted = tmp_path / "planted.py"
    planted.write_text("bad = 'Xi_cosmo'\n", encoding="utf-8")
    violations = scan_e1_no_sbt([planted])
    assert violations and "Xi name" in violations[0]


def test_e1b_ordering_guard(tmp_path: Path) -> None:
    """E1-B is blocked unless the E1-A reproduction summary records green gates."""
    failing = tmp_path / "summary_failing.json"
    failing.write_text(json.dumps({"gates": {"G-E1-REPRO-CMBONLY": {"pass": False}}}), encoding="utf-8")
    with pytest.raises(AssertionError):
        assert_e1b_allowed(failing)

    passing = tmp_path / "summary_passing.json"
    passing.write_text(
        json.dumps({"gates": {"G-E1-REPRO-CMBONLY": {"pass": True}, "G-E1-REPRO-NO-SBT": {"pass": True}}}),
        encoding="utf-8",
    )
    assert_e1b_allowed(passing)


def _scan_files(path: Path) -> list[Path]:
    suffixes = {".py", ".yaml", ".yml", ".json", ".md"}
    if path.is_file():
        return [path] if path.suffix in suffixes else []
    return sorted(file_path for file_path in path.rglob("*") if file_path.is_file() and file_path.suffix in suffixes)
