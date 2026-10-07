"""Determinism checks for committed synthetic E0 artifacts."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
E0_DIR = ROOT / "experiments" / "E0_synthetic"
E0_OUTPUTS = E0_DIR / "outputs"


FITTED_SUMMARY_PATHS = {
    "/gates/G-E0-2.4/value", "/gates/G-E0-2.6/value/chi2_gap_per_z",
    "/gates/G-E0-2.7/value", "/headline/apparent_omega_lambda",
    "/headline/rewrite_chi2", "/headline/rewrite_oos_ratio",
}


def _compare_json_scalars(left: Any, right: Any, path: str = "", *, historical: bool = False) -> list[str]:
    violations: list[str] = []
    if isinstance(left, dict):
        if left.keys() != right.keys():
            return [path + "/keys"]
        for key, value in left.items():
            violations.extend(_compare_json_scalars(value, right[key], f"{path}/{key}", historical=historical))
    elif isinstance(left, list):
        if len(left) != len(right):
            return [path + "/length"]
        for index, (item_left, item_right) in enumerate(zip(left, right)):
            violations.extend(_compare_json_scalars(item_left, item_right, f"{path}/{index}", historical=historical))
    elif isinstance(left, float) or isinstance(right, float):
        denom = max(abs(float(left)), abs(float(right)), 1.0)
        tol = 1.0e-6 if historical and path in FITTED_SUMMARY_PATHS else 1.0e-12
        if not np.isfinite([left, right]).all() or abs(float(left) - float(right)) / denom >= tol:
            violations.append(path)
    elif left != right:
        violations.append(path)
    return violations


def test_e0_committed_summary_records_determinism() -> None:
    """The committed E0 summary records the internal determinism gate as passing."""
    path = E0_OUTPUTS / "summary.json"
    if not path.exists():
        pytest.skip("E0 artifacts not present")
    summary = json.loads(path.read_text(encoding="utf-8"))
    assert summary["gates"]["G-E0-0.1"]["pass"] is True


def test_e0_rerun_reproduces_summary_and_arrays(tmp_path: Path) -> None:
    """Strict same-environment replay; numerical comparison to historical fits.

    L-BFGS-B finite-difference optima drift across CPU/library builds. Only the
    named fitted fields use 1e-6 relative tolerance against historical outputs;
    gate decisions and generated inputs retain strict checks. This does not
    claim portable bitwise reproduction of floating-point optimizer results.
    """
    summary_path = E0_OUTPUTS / "summary.json"
    if not summary_path.exists():
        pytest.skip("E0 artifacts not present")
    outdir = tmp_path / "e0_verify"
    subprocess.run(
        [
            sys.executable,
            str(E0_DIR / "run.py"),
            "--config",
            str(E0_DIR / "config.yaml"),
            "--outdir",
            str(outdir),
        ],
        cwd=ROOT,
        env={**os.environ, "OMP_NUM_THREADS": "1"},
        check=True,
    )
    committed = json.loads(summary_path.read_text(encoding="utf-8"))
    rerun = json.loads((outdir / "summary.json").read_text(encoding="utf-8"))
    assert _compare_json_scalars(committed, rerun, historical=True) == []
    second = tmp_path / "e0_replay"
    subprocess.run(
        [sys.executable, str(E0_DIR / "run.py"), "--config", str(E0_DIR / "config.yaml"), "--outdir", str(second)],
        cwd=ROOT, env={**os.environ, "OMP_NUM_THREADS": "1"}, check=True,
    )
    replay = json.loads((second / "summary.json").read_text(encoding="utf-8"))
    assert _compare_json_scalars(rerun, replay) == []
    fitted_arrays = {"lcdm_distance", "rewrite_distance", "rewrite_proxy"}
    for path in sorted((E0_OUTPUTS / "arrays").glob("*.npz")):
        old = np.load(path)
        fresh = np.load(outdir / "arrays" / path.name)
        again = np.load(second / "arrays" / path.name)
        assert old.files == fresh.files == again.files
        for name in old.files:
            np.testing.assert_array_equal(fresh[name], again[name])
            tol = 1e-6 if path.name == "toy2_mock_distances.npz" and name in fitted_arrays else 1e-12
            np.testing.assert_allclose(old[name], fresh[name], rtol=tol, atol=1e-12)
