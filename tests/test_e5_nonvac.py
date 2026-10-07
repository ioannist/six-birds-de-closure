"""Tests for the E5-v3 staging-axis non-vacuity metric."""

from __future__ import annotations

import json
import importlib.util
import hashlib
from pathlib import Path

import numpy as np
import pytest

from sbt_cosmo.audits.metrics import nonvac_metrics


def _load_nonvac_script():
    path = Path("scripts/e5_v3_nonvac.py")
    spec = importlib.util.spec_from_file_location("e5_v3_nonvac", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_nonvac_synthetic_nonabsorbed_direction_passes() -> None:
    cov = np.eye(4)
    t = np.array([3.0, 0.0, 0.0, 0.0])
    metrics = nonvac_metrics(t, cov, cov)
    assert metrics["norm_pre"] == pytest.approx(3.0)
    assert metrics["norm_post"] == pytest.approx(3.0)
    assert metrics["retained"] == pytest.approx(1.0)
    assert metrics["NONVAC_pass"] is True


def test_nonvac_synthetic_absorbed_direction_fails() -> None:
    cov = np.eye(4)
    cov_marg = np.eye(4)
    cov_marg[0, 0] = 400.0
    metrics = nonvac_metrics(np.array([3.0, 0.0, 0.0, 0.0]), cov, cov_marg)
    assert metrics["norm_pre"] == pytest.approx(3.0)
    assert metrics["norm_post"] == pytest.approx(0.15)
    assert metrics["retained"] == pytest.approx(0.05)
    assert metrics["NONVAC_pass"] is False


def test_hsc_full_photoz_axis_fails_if_nonvac_artifact_exists() -> None:
    path = Path("results/E5/E5_v3_nonvac.json")
    if not path.exists():
        pytest.skip("E5_v3_nonvac artifact has not been generated in this checkout")
    report = json.loads(path.read_text())
    rows = {
        (row["family"], row["axis"]): row
        for row in report["rows"]
    }
    hsc_photoz = rows[("HSC-Y3", "photo_z_original_minus_desi_recal")]
    assert hsc_photoz["NONVAC_pass"] is False


def test_genuine_scale_cut_increment_is_data_amplitude_independent() -> None:
    scale_cut_increment = _load_nonvac_script().scale_cut_increment
    theory = np.array([10.0, 20.0, 30.0, 40.0])
    scale = np.array([900.0, 1200.0, 1800.0, 2600.0])
    data = 100.0 * theory
    t1 = scale_cut_increment(theory, scale, 1000.0, 2000.0, data_vector=data)
    t2 = scale_cut_increment(theory, scale, 1000.0, 2000.0, data_vector=2.5 * data)
    assert np.array_equal(t1, np.array([0.0, 20.0, 30.0, 0.0]))
    assert np.array_equal(t1, t2)


def test_kids_official_massdep_ia_covariance_loads() -> None:
    cov_path = Path("data/raw/kids_massdep_ia/massdep_cov.txt")
    means_path = Path("data/raw/kids_massdep_ia/massdep_means.txt")
    cov = np.loadtxt(cov_path)
    means = np.loadtxt(means_path)
    assert cov.shape == (8, 8)
    assert means.shape == (8,)
    assert np.allclose(cov, cov.T)
    assert np.linalg.eigvalsh(cov).min() > 0.0
    assert hashlib.sha256(cov_path.read_bytes()).hexdigest() == "7c47b9b3051a7772e58086f78ec7e136b32a8c9a5bedbd31e8b44580468ab328"


def test_kids_legal_nonvac_artifact_if_present() -> None:
    path = Path("results/E5/E5_v3_nonvac.json")
    if not path.exists():
        pytest.skip("E5_v3_nonvac artifact has not been generated in this checkout")
    report = json.loads(path.read_text())
    kids_scale = [
        row
        for row in report["rows"]
        if row["family"] == "KiDS-Legacy" and row["axis"].startswith("scale_cut_")
    ]
    assert kids_scale
    assert all(row["nuisance_legality"] == "legal_official_massdep_ia" for row in kids_scale)
    assert any(row["eligible_NONVAC_pass"] is True for row in kids_scale)
