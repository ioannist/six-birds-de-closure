from __future__ import annotations

import math
import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def load_script(name: str):
    path = ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


run = load_script("de_audit_run")
validator = load_script("de_audit_validate")


class DummyFit:
    def __init__(self, m: float, sigma: float = 0.2) -> None:
        self.params = {"m": m}
        self.m_sigma = sigma


def test_aic_bic_formulas() -> None:
    assert run.aic(10.0, 3) == 16.0
    assert math.isclose(run.bic(10.0, 3, 100), 10.0 + 3.0 * math.log(100.0))


def test_staging_score_zero_for_identical_splits() -> None:
    fits = {"joint": DummyFit(0.1), "sn_only": DummyFit(0.1), "bao_only": DummyFit(0.1)}
    assert run.staging_score(fits) == 0.0


def test_staging_score_grows_for_split_shift() -> None:
    fits = {"joint": DummyFit(0.0, 0.1), "sn_only": DummyFit(1.0, 0.1), "bao_only": DummyFit(0.0, 0.1)}
    assert run.staging_score(fits) > 5.0


def test_validator_exports_derivation_function() -> None:
    assert callable(validator.derive)
