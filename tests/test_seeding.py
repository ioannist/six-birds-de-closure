"""Seed discipline checks for G-REPO-5."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN_DIRS = [ROOT / "sbt_cosmo", ROOT / "experiments"]


def test_no_bare_rng_calls() -> None:
    """No bare np.random.* or random.* calls appear outside explicit seed plumbing."""
    violations: list[str] = []
    for directory in SCAN_DIRS:
        for path in directory.rglob("*.py"):
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
            for node in ast.walk(tree):
                if not isinstance(node, ast.Call):
                    continue
                func = node.func
                if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Attribute):
                    if (
                        isinstance(func.value.value, ast.Name)
                        and func.value.value.id == "np"
                        and func.value.attr == "random"
                        and func.attr != "default_rng"
                    ):
                        violations.append(f"{path.relative_to(ROOT)}:{node.lineno}: np.random.{func.attr}")
                if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
                    if func.value.id == "random" and func.attr not in {"seed"}:
                        violations.append(f"{path.relative_to(ROOT)}:{node.lineno}: random.{func.attr}")
    assert violations == []


def test_seed_blocks_present() -> None:
    """All experiment configs carry the required seed block."""
    import yaml

    missing: list[str] = []
    for path in (ROOT / "experiments").glob("E*/config.yaml"):
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
        seed = data.get("seed", {})
        if not {"numpy", "python", "sampler"} <= set(seed):
            missing.append(str(path.relative_to(ROOT)))
    assert missing == []
