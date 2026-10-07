"""Single Xi_cosmo source checks for G-REPO-3."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _definitions(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            names.append(node.name)
    return names


def test_xi_single_source() -> None:
    """XiCosmo and its canonical evaluator are defined only under sbt_cosmo/xi."""
    hits: list[tuple[str, str]] = []
    for path in (ROOT / "sbt_cosmo").rglob("*.py"):
        for name in _definitions(path):
            if name in {"XiCosmo", "evaluate_xi_cosmo"}:
                hits.append((name, str(path.relative_to(ROOT))))
    assert sorted(hits) == [
        ("XiCosmo", "sbt_cosmo/xi/residual.py"),
        ("evaluate_xi_cosmo", "sbt_cosmo/xi/residual.py"),
    ]


def test_no_experiment_xi_redefinition() -> None:
    """Experiments may call the package API but must not define their own XiCosmo."""
    bad: list[str] = []
    for path in (ROOT / "experiments").rglob("*.py"):
        defs = set(_definitions(path))
        if {"XiCosmo", "evaluate_xi_cosmo", "apply_rewrite"} & defs:
            bad.append(str(path.relative_to(ROOT)))
    assert bad == []
