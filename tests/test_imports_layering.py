"""Structural import-boundary checks for G-REPO-2."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "sbt_cosmo"

FORBIDDEN = {
    "background": ("sbt_cosmo.probes", "sbt_cosmo.inference", "sbt_cosmo.xi"),
    "growth": ("sbt_cosmo.probes", "sbt_cosmo.inference"),
    "probes": ("sbt_cosmo.inference", "experiments"),
    "xi": ("sbt_cosmo.probes", "sbt_cosmo.inference"),
    "audits": ("sbt_cosmo.inference", "experiments"),
    "hubble": ("experiments",),
    "inference": ("experiments",),
    "aor": (
        "sbt_cosmo.background",
        "sbt_cosmo.growth",
        "sbt_cosmo.probes",
        "sbt_cosmo.xi",
        "sbt_cosmo.audits",
        "sbt_cosmo.hubble",
        "sbt_cosmo.inference",
    ),
    "io": ("experiments",),
    "viz": ("experiments",),
}


def _imports(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    found: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            found.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            found.append(node.module)
    return found


def test_imports_layering() -> None:
    """Package modules obey the module-boundary import table."""
    violations: list[str] = []
    for path in PACKAGE.rglob("*.py"):
        rel = path.relative_to(PACKAGE)
        top = rel.parts[0] if len(rel.parts) > 1 else ""
        imports = _imports(path)
        for imported in imports:
            if imported.startswith("experiments"):
                violations.append(f"{rel}: imports {imported}")
            for forbidden in FORBIDDEN.get(top, ()):
                if imported == forbidden or imported.startswith(f"{forbidden}."):
                    violations.append(f"{rel}: imports forbidden {imported}")
    assert violations == []
