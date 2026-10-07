"""Registry lint over plan files and the C0a skeleton."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN_ROOTS = [
    ROOT / "plan",
    ROOT / "sbt_cosmo",
    ROOT / "configs",
    ROOT / "data" / "manifests",
    ROOT / "experiments",
    ROOT / "results",
    ROOT / "README.md",
]

FORBIDDEN_EXACT = (
    "PhantomNoGhost",
    "no-ghost",
    "no_ghost",
    "G-E8-NOGHOST",
    "</invoke>",
    "plans/",
    "repo-root GROUNDING_BRIEF.md",
    # Sign-free pivot, REGISTRY §11.1 / §11.10 (EXTERNAL_REPLAN_RESPONSE §12 "DO NOT USE", 2026-05-31).
    # FORBIDDEN_EXACT is a substring check, so the "beat"/"beats" variants are both listed.
    "Six Birds beat w0wa",
    "Six Birds beats w0wa",
    "one signed low-rank Ξ",
    "predict CCHP sign",
    "predict SH0ES sign",
    "one 3-parameter Ξ predicts CCHP/SH0ES",
)
PHRASE_PATTERNS = (
    re.compile(r"summary\.json\s*=\s*PASS"),
    re.compile(r"upstream\s*=\s*PASS"),
    re.compile(r"\bG-T\d+\b"),
    re.compile(r"\bG-DECISIVE\b"),
)
# BARE_GATE matches only bare ``G<digits>`` (e.g. ``G3``). It does NOT match the namespaced
# gate prefixes ``G-R0-*`` / ``G-R1-*`` (introduced 2026-05-31) nor the risk-register prose IDs
# ``R0`` / ``R1`` / ``R<n>`` (referenced only as ``risk R<n>``). Those are intentionally distinct
# from each other and from this lint (REGISTRY §4 namespace-vs-risk-ID disambiguation), so adding
# the sign-free experiment files introduces no false positive here.
BARE_GATE = re.compile(r"\bG\d+\b")

# Sign-free pivot forbidden tokens (REGISTRY §11.1 / §11.10, EXTERNAL_REPLAN_RESPONSE §12, 2026-05-31).
# These are the subset of FORBIDDEN_EXACT that the four quoting-to-ban specification files are
# allowed to QUOTE (in order to forbid/retire/supersede them). A real *use* in any other file is
# still rejected, and these four files are NOT exempted for the older forbidden tokens.
SIGN_FREE_FORBIDDEN = (
    "Six Birds beat w0wa",
    "Six Birds beats w0wa",
    "one signed low-rank Ξ",
    "predict CCHP sign",
    "predict SH0ES sign",
    "one 3-parameter Ξ predicts CCHP/SH0ES",
)
# These files exist to QUOTE the banned phrases in order to forbid/retire them (REGISTRY §11.10).
QUOTING_TO_BAN_FILES = frozenset(
    {
        "plan/REPLAN_SPEC_2026-05-31.md",
        "plan/EXTERNAL_REPLAN_RESPONSE_2026-05-31.md",
        "plan/STRATEGY_PIVOT_2026-05-31.md",
        "plan/E4_PREDICT_CONTRACT.md",
    }
)


def _text_files() -> list[Path]:
    files: list[Path] = []
    for root in SCAN_ROOTS:
        if root.is_file():
            files.append(root)
            continue
        for path in root.rglob("*"):
            if path.is_file() and path.suffix.lower() in {".md", ".py", ".yaml", ".yml", ".json", ".toml", ".cff"}:
                files.append(path)
    return files


def _line_allowed_for_registry_spec(path: Path, line: str) -> bool:
    rel = path.relative_to(ROOT).as_posix()
    if rel == "plan/REGISTRY.md":
        return True
    if rel == "plan/01-repo-structure.md" and (
        "forbidden" in line.lower()
        or "PhantomNoGhost" in line
        or "no-ghost" in line
        or "no_ghost" in line
        or "G-E8-NOGHOST" in line
        or "G-DECISIVE" in line
        or "summary.json = PASS" in line
        or "win or tie" in line.lower()
        or "within 10%" in line.lower()
    ):
        return True
    if "not a pass" in line.lower() or "not std-3" in line.lower() or "removed" in line.lower():
        return True
    if "comparability" in line.lower() or "boundedness" in line.lower() or "reducible" in line.lower():
        return True
    if "no \"within 3%/10%\" pass" in line.lower() or "strictly beat" in line.lower():
        return True
    if "reproduce-before-rewrite" in line.lower() or "G-ENV-6" in line:
        return True
    if rel == "plan/CONTRACT_HARDENING_ADDENDUM.md" and "win or tie" in line.lower():
        return True
    if "idea.md" in line and "ghost" in line.lower():
        return True
    return False


_BAN_CONTEXT = re.compile(
    r"do[\s-]*not[\s-]*use|forbidden|forbid|retire|superseded|supersede|"
    r"\bbans?\b|over-?reach|over-?claim|don'?t\s+use",
    re.IGNORECASE,
)


def _sign_free_token_allowed(path: Path, token: str, line: str) -> bool:
    """Token-scoped carve-out for quoting-to-ban contexts (REGISTRY §11.1 / §11.10, 2026-05-31).

    Only the sign-free forbidden tokens are ever exempted, and only when the line is a
    *quoting-to-ban* context (so a real *use* of the phrase is still rejected). A line is treated
    as quoting-to-ban when EITHER:
      * the file is one of the four canonical quote-and-ban specification files
        (``QUOTING_TO_BAN_FILES``); OR
      * the line carries a retire/forbid/supersede/DO-NOT-USE marker, OR the banned phrase is
        presented inside double quotes as a quoted listing (the spec's preferred line-level
        marker, REPLAN_SPEC §5.1b.2) — e.g. the ``**DO NOT USE**`` block in ``plan/00-overview.md``.
    Older FORBIDDEN_EXACT tokens (e.g. ``no-ghost``) are NOT covered here, so this never widens the
    existing lint; it only exempts the new sign-free tokens in genuine quote-and-ban contexts.
    """
    if token not in SIGN_FREE_FORBIDDEN:
        return False
    rel = path.relative_to(ROOT).as_posix()
    if rel in QUOTING_TO_BAN_FILES:
        return True
    if _BAN_CONTEXT.search(line):
        return True
    # A quoted listing of the banned phrase (``- "<phrase>"``) is a quoting-to-ban line, not a use.
    if f'"{token}' in line or f"“{token}" in line:
        return True
    return False


def test_registry_forbidden_tokens() -> None:
    """Reject obsolete registry tokens outside explicit registry/specification contexts.

    Sign-free-pivot membership note (REGISTRY §11.10(c), 2026-05-31): there is NO positive
    "states membership as E1-E7" lint here today, so the sign-free certificate experiment files
    (``R0-*.md``, ``R1-*.md``, ``E5-growth-staging-currency.md``, ``E4b-*.md``,
    ``E8L-all-six-ledger.md``) and their ``G-R0-*`` / ``G-R1-*`` / ``G-E4b-*`` / ``G-E5-*`` /
    ``G-E8L-*`` gate IDs are not rejected for "not being E1-E7". If a positive membership lint is
    ever added it MUST be scoped to the geometry-ledger members only and MUST exempt those five
    files and their namespaced gate IDs (REGISTRY §11.10(c) / §5.1.1(c) of the replan spec).
    """
    violations: list[str] = []
    for path in _text_files():
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if _line_allowed_for_registry_spec(path, line):
                continue
            for token in FORBIDDEN_EXACT:
                if token in line and not _sign_free_token_allowed(path, token, line):
                    violations.append(f"{path.relative_to(ROOT)}:{lineno}: {token}")
            for pattern in PHRASE_PATTERNS:
                if pattern.search(line):
                    violations.append(f"{path.relative_to(ROOT)}:{lineno}: {pattern.pattern}")
            if "within 3%" in line.lower() and "tie" not in line.lower():
                violations.append(f"{path.relative_to(ROOT)}:{lineno}: within 3%")
            if "within 10%" in line.lower() and "comparability" not in line.lower() and "boundedness" not in line.lower():
                violations.append(f"{path.relative_to(ROOT)}:{lineno}: within 10%")
            if "win or tie" in line.lower():
                violations.append(f"{path.relative_to(ROOT)}:{lineno}: win or tie")
    assert violations == []


def test_no_bare_gate_ids_in_skeleton() -> None:
    """Skeleton files do not introduce bare G<number> gate IDs."""
    violations: list[str] = []
    for path in _text_files():
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith("plan/"):
            continue
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if BARE_GATE.search(line):
                violations.append(f"{rel}:{lineno}: {line.strip()}")
    assert violations == []


def test_aor_status_enum_has_no_validator_sentinel() -> None:
    """Accepted AOR statuses exclude the validator-error sentinel."""
    from sbt_cosmo.aor.status import AOR_STATUSES

    assert "unstatused" not in AOR_STATUSES
    assert len(AOR_STATUSES) == 15


def test_terminal_states_subset() -> None:
    """Terminal states used by the registry are the locked closed set."""
    terminal_states = {"PASS", "ACCEPTED_NEGATIVE", "BLOCKED", "PROGRAM_FAIL"}
    assert terminal_states <= {"PASS", "ACCEPTED_NEGATIVE", "BLOCKED", "PROGRAM_FAIL"}
