#!/usr/bin/env python3
r"""Regenerate sections/*.tex and appendices/*.tex from contents/*.md.

Pipeline (matches the original scaffold integration):
  1. pandoc -f markdown -t latex --natbib   ([@key] -> \\citep{key}, @key -> \\citet{key})
  2. strip the leading heading number the markdown carries (LaTeX auto-numbers)
  3. map the non-ASCII glyphs the lmodern/inputenc preamble cannot render to LaTeX macros

The abstract (contents/sec_00_abstract.md) is written, citation-free, between
\begin{abstract} and \end{abstract} in main.tex.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CONTENTS = ROOT / "contents"

# non-ASCII -> LaTeX (dashes/ellipsis are left to pandoc's smart extension)
UNICODE_MAP = {
    "§": r"\S{}",                 # §
    "Λ": r"\ensuremath{\Lambda}", # Λ
    "λ": r"\ensuremath{\lambda}", # λ
    "κ": r"\ensuremath{\kappa}",  # κ
    "ε": r"\ensuremath{\varepsilon}", # ε
    "σ": r"\ensuremath{\sigma}",  # σ
    "Δ": r"\ensuremath{\Delta}",  # Δ
    "→": r"\ensuremath{\to}",     # →
    "⇒": r"\ensuremath{\Rightarrow}", # ⇒
    "↔": r"\ensuremath{\leftrightarrow}", # ↔
    "×": r"\ensuremath{\times}",  # ×
    "≈": r"\ensuremath{\approx}", # ≈
    "≠": r"\ensuremath{\neq}",    # ≠
    "±": r"\ensuremath{\pm}",     # ±
    "−": r"\ensuremath{-}",       # − (minus)
    "¹": r"\ensuremath{^{1}}",    # ¹
    "²": r"\ensuremath{^{2}}",    # ²
    "⁰": r"\ensuremath{^{0}}",    # ⁰
}

SECTION_RE = re.compile(r"(\\(?:sub)*section\{)\d+(?:\.\d+)*\.?\s+")
APP_SEC_RE = re.compile(r"(\\section\{)Appendix\s+[A-Z]\s+---\s+")
APP_SUB_RE = re.compile(r"(\\(?:sub)*section\{)[A-Z]\.\d+(?:\.\d+)*\s+")
TEXTTT_RE = re.compile(r"\\texttt\{([^{}]*)\}")


def break_paths(tex: str) -> str:
    """Let inline code (\\texttt, from markdown `code`) line-break at path
    separators so long file paths / commands don't overrun the margin.
    \\allowbreak is a zero-width optional break: no visual change, just permits
    wrapping after '/' and an escaped underscore."""
    def repl(m: "re.Match[str]") -> str:
        s = (m.group(1).replace("/", "/\\allowbreak ")
                       .replace("\\_", "\\_\\allowbreak ")
                       .replace("-", "-\\allowbreak "))
        return "\\texttt{" + s + "}"
    return TEXTTT_RE.sub(repl, tex)


def uncount_plain_tables(tex: str) -> str:
    """longtable steps the table counter even without a caption; undo that for
    pandoc's uncaptioned pipe tables so captioned tables are numbered 1, 2, ..."""
    out, pos = [], 0
    for m in re.finditer(r"\\begin\{longtable\}.*?\\end\{longtable\}", tex, flags=re.S):
        out.append(tex[pos:m.end()])
        if "\\caption" not in m.group(0):
            out.append("\n\\addtocounter{table}{-1}")
        pos = m.end()
    out.append(tex[pos:])
    return "".join(out)


def pandoc(src: Path) -> str:
    out = subprocess.run(
        ["pandoc", "-f", "markdown", "-t", "latex", "--natbib", str(src)],
        check=True, capture_output=True, text=True,
    )
    return out.stdout


def post(tex: str, *, appendix: bool) -> str:
    tex = SECTION_RE.sub(r"\1", tex)
    if appendix:
        tex = APP_SEC_RE.sub(r"\1", tex)
        tex = APP_SUB_RE.sub(r"\1", tex)
    for u, latex in UNICODE_MAP.items():
        tex = tex.replace(u, latex)
    tex = break_paths(tex)
    tex = uncount_plain_tables(tex)
    return tex


def main() -> None:
    n = 0
    for md in sorted(CONTENTS.glob("sec_*.md")):
        if md.stem == "sec_00_abstract":
            continue
        (ROOT / "sections" / f"{md.stem}.tex").write_text(post(pandoc(md), appendix=False))
        n += 1
    for md in sorted(CONTENTS.glob("app_*.md")):
        (ROOT / "appendices" / f"{md.stem}.tex").write_text(post(pandoc(md), appendix=True))
        n += 1
    main_tex = ROOT / "main.tex"
    text = main_tex.read_text()
    start = text.index("\\begin{abstract}\n") + len("\\begin{abstract}\n")
    end = text.index("\\end{abstract}")
    abstract = post(pandoc(CONTENTS / "sec_00_abstract.md"), appendix=False).strip()
    main_tex.write_text(text[:start] + abstract + "\n" + text[end:])
    print(f"regenerated {n} .tex files and the abstract in main.tex")


if __name__ == "__main__":
    main()
