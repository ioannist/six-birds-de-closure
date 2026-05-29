# Eddy package-review request (template — manager fills the bracketed parts)

PACKAGE UNDER REVIEW: [name it, e.g. "Experiment 1: DESI DR2 reproduction" or "Proposition 2 + Lean mechanization"]

PACKAGE MANIFEST: ops/packages/[package].md — read it first and verify it against the accepted packet manifests it cites (ops/dispatches/<role>/<ts>.md): do the claimed artifacts, results, and accepted packets actually exist and match?

ARTIFACTS (verify these in the repo, do not trust the summaries below):
- [exact files/dirs: code entry points, math notes, Lean sources, result files/figures]

WHAT WAS CLAIMED (from the accepted packet reports):
- [paste the net claims / results being asserted]

PASS CRITERIA THIS PACKAGE MUST MEET (quote from idea.md):
- [the relevant idea.md §6 pass criterion / §10 standard]

Run your full six-dimension review (correctness, framework alignment, Lean integrity, no-overclaim/no-smuggling, pass criteria, reproducibility). RUN the code and `lake build` rather than trusting the reports. Return **PASS / PASS-WITH-FIXES / FAIL** and a numbered findings list: severity (blocker/major/minor), `file:location`, defect, required fix.
