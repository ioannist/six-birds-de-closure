# Manager packet-review rubric (reusable)

Apply this to **EVERY packet** returned by Cody or Ralph, BEFORE accepting it. Do **not** trust the agent's self-report — verify against the actual repo. Record the verdict and the verification evidence in that packet's manifest (`ops/dispatches/<role>/<ts>.md`). Verdict: **ACCEPT** or **FIX-REQUIRED**.

## Mandatory verification artifacts (no acceptance without these)
Verification must be EVIDENCE, not a glance. For each packet, run and record (in the manifest):
- [ ] **Changed-files review (PRIMARY = the manifest's hash delta):** the dispatch manifest's "Files changed by this dispatch" section (before/after content hashes) is the authoritative change set — this repo is largely untracked, so plain `git diff` misses new files and must NOT be the authority. Confirm that hash-delta set matches the agent's report; use `git diff` / `git add -N` only to inspect the *content* of changed files. Claims unbacked by the hash delta ⇒ FIX. **The delta only sees non-ignored files: a deliverable that must be reviewed must NOT be gitignored. An agent citing a gitignored path (`ops/runs/`, `.lake/`, data caches) as a result ⇒ FIX.**
- [ ] **Clean rerun (code):** run the documented reproduction command yourself; compare outputs to the reported numbers (exact match, or within the spec's stated tolerance). Record the command and its result. If results are large, compare a checksum/table.
- [ ] **Lean trust-base diff (math):** run `ops/bin/lean-trust-scan.sh --diff` — it compares the whole Lean tree against the committed `ops/lean-trust-baseline.txt` at the OCCURRENCE level (`file` × `keyword` × `normalized line`, so a 2nd axiom/sorry in a file that already had one is caught) and exits nonzero listing every ADDED occurrence (`sorry`/`admit`/`axiom`/`constant`/`opaque`/`unsafe`/`native_decide`/`implemented_by`). Every addition must be justified with provenance or disclosed as deferred (the corpus uses opacity-guarded axioms by design, so the test is *growth is justified*, not zero). Confirm `lake build` passes from clean. **On ACCEPTING a Lean package, refresh the baseline (`ops/bin/lean-trust-scan.sh --baseline`) and commit it.** Record machine-checked vs deferred.

## 0. Scope & honesty
- [ ] Did the packet do exactly what was dispatched — nothing skipped, nothing smuggled in?
- [ ] Any fabricated results, stubbed outputs presented as real, or hand-tuning to hit a target?

## 1. Correctness
- **Math (Ralph):** definitions well-formed; every proof step valid; no hidden gap; the result proven is the result stated (not weaker/different).
- **Code (Cody):** runs from a clean state; deterministic (seeds/versions pinned); results reproduce; matched null/driven controls present.

## 2. Framework alignment (SBT discipline)
- [ ] Ξ used as the Schur-complement adequacy residual (Adequacy Residuals / Needle Killer), not an undefined symbol.
- [ ] Ξ_cosmo's status (adequacy residual vs distinct rewrite operator) stated, not fudged.
- [ ] Named laws cited correctly: **F11** (factors through access quotient), **F2** (source refinement + minimal target coarsening — NOT a three-repair list; "operator rewrite" is the P1/Descent–Repair chart, not F2), **F4** (four exclusive statuses), **F9** (no unstatused residual). Not silently reinvented.
- [ ] AOR statuses from the canonical set (11 base + 4 asymptotic); every residual is statused (F9).
- [ ] Primitives P1–P6, route mismatch RM, idempotence defect δ used per their corpus definitions.

## 3. Lean integrity (when the packet touches Lean)
- [ ] The pinned Lean project exists and `lake build` passes (Lean gate; see ops/README.md — first Ralph packet scaffolds it).
- [ ] No `sorry` / `admit` / conclusion-as-axiom / opaque trust-base axiom standing in for the theorem (gap scan above).
- [ ] Traceability disclosure honest: explicit about machine-checked vs deferred. Deferred ≠ proven.

## 4. No overclaim / no smuggling
- [ ] Claim grades honest (conditional / recognition-grade where the proof or data require it).
- [ ] Nothing assumed that the packet was supposed to establish.
- [ ] Non-claims respected (e.g. NOT "we refute a fundamental Λ"; idea.md and the precursor are explicit that Λ is not ruled out).

## 5. Pass criteria (experiments)
- [ ] The operationalized acceptance spec (`ops/specs/<exp>.md`) is GENUINELY met: standard DESI DR2 contours reproduced BEFORE any Six Birds machinery; ONE low-rank Ξ improving geometry+growth+calibration (not a per-probe fudge); out-of-sample win where required; staging fingerprint where required.

## Verdict & fix loop (with convergence guard)
- **ACCEPT** → fill the manifest (verdict + verification evidence), log in `manager_log.md`, proceed.
- **FIX-REQUIRED** → write a concrete, *high-level* fix request (cite `file:location`, the defect, the required outcome — not line-by-line code) and dispatch it back to the **same** agent. Bump the manifest's `fix iteration`. Re-review on return. Do NOT fix it yourself.
- **Convergence guard:** at most **2 fix iterations** on the same packet. If it still fails after the 2nd, do NOT bounce a 3rd time — either (a) re-scope into a smaller, more precisely specified packet, or (b) escalate: dispatch Eddy for an independent diagnosis, and surface to the human as a blocker. Record the escalation in `manager_log.md`.
