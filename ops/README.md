# ops/ — manager harness for "Dark Energy as Closure"

The human is the project owner; **Claude (the assistant) is the live MANAGER** across sessions. All coding / math / Lean is done by three persistent OpenAI **codex** sessions, driven from here:

- **Cody** — coder: Python pipelines, experiments, data, numerics, reproducibility.
- **Ralph** — mathematician: definitions, proofs, AND Lean 4 mechanization.
- **Eddy** — independent reviewer, invoked per completed work **PACKAGE** (not per packet).

Scope of this phase: experiments + math + Lean + results. **No prose / manuscript writing.**

## Files & dirs
- `bin/codex-dispatch.sh <role> <prompt_file> [effort]` — **fail-closed** dispatcher. First call per role → stdin bootstrap (records the thread UUID); later calls resume by UUID and **verify codex resumed that same thread** (aborts on mismatch). Captures the final message via `codex -o` (reliable, full multiline). Validates exit code, timeout (`CODEX_TIMEOUT`, default 1800s), a `turn.completed` event, and a non-empty final message. Sandbox = `workspace-write` + `approval_policy="never"` (replaces deprecated `--full-auto`). Forbidden writes to `~/.codex/memories` are detected by content hash and **fail the dispatch closed** (`CODEX_ALLOW_MEMORY_WRITE=1` overrides). Writes a committed manifest to `dispatches/<role>/`: `<ts>.md` on success, or **`<ts>.FAILED.md`** on any failure after codex ran (rc, stderr tail, before/after file-hash delta) so aborted runs never leave silent, unaudited edits. Run ids are collision-resistant (nanoseconds + PID, with a pre-existence guard) so rapid same-second dispatches never overwrite each other. The manifest's hash delta — not `git diff` — is the authoritative changed-files record. Reasoning effort inherits `~/.codex/config.toml` (xhigh) unless the 3rd arg overrides it. (`CODEX_MEMDIR` is a test-only override of the memory-store path used by the self-test.)
- `bin/codex-last.sh <jsonl>` — fallback full-text final-message extractor (primary path is `-o`).
- `bin/lean-trust-scan.sh [--occurrences|--baseline|--diff]` — whole-tree Lean trust-base scan at the OCCURRENCE level (`<file>\t<keyword>\t<normalized-line>`). The diff is a MULTISET comparison (duplicates preserved), so even a 2nd byte-identical trust line in a file that already had one is flagged. `--diff` exits 2 listing any NEW occurrence vs the committed `lean-trust-baseline.txt`; `--baseline` refreshes it on accept.
- `bin/selftest.sh` — hermetic regression test of the harness (fake `codex`, throwaway repos, no real calls), **29 checks, must stay green**: dispatch validation incl. invalid-JSONL / empty-`-o` / missing-thread-id / forbidden-memory-write fail-closed paths, FAILED manifests, resume-mismatch, timeout, run-id uniqueness, multiline capture, and the Lean multiset occurrence-diff. Run after any harness edit.
- `lean-trust-baseline.txt` — committed accepted Lean trust base. Created on the FIRST accepted Lean package (none exists yet); refreshed by `--baseline`.
- `bootstrap/{cody,ralph,eddy}.md` — first-dispatch prompts (role + corpus + discipline).
- `review_rubric.md` — the manager's reusable per-packet review checklist (verify against the repo with mandatory evidence; convergence guard). NOT sent to codex.
- `prompts/eddy-review.md` — reusable package-review template for Eddy.
- `specs/` — **committed** experiment acceptance specs (`<exp>.md`); the manager operationalizes idea.md's pass criteria into quantitative gates BEFORE dispatching Cody.
- `dispatches/<role>/<ts>.md` + `<ts>.prompt.md` — **committed** per-packet audit manifests (prompt copy, working-tree snapshot, manager verdict + verification evidence).
- `packages/<package>.md` — **committed** package manifests; author one before each Eddy review.
- `manager_log.md` — append-only decision / dispatch / review log.
- `threads/.codex_thread_id_<role>` — thread UUIDs. **MACHINE-LOCAL runtime state, gitignored** (rollouts live under `~/.codex/sessions` on this machine; UUIDs are not portable).
- `runs/<role>/*` — transcripts / stderr / captured messages (gitignored).

## Bootstrap each role once
    ops/bin/codex-dispatch.sh cody  ops/bootstrap/cody.md
    ops/bin/codex-dispatch.sh ralph ops/bootstrap/ralph.md
    ops/bin/codex-dispatch.sh eddy  ops/bootstrap/eddy.md

## Per-packet loop
1. (Experiments) ensure an acceptance spec exists: `ops/specs/<exp>.md`.
2. Write a single-step prompt to a scratch file, e.g. `ops/runs/cody/next.md`.
3. `ops/bin/codex-dispatch.sh cody ops/runs/cody/next.md` → it writes a manifest under `dispatches/cody/`.
4. Apply `review_rubric.md` against the actual repo; record verdict + verification evidence in the manifest. ACCEPT, or dispatch a fix back to the same role (≤2 iterations, then re-scope/escalate).
5. When a coherent package is done: write `packages/<package>.md`, fill `prompts/eddy-review.md`, dispatch `eddy`; triage findings; route fixes.

## Gates
- **Lean gate:** the first Ralph packet scaffolds + pins the Lean project so `lake build` runs; no Lean result is accepted until it builds from clean.
- **Reproduce-before-extend:** standard DESI DR2 contours must be reproduced before any Six Birds machinery is added (idea.md §6 Exp 1).
- **Deliverables must be tracked (non-ignored) files.** The authoritative change evidence (the manifest hash delta) only sees non-ignored files. So any artifact that must be reviewed — results tables, figures, generated data manifests — must NOT be gitignored. Ignored paths (`ops/runs/`, `.lake/`, large data caches) are never accepted as deliverables; if an agent cites one as a result, that's a FIX. Keep `.gitignore` to genuinely re-creatable/local state.

## Recovery (thread continuity)
Thread UUIDs are local; rollouts under `~/.codex/sessions` may be absent on another machine/user or after cleanup. If a dispatch aborts with **RESUME MISMATCH** or the session can't resume: delete the stale `threads/.codex_thread_id_<role>`, re-bootstrap that role, and replay context by pointing it at the committed manifests under `dispatches/<role>/` and `packages/` (and the relevant repo artifacts). Continuity of *project state* lives in those committed manifests + the repo, not in the codex session.
