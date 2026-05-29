# FINAL pre-implementation review — Six Birds: "Dark Energy as Closure"

You are an exceptionally careful reviewer. This is the **last gate before implementation begins**, so
review for **scientific/mathematical correctness, design soundness, and anything that slipped** — not
just internal consistency. You are reviewing a *blueprint* and its *execution harness*; nothing has
been run, built, fitted, or proved yet, and you should NOT run experiments or build anything. Judge
whether a competent codex-driven team could execute this and get *correct, decisive, honest* science.

You have been given a zip of the entire repository. Unzip it and read everything; grep freely.

## What's in the repo
- `idea.md` — the source research program (read the post-§10 **UPDATE** block on the Hubble readout
  field / holonomy / route matrix / lawful plurality).
- `docs/papers/` — the Six Birds Theory (SBT) corpus (48 papers + `INDEX.md`) the plan claims to
  ground in. Spot-check that the plan's use of SBT constructs matches the corpus.
- `plan/` — the implementation blueprint (24 files):
  - `REGISTRY.md` — the locked cross-cutting **contract** (read §1–§11 first; where any file disagrees,
    the registry wins).
  - `GROUNDING_BRIEF.md` — datasets, software stack, determinism, AOR vocabulary, compute budgets.
  - `00-overview … 10-execution-mapping`, `experiments/E0 … E8`.
- `ops/` — the **execution harness**: a manager (a Claude session) drives three persistent OpenAI
  *codex* sessions — **Cody** (coder), **Ralph** (mathematician + Lean), **Eddy** (reviewer) — via
  `bin/codex-dispatch.sh` (fail-closed), with committed per-packet/package manifests, a review rubric,
  a whole-tree Lean trust-scan, and a hermetic self-test. Review this too: it is what will *run* the plan.

The plan has survived many adversarial review rounds focused on contract propagation; assume the
propagation is clean and instead spend your effort on the deeper questions below.

## §1 — Scientific & mathematical correctness (spend the most effort here)
- **The thesis.** Is "dark energy = the shadow of a single low-rank closure residual `Ξ_cosmo`,
  reused across all probes" actually a coherent, falsifiable scientific claim, or does the
  coherence gate (one `Ξ` across E1–E7, cross-amplitudes within 10× & consistent sign) admit trivial
  satisfaction or impossible demands? Is the 10× band defensible?
- **The four residuals** (`δ_p`, `RM_p`, `LG_{p,q}`, `PPD_{p→q}`, `04` §4): are they well-posed, with a
  sensible metric `d`, and *actually computable* from the named data products? Any that are circular,
  ill-defined, or not estimable from what `03` provides?
- **Ξ_cosmo ↔ adequacy-residual (Schur complement) reconciliation** (`04` §1.2, conditional/numerical):
  is the per-sector `(L_p, D_p, C_p, transport, projection, covariance blocks)` construction real and
  consistent with the `Adequacy_Residuals` paper, or hand-waved? Does the `λ·complexity` argument truly
  defend against the "fudge function" critique?
- **The four propositions** (P1↔F2, P2↔F11, P3↔F4, P4): are the proof strategies valid? In particular —
  P3/F4 (CDDR as local–global gluing) and **P4** (the finite, positive, stable rewrite operator whose
  `w_eff` crosses −1 with "no growing mode"): is the construction actually achievable, and is "no
  growing mode / stable effective readout" a *meaningful, non-vacuous* claim given that ghost-absence
  is explicitly out of scope? Could P4 be true-but-trivial?
- **Hubble holonomy `𝔥_γ`** (the UPDATE pillar): is "transport a Hubble posterior around a loop of
  routes via declared bridges and compare" mathematically well-defined? Are the bridge maps `B_γ`
  specified concretely enough to compute, and is the LP1–LP5 set genuinely a strong test (E4)?
- **Experiment decisiveness**: for E1–E8, can each actually FAIL, and are the pass gates measuring what
  they claim (e.g. reproduce-before-extend in E1; the distance-duality adjudication in E2; the
  out-of-sample WIN in E8)? Flag any gate that is unfalsifiable, circular, or gameable.
- **Data & physics realism**: are the datasets (DESI DR2 BAO, Planck, Pantheon+/Union3/DES-SN5YR,
  DES Y6/KiDS/HSC, DESI RSD, CMB lensing, SH0ES/CCHP/TDCOSMO/sirens, CC_HZ) the right ones, used
  correctly, with sound fallbacks? Is reproducing the DESI DR2 `w0wa` significance feasible with the
  specified stack? Is the real-physical-CCL (non-surrogate) LSS plan in E5 realistic?

## §2 — Lean / formal-mechanization feasibility (`05`)
Are targets T1–T7 (+ T-E6) actually mechanizable as scoped, in reasonable effort? Is the mathlib-free
vs mathlib (T3 Schur, T5 stable-readout) split realistic? Does each Lean target prove something
*meaningful* (not a vacuous finite instance)? Is the trust-base/`no sorry/axiom` discipline sound, and
the "PhantomStableReadout states the finite stability property only" target non-trivial?

## §3 — Design & architecture (the plan AND the ops/ harness)
- **Harness:** is `ops/bin/codex-dispatch.sh` genuinely fail-closed and free of footguns (resume
  verification, timeout, sandbox, the forbidden-codex-memory check)? Are committed manifests + the
  review rubric + Eddy's package cadence a sound audit loop? Does the hermetic self-test actually guard
  the claims? Any single point of failure or way a bad packet slips through?
- **Plan architecture:** is the `08` dependency DAG correct (E1-A hard gate; E8 last; the ≤3-track
  concurrency)? Are gate IDs unique/resolvable and is the `tests/test_registry.py` lint spec (in `01`)
  sufficient to enforce the contract mechanically? Is the coder/mathematician/reviewer decomposition in
  `10` complete and unambiguous? Is the compute budget plausible?

## §4 — Contract-integrity sweep (confirm clean; it's been the recurring failure mode)
Grep-confirm zero real violations (a hit is OK only inside `REGISTRY.md`, the `01` lint spec, or an
explicit scoping/negation/literature mention): forbidden tokens (`PhantomNoGhost`, `no-ghost`,
`no_ghost`, `without ghost`, bare `G-T<n>`, bare `G-DECISIVE`, `G-E8-NOGHOST`); OOS weak-pass ("within
3%", "within 1.1×", "≤ best … within 3%", "win or tie") used as a PASS; E6 within-10%-of-IDE as a std-3
OOS win; `G-E4-DECISIVE` ≠ model-comp ∧ LP1–LP5; "identical chains"/"float64 tables" as a determinism
requirement; E8 universal `=PASS` dependency; F2 stated as three repairs / operator-rewrite as an F2
repair (must be P1 extension); `unstatused` as an accepted AOR status; noncanonical dataset keys.

## §5 — Completeness vs idea.md
Confirm coverage of: E0–E8 (incl. synthetic demos), P1–P4, the Schur reconciliation, the Hubble UPDATE
(LP1–LP5/holonomy/route matrix), Lean T1–T7, the five §10 evidence standards, and the precursor's two
admitted weaknesses (m≈0 background degeneracy; surrogate LSS backend). Flag anything missing or
under-specified for an executor.

## §6 — "What will bite during implementation" (your expert prediction)
Independent of the contract: where will this plan realistically stall, fail, or produce a
non-decisive result when actually executed? Consider data availability (e.g. full likelihoods vs
compressed fallbacks), the difficulty of implementing the real 3×2pt/CCL likelihood, MCMC/nested-
sampling convergence and compute, whether the coherence gate is too strict (forces failure) or too
loose (admits fudge), whether P4's construction is harder than scoped, and whether the Hubble
route-matrix has enough independent recomputable cells for a real holonomy. Rank by likelihood × impact.

## Output
Overall verdict — **READY-TO-EXECUTE / READY-WITH-NITS / NOT-READY**. Then:
1. Prioritized findings: severity (blocker/major/minor), `file:line`, the defect, the concrete fix —
   marking each as a real issue vs a scoping/lint-spec false positive.
2. The §4 sweep result (per pattern: clean / violations).
3. The §5 completeness table.
4. The §6 implementation-risk register (ranked).
5. The single highest-value improvement to make before kickoff.
