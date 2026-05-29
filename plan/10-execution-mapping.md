# Plan 10 — Execution Mapping: From Blueprints to Work Packets

> **Status:** PLANNING / BLUEPRINT. This file is the **bridge to the implementation phase**. It
> describes *how* the authored plan files (`plan/00`–`plan/08`, `plan/experiments/E0`–`E8`) become
> dispatchable **work packets** for a later codex/manager-driven execution, and *who* owns each kind
> of work (a **coder / mathematician / reviewer** split). It also fixes the **per-experiment
> acceptance-spec** every packet must carry and a **recommended dispatch order**.
>
> **Hard constraint (do not violate now).** This is a *mapping* only. It does **not** invoke codex,
> any manager, the `ops/` dispatch harness, any external agent, or any memory store, and it runs
> nothing. It specifies the contract the *later* execution process will consume. The decisions about
> *what runs when* are owned by `plan/08-sequencing-dag.md`; the decisions about *what counts as
> success* are owned by `plan/07-pass-fail-gates.md` and each `plan/experiments/E#.md` §gates section;
> the decisions about *what artifact must exist* are owned by `plan/06-results-manifest.md`. **This
> file owns only the role-split, the packet schema, the acceptance-spec authoring contract, and the
> dispatch grouping.** Where this file and a sibling disagree, the sibling wins on its owned subject
> and this file is corrected.
>
> **Authoritative upstream (consistency anchors):**
> - `plan/00-overview.md` — thesis, scope (build phase, no manuscript/ops/codex/memory), §6 gates,
>   §8 definition of done, §7 AOR carrier progression.
> - `plan/01-repo-structure.md` — package layout (`sbt_cosmo/`), the `experiments/<E#>/{config.yaml,
>   run.py,README.md,outputs/}` runner contract, tracked-vs-ignored policy, structural gates
>   G-REPO-1–G-REPO-16, the `tests/` suite.
> - `plan/02-environment-and-deps.md` — pinned stack, CI tiers T0–T5, gates G-ENV-1–G-ENV-9, lockfile
>   strategy.
> - `plan/03-data-acquisition.md` — `io/datasets.py` loaders, `data/manifests/*.json`, G-DATA gates.
> - `plan/04-formal-foundations.md` — the locked math (carrier, four residuals, ansatz, kernels,
>   metric `d`, P1–P4, AOR atlas), the `[T]`/`[C]`/`[E]` grade convention.
> - `plan/05-lean-mechanization.md` — Lean targets T1–T7, gates L1–L9, the trust base + disclosure.
> - `plan/06-results-manifest.md` — the canonical artifact inventory + acceptance checks per artifact.
> - `plan/07-pass-fail-gates.md` — the consolidated gate register (the single source of thresholds).
> - `plan/08-sequencing-dag.md` — the dependency DAG, phases, critical path, ≤3-track concurrency.
> - `GROUNDING_BRIEF.md` — datasets, stack, determinism, AOR vocabulary, compute budgets.
> - `idea.md` — the science (incl. the UPDATE block: Hubble readout field / holonomy / lawful
>   plurality).

---

## 0. What "execution mapping" means here

The planning phase produced **blueprints** (prose + schemas + gate tables). The implementation phase
will produce **artifacts** (code, Lean proofs, fitted results, ledgers) by *materializing* those
blueprints. The later execution apparatus is a **manager** that dispatches **work packets** to
**workers**, and a **reviewer** loop that accepts or rejects each delivered packet against a written
**acceptance-spec**.

This file defines the four objects that connect the two phases:

1. **The worker roles** (§1) — `coder`, `mathematician`, `reviewer` — and exactly which kind of work
   each owns, with a tie-break rule for boundary cases.
2. **The work-packet schema** (§2) — the standard envelope every dispatched unit carries (inputs,
   deliverables, acceptance-spec reference, gates, role, dependencies, determinism contract).
3. **The decomposition** (§3–§5) — how each plan file (foundation packets) and each experiment
   (experiment packets) splits into role-typed packets with named deliverables.
4. **The dispatch order** (§7) — a recommended packet-level ordering, *derived from* and *consistent
   with* the `plan/08` phase plan and the ≤3-track concurrency cap, expressed at packet granularity.

The mapping is **declarative**: it tells the later manager *what packets exist and how they relate*,
not *how to talk to codex*. No execution mechanics (process spawning, prompt construction, retry
policy, memory writes) are specified here — those belong to the implementation phase's own harness,
which is out of scope per `plan/00` §2.

---

## 1. The three worker roles

The work splits into three roles. The split is by **deliverable kind**, not by experiment: a single
experiment produces packets for all three roles. The reviewer is *never* the author of the artifact
it reviews (independence discipline, mirroring `Six_Birds_for_Neutrino_Mass`'s null/driven-control
separation and `AOR`'s disclosure-tier audit).

### 1.1 Coder (`role: coder`)

**Owns:** all Python code and pipelines under `sbt_cosmo/`, all `experiments/<E#>/{config.yaml,
run.py}`, the `io/`/`viz/`/`inference/` plumbing, the `tests/` suite, the environment/lockfiles,
the data loaders + manifests, and the *running* of every numerical experiment (MCMC, nested
sampling, CCL forward models) to produce committed result artifacts.

Coder deliverables (by plan-file authority):
- `sbt_cosmo/` submodules with the `plan/01` §3 module-boundary contract.
- `experiments/<E#>/` runner trees and their committed `outputs/` (manifest, `summary.json`,
  tables, figures, `posterior_summary.npz`, `aor_status.json`) per `plan/06`.
- `tests/` (`plan/01` §12), CI tiers T0–T5 (`plan/02` §5), `pyproject.toml` + lockfiles.
- `data/manifests/*.json`, `data/README.md`, `io/datasets.py` loaders + checksums (`plan/03`).
- All `[E]`-graded results (empirical, decided by data).

The coder is the role that *consumes compute*. The `plan/08` §4 critical path and `GROUNDING_BRIEF`
§IV compute budgets are coder-packet costs.

### 1.2 Mathematician (`role: mathematician`)

**Owns:** the locked math of `plan/04` (proofs, lemmas, the `[T]`/`[C]` grading), the entire Lean
track `lean/SbtCosmo/*.lean` + `lean/manifests/` (`plan/05`), and the *mathematical-correctness*
specification of the residual/kernel/audit definitions the coder implements. The mathematician
authors the **structural skeleton**; the coder authors the **numerical realization**; the two must be
**structurally aligned** (the `plan/05` gate **L8**: the Lean witness's carrier/grid/route labels are
structurally identical to the coder's E0 toy / E3 `w_eff` grid / E4 route registry).

Mathematician deliverables (by plan-file authority):
- `plan/04` proofs/lemmas as written (Reconciliation Lemma, P1–P4 strategies, kernel-linearity and
  stable-readout spectral arguments) — these are `proof`-type artifacts (`plan/06` §0.1).
- `lean/SbtCosmo/{Common,Idempotence,RouteMismatch,Schur,LocalGlobal,PhantomStableReadout,Holonomy,
  AORStatus}.lean` — targets **T1–T7** (`plan/05` §2) — `Lean`-type artifacts.
- `lean/manifests/{trust_base.txt,coverage_table.md}` and the axiom-audit discipline (`plan/05` §6).
- The mathematical acceptance criteria a coder formula must meet (e.g. "kernels linear in
  `(a₀,a₁,a₂)` to <1%", "metric `d` is covariance-whitened and PD-quotient-safe") — authored as the
  *math half* of each experiment's acceptance-spec (§6).
- All `[T]`-graded results (theorem-grade) and the `[C]`-graded conditional results' hypotheses.

The mathematician's track is **off the numerical critical path** (`plan/05` §0; `plan/08` §4) — Lean
builds in minutes — but it **gates** specific coder claims: E3's `G-E3-LEAN`, E8's stable-readout
certificate column, and the program-wide `G-PHASE-LEAN` / `G-PHASE-AOR` (F9) obligations.

### 1.3 Reviewer (`role: reviewer`)

**Owns:** the *acceptance decision* for every delivered packet, executed strictly against the
written acceptance-spec (§6) and the consolidated gate register (`plan/07`). The reviewer reads only
**committed artifacts** (the "reproduce-without-rerun" surface of `plan/01` §7 / G-REPO-8) and re-derives
every gate; it does not re-run expensive inference. The reviewer is the role that enforces the
discipline that makes a `FAIL` an acceptable scientific outcome **iff statused** (`plan/00` §8).

Reviewer deliverables (per packet):
- A **review verdict** record: `accepted | rejected | accepted-with-status`, citing the exact gate
  IDs evaluated (verbatim from `plan/07`) and their pass/fail and measured values.
- A **gate re-derivation** from the committed `summary.json` / tables / figures (mirrors
  `tests/test_gates.py`, `plan/01` §12), confirming each threshold without re-running.
- An **AOR-status check**: every surviving residual in the packet's `aor_status.json` is typed with
  exactly one base status; zero `unstatused` (G-REPO-10 / F9).
- A **coherence check** at the experiment-pair level when the packet touches the coherence ledger
  (the make-or-break `G-PHASE-COHERENCE`, `plan/07` §2.2): cross-amplitudes within 10× and consistent
  sign vs the already-committed ledger entries.
- A **scope/disclosure check** for math/Lean packets (every Lean target carries its `plan/05` §5
  scope disclaimer; no undisclosed narrowing; trust base within allowlist).

The reviewer must be a **distinct actor** from the packet's author. A coder-authored experiment is
reviewed by the reviewer role reading committed artifacts; a mathematician-authored Lean target is
reviewed by the reviewer role running the axiom audit + `lake build` receipt check (`plan/05` §6).

### 1.4 Role boundary tie-breaks (so no packet is unowned or double-owned)

| Boundary case | Owner | Rule |
|---|---|---|
| The `sbt_cosmo/xi/` residual + kernels + rewrite operator *implementation* | **coder** | code is coder; the *definition it must satisfy* is mathematician (a math acceptance criterion, §6) |
| The `sbt_cosmo/xi/stability.py` stable-readout / eigenvalue numerics | **coder** | numerical; but its *spectral-positivity correctness statement* is the mathematician's `plan/04` §7 / Lean T5 |
| `sbt_cosmo/aor/` status-ledger *code* | **coder** | code is coder; the *well-formedness law* (F9) is mathematician's Lean T7 + reviewer's check |
| `lean/` proofs | **mathematician** | always |
| `plan/04` proofs/lemmas (paper-grade) | **mathematician** | always |
| Deciding a delivered packet PASS/FAIL/statused | **reviewer** | always; reviewer ≠ author |
| Authoring the acceptance-spec text (§6) | **coder + mathematician jointly**, reviewer validates | each owns its half (numeric vs structural); reviewer confirms completeness before dispatch |
| Running an experiment and committing its `outputs/` | **coder** | always |
| The cross-experiment coherence verdict | **reviewer** | reviewer adjudicates; coder produces the ledger rows; mathematician owns the tolerance definition (`plan/04` §9.4) |

**Hard rule:** every packet in §3–§5 has exactly one `role` owner and at least one independent
`reviewer` pass before it is `accepted`. No packet is authored and accepted by the same actor.

---

## 2. The work-packet schema (the dispatch envelope)

Every dispatchable unit is a **work packet** — a self-contained, declarative JSON-able record the
later manager consumes. This schema is fixed here so all foundation/experiment decompositions below
share one shape. (This is a *spec*, not a runtime object; the manager materializes it later.)

```json
{
  "packet_id": "WP-E1-CODE",                 // unique; convention §2.1
  "title": "DESI DR2 reproduction pipeline + first geometry Xi",
  "role": "coder",                            // coder | mathematician | reviewer
  "owns_plan_files": ["plan/experiments/E1-desi-dr2-reproduction.md", "plan/01", "plan/03"],
  "inputs": {                                 // artifacts/files that must exist before start
    "blockedBy_packets": ["WP-FND-PKG", "WP-FND-DATA", "WP-FND-MATH"],
    "datasets": ["DESI_DR2_BAO", "PLANCK_2018", "PANTHEON_PLUS", "UNION3", "DES_SN5YR"],
    "reads_artifacts": ["data/manifests/*.json", "sbt_cosmo/xi/*"]
  },
  "deliverables": [                           // exact committed paths (from plan/06)
    "experiments/E1_desi_dr2_repro/{config.yaml,run.py}",
    "runs/E1/<run_id>/{manifest.json,summary.json,aor_ledger.json}",
    "results/tables/E1_{parameters,w0wa,significance,chi2_blocks}.csv",
    "results/xi_cosmo_coherence.csv (E1-B rows)"
  ],
  "acceptance_spec": "plan/10 §6 + acceptance-specs/E1.md (authored before dispatch)",
  "gates": ["G-E1-REPRO-*", "G-E1-SBT-*", "G-PHASE-LCDM", "G-PHASE-W0WA", "STD-1", "STD-3"],
  "blocking": true,                           // is this a BLOCKING packet (plan/07 semantics)?
  "determinism": {"seeded": true, "likelihood_bitwise": true, "summary_tol": "1e-12 scalar", "chains": "statistical-equivalence (R̂<1.01, ESS, means/cov within MC error) — NOT bitwise"},
  "compute_budget": "12-24 h, 32 CPU (GROUNDING_BRIEF §IV w0wa row)",
  "phase": "1 (E1-A) then 1.5 (E1-B)",        // from plan/08 phase plan
  "reviewer_packet": "WP-E1-REVIEW",          // the independent acceptance packet
  "on_fail": "see plan/08 §9 propagation (E1-A failure halts the program)"
}
```

### 2.1 Packet ID convention

- Foundation packets: `WP-FND-<DOMAIN>` (e.g. `WP-FND-PKG`, `WP-FND-ENV`, `WP-FND-DATA`,
  `WP-FND-MATH`, `WP-FND-LEAN`, `WP-FND-CI`).
- Experiment packets: `WP-<E#>-<ROLE-TAG>` where `ROLE-TAG ∈ {CODE, MATH, LEAN, REVIEW}`
  (e.g. `WP-E3-CODE`, `WP-E3-LEAN`, `WP-E3-REVIEW`). An experiment with no Lean obligation omits the
  `LEAN` packet; one with a paper-proof obligation keeps a `MATH` packet distinct from `LEAN`.
- Coherence/synthesis packets: `WP-COHERENCE`, `WP-E8-CODE`, `WP-E8-REVIEW`.

### 2.2 Packet invariants (the manager must enforce these; this file only declares them)

- **Single owner, independent review.** One `role`; a distinct `reviewer_packet` (§1.3).
- **Edge fidelity.** Every `blockedBy_packets` edge maps to a `blockedBy` edge in the owning plan
  file — *no invented edges* (the `plan/08` S2 gate, lifted to packet granularity).
- **Acceptance-spec exists before dispatch.** A packet may not be dispatched until its
  `acceptance_spec` (§6) is authored and reviewer-validated for completeness.
- **Determinism contract.** Every coder packet that runs inference records seeds + a manifest and
  reproduces the **likelihood/forward-model evaluations bitwise** and the **committed summaries to a
  stated tolerance**; MCMC/PolyChord chains are validated by **statistical equivalence** (`R̂<1.01`,
  ESS, means/cov within MC error), NOT bitwise across environments (`plan/01` G-REPO-4; `plan/02`
  G-ENV-3; REGISTRY §11.6).
- **Reproduce-without-rerun.** Every coder packet commits the artifacts the reviewer needs to
  re-derive all gates without re-running (`plan/01` G-REPO-8; `plan/06` §0.2).

---

## 3. Foundation packets (materializing `plan/00`–`plan/05`, `plan/02` CI)

The foundation layer (`plan/08` §2.1) becomes the following packets. These produce no experiment
results; they stand up the repo, environment, data, math, and Lean scaffolds that every experiment
packet depends on. They map to `plan/08` **Phase 0** (3-way parallel: env / data / math+Lean).

| Packet | Role | Owns plan files | Key deliverables | Exit gates | Reviewer |
|---|---|---|---|---|---|
| `WP-FND-PKG` | coder | `plan/01` | `sbt_cosmo/` skeleton with §3 module boundaries; `experiments/<E#>/` trees; `results/`, `configs/`, `tests/` skeleton; `.gitignore`; `pyproject.toml` | G-REPO-1 (installs), G-REPO-2 (layering), G-REPO-3 (single Ξ source), G-REPO-5 (no unseeded RNG), G-REPO-16 (naming) | `WP-FND-PKG-REVIEW` |
| `WP-FND-ENV` | coder | `plan/02` | `environment.yml`, `conda-lock.yml`, `requirements.lock.txt`, CLASS/classy + CAMB build, cobaya likelihood provisioning, container digest | `plan/02` G-ENV-1–G-ENV-9 (esp. **G-ENV-2 CLASS↔CAMB ≤0.1%/0.2%**, **G-ENV-4 pyccl↔CLASS <1%/0.5%**) | `WP-FND-ENV-REVIEW` |
| `WP-FND-DATA` | coder | `plan/03` | `io/datasets.py` loaders → `ProbeData`; `data/manifests/*.json` + checksums; `data/README.md`; route-tagged Hubble posteriors + `route_matrix.json` | G-DATA-1..9 (covariance PD, catalog complete, reproduce-before-rewrite, route-tagged, no-unstatused fallback) | `WP-FND-DATA-REVIEW` |
| `WP-FND-MATH` | mathematician | `plan/04` | locked carrier + four residuals + ansatz + kernels `K_L/K_M/K_G/K_S/K_{r,ℓ}` + metric `d`; Reconciliation Lemma; P1–P4 strategies graded `[T]`/`[C]`/`[E]` | `plan/04` §9: Schur sanity (min eig ≥ −1e-8), kernel linearity <1%, rank ceiling ≤ ΛCDM+3 / ≤5–7 | `WP-FND-MATH-REVIEW` |
| `WP-FND-LEAN` | mathematician | `plan/05` | `lean/` project: toolchain v4.28.0, `lakefile.lean`, pinned `lake-manifest.json`, `Common.lean` + T1–T7 module stubs, `manifests/{trust_base.txt,coverage_table.md}` | L1 (build green), L2 (zero sorry), L3 (zero escapes), L4 (trust-base closure), L7 (disclosure) | `WP-FND-LEAN-REVIEW` |
| `WP-FND-CI` | coder | `plan/01` §12, `plan/02` §5 | `tests/` suite (layering, determinism, seeding, manifest-schema, gates, xi-single-source, audits-contract, naming); CI tiers T0–T5 fail-closed | `plan/01` G-REPO-1–G-REPO-16 wired; `plan/02` CI T0–T5 budgets | `WP-FND-CI-REVIEW` |

> **Foundation independence (3-way parallel, `plan/08` Phase 0).** `WP-FND-ENV` (env),
> `WP-FND-DATA` (data), and `{WP-FND-MATH, WP-FND-LEAN}` (math+Lean) touch disjoint artifact domains
> and may run concurrently. `WP-FND-PKG` is the common prerequisite for all of them (the skeleton must
> exist first) and `WP-FND-CI` follows `WP-FND-PKG`+`WP-FND-ENV`. **Barrier:** no experiment packet
> starts until the foundation packets it depends on are `accepted`.

---

## 4. Experiment packets (the role-split of each E0–E8)

Each experiment splits into a **coder** packet (always), an optional **mathematician/Lean** packet
(when the experiment carries a `plan/05` target or a `plan/04` proof obligation), and a **reviewer**
packet (always, independent). The table below gives, per experiment: the packet set, the owning
experiment plan file, the headline gates (verbatim IDs from `plan/07` / the `E#.md` files), the Lean
target if any, and the `plan/08` phase. Thresholds are **not** restated here (single source of truth =
`plan/07` + the `E#.md`); only the **mapping** is.

| Exp | Coder packet | Math/Lean packet | Reviewer packet | Headline gates (IDs, from plan/07) | Lean target | Phase (plan/08) |
|---|---|---|---|---|---|---|
| **E0** | `WP-E0-CODE` (4 deterministic toys; route rehearsal; stable-readout witness) | `WP-E0-LEAN` (optional: RouteMismatch T2 anchor + Toy-3 finite stability witness) | `WP-E0-REVIEW` | G-E0-1.2/G-E0-1.3/G-E0-1.5, G-E0-2.4/G-E0-2.5/G-E0-2.7, G-E0-3.1/G-E0-3.3/G-E0-3.4, G-E0-4.1/G-E0-4.2/G-E0-4.3/G-E0-4.5/G-E0-4.6, G-E0-0.1–G-E0-0.4 | T2 (anchor), T5 (witness, shared with E3) | 1 (∥ E1-A) |
| **E1** | `WP-E1-CODE` (E1-A repro **BLOCKING**, then E1-B first geometry Ξ) | — (kernels from `WP-FND-MATH`; no new proof) | `WP-E1-REVIEW` | G-E1-REPRO-* (BLOCKING), G-E1-SBT-FIT/OOS/DUAL, G-PHASE-LCDM/W0WA, STD-1, STD-3 | — | 1 (E1-A), 1.5 (E1-B) |
| **E2** | `WP-E2-CODE` (CDDR η(z); M0/M1/M2/M1+2/M_AM; F_collapse) | `WP-E2-LEAN` (T4 numerical η(z) status witness, scaffold) | `WP-E2-REVIEW` | G-E2-REPRO, G-E2-CALIB, F4-status, G-E2-OOS/BIC/SHAPE/RANK, **G-E2-COHERE** | T4 (LocalGlobal, P3) | 2 (∥ E5) |
| **E3** | `WP-E3-CODE` (Leg A construct stable-readout operator; Leg B data fit; stability audit) | `WP-E3-LEAN` (**T5 full finite witness**, P4; complete proof) | `WP-E3-REVIEW` | **G-E3-CONSTRUCT**, **G-E3-LEAN**, G-E3-REPRO/DATA/ZC-STAB/FALSEPOS/BAYES/OOS/RANK, **G-E3-COHERE** | T5 (PhantomStableReadout, P4) | 3a |
| **E4** | `WP-E4-CODE` (route matrix; 3 nested models; holonomy 𝔥_γ; LP1–LP5) | `WP-E4-LEAN` (T6 finite route-graph holonomy nonzero residue) | `WP-E4-REVIEW` | G-E4-0a/G-E4-0b, G-E4-1, G-E4-2, G-E4-2-permutation, G-E4-T1/T2/T3/T4/T5, **G-E4-DECISIVE** (= model-comp ∧ LP1–LP5), `G-E4-ROUTEREUSE` (weaker `[E]`/partial) | T6 (Holonomy) | 3a |
| **E5** | `WP-E5-CODE` (real CCL 3×2pt/RSD; 5 staging axes; G0/G1/G2/G_sys/G_MG ladder) | — (uses `WP-FND-MATH` K_G/K_S; no new proof) | `WP-E5-REVIEW` | G-E5-BACKEND/REPRO/NOSURR/RANK/KERNEL, D_scale verdict, G-E5-OOS/DUAL/BIC, **G-E5-COHERE** | — | 2 (∥ E2) |
| **E6** | `WP-E6-CODE` (E6-A IDE repro; E6-B Q↔Q_Ξ background; E6-C growth + leave-one-out PPD) | `WP-E6-LEAN` (T-E6 continuity chart-map soundness witness) | `WP-E6-REVIEW` | G-E6-REPRO-*, G-E6-BG-Q/HZ/SPAN/LEAN, G-E6-GROWTH-RED/INT, G-E6-PPD/MUSIGMA, **G-E6-COH**, G-E6-RANK | T-E6 (`IdeChartMap.lean`) | 3a |
| **E7** | `WP-E7-CODE` (6-model MG ladder; (μ,Σ) prediction; F2 shared-obstruction; MG stability) | — (reuses E3 `PhantomStableReadout` machinery; F2 from `WP-FND-MATH`) | `WP-E7-REVIEW` | G-E7-BACKEND/REPRO, **G-E7-MUSIGMA**, G-E7-F2/NECESSITY/STABILITY, **G-E7-COHERE**, G-E7-OOS/RANK/KERNEL/COV | (reuses T5) | 3b (after E3) |
| **E8** | `WP-E8-CODE` (6-contender competition; PolyChord evidence; OOS battery L1–L5; PPC) | — (no new proof; consumes E3 stable-readout cert) | `WP-E8-REVIEW` | **G-E8-OOS-DECISIVE** (std-3), G-E8-EVID/BIC/RANK/FROZEN/STABLEREADOUT/REPRO/PPC/CONV/COV, **G-E8-COHERENCE**, G-E8-DEPS/DET, G-E8-STAGING/PLURALITY | — | 4 (last, single-track) |

> **The standalone coherence packet.** Beyond each experiment's own `G-*-COHERE`, there is one
> program-level `WP-COHERENCE` (role `reviewer`) that re-asserts the make-or-break
> `G-PHASE-COHERENCE` across the *committed* `results/xi_cosmo_coherence.csv` after each experiment
> appends, and a final assertion inside `WP-E8-REVIEW`. Its early-stop authority is the `plan/08` S8
> rule: the **first** >10×/sign-flip inconsistency aborts the phase (statused), so this reviewer
> packet is *re-invoked* after E1-B, E2, E5, E3, E4, E6, E7 each commit their ledger row — not only at
> E8.

---

## 5. Cross-cutting packets (not owned by a single experiment)

| Packet | Role | Scope | Deliverables | Gates |
|---|---|---|---|---|
| `WP-COHERENCE` | reviewer | the shared-Ξ make-or-break check, re-run after every ledger append | coherence verdict per pair; early-stop trigger | `G-PHASE-COHERENCE` (make-or-break), `plan/08` S8 |
| `WP-AOR-MASTER` | reviewer | consolidate `aor_status_table.csv` rows into `results/tables/aor_status_master.csv`; assert zero `unstatused` | the AOR master ledger | `G-PHASE-AOR` (F9), carrier reaches AOR target |
| `WP-SHADOW-MAP` | coder | populate `results/tables/one_residual_nine_shadows.csv` with measured per-row residuals (the §3-of-`plan/00` map) | the shadow-map table | tied to E8 acceptance |
| `WP-DETERMINISM-AUDIT` | reviewer | rerun ≥1 experiment from its manifest; confirm likelihood/forward-model bitwise reproduction + committed summaries to tolerance; chains by statistical equivalence (not bitwise) | determinism receipt | `G-PHASE-DET` (`plan/00` §8 item 8) |
| `WP-LEAN-AXIOM-AUDIT` | reviewer | run the `#print axioms` closure + trust-base diff across T1–T7 | axiom-audit pass record | L4 (trust-base), L2/L3 (no escapes) |

---

## 6. The per-experiment acceptance-spec (what each packet must author *before* dispatch)

The **acceptance-spec** is the written contract the reviewer uses to accept/reject a delivered
packet. One acceptance-spec per experiment (and one per foundation packet) is authored as a small
tracked file — proposed path **`acceptance-specs/<E#>.md`** (and `acceptance-specs/FND-<domain>.md`)
under the repo, *authored in the implementation phase, not now*. This section fixes its **mandatory
sections** so that every spec is uniform and reviewer-checkable. It is the operational lift of
`plan/06` (artifact inventory) + `plan/07` (gate register) into a per-packet checklist.

Each acceptance-spec **must** contain these sections:

1. **Scope & charter.** One sentence; a link to the owning `plan/experiments/E#.md` and the relevant
   `idea.md` §/UPDATE-block anchor. States what the packet does and explicitly what it does **not**
   claim (the scope disclaimer; for Lean packets this is the `plan/05` §5 disclaimer verbatim).
2. **Inputs / prerequisites.** The exact `blockedBy_packets` (must equal the `E#.md` `blockedBy`),
   dataset keys (from `plan/03`), upstream artifacts read (e.g. `results/xi_cosmo_coherence.csv`
   rows). Reviewer checks all exist + are `accepted` before the packet was dispatched (edge fidelity,
   `plan/08` S2/S4).
3. **Deliverable manifest.** The exact committed paths the packet must produce, copied from
   `plan/06`'s inventory rows for that experiment, each with its `plan/06` acceptance check. Reviewer
   checks every path exists, is schema/format-valid, and is **tracked** (not under a gitignored
   `chains/`).
4. **Gate table (the pass/fail contract).** Every gate ID **verbatim from `plan/07`** that governs
   this packet, with: metric, threshold, grade `[E]/[T]/[C]`, BLOCKING flag, and the committed
   artifact key in `summary.json` where its scalar lives. Reviewer re-derives each from committed
   artifacts (reproduce-without-rerun). **No threshold is restated with a new number** — it is cited.
5. **Reproduction floor (STD-1).** The specific published-baseline recovery that must pass **before**
   any Ξ object is added (e.g. E1's `G-E1-REPRO-*`; E2/E3/E5/E6/E7 reproduction legs). This section
   is the explicit "reproduce-before-reinterpret" gate for the packet.
6. **Coherence obligation.** Which `Ξ_cosmo` amplitudes/kernels this packet writes to the ledger, and
   the `G-PHASE-COHERENCE` tolerance (10×, consistent sign) it must satisfy against already-committed
   rows. Reviewer runs the `WP-COHERENCE` check. (Make-or-break.)
7. **Math/structural alignment (for packets with a Lean/math counterpart).** The structural-alignment
   obligation (`plan/05` L8): the coder's carrier/grid/route labels must match the mathematician's
   Lean witness. Names the paired `WP-<E#>-LEAN`/`WP-<E#>-MATH` packet and the `#eval`/witness-node
   consistency check (e.g. E3's "`#eval` witness matches Python `z_c`/sign at witness node").
8. **AOR statusing.** The set of residuals this packet must type, and the requirement that each
   carries exactly one base status with zero `unstatused` (F9 / G-REPO-10). Includes the **pre-registered
   honest-negative verdicts** (e.g. E2's "rewrite-residual verdict", E6's "out_of_scope real
   interaction", E7's "MG not preferred is a logged outcome, not a failure") so the reviewer can
   distinguish a *valid statused negative* from a *program failure*.
9. **Determinism contract.** Seeds policy, manifest schema reference, and the rerun rule (likelihood/forward-model bitwise; committed summaries to tolerance; MCMC/PolyChord chains by statistical equivalence, not bitwise)
   (`plan/01` G-REPO-4; `plan/02` G-ENV-3). For ≥1 packet per phase, the `WP-DETERMINISM-AUDIT` reruns it.
10. **Failure-propagation note.** What a failure of each BLOCKING gate does to the schedule, copied
    from `plan/08` §9 (e.g. "E1-A failure halts the program", "coherence violation fails the phase",
    "individual E4/E6/E7 gate failure degrades to a statused E8 row").

> **Authoring ownership of the spec.** Sections 1–6, 9 are coder+reviewer; sections 7 is
> mathematician; section 8, 10 are reviewer-validated. The spec is **complete** (all 10 sections
> present, every gate ID resolvable to `plan/07`, every deliverable path resolvable to `plan/06`)
> **before** the packet is dispatched — this completeness check is itself a reviewer gate (§1.3).

### 6.1 Acceptance-spec completeness gates (this file's own gates — see §8)

A per-experiment acceptance-spec is **complete** iff: all 10 sections present (A-SPEC-1); every gate
ID in §4 of the spec appears verbatim in `plan/07` (A-SPEC-2); every deliverable path appears in
`plan/06` (A-SPEC-3); `blockedBy_packets` equals the `E#.md` `blockedBy` (A-SPEC-4); the coherence
and AOR obligations are present (A-SPEC-5). These are checked **before** dispatch.

---

## 7. Recommended dispatch order (packet granularity)

This is the recommended order the later manager should dispatch packets in. It is **derived from and
consistent with** `plan/08` (the phase plan, the ≤3-track cap, the critical path, the
failure-propagation rules). `plan/08` owns ordering; this section lifts it to *packet* granularity
and adds the role-split. Where this and `plan/08` differ, `plan/08` wins.

> **Concurrency rule (from `plan/08` §1, §8):** at most **3 tracks** active at any instant; two
> packets may co-run only if there is no `blockedBy` edge between them and they do not write the same
> file. The shared write surfaces (`results/xi_cosmo_coherence.csv`,
> `results/coherence_ledger/<E>.json`, `results/aor_status_table.csv`) must be appended with
> per-experiment keys or the writers serialized.

**Dispatch wave 0 — foundation (3-way parallel after `WP-FND-PKG`).**
1. `WP-FND-PKG` (coder) — skeleton; the common prerequisite. Then concurrently (≤3):
2. `WP-FND-ENV` (coder), `WP-FND-DATA` (coder), `{WP-FND-MATH (math) → WP-FND-LEAN (math)}`.
3. `WP-FND-CI` (coder) after PKG+ENV. Each foundation packet's reviewer packet follows its author.
   **Barrier:** all foundation reviewer packets `accepted` (esp. `plan/02` **G-ENV-2** backend-agreement
   and **G-ENV-4** pyccl↔CLASS) before any experiment packet — a `G-ENV-2` failure *halts* (no physical
   Ξ claim until tooling route-mismatch is statused, `plan/08` §9).

**Dispatch wave 1 — sanity + the program gate (2-way parallel).**
4. `WP-E0-CODE` (coder, data-free) ∥ `WP-E1-CODE/E1-A` (coder, **BLOCKING reproduction gate**).
   Their reviewer packets follow. `WP-E0-LEAN` (math) runs alongside (minutes).
   **Hard barrier — the program gate:** `WP-E1-REVIEW` must accept E1-A (DESI DR2 reproduced) before
   **anything** downstream. If E1-A fails, **halt**: no Ξ is ever instantiated (`plan/08` §9; `plan/00`
   §6.1). Only after acceptance does `WP-E1-CODE/E1-B` (first geometry Ξ → `xi_cosmo_coherence.csv`)
   run, immediately followed by `WP-COHERENCE` (reviewer) seeding the ledger.

**Dispatch wave 2 — the E2/E5 fan-out (2-way parallel).**
5. `WP-E2-CODE` (coder) ∥ `WP-E5-CODE` (coder). E5 is the schedule pinch point (gates E4/E6/E7,
   `plan/08` §4) and the most expensive non-E8 coder packet (real CCL backend) — **dispatch it first
   within the wave** and protect its compute. `WP-E2-LEAN` (math, T4) runs alongside. Their reviewer
   packets + a `WP-COHERENCE` re-check follow each ledger append (per-experiment keys E2.json/E5.json
   so concurrent appends do not race). **Barrier:** E5 accepted before wave 3.

**Dispatch wave 3a — repair-chart + Hubble (3-way parallel, the cap bites).**
6. `WP-E3-CODE` (coder) ∥ `WP-E4-CODE` (coder) ∥ `WP-E6-CODE` (coder), with their math/Lean packets
   `WP-E3-LEAN` (T5, the P4 centerpiece), `WP-E4-LEAN` (T6), `WP-E6-LEAN` (T-E6) running off the
   numerical critical path. E7 is **excluded** here (it needs E3's stable-readout machinery). Reviewer
   packets + `WP-COHERENCE` re-checks follow each. **Barrier:** E3 accepted (its stability/stable-readout
   certificate machinery exists) before E7.

**Dispatch wave 3b — modified gravity (after E3).**
7. `WP-E7-CODE` (coder), reusing the E3 `PhantomStableReadout` instability audit; `WP-E7-REVIEW` +
   `WP-COHERENCE`. May overlap the *tails* of E3/E4/E6 only if ≤3 tracks total and E3's stable-readout
   certificate is already committed. **Barrier:** every upstream experiment E1–E7 reaches a
   `terminal_state ∈ terminal_accepted = {PASS, ACCEPTED_NEGATIVE}` before E8 (per `REGISTRY` §2; a
   `BLOCKED`/`PROGRAM_FAIL` upstream means E8 cannot run — **not** universal `PASS`).

**Dispatch wave 4 — synthesis (single track, last).**
8. `WP-E8-CODE` (coder) — 6-contender competition, PolyChord evidence, OOS battery, PPC; **freeze Ξ
   from the coherence ledger (no re-tuning)**. Then the closing reviewer packets:
   `WP-E8-REVIEW` (incl. the final `G-E8-OOS-DECISIVE` and `G-E8-COHERENCE`), `WP-COHERENCE` (final
   assertion), `WP-AOR-MASTER` (F9, zero `unstatused`), `WP-SHADOW-MAP`, `WP-LEAN-AXIOM-AUDIT`,
   `WP-DETERMINISM-AUDIT`. E8 is **strictly single-track and strictly last** (`plan/08` §5 Phase 4);
   it is the heaviest node — co-schedule nothing with it.

### 7.1 One-line dispatch summary

```
WP-FND-PKG → {WP-FND-ENV ∥ WP-FND-DATA ∥ (WP-FND-MATH→WP-FND-LEAN)} → WP-FND-CI
→ {WP-E0-CODE ∥ WP-E1-CODE(E1-A = PROGRAM GATE)}        [halt if E1-A fails]
→ WP-E1-CODE(E1-B) → WP-COHERENCE(seed)
→ {WP-E2-CODE ∥ WP-E5-CODE}                              [E5 first; pinch point]
→ {WP-E3-CODE ∥ WP-E4-CODE ∥ WP-E6-CODE}                 [3-track cap]
→ WP-E7-CODE                                             [needs E3 stable-readout machinery]
→ WP-E8-CODE → {WP-E8-REVIEW, WP-COHERENCE(final), WP-AOR-MASTER, WP-SHADOW-MAP, audits}
```
(Each `WP-*-CODE`/`WP-*-MATH`/`WP-*-LEAN` is followed by its independent `WP-*-REVIEW`; coherence is
re-checked after every ledger append, not only at E8.)

### 7.2 Failure-propagation at packet level (lifted from `plan/08` §9)

| Failing packet/gate | Packet-level effect |
|---|---|
| `WP-FND-ENV` G-ENV-2 (backend disagreement) | **Halt.** No physical Ξ packet admissible until tooling route-mismatch statused. |
| `WP-FND-DATA` G-DATA-1 (a covariance not PD) | Quarantine that probe (`Σ†` on legal quotient) or status its dependent experiment `blocked`; downstream proceeds without it. |
| `WP-E1-CODE/E1-A` reproduction gate | **Program halt.** No Ξ packet (E1-B, E2–E8) dispatched. The single hardest barrier. |
| `WP-E2-CODE` gluing-reading "fails" | **Not** a program failure — pre-registered rewrite-residual verdict; E3/E4/E8 proceed. |
| `WP-E3-CODE`/`WP-E3-LEAN` construction/Lean/coherence/rank fails | **Program failure** (terminal `PROGRAM_FAIL`): the P4 stable-readout construction/witness/coherence did not close — E8 does **not** run (E3 not terminal-accepted). A *data-gate* negative (`G-E3-DATA` → `blocked`; `G-E3-FALSEPOS`/`G-E3-BAYES`) is instead a pre-registered `ACCEPTED_NEGATIVE`; E7 reuses the machinery; E8 records the statused negative. |
| any `WP-COHERENCE` >10×/sign-flip | **Make-or-break: abort the phase**, statused. First violation stops scheduling later experiment packets (`plan/08` S8). |
| `WP-E4/E6/E7-CODE` individual gate | Statused as a pre-registered `ACCEPTED_NEGATIVE` (a `terminal_accepted` state); E8 still runs (E8 depends on each upstream reaching `terminal_state ∈ terminal_accepted`, not universal `PASS` — `REGISTRY` §2). Feeds the competition matrix as a statused row. |
| `WP-E8-CODE` `G-E8-OOS-DECISIVE` (in-sample-only win) | Central claim **not** supported; recorded honestly; phase still "done" (audited-outcome definition). |

---

## 8. Pass/fail gates for THIS file (execution-mapping gates)

This file owns the role-split, the packet schema, the acceptance-spec contract, and the dispatch
grouping. A program build is **mapping-PASS** iff all hold (checked by the later manager + a CI lint;
declared, not run, here):

| # | Gate | Threshold / criterion | Checked by |
|---|---|---|---|
| M1 | **Total coverage** | every plan file (`plan/00`–`plan/08`) and every experiment E0–E8 maps to ≥1 packet; 0 unmapped plan files; 0 unmapped experiments | diff §3/§4/§5 vs the plan-file inventory |
| M2 | **Single owner** | every packet has exactly one `role ∈ {coder, mathematician, reviewer}`; 0 unowned, 0 double-owned (tie-breaks §1.4 resolve all boundary cases) | packet-schema lint |
| M3 | **Independent review** | every non-reviewer packet has a distinct `reviewer_packet`; reviewer ≠ author for every accepted packet | dispatch-log audit |
| M4 | **Edge fidelity** | every packet `blockedBy_packets` edge equals a declared `blockedBy` edge in the owning plan file; 0 invented, 0 dropped (lifts `plan/08` S2 to packets) | diff vs `blockedBy` lists |
| M5 | **Acceptance-spec completeness** | every packet has a complete acceptance-spec (§6.1 A-SPEC-1..5) authored and reviewer-validated **before** dispatch | reviewer pre-dispatch check |
| M6 | **Gate-ID resolvability** | every gate ID cited in any acceptance-spec resolves verbatim to a row in `plan/07`; **0 new thresholds invented** in any spec | grep §4 of each spec vs `plan/07` |
| M7 | **Deliverable resolvability** | every deliverable path in any packet resolves to a `plan/06` inventory row with an acceptance check | diff vs `plan/06` |
| M8 | **Dispatch order consistency** | the §7 order satisfies every `blockedBy` edge and the ≤3-track cap; it is a valid refinement of the `plan/08` topological order (`plan/08` §7) and never violates E1-A-gate / E5-before-{E4,E6,E7} / E3-before-E7 / E8-last | diff §7 vs `plan/08` §5/§7/§8 |
| M9 | **No execution side-effects from this file** | authoring/consuming this mapping invokes 0 of {codex, manager, `ops/`, external agent, memory store}; this file only declares | manual review (this is a planning artifact) |
| M10 | **Make-or-break wiring** | `WP-COHERENCE` is dispatched after **every** coherence-ledger append (not only at E8), with first-violation early-stop authority (`plan/08` S8) | dispatch-log audit |

---

## 9. Inputs, method, outputs of this plan

**Inputs:** `plan/00`–`plan/08` (role/scope/gates/sequencing), `plan/experiments/E0`–`E8`
(`blockedBy`/`blocks`, gate sections, deliverables), `plan/06` (artifact inventory + acceptance
checks), `plan/07` (consolidated gate register = single source of thresholds), `plan/08` (phases,
critical path, ≤3-track cap, failure propagation), `GROUNDING_BRIEF.md` (datasets/stack/
determinism/AOR/compute), `idea.md` (science + UPDATE block).

**Method:** define three deliverable-typed worker roles with a boundary tie-break table → fix a
single declarative work-packet schema → decompose each foundation plan file and each experiment into
role-typed packets with named committed deliverables and verbatim gate IDs → specify the mandatory
10-section per-experiment acceptance-spec (the reviewer's contract) → lift the `plan/08` phase plan to
packet granularity as a recommended dispatch order with the ≤3-track cap and failure propagation →
operationalize the whole as the M1–M10 mapping gates.

**Outputs of executing this plan (later, not now):** the later manager consumes §2 (packet schema),
§3–§5 (the packet set), §6 (acceptance-spec sections), §7 (dispatch order), enforces §8 (M1–M10), and
the implementation phase authors one `acceptance-specs/<E#>.md` per experiment + per foundation
domain. **No code, proof, experiment result, or dispatch is produced by this file.** It is the bridge
contract; the experiments themselves are defined in `plan/experiments/E#.md` and executed downstream.

---

## 10. One-paragraph executive summary for the manager

Split all implementation work into three deliverable-typed roles — **coder** (Python pipelines,
`sbt_cosmo/`, experiment runners, data loaders, CI, and all `[E]` results), **mathematician** (the
`plan/04` proofs and the `lean/` T1–T7 targets, all `[T]`/`[C]` results), and **reviewer** (the
independent accept/reject decision against a written acceptance-spec, reading only committed
artifacts). Wrap every dispatchable unit in the §2 packet schema (single owner, independent reviewer,
edge-fidelity, determinism, reproduce-without-rerun). Materialize the foundation packets first
(`WP-FND-PKG` then env/data/math+Lean three-up, then CI), gated by the CLASS↔CAMB and pyccl↔CLASS
agreement checks. Run **`WP-E0-CODE` ∥ `WP-E1-CODE/E1-A`** and **stop the world on E1-A** — if DESI
DR2 does not reproduce, no Ξ packet is ever dispatched. Then E1-B (first geometry Ξ), fan out to
**E2 ∥ E5** (E5 first, the pinch point), then **E3 ∥ E4 ∥ E6** (3-track cap), then **E7** (needs E3's
stable-readout machinery), then **E8 alone, last**. Re-run the make-or-break `WP-COHERENCE` reviewer packet
after every coherence-ledger append, abort the phase on the first >10×/sign-flip inconsistency, and
close with `WP-AOR-MASTER` (zero `unstatused`, F9), the shadow-map table, the Lean axiom audit, and a
determinism rerun. This file invokes none of that apparatus now; it only specifies the mapping.
