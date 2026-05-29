# Six Birds — Dark Energy as Closure: Plan Index

**Program.** Dark Energy as Closure — a Six Birds resolution of the cosmological paradoxes. The thesis: dark energy is the *shadow of a failed closure*; one low-rank residual `Ξ_cosmo(z, ℓ, p)` casts many shadows (cosmological constant, Hubble tension, DESI `w(z)`, distance duality, phantom crossing, `S₈`, coincidence, interacting dark energy, modified gravity). See `00-overview.md` §3 for the corrected nine-paradox-to-one-residual shadow map.

**Status:** **PLAN COMPLETE; implementation not started.**

> **What this directory is.** A complete, implementation-ready *blueprint* to be **executed LATER by a separate codex-driven apparatus**. Nothing here is run, built, fit, or proved now. No experiment is executed, no external agent is invoked, no memory store is written, and the `ops/` dispatch harness is not used. Every plan file operationalizes its qualitative goals into concrete, pre-registered, quantitative pass/fail gates so the downstream executor can run experiments E0–E8, the formal-math track, and the Lean track without ambiguity. The single authoritative reference for datasets, software stack, determinism standards, AOR vocabulary, and program-level gates is `GROUNDING_BRIEF.md` (in this directory); every plan file is consistent with it.

---

## How to read this

1. **Start at [`00-overview.md`](00-overview.md).** It states the thesis, defines the closure package and the four measurable residuals (`δ_p`, `RM_p`, `LG_{p,q}`, `PPD_{p→q}`), fixes the scope of this phase, and gives the definition of done. Read `GROUNDING_BRIEF.md` alongside it.
2. **Read the foundation files in order: `01` → `05`.** Repo structure, environment, data, the locked math, then the Lean mechanization. These are the *enabling artifacts* every experiment depends on.
3. **Read the experiments `E0` → `E8` in sequence.** They are gated: reproduce before you reinterpret, and **no `Ξ_cosmo` object exists anywhere until the E1 reproduction gate (E1-A) passes**. `E8` is strictly last.
4. **Use `06`–`10` as cross-cutting contracts:** the deliverable inventory, the consolidated gate register, the execution DAG, the risk register, and the execution mapping.
5. **The make-or-break gate** is cross-experiment coherence: one `Ξ_cosmo` reused across E1–E7 with cross-amplitudes within tolerance (see `00-overview.md` §6.4, `07-pass-fail-gates.md`). The single program-deciding gate is `G-E8-OOS-DECISIVE` (out-of-sample win).

---

## Table of contents

### Foundation

| File | One-line description |
|------|----------------------|
| [`GROUNDING_BRIEF.md`](GROUNDING_BRIEF.md) | The authoritative shared source of truth (datasets + handles, software stack, determinism standards, AOR vocabulary, program-level gates). Every other plan file is consistent with it; experiment files reference it as `../GROUNDING_BRIEF.md`. |
| [`REGISTRY.md`](REGISTRY.md) | The single machine-checkable source of truth for cross-cutting conventions (canonical AOR status enum, experiment terminal states, E1–E7 coherence-ledger membership, the gate-ID namespacing scheme, locked claim grades, `XiToy` vs `Ξ_cosmo` naming, artifact authority, and the E8 win/tie/fail definitions); where any file disagrees, the registry wins, and `tests/test_registry.py` lints committed artifacts against it. |
| [`CONTRACT_HARDENING_ADDENDUM.md`](CONTRACT_HARDENING_ADDENDUM.md) | LOCKED peer-contract closing the final-review under-specifications: the per-probe **observable dictionary** and explicit per-sector **Schur realization** (§1–§2); **theoretical-vs-empirical** residual estimators (§3); the **three P4 certificates** — native-currency positivity (P-dens) ∧ rewrite/adequacy positivity (P-adeq) ∧ spectral stability (S-stab), pairwise *not* equivalent (§4); the **Hubble bridge-map / holonomy** transport state-vector + loop eligibility (§5); the **canonical formulas & thresholds index** (`w_eff` sign, IDE `(1+w)`, E2 20%/50%, OOS-tie, P1 (H-faithful); §6); the dimensionless **coherence-amplitude** normalization + 3×/10×/30× sensitivity (§7); and the execution-contract **patch ledger** (§8). Where a file disagrees on these items, this addendum wins (REGISTRY wins over both on items it also covers). |
| [`00-overview.md`](00-overview.md) | Master conceptual overview and entry point: thesis, closure package, four residuals, minimal `Ξ` ansatz, Hubble readout/holonomy/lawful-plurality, propositions P1–P4 (anchored to Foundations-IV F2/F4/F9/F11), AOR vocabulary, scope, and the definition of done with quantitative gates. |
| [`01-repo-structure.md`](01-repo-structure.md) | Implementation repository layout and conventions: the `sbt_cosmo/` package mapped 1:1 onto the closure-carrier objects, the `lean/`, `data/`, `experiments/E0–E8`, `results/`, `configs/`, `tests/` trees, determinism/reproduce-without-rerun rules, tracked-vs-ignored policy, and structural gates G-REPO-1..16. |
| [`02-environment-and-deps.md`](02-environment-and-deps.md) | Software-environment and dependency blueprint: pinned stack (Python 3.11, cobaya, CLASS+CAMB, pyccl/CCL, PolyChord, getdist/arviz, Lean 4 v4.28.0 + mathlib), lockfile strategy, build-footgun checklist, per-experiment compute budget, CI tiers T0–T5, and environment gates G-ENV-1..9. |
| [`03-data-acquisition.md`](03-data-acquisition.md) | Definitive data-acquisition plan: every dataset across BAO/CMB/SN/weak-lensing/Hubble-sector with exact release, handle, product, format, loader spec, AOR-statused fallback, tracked provenance/checksum manifests, route-tagged Hubble loaders for E4, and gates G-DATA-1..9. |
| [`04-formal-foundations.md`](04-formal-foundations.md) | Locked mathematical specification: reconciliation of `Ξ_cosmo`/`Δ_SBT` with the Schur-complement adequacy residual, the carrier `𝔉_cosmo`, the low-rank ansatz and observable kernels `K_L/K_M/K_G/K_S/K_{r,ℓ}`, finite definitions of the four residuals, propositions P1–P4 + F9 with proof strategies, Hubble holonomy and lawful-plurality tests LP1–LP5, AOR strata/atlas, and the quantitative gate section. |
| [`05-lean-mechanization.md`](05-lean-mechanization.md) | Lean 4 mechanization plan: pinned toolchain and selective mathlib, `lakefile` and `SbtCosmo` module layout, seven mechanization targets T1–T7 (idempotence, route-mismatch, Schur PSD, F4 local-global, phantom-stable-readout witness, route-graph holonomy, no-unstatused-residual), three-tier disclosure discipline, trust-base allowlist, and gates L1–L9 (no `sorry`/`axiom`). |

### Experiments

| File | One-line description |
|------|----------------------|
| [`experiments/E0-synthetic-demos.md`](experiments/E0-synthetic-demos.md) | E0 data-free sanity layer: four deterministic synthetic demos (route-mismatch vs nonlinearity; null-Λ heterogeneous patch generator recovering apparent `Ω_Λ≈0.60`; positive/stable rewrite operator whose `w_eff` crosses −1 with no growing mode (stable effective readout) — the P4 witness; a 7×6 Hubble route-matrix recovery rehearsing E4 lawful plurality). |
| [`experiments/E1-desi-dr2-reproduction.md`](experiments/E1-desi-dr2-reproduction.md) | E1 blocking reproduction gate: from-scratch cobaya+CLASS recovery of ΛCDM/wCDM/w0waCDM over five data combinations matching published DESI DR2 contours and significances, then E1-B adds the first minimal SBT geometry `Ξ`. No `Ξ` object exists anywhere in the program until E1-A passes. |
| [`experiments/E2-distance-duality.md`](experiments/E2-distance-duality.md) | E2 distance duality as a local-global obstruction: CDDR audit `η(z)`, nested models M0/M1/M2 with the `Ξ`-gluing chart, Foundations-IV F4 four-status classification, the `w_a`-collapse adjudication, and the Afroz-Mukherjee vs Crossing-Statistics replication, with the M_B/r_d calibration degeneracy isolated. |
| [`experiments/E3-phantom-crossing.md`](experiments/E3-phantom-crossing.md) | E3 phantom crossing with stable readout (Proposition P4 centerpiece): Leg A constructs a positive, stable, audit-closed rewrite operator whose `w_eff` crosses −1 with a stable-readout certificate and Lean witness; Leg B fits the same `Ξ` to the DESI DR2 extended-DE `w(z)`, with Keeley false-positive and Dinda global-Bayesian controls. |
| [`experiments/E4-hubble-route-matrix.md`](experiments/E4-hubble-route-matrix.md) | E4 Hubble route matrix and holonomy (the idea.md UPDATE pillar): a 7-route × staging-column matrix `H₀^{(r,ℓ)}`, three nested models (null / per-route noise / single low-rank `Ξ`), Hubble holonomy `𝔥_γ` with a mandatory protocol-trap internalization control, and the five lawful-plurality tests. |
| [`experiments/E5-growth-staging-S8.md`](experiments/E5-growth-staging-S8.md) | E5 growth/staging sweep for the `S₈` chart: five staging axes across DES Y6/KiDS/HSC/DESI-RSD/CMB-lensing with a REAL physical CCL/pyccl forward model (no surrogate headline), the residual staging-slope fingerprint `∂Ξ/∂ℓ ≠ 0` charged only after systematics saturation, and the make-or-break coherence gate vs E1's geometry amplitude. |
| [`experiments/E6-ide-accounting.md`](experiments/E6-ide-accounting.md) | E6 interacting-dark-energy as accounting shadow: shows `Q_IDE` is the P6 continuity-equation chart of the single `Ξ_cosmo`, reproducing standard IDE/S-IDE fits first, establishing background equivalence, then deciding off-background via growth (`fσ8`, `S₈`, `μ0/Σ0`) and the Schur adequacy residual whether a real interaction is needed. |
| [`experiments/E7-modified-gravity.md`](experiments/E7-modified-gravity.md) | E7 modified gravity as another descent-repair chart (P1↔F2): uses DESI full-shape MG results (`μ0/Σ0` GR-consistent while `w0wa` background is preferred) to argue the anomaly lives in the closure layer, with a 6-model ladder, the central "where the modification lives" prediction, instability audits, and MG admitted as a lawful alternative repair. |
| [`experiments/E8-model-competition.md`](experiments/E8-model-competition.md) | E8 global model-competition synthesis (strictly last): six contenders (ΛCDM, w0waCDM, CDDR-only, IDE, MG, SBT-`Ξ`) fit on the same maximal joint dataset, judged by Bayesian evidence (PolyChord), the leave-one-probe-out out-of-sample battery, and posterior-predictive checks; the binding gate requires SBT-`Ξ` to WIN out-of-sample with the frozen, coherence-checked single residual. |

### Cross-cutting contracts

| File | One-line description |
|------|----------------------|
| [`06-results-manifest.md`](06-results-manifest.md) | Authoritative deliverable inventory: the single canonical list of EVERY result artifact (figures, tables, numbers, arrays, proofs, Lean declarations, manifests, ledgers) the implementation must produce, each with a committed path and an acceptance check that cites the governing gate verbatim. |
| [`07-pass-fail-gates.md`](07-pass-fail-gates.md) | Consolidated machine-readable register of every quantitative pass/fail gate (per-experiment, the five hard evidence standards STD-1..5, the pre-registered failure modes), giving gate ID, metric, threshold, governed experiments, and locked source; this is the contract `tests/test_gates.py` checks against each committed `summary.json`. |
| [`08-sequencing-dag.md`](08-sequencing-dag.md) | Dependency DAG and execution-order contract: foundation (F-layer) and experiment (E-layer) nodes, the `blocks`/`blockedBy` edges, the critical path, and the parallelism rule (sequential per track, at most 3 genuinely-independent tracks concurrent). |
| [`09-risk-register.md`](09-risk-register.md) | Risk register: enumerated program risks (data-access failure, backend mismatch, coherence-gate break, non-convergence, surrogate-backend weakness, ghost requirement, out-of-sample loss) with likelihood/impact, mitigations, the AOR-statused fallback path, and explicit honest-negative outcomes that are valid science rather than failure. |
| [`10-execution-mapping.md`](10-execution-mapping.md) | Execution mapping: how this blueprint maps onto the downstream codex-driven apparatus — the run-manifest contract, per-node dispatch order, materialization of the repo skeleton/environment/loaders/`sbt_cosmo` carriers, and the hand-off conventions linking each plan file to its executable units. |
| [`README.md`](README.md) | This file: the master index and orientation for the `plan/` directory. |

---

## Phase scope reminder

This phase delivers experiments **E0–E8**, the locked **math** (`04`), the **Lean** artifacts for P1–P4 (`05`), and the **committed results** (`06`). It explicitly EXCLUDES any manuscript/prose, the `ops/` dispatch harness, external agents, and any memory store. The terminal acceptance is: every `06` artifact exists at its committed path and passes its acceptance check; every `07` gate is recorded PASS or is an AOR-statused honest negative; the make-or-break coherence gate is green; and `G-E8-OOS-DECISIVE` is decided. See `00-overview.md` §8.

**Status line:** PLAN COMPLETE; implementation not started.
