# REGISTRY — the single machine-checkable source of truth

This file resolves the cross-cutting conventions every other `plan/` file MUST conform to.
Where any file disagrees with this registry, **the registry wins**. A `tests/test_registry.py`
lint (specified in `01-repo-structure.md`) checks committed artifacts against these tables.

Authored after an external NOT-READY review of the plan to remove scientific over-claims and
24-author cross-file drift. Read alongside `GROUNDING_BRIEF.md` and **`CONTRACT_HARDENING_ADDENDUM.md`**
— the LOCKED peer-contract that pins the observable dictionary, per-sector Schur realization, the two
(non-equivalent) P4 certificates, the Hubble bridge maps, the canonical formulas/thresholds index, and
the coherence-amplitude normalization, closing a second review's under-specification findings.

---

## 1. AOR status vocabulary (canonical)

Every residual / claim carries **exactly one** status from this closed enum (from the AOR paper).

**Base (11):** `zero`, `budgeted`, `bridged`, `hidden`, `moduli`, `selected`, `probabilistic`,
`out_of_scope`, `nonclaim`, `blocked`, `approved_other`.
**Asymptotic (4):** `asymptotic_budgeted`, `summable`, `contractive`, `eventual_zero`.

- **`unstatused` is NOT a status.** It is a **validator-error sentinel**: any residual that ends a
  phase tagged `unstatused` is a **gate failure** (F9, No-Unstatused-Residual). Files must never list
  `unstatused` inside the accepted enum. Not-claiming something is represented by `nonclaim`, which IS
  a valid status.
- The Lean enum `SBTCosmo.AORStatus` contains the 15 valid statuses only; `unstatused` is modeled as
  the *absence* of a status (a validator error), not a constructor.

## 2. Experiment terminal states (`summary.json.terminal_state`)

Every experiment run resolves to exactly one terminal state:

| State | Meaning |
|---|---|
| `PASS` | All gates met; the SBT-positive result holds. |
| `ACCEPTED_NEGATIVE` | A pre-registered honest-negative outcome (e.g. E6 "real interaction needed", E2 "pure gluing", E5 "no staging fingerprint after systematics"). A valid scientific finding, fully statused. |
| `BLOCKED` | Could not run to a verdict (missing data/likelihood/dependency); statused `blocked`. |
| `PROGRAM_FAIL` | A make-or-break violation (failed E1-A reproduction, coherence break, or a **construction-level** required-ghost / no-stable-readout-witness — E3 `G-E3-CONSTRUCT`/`G-E3-LEAN`/`G-E3-COHERE`/`G-E3-RANK`). Halts the phase. A *data-gate* ghost-required outcome (E3 `G-E3-DATA`, "the data-preferred crossing requires a ghost") is instead terminal `ACCEPTED_NEGATIVE`, NOT `PROGRAM_FAIL`. |

**`terminal_accepted := {PASS, ACCEPTED_NEGATIVE}`.**

- **E8 dependency rule:** E8 depends on every upstream experiment being in `terminal_accepted` — **NOT**
  universal `PASS`. `BLOCKED`/`PROGRAM_FAIL` upstream means E8 cannot run.
- The old "every upstream `summary.json` = PASS" wording is **replaced** by "every upstream
  `terminal_state ∈ terminal_accepted`."

## 3. Coherence ledger membership (the make-or-break)

The single low-rank `Ξ_cosmo` is fit in **exactly these experiments**, whose amplitudes enter the
coherence ledger `results/xi_cosmo_coherence.csv`:

**Coherence members = { E1, E2, E3, E4, E5, E6, E7 }** (all seven that fit a real-data `Ξ`).

- **E0 is excluded** — it fits a *synthetic injected* `XiToy`, not `Ξ_cosmo` (see §6).
- **E8 is the judge, not a member** — it consumes the frozen ledger and never re-fits.
- Every file must state the membership as **E1–E7** (no variant that drops E4/E6 or adds E0/E8).
- Coherence criterion (locked): cross-amplitudes within **10×** and consistent sign; any pair
  violating it ⇒ `PROGRAM_FAIL` (gate `G-PHASE-COHERENCE`).

## 4. Gate-ID namespacing (no bare `G<n>`)

Bare `G0…G16` currently collide across scopes. Canonical rule: **every gate ID is namespaced by its
owning document**, and all references use the namespaced form. No bare `G<n>` may remain anywhere.

| Owning doc | Old form | Canonical form |
|---|---|---|
| `01-repo-structure.md` (structural gates) | `G1…G16` | `G-REPO-1 … G-REPO-16` |
| `02-environment-and-deps.md` (environment gates) | `G1…G9` | `G-ENV-1 … G-ENV-9` |
| `03-data-acquisition.md` | already `G-DATA-*` | keep |
| `04-formal-foundations.md` | mixed | `G-FORMAL-*` (rename any bare/`§9.x` gate) |
| `experiments/E0` | bare `G<n>` | `G-E0-<n>` |
| `experiments/E1–E8` | already `G-E1-*` … `G-E8-*` | keep; rename any stray bare `G0/G0b` (E4) → `G-E4-0/G-E4-0b` |

- Already-namespaced IDs are preserved verbatim: `G-E1-REPRO`, `G-E1-SBT`, `G-DATA-1`, `G-E5-NOSURR`,
  `G-E8-OOS`, `G-PHASE-COHERENCE`, etc.
- Other prefixes are already distinct and are KEPT as-is (no collision): Lean `L1…L9`, execution-mapping
  `M1…M10`, sequencing `S1…S10`, evidence standards `STD-1…STD-5`, acceptance-spec `A-SPEC-1…5`.
- **Model labels are NOT gates.** The staging/model-ladder tokens `G0, G1, G2, G_sys, G_MG` in E5/E7 and
  the nested-model labels `M0, M1, M2` (E2/E8) are MODEL identifiers — left verbatim and excluded from
  the no-bare-`G<n>` lint. Only gate IDs are namespaced.
- A cross-reference to a bare `G<n>` is resolved by reading the gate's defining document and rewriting
  to that document's canonical form.

## 5. Claim grades (honest claims — locked by the review)

Grades: `[T]` theorem-grade (proved + Lean), `[C]` conditional/recognition-grade (depends on a named
import or numerical witness), `[E]` empirical (data-fit result).

- **P4 / E3 / Lean phantom target — DOWNGRADED.** The deliverable is: *a positive, stable, audit-closed
  finite rewrite operator whose effective readout `w_eff(z)` crosses −1 with **no growing mode** (stable
  finite effective readout).* This is **grade `[T]`** as a finite-witness stability statement.
  The stronger claim "**no negative-kinetic (ghost) degree of freedom**" requires a Lagrangian /
  Hamiltonian / kinetic-metric framework that this program does NOT build; it is therefore
  **`out_of_scope`** (statused) unless such a framework is added. Wording must say "no growing
  mode / stable effective readout", NOT "no ghost", anywhere a Lagrangian is not exhibited. The Lean
  target `SBTCosmo.PhantomNoGhost` is renamed/clarified to `SBTCosmo.PhantomStableReadout` and states
  the finite stability property only.
- **Ξ_cosmo ↔ Schur adequacy residual — CONDITIONAL.** The identity "audit cost = Schur energy after
  whitening" is **grade `[C]`**, established **per-sector and numerically**, not asserted as a proved
  theorem. `04-formal-foundations.md` must specify, for each probe sector `p`, the concrete
  `(L_p, D_p, C_p, transport, projection, covariance blocks, residual readout)` and either prove the
  equality for that sector or mark it `[C]` (numerical) with the residual `‖Ξ_C − audit_cost‖` reported.
  No file may state the reconciliation as unconditionally proved.

## 6. `XiToy` vs `Ξ_cosmo` (naming, locked)

- **`XiToy`** = a *synthetic, injected* residual used only in **E0** demos. Fitting/recovering it is allowed
  before E1.
- **`Ξ_cosmo`** = the *real-data-fitted* closure residual. **No `Ξ_cosmo` object is fit on real data
  before the E1-A reproduction gate passes.** The "no Ξ before E1" rule means **no real-data `Ξ_cosmo`**;
  it does not constrain `XiToy`. Sequencing language (`08`) and E0 must use `XiToy` to avoid the apparent
  contradiction.

## 7. Artifact authority (committed vs ignored)

- Gate evidence MUST be derivable from **committed** artifacts. For every experiment, commit compact
  posterior **summaries** under `results/<E#>/` — mean vector, covariance, optionally thinned samples —
  each with a `sha256`, in a tracked `results/<E#>/posteriors/`.
- Raw sampler chains under `runs/**/chains/*.hdf5` are **gitignored reproducibility byproducts** and
  **no gate may depend on them**. E4's inverse-ladder (and any cross-experiment posterior consumption)
  reads the committed summary, not an ignored chain.

## 8. E8 out-of-sample verdict (`win` / `tie` / `fail`, locked)

Define on the primary leave-one-probe-out OOS metric (predictive log-score / Δχ²_OOS), with model
complexity penalized (evidence or information criterion):

- **`win`** — SBT-`Ξ` is better than **every** alternative on the primary OOS metric by **more than the
  combined uncertainty band** AND after the complexity penalty, AND has **no silent loss** on any
  critical leg (geometry, growth, Hubble). Only `win` satisfies STD-3 / `G-E8-OOS-DECISIVE`.
- **`tie`** — within the uncertainty band of the best alternative. **A tie is NOT a pass** of the
  out-of-sample standard.
- **`fail`** — loses overall, or loses on any critical leg.
- The old "passes when within 3% of the best model" wording is **removed**.

## 9. Time-delay (and multi-anchor) H0 handling (E4 / 03)

- Time-delay (`TDCOSMO`/`H0LiCOW`) and similar model/prior-dependent `H0` determinations are ingested as
  **posterior families / model variants**, not a single Gaussian scalar. E4 is run **with and without**
  the time-delay route; the model-dependence is statused (`moduli` or `selected`).
- Route-matrix cells with only a published summary (no recomputable likelihood) are tagged
  `summary_only` and excluded from any gate that requires recomputation.

## 10. Documentation hygiene

- No stray tool/markup tokens (e.g. a literal `</invoke>`); no references to a `plans/` directory or a
  repo-root `GROUNDING_BRIEF.md` (the brief lives at `plan/GROUNDING_BRIEF.md`).
- `tests/test_registry.py` lints: no bare `G<n>`; `unstatused` never in an accepted-status list; terminal
  states ⊆ §2 enum; coherence membership = E1–E7 everywhere; no gate references an ignored path.

---

## 11. Propagation amendments (locked after the second plan review)

The registry must be **propagated to every file**; a split where some files keep old language is itself
a defect. These amendments are binding everywhere.

**11.1 Forbidden tokens (the `tests/test_registry.py` lint MUST reject these anywhere except this REGISTRY):**
`PhantomNoGhost`, `no-ghost`, `no_ghost`, `without ghost(s)`, a bare `G-T<n>`, a bare `G-DECISIVE`,
`G-E8-NOGHOST`; the phrases "within 3%" / "within 10%" / "win or tie" used as an OOS *pass*;
"summary.json = PASS" / "upstream = PASS" used as the E8 dependency; a coherence ledger or artifact
inventory missing any of E1–E7.

**11.2 P4 / phantom terminology (completes §5).** Canonical names: Lean target/module
`SbtCosmo.PhantomStableReadout` (theorem `phantom_stable_readout_witness`); the diagnostic is the
**stable-readout certificate** (boolean `stable_readout`) **IS the full P4 pass** = the **conjunction of
three components**: **P-dens** (native-currency density `ρ_eff > 0`); **P-adeq** (rewrite-operator/adequacy
positivity `sym_C(R[Ξ]) ⪰ 0` ↔ Schur `Ξ_C ⪰ 0`, `G-FORMAL-1`); and **S-stab** — the **no-growing-mode**
condition `max Re λ(J) ≤ 0` on the *continuous-generator* Jacobian `J` (finite; kernel-checkable via
Gershgorin discs in the closed left half-plane, or a Lyapunov `J^*C+CJ ⪯ 0`; for a discretized one-step map,
spectral radius `≤ 1`). **"No-growing-mode" names S-stab specifically; "stable-readout certificate" names the
three-way conjunction.** **Positivity (P-dens, P-adeq) is NOT stability (S-stab)** (a `C`-PSD operator has
*growing* `C`-energy — `CONTRACT_HARDENING_ADDENDUM.md` §4). The boolean `stable_readout` := (P-dens ∧
P-adeq ∧ S-stab) where all three apply (E3/E1); **E0's toy `stable_readout` records its available subset
P-dens ∧ S-stab** (P-adeq deferred to E3, ADDENDUM §4) and must be read with that scope. The Lean
`PhantomStableReadout` witness establishes the **S-stab (no-growing-mode) component + crossing** for the
finite construction; P-dens and P-adeq are the **E3 numerical** checks of the full certificate. The full negative-kinetic-DOF (ghost) exclusion is
`out_of_scope`. No file uses "no-ghost"/"PhantomNoGhost"/"without ghost" as a claim or a name. (Genuine
*literature/risk* mentions like "the data could require a ghost" are fine — they describe a failure mode,
not an SBT claim.)

**11.3 Gate-ID canonical names (completes §4).** E4 model-comparison/holonomy gates =
`G-E4-T1 … G-E4-T5` and `G-E4-DECISIVE`; E8 stability column gate = `G-E8-STABLEREADOUT`.

**11.4 E8 acceptance (completes §2, §8).** E8 depends on upstream `terminal_state ∈ {PASS, ACCEPTED_NEGATIVE}`
(never universal PASS); it sources the coherence ledger from **all of E1–E7**; its decisive gate
`G-E8-OOS-DECISIVE` passes ONLY on a strict OOS **win** (better than every alternative beyond the combined
uncertainty band AND after the complexity penalty, with no silent loss on a critical leg) — a tie is not a
pass; no "within 3%/10%" pass anywhere.

**11.5 E4 lawful plurality (completes §5).** The POSITIVE Hubble-holonomy / lawful-plurality result
requires **all five tests LP1–LP5** (`idea.md` UPDATE) to pass. A result that passes mainly on single-`Ξ`
low-rank route reuse (model comparison) without all of LP1–LP5 is reported as a weaker **"route-reuse"**
finding, graded `[E]`/partial — NOT as the lawful-plurality claim.

**11.6 Determinism (realistic).** Require (a) **deterministic likelihood / forward-model evaluations**
(bitwise reproducible given fixed inputs) and (b) **committed posterior summaries reproducible to a stated
tolerance**. Do NOT require bitwise-identical MCMC/PolyChord chains across environments; chains are
validated by **statistical equivalence** (parameter means/covariance within MC error; `R̂ < 1.01`; ESS
thresholds). Only the E0 toy demos (no sampler) are bitwise reproducible.

**11.7 Lean T5 feasibility.** T5 (phantom stable readout) MAY use mathlib (matrix/spectral machinery), OR
be reduced to a finite algebraic certificate (e.g. a Gershgorin-disc bound / explicit characteristic-
polynomial sign test) with no abstract spectral claim. The mathlib-free preference applies to the other
targets where feasible, not to T5 by force.

**11.8 Schur reconciliation wording (completes §5).** The statement "the four-residual sum equals the audit
energy" is a **sector-by-sector numerical comparison target** under `G-FORMAL-3` (grade `[C]`), NOT an
exact identity. No file may call it "exactly" the audit energy.

**11.9 E2 amplitude criterion (single definition).** The CDDR/local-global verdict in E2: the **gluing-residual**
reading is supported when the `η≠1` (LG) chart absorbs the **majority (> 50%)** of the apparent `w_a`
signal (M2-vs-M1 amplitude share / Δχ²); the **rewrite** reading when it absorbs a small fraction (< ~20%);
**mixture** otherwise. The brief and E2 must state this one criterion consistently (no contradictory
"< 50%" gluing threshold).
