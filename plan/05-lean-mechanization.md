# Plan 05 — Lean 4 Mechanization

**Program:** Dark Energy as Closure — a Six Birds resolution of the cosmological paradoxes
**Status:** PLANNING / BLUEPRINT. To be executed later by a separate codex-driven process. Nothing here is run, built, or proved now.
**Scope of this file:** the complete Lean 4 mechanization plan for the `lean/` project sketched in `plan/01-repo-structure.md` §5 and pinned in `plan/02-environment-and-deps.md` §1.6. It fixes the lakefile + toolchain/mathlib pin, the module layout, and — for each mechanization target — the exact Lean statement, its source proposition, the inputs/method/outputs, the disclosure tier, and the experiment/proposition it maps to. It states what stays paper-proof and why, the honest traceability/disclosure discipline, and quantitative pass/fail gates. **No `sorry`/`admit`/project-local `axiom`/`opaque`/`constant` in delivered targets.**

**Authoritative upstream (consistency anchors):**
- `idea.md` — full program; §1 closure package, §3 nine-shadows map, §4 carrier + four residuals + four propositions P1–P4, §5 minimal `Ξ` ansatz + kernels, §6 experiments E1–E7/E9, §10 five hard standards, and the post-§10 **UPDATE** block (Hubble readout field `H₀^{(r,ℓ)}`, Hubble holonomy `𝔥_γ`, route matrix, lawful plurality).
- `GROUNDING_BRIEF.md` — §II.D Lean 4 ≥4.0 (v4.28.0 tested) + mathlib selective; §VI audit gates 5 (phantom-crossing stable readout, no growing mode), 6 (route mismatch), 7 (Hubble holonomy); Part 4 AOR statuses; Part 5 carrier progression.
- `plan/00-overview.md` — §5 the four propositions → Foundations-IV anchors `thm:F2 / thm:F4 / thm:F9 / thm:F11`; §6 gates; §8 definition-of-done item 5 (P1, P4 complete Lean proofs; P2, P3 scaffold + verified-computation witness reusing F11/F4).
- `plan/01-repo-structure.md` — §5 `lean/` skeleton (`SbtCosmo/Idempotence.lean`, `RouteMismatch.lean`, `Holonomy.lean`, `PhantomStableReadout.lean`, `AORStatus.lean`); `.lake/` gitignored; green `lake build` is the receipt recorded in the run manifest under `lean.{toolchain, mathlib_rev, build}`.
- `plan/02-environment-and-deps.md` — §1.6 elan + Lean `v4.28.0` + pinned mathlib commit; §5 CI tier **T5** (`lake build` on `lean/` changes, <15 min); §6 gate **G-ENV-9** (`lake build` green, no `sorry`, else claims → `recognized_grade`).

**Corpus grounding (proof patterns + exact named anchors), all under `docs/papers/`:**
- `Foundations_IV` — named layer-agnostic laws with direct Lean theorems: **F2** Descent–Repair Normal Form (`Transport.DescentRepair.descent_repair_normal_form`), **F4** Local–Global Obstruction Normal Form (`Transport.LocalGlobalObstruction.local_global_obstruction_normal_form`, four-status classification), **F9** No Unstatused Residual (`Stability.NoUnstatusedResidual.no_unstatused_residual`), **F11** Adequacy / No-Overread (`Access.Adequacy.adequacy_no_overread`) + access quotient (`def:access-quotient`, `Access.Quotientality.quotientality`). Uses the **opacity-guard** pattern for substrate-pending axioms.
- `Adequacy_Residuals` — adequacy residual `Ξ_C(D|L)` = Schur complement of block currencies; projection identity `Ξ = T_D(I−P_L)T_D^* ⪰ 0` and exact-adequacy four-way equivalence. Lean namespace `SixBirdsNeedles.Xi.*` (`Xi.OptimalResidual.optimalResidualIdentity`, `Xi.OptimalResidual.exactAdequacy`).
- `AOR` — carrier completion; eight-stratum defect `Ξ_SB`, forced-residual theorem, status atlas, `PreSB → RefStableAOR → CascadeStableAOR → AOR` hierarchy. Lean namespace `SixBirdsNeedles.AOR.*`; **trust base** `lean/manifests/trust_base.txt = {propext, Classical.choice, Quot.sound, choice, funext}`; **three-tier disclosure** (`faithful` / `narrowed_surrogate` / `partial`); manifest checker audits theorem closures against the trust base; **`sorry`/`axiom`/`opaque`/`constant` forbidden**.
- `Holonomy_with_Memory` — fixed-support route transport; current quotient `Q` vs predictive quotient `M`; loop action trivial on `Q` while nontrivial on `M` (`predictiveToCurrent_commutes_with_loopAction`, `loopAsymmetry_exhibits_movedPredictive_fixedCurrent`). Foundation for the Hubble-holonomy target.
- `Emergence_IS_the_Needle_Killer` — layer-dissolving / membrane discipline (framework-bound limits) grounding the P4 stability argument.
- `Six_Birds_for_Neutrino_Mass` — worked Lean+Python cross-lens audit template (the methodological pattern these receipts mirror).

---

## 0. Role of Lean in this program (read first)

Lean is **off the critical path** for the numerical cosmology pipeline (`plan/02` §0.5; `plan/01` §5). The Python pipeline (`sbt_cosmo/`) runs with zero Lean dependency. Lean produces **certified audit receipts** for the discrete/structural backbone of the program: the parts of the argument that are *finite and exact* and therefore mechanizable to theorem grade. The division of labour is sharp and is itself an honesty discipline:

| Layer | Object | Verified by | Why |
|---|---|---|---|
| **Structural / finite-exact** | idempotent packaging fixed points; route-mismatch positivity on finite carriers; Schur-complement PSD + exact-adequacy equivalence; the F4 four-status classification of a finite gluing record; a finite phantom-crossing witness; a finite route-graph holonomy example | **Lean 4** (this plan) | Discrete, finite, exact ⇒ a kernel-checked proof is *the* strongest possible warrant; no statistics needed. |
| **Numerical / inferential** | DESI/Planck/SN/WL likelihoods, MCMC posteriors, `χ²`, BIC, `R̂`, out-of-sample RMSE, staging spectra | **Python** (`sbt_cosmo/`, experiments E0–E8) + determinism gates | Continuous, data-driven, statistical ⇒ Lean cannot and should not certify these; they are reproduced + statused in the AOR ledger. |

**The cardinal rule of this plan.** A Lean target proves the *structural skeleton* of a proposition (e.g. "a positive, stable rewrite operator can induce an effective `w_eff < −1`" on a finite explicit instance). It does **not** prove the *empirical* claim (e.g. "the real universe's `w_eff` crosses −1"). The empirical claim is the job of the experiments. Conflating the two is exactly the over-read F11 forbids; every receipt below carries an explicit **scope line** disclaiming the empirical lift. This is the same discipline the corpus uses (`Foundations_IV` opacity-guards; `AOR` disclosure tiers; `Holonomy_with_Memory` "we do not claim genericity").

---

## 1. Toolchain, lakefile, and mathlib pin

### 1.1 Toolchain

- **`lean/lean-toolchain`** (tracked, exact): `leanprover/lean4:v4.28.0`. Matches the corpus pin (`Foundations_III` validator, INDEX "Notes", `plan/02` §1.6). Installed via **elan** (`plan/02` §2.1 step 5).
- The Lean project is **isolated**: its own `lean-toolchain` + `lakefile` + `lake-manifest.json`, decoupled from the Python conda/pip env, so `lake build` is reproducible independent of the cosmology stack.

### 1.2 Mathlib policy — selective, pin a commit, default to mathlib-free

Per `GROUNDING_BRIEF` §II.D ("mathlib imported selectively") and the corpus convention (the needles project "remains mathlib-free … categorical records, fixed-point packages, residual types … represented locally by Lean structures, inductive types, and `Prop`-valued predicates"):

- **Default (preference, not a blanket rule): mathlib-free.** Targets T1, T2, T4, T6 (idempotence, route mismatch, F4 four-status, holonomy) are over **finite explicit carriers** (`Fin n`, `Bool`, finite `structure`s, decidable `Prop`s). These require **no mathlib** and must compile against core Lean 4 + `Std`/`Batteries` only. Keeping them mathlib-free makes `lake build` fast (CI tier T5 budget <15 min, `plan/02` §5) and keeps the trust base minimal. The mathlib-free preference applies to these targets **where feasible**; it is **not forced on T3 or T5** (REGISTRY §11.7).
- **Opt-in for linear-algebra targets only.** Target T3 (Schur-complement PSD + exact adequacy) needs matrices, `PosSemidef`/`PosDef`, the Loewner order (`A ⪯ B ↔ 0 ⪯ B − A`), and the Moore–Penrose pseudoinverse `†`. These live in mathlib (`Mathlib.LinearAlgebra.Matrix.PosDef`, `Mathlib.LinearAlgebra.Matrix.Spectrum`, `Mathlib.Analysis.Matrix`). T3 imports mathlib; it is isolated in its own module + (optionally) its own Lake target so a mathlib outage cannot block the mathlib-free receipts.
- **T5 route (chosen, REGISTRY §11.7).** T5 (phantom stable readout) MAY use mathlib's matrix/spectral machinery, OR be reduced to a **finite algebraic certificate** (a Gershgorin-disc bound / an explicit characteristic-polynomial sign test) carrying **no abstract spectral claim**. T5 is **not forced mathlib-free**. **This plan chooses the finite-algebraic-certificate route**: the no-growing-mode certificate is a decidable rational Gershgorin-disc / characteristic-polynomial sign test, so T5 stays mathlib-free *by this choice* (not by force) and makes no abstract spectral claim. If the executor instead elects the mathlib spectral route, T5 imports mathlib like T3 and is isolated the same way. Either route is permitted; the choice must be recorded once in `coverage_table.md` and used consistently.
- **Pin a commit.** `lean/lake-manifest.json` (tracked) pins the **exact mathlib git revision** compatible with `v4.28.0`. `lake build` is hash-deterministic given the toolchain + manifest. The pinned `mathlib_rev` is recorded in every run manifest (`plan/01` §9.3 `lean.mathlib_rev`).

### 1.3 `lean/lakefile.lean` (specification)

A `lakefile.lean` (preferred over TOML for the corpus, to declare two library targets and the mathlib-optional dependency) declaring:

```lean
import Lake
open Lake DSL

package «sbtCosmo» where
  -- forbid project-local escapes at the build level
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

-- Mathlib is pinned in lake-manifest.json; only the linear-algebra target uses it.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "<PINNED_COMMIT_v4.28.0_compatible>"

-- Mathlib-free receipts (fast; T1, T2, T4, T6, AOR status).
@[default_target]
lean_lib «SbtCosmo» where
  globs := #[.submodules `SbtCosmo]
  -- modules listed in §2 except Schur

-- Mathlib-dependent receipt (T3 only), isolated so it can be skipped if mathlib is unavailable.
lean_lib «SbtCosmoSchur» where
  globs := #[`SbtCosmo.Schur]
```

Notes:
- `warningAsError := true` turns any `sorry` warning into a build failure (belt-and-braces over the manifest checker of §6).
- `autoImplicit false` is required so that mistyped identifiers do not silently become free variables (a common source of vacuous "theorems").
- The two-library split (`SbtCosmo` mathlib-free, `SbtCosmoSchur` mathlib-dependent) lets CI build the fast set on every `lean/` change and the Schur set on a longer cadence; both are required for the green gate at release.

---

## 2. Module layout

Mirrors and elaborates `plan/01` §5 (`lean/SbtCosmo/{Idempotence, RouteMismatch, Holonomy, PhantomStableReadout, AORStatus}.lean`), adding the Schur and Common modules and the manifests directory required by the corpus disclosure discipline.

```
lean/
├── lean-toolchain                       # tracked — leanprover/lean4:v4.28.0
├── lakefile.lean                        # tracked — §1.3
├── lake-manifest.json                   # tracked — pinned mathlib commit
├── README.md                            # tracked — what each receipt certifies; `lake build` to check;
│                                         #            scope disclaimers; mapping to P1–P4 / E0–E8
├── manifests/
│   ├── trust_base.txt                   # tracked — allowlisted kernel axioms (§6.2)
│   └── coverage_table.md                # tracked — per-declaration coverage + disclosure tier (§5)
└── SbtCosmo/
    ├── Common.lean                       # finite carriers, decidable equality helpers, a metric/defect
    │                                      #   abstraction `d`, the FiniteCarrier structure; mathlib-free
    ├── Idempotence.lean                  # TARGET T1  — packaging fixed points  (δ-defect, P5)
    ├── RouteMismatch.lean                # TARGET T2  — route-mismatch positivity (RM_p, P1/P3)
    ├── Schur.lean                        # TARGET T3  — adequacy residual PSD + exact adequacy (Ξ, F11/Adeq)
    │                                      #             *** the ONLY module importing mathlib ***
    ├── LocalGlobal.lean                  # TARGET T4  — F4 four-status gluing classification (P3)
    ├── PhantomStableReadout.lean         # TARGET T5  — finite phantom-crossing stable-readout (no growing mode) witness (P4)
    ├── Holonomy.lean                     # TARGET T6  — finite route-graph Hubble-holonomy nonzero residue
    └── AORStatus.lean                    # TARGET T7  — no-unstatused-residual well-formedness (F9)
```

**Dependency arrows (must be acyclic; `Common` is the only shared base):**
`Idempotence, RouteMismatch, LocalGlobal, PhantomStableReadout, Holonomy, AORStatus → Common`; `Schur → mathlib` only. No module imports another target module (each receipt is self-contained on `Common`), so a failure in one receipt localizes.

**Naming convention (corpus-consistent):** declarations use the `SixBirdsNeedles`-style flat dotted names recorded in the coverage table, but namespaced under this project, e.g. `SbtCosmo.Idempotence.packaging_fixedpoint`, `SbtCosmo.RouteMismatch.route_mismatch_nonneg`, `SbtCosmo.Schur.adequacy_residual_psd`, `SbtCosmo.Schur.exact_adequacy`, `SbtCosmo.LocalGlobal.four_status_classification`, `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness`, `SbtCosmo.Holonomy.route_holonomy_nonzero`, `SbtCosmo.AORStatus.no_unstatused_residual`.

---

## 3. The seven mechanization targets

Each target gives: **source proposition**, the **exact Lean statement** (signature; the body is the executor's job but must contain no `sorry`/`axiom`/`opaque`), **inputs / method / outputs**, **disclosure tier**, **scope line** (what is NOT claimed), and the **experiment/proposition map**.

A small shared vocabulary from `Common.lean` is used below:

```lean
namespace SbtCosmo.Common
/-- A finite carrier: a finite microstate type with decidable equality. -/
structure FiniteCarrier where
  X       : Type
  [fin    : Fintype X]
  [decEq  : DecidableEq X]
/-- An abstract nonnegative defect/metric on a finite type, used for δ and RM.
    Concretely instantiated by a `0/1` Hamming-style mismatch count or a rational ℓ¹ distance;
    kept abstract so receipts are about *structure*, not a particular numeric metric. -/
structure Defect (X : Type) where
  d        : X → X → ℚ        -- rationals: exact, decidable, mathlib-free
  nonneg   : ∀ a b, 0 ≤ d a b
  zero_iff : ∀ a b, d a b = 0 ↔ a = b
  symm     : ∀ a b, d a b = d b a
end SbtCosmo.Common
```

Using ℚ (not ℝ) for the mathlib-free targets keeps everything decidable and exact while still expressing "≥ 0" and "> 0" honestly.

---

### TARGET T1 — Idempotent-packaging fixed points

- **Source proposition.** Packaging `E_{θ,p} = U_θ ∘ f_p` is a closure: a successful macro layer is a *fixed point* of an idempotent endomap, and the idempotence defect `δ_p = d(E², E)` vanishes **iff** the carrier sits in the fixed-point set. This is the P5 primitive (INDEX: "idempotent endomap with fixed points"; `idea.md` §4 `δ_p`; grounded in `A Six Birds' Eye View of Quantum Theory`, where "dephasing = idempotent packaging, fixed points = diagonal states").
- **Exact Lean statement.**

```lean
namespace SbtCosmo.Idempotence
open SbtCosmo.Common

/-- An idempotent packaging operator on a finite carrier. -/
structure Packaging (C : FiniteCarrier) where
  E    : C.X → C.X
  idem : ∀ x, E (E x) = E x          -- E∘E = E

/-- Fixed points of the packaging operator. -/
def isFixed {C} (P : Packaging C) (x : C.X) : Prop := P.E x = x

/-- (a) The image of E is exactly its fixed-point set. -/
theorem image_eq_fixedSet {C} (P : Packaging C) :
    ∀ x, (∃ y, P.E y = x) ↔ isFixed P x := by
  sorry  -- EXECUTOR: prove. forward: idem; backward: y := x.

/-- (b) Idempotence-defect characterization: with defect `D`,
    δ(x) = D.d (E (E x)) (E x) = 0 for all x, and δ(x)=0 ↔ E x is a fixed point. -/
theorem delta_zero_iff_fixed {C} (P : Packaging C) (D : Defect C.X) :
    (∀ x, D.d (P.E (P.E x)) (P.E x) = 0) ∧
    (∀ x, D.d (P.E (P.E x)) (P.E x) = 0 ↔ isFixed P (P.E x)) := by
  sorry  -- EXECUTOR: prove via P.idem and D.zero_iff.
end SbtCosmo.Idempotence
```

  (The `sorry` placeholders above are **specification markers for the executor only**; the delivered file has them discharged. They will not appear in any committed/green build — see §6.)
- **Inputs:** finite carrier `C`, an idempotent `Packaging`, the abstract `Defect`. **Method:** elementary equational reasoning from `idem` + `Defect.zero_iff`; mathlib-free; fully `decide`-able on any concrete finite instance. **Outputs:** two theorems; an `example` instantiating them on the E0 null-Λ toy packaging (a 2–3 state lumping) so the receipt is demonstrably non-vacuous.
- **Disclosure tier:** **`faithful` (T1)** — the Lean statement *is* the mathematical claim, no narrowing.
- **Scope line (README):** "Certifies that an idempotent packaging operator's image equals its fixed-point set and that δ vanishes exactly there. Does NOT claim any particular cosmological lens is idempotent — that is measured numerically per probe in `audits/delta.py`."
- **Maps to:** P5 primitive; experiment **E0** (synthetic toy: packaging must idempotently lump heterogeneous patches) and the `δ_p ≈ 0` reproduction check in **E1**. Overview §6.3 E0 gate "`δ ≈ 0`".

---

### TARGET T2 — Route-mismatch positivity

- **Source proposition.** Route mismatch `RM_p(x) = d(E_{θ,p} T x, T_θ E_{θ,p} x)` is a **nonnegative** defect that is **zero exactly when packaging commutes with dynamics** (the "evolve→package" vs "package→evolve" routes agree), and is **positive on at least one explicit nonlinear/heterogeneous carrier** (the precursor's "RM 0 in linear regime, >0 with nonlinearity", `A Six Birds' Eye View of Dark Energy`; `idea.md` §1, §4 `RM_p`). This is the structural core of "dark energy = least rewrite repairing a route mismatch."
- **Exact Lean statement.**

```lean
namespace SbtCosmo.RouteMismatch
open SbtCosmo.Common

/-- A finite closure package: micro dynamics T, macro dynamics Tθ, packaging E. -/
structure Package (C : FiniteCarrier) where
  T  : C.X → C.X            -- micro evolution
  E  : C.X → C.X            -- packaging E_{θ,p}
  Tθ : C.X → C.X            -- macro (FLRW-completed) evolution on packaged states

/-- Route mismatch at x: distance between (package∘evolve) and (evolve∘package). -/
def RM {C} (K : Package C) (D : Defect C.X) (x : C.X) : ℚ :=
  D.d (K.E (K.T x)) (K.Tθ (K.E x))

/-- (a) RM is always nonnegative. -/
theorem route_mismatch_nonneg {C} (K : Package C) (D : Defect C.X) (x : C.X) :
    0 ≤ RM K D x := D.nonneg _ _

/-- (b) RM vanishes everywhere iff the commuting square holds:  E∘T = Tθ∘E. -/
theorem route_mismatch_zero_iff_commutes {C} (K : Package C) (D : Defect C.X) :
    (∀ x, RM K D x = 0) ↔ (∀ x, K.E (K.T x) = K.Tθ (K.E x)) := by
  sorry  -- EXECUTOR: pointwise D.zero_iff.

/-- (c) Non-vacuity: an explicit finite *heterogeneous* package with a witness x₀
    at which RM > 0 (the "nonlinear regime" of the precursor). -/
theorem route_mismatch_pos_witness :
    ∃ (C : FiniteCarrier) (K : Package C) (D : Defect C.X) (x₀ : C.X), 0 < RM K D x₀ := by
  sorry  -- EXECUTOR: construct the 2-patch heterogeneous toy; `decide` the strict positivity.
end SbtCosmo.RouteMismatch
```

- **Inputs:** finite `Package`, abstract `Defect`. **Method:** (a) immediate from `Defect.nonneg`; (b) pointwise `zero_iff`; (c) an explicit construction (the two-patch heterogeneous generator of E0) with `decide` (preferred — kernel-checked; `native_decide` only where `decide` is computationally infeasible, and then each occurrence is a justified entry in the Lean trust baseline since it trusts the compiler — REGISTRY §11.7 / `ops/bin/lean-trust-scan.sh`) closing the strict inequality over ℚ. Mathlib-free. **Outputs:** three theorems including the non-vacuity witness, whose carrier is the **same** structure E0 uses (the executor must keep the Lean witness and the Python E0 toy structurally identical — a coherence note in the coverage table).
- **Disclosure tier:** **`faithful` (T1)**.
- **Scope line:** "Certifies route mismatch is a nonnegative defect, zero iff the package/dynamics square commutes, and strictly positive on an explicit heterogeneous toy. Does NOT claim the magnitude or redshift shape of the cosmological RM — those are fit numerically (E1) and reduced by `Ξ_cosmo` (E0/E1)."
- **Maps to:** **P1** (operator rewrite repairs the mismatch) and the P3 route primitive; experiments **E0** (RM > 0 on the heterogeneous generator; RM → 0 after the `Ξ` rewrite) and **E1**. Overview §6.3 E0; GROUNDING_BRIEF §VI gate 6 (route-mismatch audit).

---

### TARGET T3 — Adequacy-residual Schur complement: PSD + exact-adequacy equivalence

- **Source proposition.** The closure residual `Ξ_cosmo` is, formally, the **Schur complement** of the native (FLRW/ΛCDM) block inside the joint native+dissolving currency matrix (`Adequacy_Residuals`; `idea.md` §4 "Δ_SBT" identified with the Schur-complement adequacy residual; GROUNDING_BRIEF §1 — this is *the* defense against the "flexible fudge function" critique: the residual is the algebraically forced leftover, not a free function). Two theorem-grade facts must be certified:
  1. **PSD (projection identity).** `Ξ_C(D|L) = T_D (I − P_L) T_D^* ⪰ 0` — the residual is a *positive* operator (a budgeted obstruction), where `P_L` is the energy-scaled projector onto the native range. (`Adequacy_Residuals`, boxed eq. `Ξ_C(D|L)=T_D(I−P_L)T_D^* ⪰ 0`.)
  2. **Exact adequacy.** Zero residual ⟺ the dissolving probe factors through the native family (the finite "no leftover" test): the four-way equivalence among (i) `Ξ = 0`, (ii) `K_DD = K_DL K_LL^† K_LD`, (iii) range inclusion `Ran(T_D^*) ⊆ Ran(T_L^*)`, (iv) exact factorization `T_D = A T_L`. (`Adequacy_Residuals` `thm:xi:exact-adequacy`.)
- **Exact Lean statement** (mathlib; matrices over `ℝ` or a `RCLike` field `𝕜`):

```lean
namespace SbtCosmo.Schur
open Matrix

variable {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Block currency data: native K_LL ⪰ 0, dissolving K_DD ⪰ 0, cross blocks K_LD, K_DL = K_LD^*. -/
structure BlockCurrency (n m : ℕ) (𝕜 : Type) [RCLike 𝕜] where
  KLL   : Matrix (Fin n) (Fin n) 𝕜
  KDD   : Matrix (Fin m) (Fin m) 𝕜
  KLD   : Matrix (Fin n) (Fin m) 𝕜
  KLLpd : KLL.PosDef          -- NATIVE block strictly POSITIVE-DEFINITE (the mechanized case). PosDef ⇒ Invertible, so `(KLL)⁻¹` below is the GENUINE inverse, not junk. The singular-`KLL` / Moore–Penrose case is paper-proof only (see scope/disclosure). PosDef ⇒ PosSemidef where the latter is needed.
  KDDpsd : KDD.PosSemidef
  -- the full 2×2 block is PSD (block-positivity hypothesis of the paper)
  joint_psd : (Matrix.fromBlocks KLL KLD KLDᴴ KDD).PosSemidef

/-- Adequacy residual = (2,2) Schur complement of the native block KLL. -/
def adequacyResidual (B : BlockCurrency n m 𝕜) : Matrix (Fin m) (Fin m) 𝕜 :=
  B.KDD - B.KLDᴴ * (B.KLL)⁻¹ * B.KLD       -- `(KLL)⁻¹` is the GENUINE inverse: KLL is PosDef hence Invertible. The singular case would need Moore–Penrose † on Ran — that is DEFERRED to paper-proof (scope/disclosure), NOT this Lean def.

/-- (T3a) PSD: the adequacy residual (Schur complement of a PSD block in a PSD joint matrix)
    is positive semidefinite. -/
theorem adequacy_residual_psd (B : BlockCurrency n m 𝕜) :
    (adequacyResidual B).PosSemidef := by
  sorry  -- EXECUTOR: from joint_psd via the Schur-complement PSD lemma (mathlib schur_complement).

/-- (T3b) Exact adequacy (finite "no leftover" equivalence), the trivial directions
    (ii)→(iii)→(iv) certified in Lean; the hard cycle is paper-proof (see disclosure). -/
theorem exact_adequacy_trivial_chain (B : BlockCurrency n m 𝕜) :
    (adequacyResidual B = 0) →
      (∀ v, B.KDD.mulVec v = (B.KLDᴴ * (B.KLL)⁻¹ * B.KLD).mulVec v) := by
  sorry  -- EXECUTOR: definitional unfolding of the residual = 0.
end SbtCosmo.Schur
```

- **Inputs:** mathlib `Matrix`, `PosSemidef`, `fromBlocks`, the Schur-complement lemmas (`Matrix.PosSemidef.schur_complement` / `fromBlocks` PSD characterization) and (only for the deferred singular case) pseudoinverse facts. **Scope of the Lean receipt (finding-16 lock):** the mechanized definition assumes `K_LL` **positive-definite** (so `(K_LL)⁻¹` is the genuine inverse); the **singular `K_LL` / Moore–Penrose pseudoinverse** case and the Douglas–Fillmore–Williams range-factorization equivalences are **deferred to paper-proof** (disclosure below), plus a finite PD worked example. **Method:** (T3a) is the direct application of mathlib's Schur-complement-of-PSD-block lemma to `joint_psd`; this is the load-bearing receipt and should be a **`faithful` (T1)** proof. (T3b) certifies the *easy* directions of the four-way equivalence as a Lean theorem; the **hard** equivalences (the Douglas–Fillmore-Williams range-factorization criterion `(iv)↔(ii)` over a general field and the `(i)↔(ii)` direction) are **deferred to paper-proof** exactly as the source paper does (its Lean theorem "proves the trivial direction chains (ii)→(iii)→(iv) … the full cycle is established here using the Douglas–Fillmore-Williams factorization criterion"). **Outputs:** PSD theorem (faithful) + the trivial-chain theorem (narrowed) + a small worked `example` on a 1+1 block (a single native ΛCDM currency vs a single dissolving `Ξ` direction) showing `Ξ = K_DD − K_DL K_LL⁻¹ K_LD` numerically nonzero, mirroring the E1 two-probe split.
- **Disclosure tier:** **PSD = `faithful` (T1)**; **exact-adequacy = `narrowed_surrogate` (T2)** — Lean records the trivial-direction chain under the elevated Douglas–Fillmore-Williams factorization hypothesis; the full cycle is paper-proof, mirroring `Xi.OptimalResidual.exactAdequacy` in the corpus. Both rows logged in `coverage_table.md` with the narrowing note.
- **Scope line:** "Certifies that the adequacy residual is the Schur complement of the native block and is positive semidefinite (it is a *budgeted obstruction*, never negative), and the easy exact-adequacy directions. Does NOT compute the cosmological `Ξ_cosmo` numerically — the block currencies `K_LL/K_DD/K_LD` are estimated from data in `sbt_cosmo/xi/`; the Lean receipt certifies the *algebra* (`Ξ` is forced, not a free fudge function), which is the structural answer to the over-fitting critique."
- **Maps to:** **P2/F11** (the "least rewrite, not a fudge function" claim) and the `Ξ_cosmo` definition used by **all** experiments; especially the §6.4 coherence gate (`Ξ` is one algebraic object reused across probes). GROUNDING_BRIEF §1.

---

### TARGET T4 — Local–global four-status classification (F4)

- **Source proposition.** Distance-duality / SN↔BAO gluing is the statement that **locally compatible probe sections globalize into one FLRW metric-distance object iff they lie in the image of the restriction map**; and every local family carries **exactly one** of four statuses: overlap-inconsistent, compatible-non-global, globally-ambiguous, globally-exact. This is `Foundations_IV` **F4** (`thm:F4`, `Transport.LocalGlobalObstruction.local_global_obstruction_normal_form`), which `idea.md` §4 Prop 3 and §3 row 4 instantiate as the CDDR gluing obstruction (η(z) ≠ 1).
- **Exact Lean statement** (mathlib-free; a finite re-derivation of F4 specialized to the cosmological patch system):

```lean
namespace SbtCosmo.LocalGlobal
open SbtCosmo.Common

/-- A finite gluing record: global states 𝒢, local-family data 𝓕, compatibility predicate,
    restriction R with the standing hypothesis Comp(R g) for all g. -/
structure GluingRecord where
  G        : Type
  F        : Type
  [finG    : Fintype G]
  [finF    : Fintype F]
  [decF    : DecidableEq F]
  Comp     : F → Prop
  [decComp : DecidablePred Comp]
  R        : G → F
  R_comp   : ∀ g, Comp (R g)              -- every global state restricts to a compatible family

def globalizes (X : GluingRecord) (a : X.F) : Prop := ∃ g, X.R g = a

/-- The four mutually-exclusive, exhaustive statuses (CDDR charts). -/
inductive Status | overlapInconsistent | compatibleNonGlobal | globallyAmbiguous | globallyExact

def classify (X : GluingRecord) (a : X.F) : Status := ...   -- by Comp / image / fiber cardinality

/-- (T4a) Local-to-global image criterion: for compatible a, globalization ⇔ membership in im R. -/
theorem globalizes_iff_in_image (X : GluingRecord) (a : X.F) (h : X.Comp a) :
    globalizes X a ↔ a ∈ Set.range X.R := by
  sorry  -- EXECUTOR: unfold globalizes.

/-- (T4b) Exactly-one-status classification (the F4 normal form). -/
theorem four_status_classification (X : GluingRecord) (a : X.F) :
    (classify X a = Status.overlapInconsistent ↔ ¬ X.Comp a) ∧
    (classify X a = Status.compatibleNonGlobal ↔ (X.Comp a ∧ ¬ globalizes X a)) ∧
    (classify X a = Status.globallyAmbiguous   ↔ (X.Comp a ∧ globalizes X a ∧ 1 < (fiberCard X a))) ∧
    (classify X a = Status.globallyExact       ↔ (X.Comp a ∧ globalizes X a ∧ fiberCard X a = 1)) := by
  sorry  -- EXECUTOR: case split on Comp, image membership, fiber cardinality (decidable on Fintype).
end SbtCosmo.LocalGlobal
```

- **Inputs:** finite `GluingRecord` (decidable `Comp`, finite `G`, `F`). **Method:** a finite re-derivation of F4's case split (compatibility × image-membership × fiber cardinality), all decidable on `Fintype`; mathlib-free. The executor **may** instead `import`/cite the corpus `Transport.LocalGlobalObstruction.local_global_obstruction_normal_form` if the Foundations-IV Lean library is vendored — but the self-contained finite re-derivation is preferred so this repo's `lake build` is independent. **Outputs:** the image criterion + the four-status theorem + an `example` instantiating the cosmological gluing record (SN section `f_SN` + BAO section `f_BAO` over two redshift patches) and computing which status the fitted η(z)≠1 case lands in (compatible-non-global ⇒ a gluing residual, not new dark energy).
- **Disclosure tier:** **`faithful` (T1)** if self-derived; if instead delegating to the corpus theorem, **`narrowed_surrogate` (T2)** with the delegation noted.
- **Scope line:** "Certifies the four-status classification of a finite gluing record and the local-to-global image criterion. Does NOT decide which status the *real* SN/BAO data occupy — that is the E2 numerical fit of η(z); the receipt certifies that 'CDDR failure ⇒ gluing obstruction status', not new physics, is the correct structural reading."
- **Maps to:** **P3 / F4**; experiment **E2** (distance-duality as local-global obstruction). Overview §5 P3; §6.3 E2 gate.

---

### TARGET T5 — Finite phantom-crossing stable-readout (no growing mode) witness (P4)

- **Source proposition.** `idea.md` §4 Prop 4 / §6 Exp 3: there exists a **finite, positive, stable** macro-rewrite operator whose induced effective equation of state `w_eff(z) = −1 + (1+z)/3 · d/dz log ρ_eff(z)` **crosses −1**, while the underlying operator has **no growing mode** (a stable finite effective readout). The structural certificate (REGISTRY §11.7 route, chosen): the rewrite's discrete generator satisfies a **finite algebraic no-growing-mode certificate** — a Gershgorin-disc bound (every disc in the closed left half-plane) or characteristic-polynomial sign test, decidable over ℚ with **no abstract spectral claim** — yet the induced `w_eff` sampled on a finite redshift grid **dips below −1** at a witness node. This is the receipt that resolves the instability objection at the level of an existence proof, in the membrane discipline of `Emergence_IS_the_Needle_Killer`. **Scope note (REGISTRY §5).** The deliverable is grade `[T]` *only* as the finite no-growing-mode stability statement; the stronger claim "no negative-kinetic (ghost) degree of freedom" requires a Lagrangian/Hamiltonian/kinetic-metric framework this program does NOT build and is therefore `out_of_scope` (statused) — the wording everywhere is "no growing mode / stable effective readout", NOT "no ghost".
- **Exact Lean statement** (REGISTRY §11.7 route: a **finite algebraic certificate** — Gershgorin-disc bound / characteristic-polynomial sign test — so everything is finite + rational and `decide`-able, with **no abstract spectral claim**; T5 is mathlib-free *by this choice*, not by force. The alternative mathlib route under §11.7 would replace the certificate below with mathlib's matrix/spectral machinery and isolate T5 like T3.):

```lean
namespace SbtCosmo.PhantomStableReadout

/-- A finite phantom-crossing witness over a rational redshift grid. -/
structure Witness where
  N      : ℕ                          -- number of grid nodes
  z      : Fin N → ℚ                  -- redshift nodes (increasing)
  rhoEff : Fin N → ℚ                  -- effective energy density ρ_eff(z_i) > 0
  rho_pos : ∀ i, 0 < rhoEff i         -- positivity of the effective density (no negative energy)
  -- discrete generator of the rewrite (a finite stand-in for the linearized rewrite);
  -- a plain rational array `Fin N → Fin N → ℚ` keeps the finite-algebraic route mathlib-free.
  gen    : Fin N → Fin N → ℚ
  -- no-growing-mode (stability) certificate, the chosen FINITE ALGEBRAIC certificate (§11.7):
  -- a decidable, rational, kernel-checkable Gershgorin-disc bound (every disc lies in the
  -- closed left half-plane) or characteristic-polynomial sign test — NO abstract spectral claim.
  stable : NoGrowingModeCertificate gen  -- decidable rational sufficient condition for no growing mode

/-- Discrete w_eff at interior node i via the centered log-derivative of ρ_eff. -/
def wEff (W : Witness) (i : Fin W.N) : ℚ := ...   -- −1 + ((1+z_i)/3) · Δ log ρ_eff / Δ z   (rational)

/-- (T5) There is a finite witness whose generator carries a no-growing-mode certificate AND whose
    induced w_eff dips strictly below −1 at some interior node — phantom crossing with a stable
    (no-growing-mode) effective readout. -/
theorem phantom_stable_readout_witness :
    ∃ (W : Witness) (i : Fin W.N),
      NoGrowingMode W.gen ∧ wEff W i < (-1 : ℚ) := by
  sorry  -- EXECUTOR: exhibit the explicit grid + ρ_eff + generator; `decide` (preferred — kernel-checked; `native_decide` only where `decide` is computationally infeasible, and then each occurrence is a justified entry in the Lean trust baseline since it trusts the compiler — REGISTRY §11.7 / `ops/bin/lean-trust-scan.sh`).
```

  with, in `Common` or this module, a **decidable** `NoGrowingModeCertificate`/`NoGrowingMode` predicate that is the chosen **finite algebraic certificate** (§11.7) — a *rational, kernel-checkable sufficient condition* for no growing mode that makes **no abstract spectral claim**. **Chosen (this plan):** strict Gershgorin diagonal dominance with non-positive real diagonal (every Gershgorin disc lies in the closed left half-plane), OR an explicit characteristic-polynomial sign test; both are elementary, decidable over ℚ, and mathlib-free, and their soundness is a `faithful` Lean proof. (Should the executor instead elect the §11.7 mathlib spectral route, the certificate may be a Lyapunov rational PSD condition `∃ P ⪰ 0 (rational), Pᵀgen + genᵀP ⪯ 0` whose soundness is the cited control-theory fact, logged `narrowed_surrogate`; that route imports mathlib and is isolated like T3.)
- **Inputs:** an explicit finite witness (grid, `ρ_eff`, generator) constructed to match the **DESI-preferred crossing redshift** `z_c` used in E3, kept rational. **Method:** the existence proof is by explicit construction + `decide` (preferred — kernel-checked; `native_decide` only where `decide` is computationally infeasible, and then each occurrence is a justified entry in the Lean trust baseline since it trusts the compiler — REGISTRY §11.7 / `ops/bin/lean-trust-scan.sh`) on rationals; the two conjuncts are (a) the decidable no-growing-mode certificate and (b) `wEff W i < −1`. **Outputs:** the existence theorem + the explicit `Witness` term (this *is* the certificate) + an `example`/`#eval` printing the witness `w_eff` profile so it can be cross-checked against the Python E3 `w_eff(z)` curve.
- **Disclosure tier:** **`faithful` (T1)** if a Gershgorin-type decidable no-growing-mode condition is used (soundness elementary); **`narrowed_surrogate` (T2)** if a Lyapunov/minor certificate is used whose spectral soundness is cited. Logged either way.
- **Scope line:** "Certifies that a positive, stable (no-growing-mode) finite rewrite operator CAN induce w_eff < −1 — an existence proof that crossing −1 can come from a stable effective *readout*. Does NOT claim the real dark sector is this operator, nor that the universe's w_eff crosses −1 (that is the E3 empirical fit); and does NOT claim the absence of a negative-kinetic (ghost) degree of freedom — that requires a Lagrangian/kinetic-metric framework not built here and is statused `out_of_scope` (REGISTRY §5)."
- **Maps to:** **P4** (no Foundations-IV named law — uses operator-rewrite + stability, per Overview §5); experiment **E3** (phantom crossing with no growing mode; eigenvalue-stability gate `Re λ ≤ 0`). GROUNDING_BRIEF §VI gate 5; Overview §6.3 E3.

---

### TARGET T6 — Finite route-graph Hubble-holonomy nonzero residue

- **Source proposition.** `idea.md` **UPDATE** block: `H₀` is not a closure-independent scalar but a **route-indexed readout** `H₀^{(r,ℓ)}`, and the **Hubble tension is the scalar shadow of Hubble holonomy** `𝔥_γ = B_{γ#} P(H₀^{r₁}) ⊖ P(H₀^{r₁})` — a posterior transported around a loop of routes does not return unchanged. The **structural** receipt (the part Lean can certify, grounded in `Holonomy_with_Memory` + `Protocol_Trap` + `To_Plot`): on a finite route graph with composable bridge transports, there is an **explicit loop whose composite transport is non-identity** (nonzero holonomy / nonzero loop residue), AND — mirroring `Holonomy_with_Memory`'s loop-asymmetry theorem — the holonomy can be **trivial on the current quotient while nontrivial on the predictive quotient** (lawful plurality: the disagreement is structured, not noise, and not a mere current-interface bookkeeping artifact).
- **Exact Lean statement** (mathlib-free; finite group/transport on a route graph):

```lean
namespace SbtCosmo.Holonomy
open SbtCosmo.Common

/-- A finite route graph: routes (vertices) and composable bridge transports (edges)
    acting on a finite "readout state" type S (a coarse stand-in for a Hubble posterior). -/
structure RouteGraph where
  Route   : Type
  [finR   : Fintype Route]
  [decR   : DecidableEq Route]
  S       : Type                 -- finite readout-state type
  [finS   : Fintype S]
  [decS   : DecidableEq S]
  bridge  : Route → Route → (S → S)   -- transport B_{r→r'} ; partial composability via a loop list

/-- Transport composed around a loop (a nonempty list of routes returning to its head). -/
def loopTransport (Γ : RouteGraph) (loop : List Γ.Route) : Γ.S → Γ.S := ...

/-- (T6a) Nonzero holonomy: an explicit route graph and loop whose composite transport
    is NOT the identity — i.e. ∃ s, loopTransport Γ loop s ≠ s. -/
theorem route_holonomy_nonzero :
    ∃ (Γ : RouteGraph) (loop : List Γ.Route) (s : Γ.S),
      loopTransport Γ loop s ≠ s := by
  sorry  -- EXECUTOR: 3-route loop (CMB→BAO→Cepheid→CMB) with a nontrivial composite; `decide`.

/-- (T6b) Lawful-plurality asymmetry (Holonomy-with-Memory specialization):
    a loop acting trivially on the current quotient Q while moving a class of the
    predictive quotient M — disagreement is structured below the current interface. -/
theorem holonomy_current_trivial_predictive_nontrivial :
    ∃ (Γ : RouteGraph) (loop : List Γ.Route)
      (toCurrent : Γ.S → CurrentClass) (toPredictive : Γ.S → PredictiveClass),
      (∀ s, toCurrent (loopTransport Γ loop s) = toCurrent s) ∧
      (∃ s, toPredictive (loopTransport Γ loop s) ≠ toPredictive s) := by
  sorry  -- EXECUTOR: instantiate the corpus coherent-memory benchmark on the route graph; `decide`.
end SbtCosmo.Holonomy
```

- **Inputs:** an explicit finite route graph whose routes are the UPDATE-block routes (`r1 = CMB→BAO`, `r2 = BAO→SN`, `r3 = Cepheid→SN`, `r4 = TRGB→SN`, …) and whose bridge transports compose to a nontrivial loop. **Method:** explicit construction + `decide` (preferred — kernel-checked; `native_decide` only where `decide` is computationally infeasible, and then each occurrence is a justified entry in the Lean trust baseline since it trusts the compiler — REGISTRY §11.7 / `ops/bin/lean-trust-scan.sh`); T6b reuses the *coherent-memory* benchmark structure of `Holonomy_with_Memory` (current loop action trivial, predictive loop action nontrivial — the `loopAsymmetry_exhibits_movedPredictive_fixedCurrent` pattern). Mathlib-free. **Outputs:** the nonzero-holonomy theorem + the asymmetry theorem + an `example` whose route labels match the E4 route registry (`sbt_cosmo/hubble/routes.py`) so the Lean witness and the Python route matrix are structurally aligned.
- **Disclosure tier:** **`faithful` (T1)** for the finite existence theorems; the *identification* of the abstract transport with real Hubble-posterior transport is **out of Lean scope** (a numerical operation in E4) and is disclosed as such.
- **Scope line:** "Certifies that a finite route graph can carry nonzero holonomy and that holonomy can be trivial on the current quotient but nontrivial on the predictive quotient — the structural form of lawful plurality. Does NOT measure the real `𝔥_γ` (that is the E4 posterior-transport computation), nor claim every Hubble disagreement is holonomy rather than systematics; it certifies that 'structured route-dependent disagreement' is a coherent, non-vacuous phenomenon, separable from arrow-of-time (Protocol Trap) and from mere current-interface bookkeeping."
- **Maps to:** the UPDATE block; experiment **E4** (Hubble route matrix + holonomy `𝔥_γ`; lawful-plurality tests). GROUNDING_BRIEF §VI gate 7; Overview §6.3 E4.

---

### TARGET T7 — No-unstatused-residual well-formedness (F9)

- **Source proposition.** `Foundations_IV` **F9** No Unstatused Residual (`thm:F9`, `Stability.NoUnstatusedResidual.no_unstatused_residual`) + the `AOR` status atlas: given a residual type and a declared **single-valued** typed-status classifier, **every** residual receives **exactly one** valid status. Per **REGISTRY §1**, `unstatused` is **NOT a status**; it is the **absence** of a status — a validator error. The `Status` enum therefore contains only the **15 valid statuses** (11 base + 4 asymptotic) and has **no `unstatused` constructor**; an unstatused residual is modeled as a `none` from a partial classifier `R → Option Status`. This certifies the well-formedness of the AOR ledger the whole program must emit (Overview §7; `plan/01` §10 gate G-REPO-10 No-Unstatused-Residual "0 unstatused residuals").
- **Exact Lean statement** (mathlib-free):

```lean
namespace SbtCosmo.AORStatus

/-- The AOR status vocabulary (REGISTRY §1): the 15 VALID statuses only — 11 base + 4 asymptotic.
    `unstatused` is NOT a constructor here: it is the *absence* of a status (a `none`), i.e. a
    validator error, never a member of the accepted enum. -/
inductive Status
  -- base (11)
  | zero | budgeted | bridged | hidden | moduli | selected
  | probabilistic | out_of_scope | nonclaim | blocked | approved_other
  -- asymptotic (4)
  | asymptotic_budgeted | summable | contractive | eventual_zero
deriving DecidableEq

/-- A formed status package over a residual type R: a *partial* classifier whose validator
    discipline assigns a valid `Status` to every native residual (never the absence-of-status
    error). `st r = none` is exactly the "unstatused" validator error the F9 target rules out. -/
structure StatusPackage (R : Type) where
  st         : R → Option Status                -- `none` ≡ unstatused (a validator error)
  discipline : ∀ r, (st r).isSome               -- the "no-unstatused-residual" discipline

/-- (T7) No Unstatused Residual: the validator finds no absence-of-status error — every residual
    carries exactly one valid `Status` (no `none`/unstatused). -/
theorem no_unstatused_residual {R : Type} (P : StatusPackage R) :
    (∀ r, (P.st r).isSome) ∧
    (∀ r, ∃! s, P.st r = some s) := by
  sorry  -- EXECUTOR: first conjunct is P.discipline; second is ∃!-of-(some ∘ a function).
end SbtCosmo.AORStatus
```

- **Inputs:** the `Status` inductive (closed 15-status vocabulary, **no `unstatused` constructor**) + a `StatusPackage` with a partial classifier. **Method:** the first conjunct is `P.discipline` (the validator finds no `none`); the second is the trivial `∃!` for the image of the (total-on-discipline) function; mathlib-free, decidable. **Outputs:** the theorem + an `example` instantiating the program's actual residual registry (cc-bridge → `budgeted`/`out_of_scope`; CDDR gluing repaired by `Ξ` → `bridged`; irreducible systematic → `budgeted`; unfixable parameter → `moduli`) to demonstrate the ledger the experiments emit is well-formed (no `none`/unstatused).
- **Disclosure tier:** **`faithful` (T1)** for the well-formedness theorem; **`narrowed_surrogate` (T2)** if it instead delegates to the corpus `Stability.NoUnstatusedResidual.no_unstatused_residual` (delegation noted). The *correctness of each individual status assignment* (e.g. that the cc-bridge truly merits `budgeted`) is a **modeling judgment, not a theorem** — disclosed as such.
- **Maps to:** **F9** meta-obligation (enforced across all four propositions, Overview §5); the AOR ledger `aor/ledger.py`; `plan/01` gate **G-REPO-10**; Overview §8 done-item 7.

---

## 4. Target → proposition → experiment map (summary)

| Lean target | Module | Source proposition (`idea.md`) | Foundations-IV / corpus anchor | Experiment(s) | Disclosure | Mathlib? |
|---|---|---|---|---|---|---|
| **T1** idempotent packaging fixed points | `Idempotence.lean` | §4 `δ_p`; P5 | Quantum Theory (dephasing fixed points) | E0, E1 | faithful | no |
| **T2** route-mismatch positivity | `RouteMismatch.lean` | §1, §4 `RM_p`; **P1** | precursor Dark Energy paper; P1/P3 | E0, E1 | faithful | no |
| **T3** Schur PSD + exact adequacy | `Schur.lean` | §4 `Δ_SBT` = Schur residual; **P2** | `Adequacy_Residuals` (`Xi.OptimalResidual.exactAdequacy`); **F11** | coherence gate; all | PSD faithful / exact narrowed | **yes (only T3)** |
| **T4** local–global four statuses | `LocalGlobal.lean` | §4 Prop 3; **P3** | **F4** `Transport.LocalGlobalObstruction.local_global_obstruction_normal_form` | E2 | faithful (or narrowed if delegated) | no |
| **T5** phantom crossing, stable readout (no growing mode) | `PhantomStableReadout.lean` | §4 Prop 4; §6 Exp 3; **P4** | `Emergence_IS_the_Needle_Killer` membrane discipline | E3 | faithful (chosen §11.7 Gershgorin / char-poly certificate; mathlib spectral route → narrowed) | no (chosen route); mathlib if spectral route elected |
| **T6** route-graph holonomy residue | `Holonomy.lean` | **UPDATE** block; `𝔥_γ` | `Holonomy_with_Memory` (`loopAsymmetry_exhibits_movedPredictive_fixedCurrent`); `Protocol_Trap`; `To_Plot` | E4 | faithful | no |
| **T7** no unstatused residual | `AORStatus.lean` | §2, §10; F9 meta | **F9** `Stability.NoUnstatusedResidual.no_unstatused_residual`; `AOR` atlas | ledger / all | faithful (or narrowed if delegated) | no |

This covers the Overview §8 done-item 5 requirement (P1 + P4 complete Lean proofs via T2/T5; P2 + P3 scaffold-plus-witness via T3/T4 reusing F11/F4) and exceeds it (T1, T6, T7 add the δ, holonomy, and ledger receipts).

---

## 5. Traceability and disclosure discipline (honest machine-checked vs deferred)

This is the heart of the plan's honesty contract, lifted directly from the corpus (`AOR` §"Mechanization disclosure tiers" + §"Standing narrowings"; `Foundations_IV` opacity-guard discipline).

### 5.1 The coverage table (`lean/manifests/coverage_table.md`, tracked)

One row per delivered declaration. Columns (matching the AOR coverage-table format):

| col | meaning |
|---|---|
| `decl` | fully-qualified Lean name, e.g. `SbtCosmo.Schur.adequacy_residual_psd` |
| `paper_claim` | the `idea.md` / proposition it backs (e.g. "P2 — `Ξ` is a Schur residual, PSD") |
| `kind` | `theorem` / `def` / `example` |
| `tier` | `faithful` (T1) / `narrowed_surrogate` (T2) / `partial` (T2-partial) |
| `narrowing` | for T2/T2-partial: the exact hypothesis elevated to a paper-citation, e.g. "Douglas–Fillmore-Williams range-factorization criterion cited; trivial chain only in Lean" |
| `experiment` | E0–E8 mapping |
| `scope_disclaimer` | the one-line "does NOT claim …" (§3 scope lines) |

### 5.2 The three tiers (and the honest wording each forces)

- **`faithful` (T1)** — the Lean statement *is* the mathematical claim; no narrowing. README/footnote wording: *"Verified in Lean as `<decl>`."* Used by T1, T2, T4 (self-derived), T5 (Gershgorin), T6, T7 (self-derived) and T3a (PSD).
- **`narrowed_surrogate` (T2)** — Lean proves a faithful *sub-claim* under an explicitly elevated hypothesis; the full statement is paper-proof. Wording: *"Mechanized in Lean as `<decl>`; the Lean theorem proves `<sub-claim>` under `<narrowing>`. The full statement is proved in the paper."* Used by T3b (exact-adequacy hard cycle), and by T4/T7 if they delegate to the vendored Foundations-IV theorems.
- **`partial` (T2-partial)** — Lean records a *fragment* and the rest is a classical paper input (the `AOR` `cascade-confluence` pattern: "Lean records the local confluence … the body supplies the Newman implication"). Permitted only if a target genuinely splits this way; **must** be flagged, never silent.

### 5.3 What stays paper-proof, and exactly why

| Claim deferred to paper-proof | Why it cannot/should not be a delivered Lean theorem here |
|---|---|
| Hard directions of exact-adequacy (`(i)↔(ii)`, `(iv)→(ii)`) over a general field | Needs the Douglas–Fillmore-Williams operator-range factorization theorem; the corpus itself elevates this as a citation rather than re-proving it in Lean. Re-deriving it is out of scope and high-risk; the PSD direction (the load-bearing "Ξ is positive, not a free function") IS delivered faithfully. |
| Spectral-radius soundness of a Lyapunov no-growing-mode certificate (only if the §11.7 mathlib spectral route is elected for T5) | The implication "Lyapunov PSD certificate ⇒ all `Re λ ≤ 0`" is a standard control-theory fact. **This plan does NOT take that route**: it chooses the §11.7 finite algebraic certificate (Gershgorin-disc / characteristic-polynomial sign test), whose soundness IS faithful and defers nothing — so this row is vacuous under the chosen route and applies only if the executor switches to the mathlib spectral route. |
| Empirical lift of every target (T1–T7) | Statistical/data claims (does the *real* universe's `w_eff` cross −1? is the *real* `𝔥_γ` ≠ 0?) are out of Lean's remit by design (§0). They are reproduced + statused numerically. Pretending Lean certifies them would be precisely the F11 over-read the program forbids. |
| Continuum `Ξ_cosmo(z,ℓ,p)` analysis, MCMC convergence, BIC, OOS RMSE | Continuous/inferential; not finite-exact; belongs to the Python pipeline + determinism gates, never to Lean. |

### 5.4 Hard prohibitions (build- and audit-enforced)

- **No `sorry`, no `admit`** in any delivered `theorem`/`def` (the §3 `sorry` markers are executor TODOs that MUST be discharged before the file is committed green; `warningAsError := true` + the manifest checker block them).
- **No project-local `axiom`, `opaque`, `constant`** in the delivered corpus (corpus rule). If a substrate fact must be assumed, it is **not** an `axiom` here; it is either (a) a delivered hypothesis on the theorem (the honest narrowing of §5.2), or (b) — only if unavoidable and only following the corpus opacity-guard pattern — an axiom **guarded by an opaque source predicate with no public constructor** so it cannot derive `False`, **and** logged as `partial`/`obligation` in the coverage table. The plan's intent is **zero** such guarded axioms; every target above is designed to need none.
- **Trust base allowlist** (`lean/manifests/trust_base.txt`, tracked): `{propext, Classical.choice, Quot.sound, choice, funext}` — the five core kernel axioms, identical to the corpus. The mathlib-free targets (T1, T2, T4, T6, T7) should close within the smaller `{propext, Quot.sound}` (Quot for the quotient `classify`/`Status`); T3 (mathlib) may use the full five. The manifest checker (§6) records each delivered theorem's `#print axioms` closure and **fails** if any axiom outside the allowlist appears.

---

## 6. Method: build, axiom audit, and CI wiring

**Inputs:** the seven module specs (§3), the lakefile + pins (§1), the disclosure tiers (§5).

**Method (executor, downstream):**
1. Scaffold `lean/` per §2; write `Common.lean` first (the shared finite-carrier + defect vocabulary).
2. Implement T1, T2, T7 (smallest, mathlib-free) to validate the build + axiom-audit pipeline end-to-end before the harder targets.
3. Implement T4, T6 (finite combinatorial), then T5 (explicit witness + decidable no-growing-mode certificate), then T3 (the only mathlib target) last.
4. After each target, run the **axiom audit**: a `lake exe`/script emits `#print axioms <decl>` for every delivered theorem and diffs the union against `trust_base.txt`; any extra axiom (or any `sorryAx`) ⇒ red. Record the per-decl closure in `coverage_table.md`.
5. Wire CI tier **T5** (`plan/02` §5): on any change under `lean/`, run `lake build` (fast `SbtCosmo` lib unconditionally; `SbtCosmoSchur` on PR-to-main / release), then the axiom audit, then a `grep`-guard for `sorry|admit|^axiom|opaque|constant` returning zero matches in `SbtCosmo/`. Budget <15 min for the mathlib-free set; the mathlib build is allowed a longer release-cadence budget.
6. Record `lean.{toolchain, mathlib_rev, build, axiom_audit}` in every experiment run manifest (`plan/01` §9.3) — a green Lean build is part of an `AOR_certified` record; a red/absent Lean build downgrades affected claims to `recognized_grade` (`plan/02` §6 G-ENV-9).

**Outputs:** a green `lake build`; `coverage_table.md` with every delivered declaration tiered; `trust_base.txt`; the per-decl axiom-closure log; the CI T5 workflow.

---

## 7. Pass/fail gates (quantitative)

These gate the **Lean deliverable only** (physics gates live in `plan/00` §6 and the E#.md files). The Lean track is **PASS** iff all of L1–L9 hold; otherwise the affected propositions are downgraded to `recognized_grade` per `plan/02` G-ENV-9 and the downgrade is itself statused (no silent failure).

| # | Gate | Quantitative threshold / criterion | Checked by |
|---|---|---|---|
| **L1** | **Build green** | `lake build` exits 0 for the `SbtCosmo` lib (mathlib-free) AND the `SbtCosmoSchur` lib (mathlib) under the pinned `lean-toolchain` (`v4.28.0`) + pinned `lake-manifest.json`. | CI T5 |
| **L2** | **Zero `sorry`/`admit`** | `grep -RnE '(\bsorry\b\|\badmit\b)' lean/SbtCosmo/` returns **0** matches; `#print axioms` of every delivered theorem contains **no** `sorryAx`. | CI T5 grep + axiom audit |
| **L3** | **Zero project-local escapes** | `grep -RnE '^\s*(axiom\|opaque\|constant)\b' lean/SbtCosmo/` returns **0** matches (target: exactly 0 guarded axioms; any guarded axiom must instead be a `partial` coverage row with a documented opacity guard — intended count **0**). | CI T5 grep |
| **L4** | **Trust-base closure** | every delivered theorem's `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound, choice, funext}`; mathlib-free targets (T1,T2,T4,T6,T7) ⊆ `{propext, Quot.sound}`. **0** axioms outside the allowlist. | axiom-audit script |
| **L5** | **Required-target coverage** | all **7** targets T1–T7 present and green; in particular the Overview §8 done-item-5 minimum is met: **P1 (T2) and P4 (T5) are `faithful`** complete proofs (no narrowing on the existence/positivity core); **P2 (T3a PSD) is `faithful`**; **P3 (T4) is delivered**. | coverage table + CI |
| **L6** | **Non-vacuity** | each existence/positivity target carries an explicit committed witness term that `decide` (preferred — kernel-checked; `native_decide` only where `decide` is computationally infeasible, and then each occurrence is a justified entry in the Lean trust baseline since it trusts the compiler — REGISTRY §11.7 / `ops/bin/lean-trust-scan.sh`) accepts: T2 `route_mismatch_pos_witness` (RM > 0), T5 `phantom_stable_readout_witness` (w_eff < −1 ∧ no-growing-mode), T6 `route_holonomy_nonzero` (loop ≠ id). A vacuous `∃` (e.g. empty carrier) **fails** — witnesses must use ≥2 states / ≥3 routes / ≥3 grid nodes. | reviewer + `example` checks |
| **L7** | **Disclosure completeness** | `coverage_table.md` has one row per delivered declaration; every `narrowed_surrogate`/`partial` row states its elevated hypothesis; every theorem has a scope disclaimer; **0** undisclosed narrowings. | reviewer + lint of coverage table |
| **L8** | **Structural alignment with Python** | the T2 RM witness carrier, the T5 `w_eff` grid + `z_c`, and the T6 route labels are **structurally identical** to the E0 toy / E3 grid / E4 route registry respectively (same state count, same route IDs); a divergence is a logged inconsistency. | reviewer cross-check vs `sbt_cosmo/` + coverage notes |
| **L9** | **Manifest recording** | every experiment run manifest records `lean.toolchain`, `lean.mathlib_rev`, `lean.build ∈ {green, red, absent}`, and `lean.axiom_audit ∈ {pass, fail}`; an `AOR_certified` claim requires `green` + `pass`. | `plan/01` §9.3, `plan/02` §3 |

**Failure semantics (honest, per F9 / No-Unstatused-Residual).** A red L1/L2/L4 on a given target downgrades exactly the propositions that target backs to `recognized_grade` and records the reason; it does **not** silently pass. A deliberately deferred hard direction (e.g. exact-adequacy hard cycle) is **not** a failure — it is a disclosed `narrowed_surrogate` row (L7), which is the expected, honest state for T3b.

---

## 8. Outputs of executing this plan (artifacts the executor must produce)

1. `lean/lean-toolchain` (`leanprover/lean4:v4.28.0`), `lean/lakefile.lean` (§1.3), `lean/lake-manifest.json` (pinned mathlib commit).
2. `lean/SbtCosmo/{Common, Idempotence, RouteMismatch, Schur, LocalGlobal, PhantomStableReadout, Holonomy, AORStatus}.lean` — the seven targets + shared base, all green, **no `sorry`/`admit`/`axiom`/`opaque`/`constant`**.
3. `lean/manifests/trust_base.txt` (the five-axiom allowlist) and `lean/manifests/coverage_table.md` (one tiered, scope-disclaimed row per declaration).
4. The axiom-audit script + the CI **T5** workflow wiring (`lake build` + grep guards + axiom diff), fail-closed.
5. `lean/README.md` — what each receipt certifies, the scope disclaimers, the target→P1–P4→E0–E8 map (§4), and `lake build` instructions.

No experiment results, no cosmology runs, and no manuscript prose are produced here (those are out of scope per the hard constraints and `plan/00` §2).

---

## 9. Consistency check against the SHARED GROUNDING BRIEF and sibling plans

- **Toolchain/mathlib:** `v4.28.0` + selective, commit-pinned mathlib — exactly `GROUNDING_BRIEF` §II.D and `plan/02` §1.6; T3 isolated as the sole mathlib consumer keeps the build fast for CI T5.
- **Module layout:** elaborates `plan/01` §5 file list (adds `Common`, `Schur`, `LocalGlobal`, `manifests/`); `.lake/` gitignored, green build = receipt recorded in the manifest — verbatim with `plan/01` §5/§9.3.
- **Propositions:** T1–T7 realize Overview §5's P1–P4 (and exceed the §8 done-item-5 minimum); F2/F4/F9/F11 anchors and the Adequacy Schur residual are used exactly as Overview §5/§10 and `Foundations_IV`/`Adequacy_Residuals` specify.
- **Gates:** L1–L9 instantiate `plan/02` G-ENV-9 (build green, no `sorry`, else `recognized_grade`), `plan/01` G-REPO-14 (`lake build` green + toolchain/mathlib recorded) and G-REPO-10 (no-unstatused-residual, here T7), and `GROUNDING_BRIEF` §VI gates 5 (T5), 6 (T2), 7 (T6).
- **Disclosure discipline:** the three-tier `faithful`/`narrowed_surrogate`/`partial` scheme, the trust-base allowlist, the opacity-guard prohibition, and the coverage table are taken directly from the `AOR` and `Foundations_IV` corpus mechanization sections — this repo's Lean honesty contract is identical to the established Six Birds corpus contract.
```
