# Six Birds Theory — Paper Index

> Literature index for `docs/papers/`. 48 papers by Ioannis Tsiokos (2026).
> Purpose: quick reference + searchable knowledge base over the Six Birds Theory (SBT) corpus.
> Each entry links the source `.tex`, gives the one-line scope, key constructs, and what it explicitly does **not** claim.

## How to use this index
- Jump to a **theme** (sections A–F) for the structural map of the corpus.
- Use the **Concept → Paper lookup** at the bottom to find which papers ground a given idea.
- Search this file for a keyword (e.g. `route mismatch`, `idempotence defect`, `holonomy`, `AOR`, `Clay`) to locate the relevant sources.

## The shared vocabulary (read this first)
SBT models a system observed through a deterministic coarse-graining ("lens") using six primitive closure roles, the **"six birds" P1–P6**:

| Bird | Role | Gloss |
|------|------|-------|
| **P1** | Operator rewrite / closure | dynamics expressible in the layer's own variables (idempotent endomap with fixed points) |
| **P2** | Constraints / gating / feasibility | which transitions/observations are admissible |
| **P3** | Protocols / holonomy | composition order matters; loop residue = curvature/route dependence |
| **P4** | Staging / refinement | ladder of resolutions and timescales `τ` |
| **P5** | Packaging | quotient microstates into macro "objects" by indistinguishability |
| **P6** | Accounting / audit | cost ledger; directionality and budget certificates |

Recurring measurable diagnostics: **idempotence defect** `δ` (does closure stabilize), **route mismatch** (does coarse-graining commute with dynamics), **arrow audit** (path-reversal KL asymmetry `Σ_T`), **closure deficit**, **adequacy residual** `Ξ`. A "theory" = a closure = (lens + completion + audit). Most papers pair Lean 4 mechanization with deterministic Python experiments and an explicit non-claims register.

---

## A. Foundations & core calculus
The framework itself — primitives, meta-theory, no-go limits.

- **[Foundations I: Foundations of Emergence Calculus](Tsiokos_2026_Six_Birds_Foundations_of_Emergence_Calculus.tex)** — 25 Jan 2026 · [zenodo.18365949](https://doi.org/10.5281/zenodo.18365949)
  Math-only framework: theories are fixed points of idempotent operators; open-endedness needs changing the operator, not iterating it. Derives P1–P6 canonically (Thm meta-prim) from composability + bounded interface. Defines TV idempotence defect, arrow-of-time as path-space KL (data-processing inequality), protocol-trap principle, and a finite forcing counting lemma (definable predicates are exponentially rare). *The root paper.*

- **[Foundations II: Admissibility, Meta-Theory, and the Exact-Six Program](Tsiokos_2026_Six_Birds_Foundations_II_Admissibility_Meta_Theory_and_the_Exact_Six_Program.tex)** — [zenodo.19672278](https://doi.org/10.5281/zenodo.19672278)
  Lifts Foundations I to theorem level: primitive role architecture (levels, boundaries, selected lifts of P1–P6); admissibility/meta-theory regime; scoped **exact-six theorem** over the domain `FATCD` (finite audited typed closure descriptions) — every D decomposes into exactly six role channels, no seventh role needed in scope. Existential (not unique) decomposition.

- **[Foundations III: A Finite Audited Interaction Calculus for SBT](Tsiokos_2026_Six_Birds_Foundations_III_A_Finite_Audited_Interaction_Calculus_for_SBT.tex)**
  Constructs `BirdInt`, a finite typed calculus recording how the six roles interact (directed cells, defects→statuses, promotion gates, no-go judgments). Theorems 1–35; 12 countermodels each blocking a specific overclaim; 4 host-bound model realizations (PICA, Cantor, abstract-interpretation, graph/cohomology). Lean 4 validator (lean4 v4.28.0).

- **[Foundations IV: A Catalog of Layer-Agnostic Structural Laws](Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex)**
  Catalog of **52 layer-agnostic laws** in a uniform normal form (setup/theorem/proof-spine/cases/interaction/nonclaims), spanning analysis, arithmetic, physics, biology, chemistry, economics, linguistics, cognition, computation. 46 direct Lean theorems + delegated/wrapper anchors with opacity-guarded trust-base axioms.

- **[No-Go Theorems for Audited Emergence](Tsiokos_2026_Six_Birds_No_Go_Theorems_for_Audited_Emergence.tex)** — 23 Mar 2026 · [zenodo.19187777](https://doi.org/10.5281/zenodo.19187777)
  Eight no-go theorems constraining honest finite emergence narratives: deterministic data-processing inequality (observation can't increase arrow), reversible+stationary ⇒ zero arrow, graph obstructions for force-like drives, variational closure-deficit identity, bounded-interface saturation (no unbounded laddering).

- **[Protocol Trap: Holonomy Without Entropy Production](Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex)** — 8 Mar 2026 · [zenodo.18906902](https://doi.org/10.5281/zenodo.18906902)
  Separates **route dependence (holonomy)** from **arrow of time**. Autonomous lifted-protocol formulation + path-reversal audit on a 3-state benchmark: external scheduling has EPR>0; autonomous unbiased-clock lift collapses arrow to 0; clock bias restores positive arrow. Reduces false-positive directionality.

---

## B. The "To X a Stone" applied series
SBT instantiated as an emergence calculus in a specific domain. Each is validation-first (Python diagnostics + Lean anchors), with null/driven controls.

- **[To Count a Stone — A Mathematics is A Theory](Tsiokos_2026_To_Count_a_Stone_with_Six_Birds_A_Mathematics_is_A_Theory.tex)** — [zenodo.18402004](https://doi.org/10.5281/zenodo.18402004)
  Calculus/analysis as closure: which compressions of discrete protocols stay coherent under refinement toward a continuum. Limits/completions/renormalizations as P4 staging + P6 accounting + P5 packaging. Discrete Leibniz identity forces derivation structure; Lean anchor for derivation uniqueness on polynomial rings.

- **[To Plot a Stone — Constructing and Auditing Emergent Geometry from Markov Dynamics](Tsiokos_2026_To_Plot_a_Stone_with_Six_Birds_Constructing_and_Auditing_Emergent_Geometry_from_Markov_Dynamics.tex)** — 5 Feb 2026 (v2 27 Feb) · [zenodo.18494975](https://doi.org/10.5281/zenodo.18494975)
  Geometry without assuming space: points = indistinguishability classes (P5), distance = optimized protocol cost / shortest path (P3+P6), curvature = loop holonomy. Exhibits E1–E5: plane/curved/fractal/anisotropic regimes + Pythagoras emergence. Companion to *To Count*. Repo: github.com/ioannist/six-birds-space.

- **[To Create a Stone — Emergent Geometric and Thermodynamic Regimes from a Minimal Stochastic Substrate](Tsiokos_2026_To_Create_a_Stone_with_Six_Birds_Emergent_Geometric_and_Thermodynamic_Regimes_from_a_Minimal_Stochastic_Substrate.tex)** — 2 Mar 2026 · [zenodo.18838994](https://doi.org/10.5281/zenodo.18838994)
  Defines **PICA** (Primitive Interaction Closure Algebra): 6×6 enable matrix ⇒ up to 36 directed interactions. 2307-run campaign (n=32–256) finds resolution-dependent signatures of geometry & stochastic thermodynamics (least-action dominance, diffusion embeddings, time-asymmetry). PICA = reusable spec object for closure mechanisms.

- **[To Become a Stone — A Physics is A Theory](Tsiokos_2026_To_Become_a_Stone_with_Six_Birds_A_Physics_is_A_Theory.tex)** — 29 Jan 2026 (v2 10 Feb) · [zenodo.18412131](https://doi.org/10.5281/zenodo.18412131)
  Multi-scale model reduction as closure-audit calculus; each physics theory = packaging operator (lens+completion+diagnostics). Three certificates: closure coherence (idempotence), audit monotonicity (DPI), route mismatch. Four instantiations: quantum dephasing, BGK kinetic closure, filtered Burgers/LES, nonlinear averaging/backreaction.

- **[To Chart a Stone — Emergence Phase Diagrams for Effective Theories in Control Space](Tsiokos_2026_To_Chart_a_Stone_with_Six_Birds_Emergence_Phase_Diagrams_for_Effective_Theories_in_Control_Space.tex)** — [zenodo.19038292](https://doi.org/10.5281/zenodo.19038292)
  **Emergence atlases**: where on control space a macro-description is feasible (closed + nontrivial + audit-safe + budget-feasible). Computed for analytic law families, full packaging spaces, and PICA. Reframes emergence as a phase-diagram problem; rival emergence definitions = slices of one atlas.

- **[To Notch a Stone — Time as a Theory Artifact of Order, Measure, and Arrow](Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex)** — 5 Feb 2026 · [zenodo.18495363](https://doi.org/10.5281/zenodo.18495363)
  Time as a closure artifact: order (succession) + ticks (staged carriers) + arrow (irreversible bookkeeping). Distinguishes causation-time (fixed closure) from enablement-time (closure rewritten). Finite Markov lab `Z=X×Φ×R`; four controlled separations (null vs driven arrow, coarse-graining reduces arrow, budget vs clock drift, closure-defect-triggered extension).

- **[To Cast a Stone — A Closure-Deficit Account of Randomness under Packaging and Budget](Tsiokos_2026_To_Cast_a_Stone_with_Six_Birds_A_Closure_Deficit_Account_of_Randomness_under_Packaging_and_Budget.tex)** — 9 Mar 2026 · [zenodo.18926433](https://doi.org/10.5281/zenodo.18926433)
  Randomness = predictive residue of non-closure (third option vs ontic/epistemic). Closure deficit `CD_τ(Π)=I(X_t; Y_{t+τ}|Y_t)`; exact entropy decomposition. Vanishes on lumpable partitions; rises with within-fiber heterogeneity; tracks route mismatch. Connects coarse-graining, limited prediction, and one-wayness (hashing).

- **[To Spend a Stone — Currency–Constraint Duality and Shadow Prices Across Closure Layers](Tsiokos_2026_To_Spend_a_Stone_with_Six_Birds_Currency_Constraint_Duality_and_Shadow_Prices_Across_Closure_Layers.tex)** — 9 Mar 2026 · [zenodo.18926771](https://doi.org/10.5281/zenodo.18926771)
  **Currency–constraint principle**: lower-layer currencies become higher-layer constraints; higher-layer currencies = shadow prices of those budgets. Constrained max-entropy closure yields dual prices. Explains why temperatures, prices, regularizers, attention weights are the same mathematical object. Lean: deterministic-pushforward KL monotonicity.

- **[To Throw a Stone — On Agents and Agenthood](Tsiokos_2026_To_Throw_a_Stone_with_Six_Birds_On_Agents_and_Agenthood.tex)** — 31 Jan 2026 (v2 10 Feb) · [zenodo.18439737](https://doi.org/10.5281/zenodo.18439737)
  Agency in finite controlled Markov kernels without goals/utilities. Three metrics: viability kernels, feasible empowerment (channel capacity under budgets), packaging idempotence defect (objecthood). Separates **agenthood** (enablement: layer persists) from **agency** (causation: interventions change futures). Lean: viability-kernel fixed point.

- **[To Wake a Stone — Audited Life-Like Signatures in Toy Substrates](Tsiokos_2026_To_Wake_a_Stone_with_Six_Birds_Audited_Life_Like_Signatures_in_Toy_Substrates.tex)** — 27 Jan 2026 (v2 16 Feb) · [zenodo.18394536](https://doi.org/10.5281/zenodo.18394536)
  Life-motivated case study (NOT a claim of creating life). Theory packages for particle + neural substrates; claims indexed to machine-readable artifact ledger. Null calibration, separable drive channel (P6), protocol holonomy as diagnostic. Explicitly disclaims open-ended ALife evolution.

- **[To XOR a Stone — Closure Diagnostics for Emergent Bits, Gates, and Booleanity](Tsiokos_2026_To_XOR_a_Stone_with_Six_Birds_Closure_Diagnostics_for_Emergent_Bits_Gates_and_Booleanity.tex)** — 9 Mar 2026 · [zenodo.18919370](https://doi.org/10.5281/zenodo.18919370)
  When does a substrate *earn* a logic layer? Logic layer = audited closure of packaged predicates. Feasibility view (propositions as feasible sets) + operator view (bits as classes, gates as macro-updates). Parity/XOR is an unusually robust coarse variable; CNOT→erased-XOR degrades closure (>8× unretained info). Falsifiable criterion for "has logic."

- **[To Chat a Stone — Language Theory Models](Tsiokos_2026_To_Chat_a_Stone_with_Six_Birds_Language_Theory_Models.tex)**
  **LTMs** (Language Theory Models): a language model as an audited ledger of finite theory extensions, not a parameter vector. Non-gradient; accumulates typed transition evidence; proposes new layers only on strict-extension certificate from a gate panel. Shakespeare feasibility study; structural probe suite (blue/red-team). Contrast with next-token prediction.

- **[To Classify a Stone — Primitive Activation and Observable Separation of Layer-Birth Classes](Tsiokos_2026_To_Classify_a_Stone_with_Six_Birds_Primitive_Activation_and_Observable_Separation_of_Layer_Birth_Classes.tex)** — 16 Mar 2026 · [zenodo.19047665](https://doi.org/10.5281/zenodo.19047665)
  How many *kinds* of layer-birth are experimentally accessible. Taxonomy of 4 classes by activation of packaging (P5), drive (P6), staging anomaly (P4). Class-I vs Class-II separation strongest (affinity at birth, no-fake-arrow controls). Capacity/depth is a post-birth field, not a primary classifier.

- **[To Lay a Stone — Finite-State Semantics for Packaging, Directionality, and Coarse-Graining](Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex)** — 15 Feb 2026
  **No-smuggling minimal-substrate semantics** for SPT: canonical machine class `S_min` (phase-in-state, deterministic lenses, induced `E_{τ,f}`, intrinsic audits `Σ_T` & ACC affinities). Protocol-trap separation, coarse-graining never increases `Σ_T`, holonomy defect with gain+mismatch bound. Turns SPT from a language into a compilation target. Lean idempotent/closure backbone.

- **[To Flatten a Stone — Critical Pairs, Holonomy, and Confluence in Rewriting Systems](Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex)** — 17 Mar 2026 · [zenodo.19061345](https://doi.org/10.5281/zenodo.19061345)
  Confluence (order-independence) and flatness (path-independence) share a local core once rewriting carries 2-cells. Reduction 2-complex; elementary flatness = local confluence. Completion = holonomy elimination. Verified on finite-ARS / string / left-linear TRS stress tests.

---

## C. Clay / hard-problem conditional closures
Conditional ("recognition-grade") closures of named open problems, all under the SB closure assumption. **None claims an unconditional standard-ZFC / Clay-Millennium result.**

- **[One Meta-Theory, Three Clay-Problem Closures](Tsiokos_2026_One_Meta_Theory_Three_Clay_Problem_Closures.tex)**
  Meta-theoretic synthesis over NS + RH + P vs NP (does not re-prove them). Negative half **Foreclosure**: typed primary carriers fall into a finite state space (non-target-equiv / tautological / bridge-failed / matrix-element-terminal). Positive half **Recognition-Mode Landing**: 7-stage route importing the load-bearing source as named recognition. 17-row formal catalog; 9 opacity-guarded obligation axioms. (BSD, Hodge out of scope.)

- **[Navier–Stokes as a Layer-Dissolving Membrane Theorem](Tsiokos_2026_Navier_Stokes_as_a_Layer_Dissolving_Membrane_Theorem.tex)**
  Applies adequacy-residual calculus + layer-dissolving endpoint to 3D incompressible NS Cauchy problem. Bradshaw–Grujić/BKM dissolving readout, audited source ledger, no-go family, Gevrey radius gate, Littlewood–Paley transport. Under closure bundle R1–R9: smooth divergence-free data (H^γ, γ>5/2) ⇒ `T_max=∞`. Recast as AOR membership witness. No unconditional Clay claim.

- **[Six Birds for Navier–Stokes: A Mechanized No-Zeno Scaffold](Tsiokos_2026_Six_Birds_for_Navier_Stokes_A_Mechanized_No_Zeno_Scaffold.tex)** — 4 Mar 2026 · [zenodo.18862865](https://doi.org/10.5281/zenodo.18862865)
  Multiscale decision scaffold separating inequality logic / NS hinge assumptions / numerics. Lean: No-Zeno engine, route-stability⇒polynomial-capacity, discrete no-go (localized tests force pointwise gain). SBT-legal variant excludes strong localization. Pinpoints where a Clay proof needs a new NS inequality; PDE implications stated as OPEN.

- **[Riemann Hypothesis via Self-Dual Trace Confinement: A Conditional Closure](Tsiokos_2026_Riemann_Hypothesis_via_Self_Dual_Trace_Confinement_A_Conditional_Closure.tex)**
  Moves RH to a formed-layer trace setting (saturated Selberg trace closure of completed ζ + functional-equation involution). Translation theorem T: anti-invariant zero ledger `AZ=0` ⇔ all nontrivial zeros on Re=1/2. Conditional landing chain uses SDTC (next paper). Outside SBT: `Γ_SDTC-Selberg ⇒ RH`. Lean mathlib-free. Not an unconditional ZFC proof.

- **[P ≠ NP under Closure of the Saturated SAT Layer](Tsiokos_2026_P_NP_under_Closure_of_the_Saturated_SAT_Layer.tex)**
  Conditional separation inside SBT. Saturated SAT layer `T_sat` observed via lawful poly-time instrument. Translation Theorems A/B reduce SAT∈P to currentization of the canonical witness producer. Under hypothesis `CSL_SAT-Hidden` (from *Hiddenness*): SAT∉P ⇒ P≠NP at recognition grade. **Class-B Irremovability** theorem = a relativization/natural-proofs/algebrization-style barrier, internal to SBT. No unconditional ZFC claim.

- **[Six Birds for Incompleteness: Fixed Packages, Package Change, and Conditional Arithmetic Lift](Tsiokos_2026_Six_Birds_for_Incompleteness_Fixed_Packages_Package_Change_and_Conditional_Arithmetic_Lift.tex)** — 24 Mar 2026 · [zenodo.19201835](https://doi.org/10.5281/zenodo.19201835)
  Formal theory = packaged closure on a frozen ledger. Fixed idempotent package saturates (no persistent strict growth) ⇒ growth needs package change. Restricted alignment theorem (efficiency transfers across cone-equivalent reps). Conditional arithmetic lift. Gödel = canonical fixed-package failure mode; new axioms = controlled package changes.

---

## D. Meta-theory machinery & transferable structural laws
Reusable apparatus cited across the corpus.

- **[Audited Operational Realisability (AOR): A Closure-Completion Reflection for Carriers with Audit Data](Tsiokos_2026_Audited_Operational_Realisability_A_Closure_Completion_Reflection_for_Carriers_with_Audit_Data.tex)**
  Meta-theory of typed carriers that close as audit systems. PreSB carrier + discharged obligations = AOR carrier. Canonical completion via Knaster–Tarski reflection `ClSB ⊣ ι`; 8-stratum defect `Ξ_SB`; 12-type residual atlas; hierarchy `RefStableAOR ⊆ CascadeStableAOR ⊆ AOR`. Newman's-lemma confluence. *Cited by NS, RH, P≠NP for the "carrier doesn't blow up in reality" record-level reading.*

- **[Self-Dual Trace Confinement (SDTC): A Structural Law for Formed Closures Under Involutive Self-Duality](Tsiokos_2026_Self_Dual_Trace_Confinement_A_Six_Birds_Structural_Law_for_Formed_Closures_Under_Involutive_Self_Duality.tex)**
  When must an involution-associated operator obstruction vanish? **Duality-confinement membrane theorem**: separating anti-invariant readout + positive domination records `AX ⪯ B_n` with `tr B_n→0` ⇒ anti-invariant ledger vanishes, mass confined to fixed locus. The recognition source for RH. Cross-substrate generalizations (CPT, gauge, function-field RH) are *predictions, not theorems*. Lean mathlib-free.

- **[Adequacy Residuals and Blind-Spot Currency](Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex)**
  What a dissolving probe family D measures beyond a native family L under audit energy C. Adequacy residual `Ξ_C(D|L)` = Schur complement of block currencies; projection identity, optimal-residual/exact-adequacy theorems, chain-rule/DPI/transfer laws, blind-spot witness (failed budget ⇒ explicit recombination vector). The `Ξ`-calculus used by *Emergence IS the Needle Killer* and NS.

- **[Emergence IS the Needle Killer](Tsiokos_2026_Emergence_IS_the_Needle_Killer.tex)**
  How "needle" obstructions stop being obstructions: passage to a higher layer with more dissolving probes. Formed-layer membrane setting (legal quotient + quadratic native currency + adequacy residual). **Layer-dissolving endpoint theorem** (no dissolving predictive needles in scope) + duality-confinement membrane theorem. Framework-bound, not universal singularity elimination. (Ξ-calculus from *Adequacy Residuals*.)

- **[Hiddenness as a Structural Law of Emergence](Tsiokos_2026_Hiddenness_as_a_Structural_Law_of_Emergence.tex)**
  When does prediction become trivial? Predictive content collapses exactly when an upstream determining state is exposed to current observation. Visibility-coupling predicate `Exposure(Lift,Substrate)`; typed **CSL core** (4 clauses). Granularity-mismatch theorem: framework's current/predictive quotients are strictly finer than P/NP at history level. *Supplies the `CSL_SAT-Hidden` hypothesis used by P≠NP.*

- **[Holonomy with Memory: Predictive Quotients, Witnesses, and Fixed-Support Route Transport](Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex)** — Apr 2026
  Histories equivalent at a current interface yet differing as predictors. Current quotient `CurrentQ` vs predictive quotient `PredictiveQ`; predictive is future-sufficient and universal. Strict refinement ⇔ current-equivalent-but-future-distinct pair; loop can act trivially on Current but not Predictive. Finite benchmarks (artifact/flattenable/latent/dissipative/coherent). *Foundational for the fixed-support series.*

- **[Reflexive SBT and Anti-Localization](Tsiokos_2026_Reflexive_SBT_and_Anti_Localization.tex)** — 15 Feb 2026
  Apply SBT primitives to the *artifacts of packaging themselves* (subspaces, feasibility dictionaries, route ladders). Localization metric `η_j` at scale 2^-j bounded by three capacities (trace/diagonal dispersion, sparse-support conditioning, route-union ledger). Conditional theorem: vanishing capacity ⇒ `η_j→0`. Needles = the obstruction turning global ledgers into sup-type bottlenecks.

- **[Strict Theory Extension on a Lawful Continuous Cantor Shell](Tsiokos_2026_Strict_Theory_Extension_on_a_Lawful_Continuous_Cantor_Shell.tex)** — [zenodo.19189353](https://doi.org/10.5281/zenodo.19189353)
  Continuous Cantor substrate from six interacting mechanisms; audited shell where full-loop dynamics are lawful. Base cocycle-pressure theory `T_0` vs completion-extension `T_1`. Four theoremlets incl. **strict theory-extension** (`T_1` not definable from `T_0`) and a thermodynamic pressure-disintegration consequence. Theorem of *theory depth*, scoped to the audited shell.

- **[The Usefulness of Non-Descending Objects: A Six Birds Theory of Mathematical Applicability](Tsiokos_2026_Why_Mathematics_Even_Works.tex)** (file: *Why_Mathematics_Even_Works*)
  Why a mathematical object is useful when it doesn't live in the problem's layer (imaginaries, infinitesimals, Galois roots, cohomology classes). Theory layers + promotion bridges + **Strict Audited Utility (SAU)** certificate. Theorem stack A–G: strict usefulness forces hidden non-descent + audited boundary descent. Four canonical witnesses. Lean = traceability harness.

- **[Persistence of SPT-Legality from Channelized Feasibility in a Multiscale Hilbert/Cell Model](Tsiokos_2026_Persistence_of_SPT_Legality_from_Channelized_Feasibility_in_a_Multiscale_Hilbert_Cell_Model.tex)** — 15 Feb 2026
  Is anti-localization legality forward-closed under time evolution? Slot-audited channelized-feasibility contract; legality via normalized max-cell concentration audit `κ_j` + feasible representations with packaging projectors. Theorem-grade constants (delocalization, frame bounds, mode growth, cellwise defect) + matched failure-mode controls. Closed regression-tested regime for "SPT-legal evolution"; finite-dim only.

---

## E. Fixed-support / Route A series
A tightly linked program building, layer by layer, on a frozen exact-finite "Route A flagship" corpus: event packaging → recombination → promotion → carrier → events/tests. Builds non-Hilbert interference-like structure without importing Hilbert space or the Born rule. Read roughly in this order.

- **[Marking, Erasure, and Recombination on Fixed Support](Tsiokos_2026_Marking_Erasure_and_Recombination_on_Fixed_Support_Exact_Finite_Evidence_from_Six_Birds_Theory.tex)** — Apr 2026
  Branch assemblages; branchwise predictive quotient `K_i` vs recombination quotient `R_i`. Benchmark suite separating classical mixture / hidden memory / route-marked suppression / erasure-conditioned recovery / cyclic / dissipative washout / artifacts. Theorem layer + aligned Lean witness. Narrow claim: recombination phenomena arise on fixed support and audit exactly.

- **[Recombination Witnesses on Fixed Support: Control-Stable Anchors and a Formal Kernel](Tsiokos_2026_Recombination_Witnesses_on_Fixed_Support_Control_Stable_Anchors_and_a_Formal_Kernel_in_Six_Birds_Theory.tex)** — Apr 2026
  Isolates a control-stable intrinsic two-anchor relative-cycle family where branchwise predictive agreement doesn't determine recombination observables. Exact-finite separation for two flagship anchors; Lean witness kernel + no-factorization corollary; matched control bundle.

- **[Promotion Criteria and Surviving Packages on Fixed Support](Tsiokos_2026_Promotion_Criteria_and_Surviving_Packages_on_Fixed_Support_in_Six_Birds_Theory.tex)** — Apr 2026
  Defines a **promotion criterion** (sufficiency, induced-update closure, 2nd-stage stability, control admissibility, protocol honesty, slice legibility). On a frozen Route A corpus an intrinsic candidate package survives honestly. Lean criterion kernel. Narrow claim: ≥1 promoted-package candidate survives.

- **[Internal Structure of a Surviving Promoted Package on Fixed Support](Tsiokos_2026_Internal_Structure_of_a_Surviving_Promoted_Package_on_Fixed_Support_in_Six_Birds_Theory.tex)** — Apr 2026
  Classifies the survivor: verdict = **intrinsic package** (the intrinsic non-indexed candidate uniquely combines descended readout, 2nd-stage stability plateau, retained invariant/quadratic families, protocol honesty). Nearby positives = erased-partner interpretation.

- **[Carrier Exactification after Promotion on Fixed Support](Tsiokos_2026_Carrier_Exactification_after_Promotion_on_Fixed_Support_in_Six_Birds_Theory.tex)**
  Internal carrier status of the survivor: lawful same-branch witness + coarse public signature shadow + protocol-indexed carrier surface, linked by **non-faithful public compression**. Seven-criterion exactification audit; 3 quadratic + 2 proto-event/test families survive. Lean verdict mirror.

- **[Carrier-to-Event Admissibility on Fixed Support](Tsiokos_2026_Carrier_to_Event_Admissibility_on_Fixed_Support_in_Six_Birds_Theory.tex)**
  Event bridge record `B_E=(C,P,I,L,V,Θ,S,A)`. From 17 candidates, 2 accepted as protocol-indexed event-level objects; **no finite admissible test family** (a readout-agreement slot is unrealized). Verdict: scoped event-level structure without accepted tests / shared-event identity / proto-effects.

- **[Accepted New-Layer Strict Tests on Fixed Support](Tsiokos_2026_Accepted_New_Layer_Strict_Tests_on_Fixed_Support_in_Six_Birds_Theory.tex)**
  Closes the test gap via a layer-local PICA route (promotion → internalize protocol coords → carrier exactification → audited source admission) producing NewLayer carriers where readout-agreement/quadratic/transition slots strict-realize natively. Accepted strict test families survive a 7-check control panel. Result: strict theory extension at the new layer.

- **[Locally Boolean, Globally Obstructed: Event Packages and Admissible Global Packaging](Tsiokos_2026_Locally_Boolean_Globally_Obstructed_Event_Packages_and_Admissible_Global_Packaging_in_Six_Birds_Theory.tex)** — 31 Mar 2026
  Contextuality-type obstruction arising from a system's own packaging — no Hilbert space/amplitudes/Born rule imported. Finite event package (local Boolean algebras + layer-relative shared-event ID + audit); obstruction = failure of admissible global realization. Stratified results (mechanism/lens/packaging axes). First computationally explicit such evidence.

---

## F. Physics applications (empirical / interpretive)
SBT applied to real physics theory and released datasets.

- **[A Six-Birds' Eye View of Quantum Theory: Operational Closure Semantics for Measurement, Contextuality, and Record Stability](Tsiokos_2026_A_Six_Birds_Eye_View_of_Quantum_Theory_Operational_Closure_Semantics_for_Measurement_Contextuality_and_Record_Stability.tex)** — 11 Feb 2026 (v2 16 Feb) · [zenodo.18608833](https://doi.org/10.5281/zenodo.18608833)
  Recasts measurement/contextuality/measurement-problem via SBT operational semantics. Separates causal dynamics from **packaging** (idempotent closure stabilizing records). SBT package `(Z,T,f,Q_f,U_f,E_f,A)`, Lean lemmas + Python. Dephasing = idempotent packaging (fixed points = diagonal states); route mismatch ≈0 iff diagonal Hamiltonian; double-slit/eraser; system–apparatus–environment. Does NOT derive Born rule or resolve Bell.

- **[A Six Birds' Eye View of Dark Energy: Closure, Route Mismatch, and Audits for Apparent Acceleration](Tsiokos_2026_A_Six_Birds_Eye_View_of_Dark_Energy_Closure_Route_Mismatch_and_Audits_for_Apparent_Acceleration.tex)** — 5 Feb 2026 (v2 10 Feb) · [zenodo.18494480](https://doi.org/10.5281/zenodo.18494480)
  Cosmological modeling as a closure package (lens+completion+audits); separates fundamental component from coarse-graining closure correction. Route mismatch 0 in linear regime, >0 with nonlinearity; heterogeneous patches give positive acceleration proxy. Demonstrated on DES SN5YR + DES Y6 BAO. Frames "dark energy" as audit-driven rewrite hypothesis. A cosmological constant is **not** ruled out.

- **[Six Birds for Neutrino Mass: Lens-Swap Stability and Packaging Audits](Tsiokos_2026_Six_Birds_for_Neutrino_Mass_Lens_Swap_Stability_and_Packaging_Audits.tex)** — 2 Mar 2026
  Casts the SPT-3G 2018→D1 likelihood swap (tightening Σm_ν toward the m_ν=0 boundary) as a packaging-stability problem. Directional cross-lens audit functional; held-out mismatch `δχ`, spectrum/multipole localization, common-staging control; reproduced under DESI DR2 BAO. Mismatch large/asymmetric, TT high-ℓ (ℓ~2000–3000) dominates. Doesn't identify pipeline root cause or fix a Σm_ν value.

---

## Concept → Paper lookup
Find the grounding source(s) for a concept.

| Concept / keyword | Primary papers |
|---|---|
| **Primitives P1–P6, derivation of** | Foundations I, II, III |
| **Exact-six theorem** | Foundations II, III |
| **52 / catalog of structural laws** | Foundations IV |
| **No-go theorems, audited limits** | No-Go Theorems; Foundations IV |
| **Idempotence defect `δ`** | Foundations I; To Become; To Plot; To Throw |
| **Route mismatch** | Foundations I; To Become; Dark Energy; Quantum Theory |
| **Arrow of time / path-reversal KL `Σ_T`** | Foundations I; No-Go; Protocol Trap; To Notch; To Lay |
| **Protocol trap (holonomy ≠ arrow)** | Protocol Trap; Foundations I; To Lay; To Notch |
| **Holonomy / curvature / route dependence** | Protocol Trap; To Plot; Holonomy with Memory; To Flatten |
| **Closure deficit** | To Cast; No-Go; To Chat |
| **Adequacy residual `Ξ` / Schur complement** | Adequacy Residuals; Needle Killer; Navier–Stokes |
| **AOR (audited operational realisability)** | AOR; cited by NS, RH, P≠NP |
| **SDTC / duality-confinement membrane** | SDTC; RH; Needle Killer |
| **Hiddenness / CSL / Exposure predicate** | Hiddenness; P≠NP; Foundations IV |
| **PICA (interaction closure algebra)** | To Create; To Chart; Foundations III; Accepted New-Layer |
| **Fixed-support / Route A / recombination** | (Section E, all 8); Holonomy with Memory |
| **Predictive vs current quotient** | Holonomy with Memory; Hiddenness |
| **Promotion / surviving package** | Promotion Criteria; Internal Structure; Carrier Exactification |
| **Contextuality / locally-Boolean obstruction** | Locally Boolean; Quantum Theory |
| **Emergent geometry / distance as accounting** | To Plot; To Create; To Chart |
| **Emergent time** | To Notch |
| **Randomness / one-wayness** | To Cast |
| **Currency / shadow prices / duality** | To Spend |
| **Agency / agenthood / empowerment / viability** | To Throw |
| **Life-like / ALife** | To Wake |
| **Logic / bits / gates / Booleanity** | To XOR |
| **Language models (non-gradient)** | To Chat |
| **Layer-birth taxonomy** | To Classify |
| **SPT minimal-substrate semantics** | To Lay; Persistence of SPT-Legality; Reflexive SBT |
| **Rewriting / confluence / critical pairs** | To Flatten |
| **Anti-localization / needles / `η_j` / `κ_j`** | Reflexive SBT; Persistence of SPT; NS No-Zeno |
| **Mathematical applicability / SAU / non-descent** | Why Mathematics Even Works; To Count |
| **Strict theory extension / definability** | Strict Cantor Shell; Foundations I; Accepted New-Layer |
| **Clay problems (NS / RH / P vs NP)** | One Meta-Theory; Navier–Stokes; NS No-Zeno; RH; P≠NP |
| **Incompleteness / Gödel / package change** | Six Birds for Incompleteness |
| **Cosmology / dark energy / DES** | Dark Energy |
| **Neutrino mass / SPT-3G / DESI** | Neutrino Mass |
| **Quantum measurement / dephasing / eraser** | Quantum Theory |

---

## Notes
- **Author:** Ioannis Tsiokos (ioannis@automorph.io / Automorph Inc.), all 2026.
- **Methodology pattern:** most papers pair **Lean 4** mechanization (often mathlib-free) with deterministic **Python** experiments, matched null/driven controls, and an explicit **non-claims register**.
- **Claim grades** recur: `accepted` (theorem-grade) vs `recognition`/`model_realization`/`real-provisional` (conditional on a named structural hypothesis or host).
- Several papers were revised (v2); dates above are first-version unless noted. Files using `\date{\today}` have no fixed date in source — DOIs are listed where present in the `.tex`.
- This index was generated from titles + abstracts/intros of the `.tex` sources. Regenerate by re-reading abstracts if papers are added.
