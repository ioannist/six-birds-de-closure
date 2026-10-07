# Dark Energy as Closure Price? — A Six Birds formal theorem, empirical boundary, and magnitude no-go

> **⚠ RELANDED (2026-06-11) — supersedes the reopen framing.** The new corpus (`../six-birds-sm-qm-gr`) supplies the structure this bank said was
> missing: Λ's value is now a **computed F50 bounded-moduli verdict** (no in-layer value-law; the in-layer content is an admissibility *window*),
> the 10¹²⁰ mismatch is **typed by the fork theorem** as a cross-layer route-mismatch, and RT-as-shadow-price (externally settled) realizes the
> Claim-S payoff structure (the dual's identity/form, never its value). The program pivots from value-hunt to **demarcation + window + audits**.
> See `results/DE_DEMARCATION_RELANDING_2026-06-11.md`.

> **⚠ CATEGORY-MISTAKE CORRECTION (2026-06-03) — READ FIRST.** The §5 "magnitude no-go" and the §6 reopen framing below are **PROOF/REDUCTION-frame**
> results and are **NOT load-bearing** as a verdict on whether Six Birds can produce the dark-energy magnitude. They prove only that the constant is not
> *reducible by proof* — which is the **definition** of an emergent quantity, true of the proton mass too, and says nothing specific about dark energy.
> The dark-energy constant, if emergent, is **run-only** (build a faithful primitive cosmological-closure substrate, RUN it PICA-style, MEASURE the
> price, VALIDATE out-of-sample — as lattice QCD gets the proton mass). The correctly-posed build-and-run question was **never probed**. The empirical
> boundary result (§2) and Claim S (§3, the *form/existence*) STAND; the magnitude-derivation conclusions (§5/§6, Routes A–E + LT3) do not. Full
> correction: `results/MAGNITUDE_IS_EMERGENT_NOT_PROVABLE_2026-06-03.md`.

**Status: BANKED RESULT (derivation leg), 2026-06-02.** Outcome **C/B**. Cleared by the external reviewer
(`plan/EXTERNAL_RULING_DERIVATION_AVENUE_CD_2026-06-02.md`) as a coherent, falsifiable, honestly-bounded endpoint. This document consolidates the
durable results and the explicit conditions that would reopen the derivation route.

---

## 0. One-paragraph conclusion

Six Birds yields **(i)** a precise empirical boundary result on the dark-energy charts; **(ii)** a structural closure-price formalism — a paper-level
Claim S theorem under explicit KKT/strict-sensitivity hypotheses, whose **finite structural witnesses and the Schur pairing are Lean-checked** (not
the full general convex-duality theorem); and **(iii)** a literature-grounded demonstration that the closure price does **not** derive the observed
dark-energy *magnitude* — screened across **two bridge routes** (stress-energy/backreaction, blocked by no-go/magnitude walls; observational/light-cone
fitting, robust mean effects `~10⁻⁵–10⁻³`, not `O(0.1)`) **and the two O(1)-by-structure amplification engines** a catalog-wide sweep of the
Foundations-IV laws could surface (the *topological/quantized* reading of the F4 obstruction, and the *criticality/singular-limit* reading) — all four
fail under the no-`Ω_Λ`-normalizer rule. This does **not** refute Six Birds as a structural theory; it banks the dark-energy *derivation* claim at
outcome **C/B** until a fixed, no-amplifier physics bridge is supplied.

---

## 1. Motivation and no-overread

Dark energy is read through several charts — `Λ` / `w₀wₐ` geometry, the `H₀` / expansion-history Hubble route, the growth/`S₈` staging chart, and the
light-cone *fitting* of a smooth FLRW model to a lumpy universe. The program's discipline (F11 / no-overread) is that **none of these charts alone
decides ontology**: a coherent residual in one chart is a chart fact, not a proof of a new substance. The Six Birds hypothesis was that a single
underlying object — a *closure price*, the dual certificate of forcing a smooth FLRW completion against a Local–Global (F4) obstruction — could
appear as `Λ`/`w(z)` in geometry, as staging/heterogeneity dependence in growth, and as a bridge obstruction in the Hubble chart. This document reports
how far that hypothesis survives rigorous, non-circular testing.

## 2. Empirical boundary result

(Full: `results/E5SP/EMPIRICAL_BOUNDARY_RESULT.md`.) The detection leg tested weak lensing (KiDS/HSC), CMB lensing, and full-shape clustering for a
growth shadow-price / obstruction signal `π`, with a row-count-null normalizer and a mandatory anti-vacuity injection (a gate that cannot fire is a
bug, not a null). The honest boundary:

- **Geometry residual** is coherent but does **not** replace `w₀wₐ`.
- **Hubble-route carrier** is underpowered/degenerate on current public data (compressed-likelihood + dynesty established the cost floor and the
  w0wa banana; not a decisive carrier).
- **Growth shadow-price detection is not executable on current public data**: slack (`H≤0.05`) and strong-binding (`H≥0.3`) live in **different probe
  types** (the support-failure theorem), so no single probe with common covariance spans both within one carrier family.
- **Carrier-identifiability (E5-CI)** showed the HSC strong-regime `π` is **omitted nonlinearity / systematics**, not a closure price: the signal
  present under a linear carrier (`π` 8–16) vanishes under a nonlinear carrier (`π=0`), with anti-vacuity firing in both — so the residual was just
  un-modeled nonlinearity.
- **Density-split feasibility (Avenue B)** is the one within-family slack→strong-binding span that passed its precondition (peak-background-split
  proxy: deep void `H≈0.008` → wall `H≈0.32`), but per §5 it is now a **systematics/audit** target, not a magnitude detection.

These enter the result as **carrier audits + a future-falsification requirement**, not as failed searches.

## 3. Claim S — the structural closure-price theorem

(Full: `math/DERIVATION_LT1_2026-06-02.md`; Lean: `lean/SbtCosmo/Derivation/ClosurePrice.lean`.)

**Statement (paper-level).** Under convexity, optimizer existence, a constraint qualification (Slater), an **active** adequacy budget, and a
differentiable, **strictly budget-sensitive** value function `V(Ω)`, there exists a nonzero structural dual certificate `λ = −V'(Ω) > 0` that prices
the Schur adequacy residual: the completion's Lagrangian carries the term `λ · tr(W · Ξ_C)`, where `Ξ_C` is the validated Schur-complement adequacy
residual (`Ξ_C ≻ 0` iff the smooth completion fails to reconcile the local block).

**The minimal-hypothesis discipline.** "Active constraint ⇒ nonzero multiplier" is **false** and is explicitly rejected via the counterexample
`min x² s.t. x ≤ 0` at `x=0` (active, Slater holds, yet `λ=0`). **Strict budget sensitivity** is the minimal extra hypothesis that forces `λ>0`. A
Loewner/matrix version is stated.

**What the theorem does NOT claim.** No Friedmann source, no pressure, no equation of state, no distance map, no `ρ_crit` scale, **no magnitude**.
Claim S is kept strictly separate from Claim P (§4).

**Lean status (precise — no overclaim).** `ClosurePrice.lean` mechanizes the **finite structural witnesses** and the **Schur pairing**, and nothing
more: (a) `active_not_implies_positive_multiplier` — the active-constraint-with-zero-multiplier KKT witness, with `active_zero_multiplier_counter
example_optimizer` making it a genuine optimizer; (b) `strict_sensitivity_positive_kkt` — the strict-sensitivity quadratic witness with `λ = 2(a−Ω) >
0`; (c) `schurEnergy = tr(W · Ξ_C)` built on the validated `Adequacy.Reconciliation` residual, and `closure_lagrangian_pairing` exposing the
`J + λ·(tr(W·Ξ_C) − Ω)` structural pairing definitionally. `lake build` passes (3140 jobs); no `sorry` / `admit` / `axiom` / `opaque`; trust base
within `{propext, Classical.choice, Quot.sound}`. **The general convex-duality/KKT theorem is paper-level under the stated hypotheses, NOT
mechanized.** The file's own header states it "mechanizes only the finite structural witnesses … proves no Friedmann-source, clock-bridge, or
dark-energy claim."

## 4. Claim P — the bridge obligation (not supplied)

(Full: `math/DERIVATION_LT1_2026-06-02.md` §Claim P; `math/DERIVATION_LT2_2026-06-02.md`.) Claim P is the physics bridge
`B : λ / Ξ_C → T_eff_ab` (effective stress-energy / observable) with five conditions: covariant; averaged-Friedmann-consistent;
Bianchi/conservation-consistent; predicts `Ω_eff`/`w(z)`/onset; **no `Ω_Λ` normalization**. **Schur/KKT does not supply B** — it has no tensor
indices, no pressure, no continuity equation, no energy scale. **Claim S cannot imply Claim P.** LT2 further tested the obvious clock/F4 bridge and
**refuted** it: SBT supplies no fixed F4/F18 rule selecting `γ(t)`, `f_v(t)`, `D_L(z)`, or the magnitude (all 5 candidate gates fail). The only `O(1)`
clock route reduces to timescape-class physics + SBT audits — i.e. imported physics, not a closure derivation.

## 5. Magnitude assessment — the gate fails on both routes

The make-or-break question is whether the closure price reaches `Ω_eff = O(0.1–1)` **without** tuning to `Ω_Λ` and **without** merely relabeling
timescape. Two routes were dissected on their own terms (the non-circularity discipline: do **not** inherit the old `Q_D`/timescape verdicts).

**Route A — stress-energy / backreaction.** (`math/DERIVATION_AVENUE_D_2026-06-02.md`.) Green–Wald / Ishibashi–Wald: small-scale inhomogeneity in the
weak-limit framework contributes a **traceless, WEC** effective `t_ab` — it **cannot mimic `Λ`**. Perturbative/kinematical backreaction `|Q_D|/H₀² ≲
10⁻⁵`. Buchert's scope critique is legitimate but supplies no `O(1)` magnitude. **Blocked.** A global-F4 obstruction is a valid *scope* objection but,
absent a dimensioned obstruction functional `O_F4` mapping to curvature/lapse/distance, opens no magnitude. Non-perturbative claims need a specific
non-weak-limit construction not supplied.

**Route C — observational / light-cone fitting.** (`math/DERIVATION_AVENUE_C_2026-06-02.md`.) This is the one **principled applicability evasion** D
found: a fitting/inference residual is *not* an effective stress-energy tensor, so the Green–Wald `t_ab` no-go does not bound it. Tested on its own
literature, with numbers:
- GMNV / Ben-Dayan luminosity-redshift backreaction: mean light-cone effect `O(10⁻³)` at `z~1` (`k_UV=1 Mpc⁻¹`); parameter determinability `10⁻³–
  10⁻⁵`; the `~10%` figure is irreducible **scatter/variance**, not a mean DE residual.
- Fleury–Clarkson–Maartens source-averaged Hubble-diagram bias: `<10⁻³` over `0.05<z<10`; parameter biases at most percent-level (`wₐ`), sub-percent
  otherwise.
- Swiss-cheese (Flanagan et al.): 35 Mpc voids at `z_s=1` → `0.003 mag` mean shift, `0.027 mag` scatter.
- **`δ_LC` does not factor through `Ξ_C`** non-tautologically: same Schur/F4 residual ⇒ same `δ_LC` is false unless `Ξ_C` is expanded to carry the
  full beam/metric/source-selection data, at which point the factorization is vacuous (an audit of the missing observable family, not a magnitude
  derivation).
- **Verdict: mean bias `~10⁻³`, not `O(0.1)`.** The only routes to `O(0.1)` import non-closure physics: large clock/lapse/void-volume (timescape-
  class, non-SBT-selected), giant/special void LTB reconstruction (model fitting, observationally constrained), or unresolved ultra-narrow-beam
  matter-discreteness (sign not fixed by closure). **None is a closure derivation.**

**Route D — the O(1)-by-structure amplification engines (catalog-wide sweep).** Routes A and C compute *perturbative* prices. A separate question is
whether some Foundations-IV law supplies a *structural* reason the effect is O(1) rather than a small perturbation (the "higher organizing layer / new
force" intuition). A screen of all ~50 catalog laws found that the bulk are bookkeeping/consistency conditions with no scale-setting content, and that
the genuine O(1)-by-structure mechanisms reduce to **two engines**, both of which were then probed and **fail** under the no-normalizer rule:
- **Topological / quantized reading of F4** (`math/DERIVATION_TOPOLOGICAL_F4_2026-06-02.md`). Hope: the gluing obstruction's natural invariant is an
  integer (Čech `Ȟ¹` / `πₙ` / anomaly / Noether charge), hence O(1) by quantization, not a perturbative residue. **NO:** the cosmological fit data are
  smooth, real-valued (fine/soft sheaves) — F4 here is an **analytic** obstruction (a Schur residual), not a topological one, so there is no integer to
  quantize; and even granting one, F4 fixes no energy scale (`M_Pl⁴` over by `10¹²⁰`, `M_Pl²H₀²` is a normalizer), and the 4-form precedent
  (Hawking / Brown–Teitelboim / Bousso–Polchinski) only inherits the discretuum/anthropic wall.
- **Criticality / singular-limit reading of F4** (`math/DERIVATION_CRITICALITY_F4_2026-06-02.md`). Hope: near a critical point divergent susceptibility
  turns the `~10⁻⁵` bare price into O(1), with the `z~0.7` onset as a bonus prediction. **NO:** the late-time structure/void transition is a finite
  **crossover**, not a demonstrated critical point (no divergent `χ_F4`); reaching O(1) needs the system tuned onto the critical surface, and no
  self-organized-criticality attractor or F4-fixed critical coupling exists (tuning = the CC problem relocated = R14); `z~0.7` is not predicted (F4
  selects no marker among many); and criticality fixes at most scaling *shape*, never the absolute `ρ_Λ` normalization. Existing critical-DE models
  (CEDE) are phenomenological — the order parameter/transition/normalization are *put in by hand*, i.e. exactly the Claim-P bridge, not evidence F4
  supplies it. Delivers none of {magnitude, onset, `w(z)`}.

**The remaining flagged engines fold into these two** (reviewer-confirmed, `plan/EXTERNAL_RULING_MAGNITUDE_ENGINES_2026-06-02.md`) — none is a
separate live engine, each failing by missing-scale or added-physics, not by being literally identical to topology/criticality:

| candidate | why it is not a separate live engine |
|---|---|
| **F35 RG-running** | needs the running scale + anomalous coefficient (`δρ_vac ~ ν_eff·M_Pl²·H²`); `ν_eff` is a fitted knob, an `H₀`-scale is a late-time normalizer |
| **F15b SSB / branch-selection** | needs a potential / order-parameter space + a vacuum-energy scale (a physics input) — criticality + a free potential |
| **F33 holography** | `ρ_DE = 3c²·M_Pl²·L⁻²` has the right dimensional form *only* by choosing an IR cutoff `L` (Hubble/event-horizon) + coefficient `c`; the horizon choice is a normalizer unless F4 derives `L` and `c` |
| **F40 anomaly** | needs QFT content, symmetry, gauge group, regulator/measure, anomaly polynomial + a scale |
| **F27 conserved charge** | needs action/symmetry/orbit; conservation does not create an energy scale |
| **F18 lawhood descent** | can validate a layer; cannot by itself amplify magnitude |
| **F51 unification** | can organize charts; does not set the scale |

So the magnitude is screened **NO across four independent routes** — two perturbative bridges (A, C) and two O(1) amplification engines (topological,
criticality), with RG/SSB/holography/anomaly/conservation/lawhood/unification folding into their missing-scale or added-physics failures. This is
**exhaustive over the current Six Birds catalog's O(1)-by-structure mechanisms under the no-`Ω_Λ`-normalizer rule** — *not* logically exhaustive over
all possible future physics.

**Route E — native dimensional transmutation (PARTIAL; the strongest internal reopen direction).**
(`math/DERIVATION_TRANSMUTATION_F4_2026-06-02.md`; external-reviewer-endorsed, `plan/EXTERNAL_RULING_TRANSMUTATION_2026-06-03.md`.) Since pure SBT
structure is dimensionless, the magnitude is re-posed as a **pure number** `r = ρ_Λ/ρ_Planck ≈ 10⁻¹²³` anchored to a single substrate unit (legitimate,
QCD-like). The native mechanism: the F4/Schur closure defect **runs** across the P4 staging ladder (a per-stage log change; the Cantor Fekete pressure
is such an object) until a defect-triggered layer-birth (To Notch enablement) at a terminal rung `j*`. Result: **the corpus fixes the running FORM**
(Schur residual currency, quotient/scale descent, the finite-forcing exponential `2^{-(N-K)}`, log-growth pressure, budget→price duality) **but NOT the
running COEFFICIENT or the endpoint** — `C_0`, `N-K`, `α_j`, `θ`, `j*` are all free (BirdInt blocks a universal β; Foundations II nonclaims block
exact-six⇒rate-fixed). The defect genuinely runs (non-vacuous), and anti-tautology holds (matching `10⁻¹²³` would require setting `N-K ≈ 399`, *a fit not
a theorem*). So it is **distinct in form** from topology (no integer needed) and criticality (no tuning needed) but **folds into the RG/scale-descent
boundary at the coefficient level**. The most-attackable knob is the endpoint `j*` (it is the holographic IR-cutoff / cosmic-coincidence problem in
disguise: `ρ_Λ ≈ M_Pl²H₀² ⇒ r ≈ (L_Pl/R_Hubble)²`). **Status: PARTIAL — reopen-condition 3 unmet; bank stands.** Named closing target = the *Structural
Transmutation Theorem* (derive `{β_j, j*}` from P1–P6 + one substrate unit, no `Ω_Λ`/`H_0`/fitted-threshold), currently blocked by explicit corpus
nonclaims.

**LT3 — the endpoint `j*` is PROVABLY not fixable from P1–P6** (`math/DERIVATION_LT3_ENDPOINT_2026-06-03.md`; reviewer-anticipated outcome). A clean
finite counterexample: two admissible presentations of the *same* system (`Z={0,1,2,3}`, `F=id`) with the *same* six-channel P1–P6 record but a
*different* threshold-free no-ladder terminal cap `j*_cap = |Def(f)| = 2^{|im(f)|}` (2 vs 4). So `j*` is **not record-invariant** — it lives in
lens/presentation/host data (the coarse-graining granularity `|im(f)|`) below the resolution of the six-channel record. **This converts the magnitude
bank from "reopen-condition unmet" to "the reopen requires NEW primitives/structure"** — a canonical granularity selector, a structural endpoint field
in the BirdInt record, or a lift-invariance theorem — *not* a theorem within the current six primitives. (And it explains *why* the cosmic coincidence
is structurally undetermined in current SBT: the IR-cutoff/horizon scale is a presentation choice, not a P1–P6 invariant.)

**Residual open thread (honest).** The ultra-narrow-beam / matter-discreteness problem (Clarkson–Ellis–Faltenbacher–Maartens–Umeh–Uzan) is genuinely
unsettled and can reach `~0.1 mag` in toy approximations — but sign and magnitude depend on beam/opacity/local-expansion physics **not supplied by
Schur/F4**. It is a future precision-cosmology/beam audit, not the next Six Birds magnitude route.

## 6. Banked outcome and reopen conditions

**Outcome C/B.** Claim S stands (structural); Claim P is not supplied; the magnitude is not closure-derived on either route. The bank is falsifiable,
not rhetorical: it reopens if **any** of the following is supplied as a fixed theorem + calculation (no post-hoc `Ω_Λ` normalizer, no amplifier):

1. **Fixed light-cone theorem.** A covariant fitting functional `F_LC` and a **non-tautological** map `Ξ_C ↦ δ_LC` (same `Ξ_C` ⇒ same `δ_LC`, without
   encoding the full beam/source outcome in `Ξ_C`) predicting mean `|δD|/D = O(0.1)`, stable sign across the SN redshift range, and ≥2 non-SN
   observables (e.g. BAO/SN distance-ratio split + CMB acoustic/lensing consistency).
2. **Fixed clock bridge.** An F4/F18 bridge producing `γ(t)`, `f_v(t)`, `H_dressed(t)`, `D_L(z)`, `Ω_eff`, and onset **without** tuning to `Ω_Λ` (LT2:
   no such SBT-only bridge is presently specified).
3. **Topological engine.** A declared cosmological bundle/defect/gauge structure with `Q_top ∈ ℤ`, a proof the actual F4 gluing has `Q_top ≠ 0`, and a
   non-circular scale `μ` with `ρ_top = Q_top·μ⁴` (or equivalent) giving `Ω_Λ = O(1)` + onset + `w(z)`.
4. **Criticality engine.** A declared closure control parameter `c`, order parameter `m`, and susceptibility `χ_F4` with a proven divergence / universal
   finite-size scaling, an SOC attractor or F4-fixed critical coupling, a non-circular scale, a predicted onset, and a non-SN check.
5. **Holographic / RG / SSB engine.** A theorem fixing the IR cutoff (holographic `L`) / running coefficient (`ν_eff`) / order-parameter potential (SSB)
   from F4/F18 **without fitting `Ω_Λ`**.
6. **New empirical carrier.** An LSST / Euclid / Roman / DESI-class single public carrier with common covariance, validated nonlinear modeling, and
   **both** slack and strong-binding shells in one family — the support the boundary result proved no current public probe supplies.

**What stands regardless.** The empirical boundary result (§2); the structural closure-price formalism (§3 — paper-level Claim S + Lean-checked
witnesses/pairing); and the magnitude no-go (§5) with these reopen conditions. Six Birds is not refuted as a structural theory; the dark-energy
*derivation* claim is banked at C/B.

**Final framing (external-reviewer-endorsed, `plan/EXTERNAL_RULING_MAGNITUDE_ENGINES_2026-06-02.md`).** *Six Birds has produced a structural
closure-price theorem and a disciplined audit of the dark-energy charts. But the observed dark-energy magnitude is not derived: perturbative
stress-energy/backreaction bridges are too small or constrained; observational/light-cone fitting mean effects are too small; topological/quantized F4
lacks both a natural integer invariant and a scale; criticality/F4 lacks a true critical point, an attractor, and a scale. RG, SSB, anomalies,
holography, and higher unification fold into these same missing-scale or added-physics failures. The derivation claim is banked at outcome C/B until a
fixed no-amplifier bridge is supplied — the honest boundary of the current dark-energy derivation claim, not a refutation of Six Birds as a structural
theory.*

**Refined framing including native transmutation (external-reviewer-endorsed, `plan/EXTERNAL_RULING_TRANSMUTATION_2026-06-03.md`).** *Six Birds provides
a lawful dimensional-transmutation FORM for closure defects, but the current corpus does not compute the pure number required for dark energy. The
Planck anchor is legitimate; the `10⁻¹²³`-scale ratio is not derived. Native transmutation is the strongest SBT-internal reopen direction; reopen-
condition 3 remains unmet; outcome C/B remains banked.* Full magnitude-route status:

| route | status |
|---|---|
| stress-energy / `Q_D` | too small / no-go |
| light-cone fitting | robust mean too small |
| topological / quantized F4 | no natural invariant + no scale |
| criticality / SOC | no demonstrated critical point / no scale |
| RG / scale descent | running form but free coefficient |
| **native transmutation** | **same: form fixed, coefficient + endpoint free (PARTIAL — strongest internal reopen direction)** |
| clock / timescape | O(1) only by importing physics |
| holography | correct dimensional form only by choosing IR cutoff + coefficient |

This is an exhaustive closure of the currently-specified magnitude engines, not a retreat. The single most-attackable remaining knob was the terminal
rung `j*` (the endpoint / cosmic-coincidence / holographic-IR-cutoff problem); **LT3 resolved it as outcome B** (`math/DERIVATION_LT3_ENDPOINT_2026-06-03.md`):
a finite counterexample (two admissible presentations, identical six-channel P1–P6 records, different threshold-free no-ladder cap `2^{|im(f)|}`) proves
the endpoint is **not record-invariant** — the current six primitives *cannot* fix `j*`. **Net: the dark-energy magnitude is not merely underived within
SBT; one of the two transmutation knobs (the endpoint) is now proven unfixable by the current primitives — so reopening the magnitude derivation requires
NEW structure (a canonical granularity selector / a structural endpoint field in the BirdInt record / a lift-invariance theorem), not a cleverer theorem
within the present corpus.** This is the cleanest possible internal closure of the magnitude program.

---

## Provenance / underlying artifacts
- Empirical: `results/E5SP/EMPIRICAL_BOUNDARY_RESULT.md`, `results/E5SP/e5ci_carrier_identifiability/`, `results/E5SP/avenueB_feasibility/`.
- Structural theorem: `math/DERIVATION_LT1_2026-06-02.md`; Lean `lean/SbtCosmo/Derivation/ClosurePrice.lean`.
- Bridge refutation: `math/DERIVATION_LT2_2026-06-02.md`.
- Magnitude gate: `math/DERIVATION_AVENUE_D_2026-06-02.md` (loophole analysis), `math/DERIVATION_AVENUE_C_2026-06-02.md` (magnitude gate).
- Plan + rulings: `plan/DERIVATION_DARK_ENERGY_AS_CLOSURE.md`, `plan/SIXBIRDS_DE_AVENUES_MAP_2026-06-02.md`,
  `plan/EXTERNAL_RULING_DERIVATION_LT1_2026-06-02.md`, `plan/EXTERNAL_RULING_DERIVATION_AVENUE_CD_2026-06-02.md`.
- Primary literature (checked against directly): Green–Wald (1011.4920, 1304.2318, 1407.8084); Ishibashi–Wald (gr-qc/0509108); GMNV (1104.1167) +
  Ben-Dayan (1202.1247, 1207.1286, 1302.0740); Räsänen (0812.2872, 0912.3370); Ellis–Stoeger + Kolb–Lamb (0911.3852); Swiss-cheese (Flanagan
  1109.1873, Brouzakis astro-ph/0703586); Bonvin/Fleury (1504.01676, 1503.07831, 1612.03726); Clarkson narrow-beam (1109.2484); Buchert
  (gr-qc/0612166, 1505.07800); Wiltshire/timescape (1102.2045).
