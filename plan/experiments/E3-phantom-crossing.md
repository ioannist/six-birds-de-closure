# E3 — Phantom Crossing With a Stable Effective Readout

> **One-line charter.** Construct a **positive, stable, audit-closed** rewrite operator `R[Ξ]` whose
> induced effective equation of state
> `w_eff(z) = −1 + ((1+z)/3) · d/dz ln ρ_eff(z)` **crosses the phantom divide `w = −1`** with **no
> growing mode** (a stable effective finite readout) — and exhibit a
> *finite witness* plus a *stable-readout certificate* (positivity + no growing mode) proving that
> crossing −1 is a property of the **effective readout**. The stronger
> "**no negative-kinetic (ghost) degree of freedom**" claim requires a Lagrangian/kinetic-metric
> framework this program does not build, so it is **`out_of_scope`** (REGISTRY §5). Then test, against
> the DESI-style `w(z)` reconstruction (arXiv:2503.14743), whether the data's preferred crossing is
> realized by such a positive/stable operator.

> **Read-order / consistency.** This file implements *one* experiment of the program defined in
> `plan/00-overview.md` (§3 shadow map row 5, §6 gates, §8 done) and `../GROUNDING_BRIEF.md`
> (datasets, stack, determinism, AOR vocabulary; §VI audit gate 5 = "phantom crossing with a stable
> effective readout"). Every formal object used here is *locked* in `plan/04-formal-foundations.md`:
> the rewrite `R[Δ]` and the low-rank ansatz (§3.1–3.2, eqs. 4–5), the metric `d` (§4.0, eq. 10), the
> residuals `δ_p`/`RM_p`/`PPD_{p→q}` (§4.1–4.4), **Proposition P4** (§6.4, eq. 19) and the
> **phantom stable-readout stability audit** (§7), and the AOR status catalogue (§8). The Lean target
> conventions are *locked* in `plan/05-lean-mechanization.md` (**TARGET T5**, module
> `SbtCosmo.PhantomStableReadout`, theorem `phantom_stable_readout_witness`). The synthetic predecessor witness is *locked* in
> `plan/experiments/E0-synthetic-demos.md` (**Toy 3**), which E3 consumes and lifts. Data products and
> access are locked in `plan/03-data-acquisition.md`. **Science source of truth:** `idea.md` §4
> ("Proposition 4: effective phantom crossing need not imply ghosts"), §6 **Experiment 3** (the
> `w_eff(z)` formula, the pass criterion), §7 ("Phantom crossing" — "a ghost appears only if one
> over-reads `w_eff` as a fundamental scalar-field equation of state"), and §10 (five hard standards).
> This file does **not** re-derive those objects; it specifies the *pipeline, the operator
> construction, the stable-readout certificate, the data fit, controls, outputs, and pre-registered
> pass/fail gates*.
>
> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean/finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a gate
> in §9 below).

---

## 1. Scientific framing and grounding

### 1.1 What this experiment is about

`idea.md` §3 (shadow map, **row 5**) and §6 **Experiment 3** state the thesis precisely:

> *"`w_eff(z)` crosses `−1` because it is a readout of a closure rewrite, not a fundamental scalar with
> negative kinetic energy."* — `idea.md` §3 row 5 (the **derivative chart** of `Ξ_cosmo`);
> `plan/00-overview` §3 row 5.

> *"Construct a positive, stable, audit-closed rewrite operator whose induced `w_eff` crosses `−1`.
> That directly resolves the ghost-instability objection."* — `idea.md` §6 Experiment 3 (verbatim
> pass criterion).

E3 is the experiment that turns **Proposition P4** (`plan/04` §6.4) into a demonstrated artifact. The
observational problem (`idea.md` §4): DESI's extended dark-energy analysis (arXiv:2503.14743) reports
that the data **prefer a `w(z)` history crossing `w = −1`**, especially at low redshift, while
non-crossing alternatives are "disfavored but not ruled out." The theory problem: a fundamental single
scalar field with `w < −1` usually requires a **wrong-sign kinetic term — a ghost** — with vacuum
instability. The Six Birds move (`idea.md` §7) is to prove:

> *Phantom crossing is a property of the effective readout, not of a fundamental Lagrangian degree of
> freedom. A ghost appears only if one over-reads `w_eff(z)` as a fundamental scalar-field equation of
> state.*

E3 must therefore deliver **two coupled results**:
- **(A) the existence/construction result `[T]`** — a *concrete*, positive, stable, audit-closed
  rewrite operator that induces `w_eff < −1` over an interval, with a kernel-checkable
  stable-readout certificate (positivity + **no growing mode**); this is the centerpiece and the pass
  gate of `idea.md` §6 Exp3. The grade-`[T]` deliverable is the **stable finite effective readout / no
  growing mode** statement; the stronger no-negative-kinetic-DOF (ghost) claim is `out_of_scope`
  absent a Lagrangian/kinetic-metric framework (REGISTRY §5).
- **(B) the empirical/data result `[E]`** — the DESI-style `w(z)` reconstruction (2503.14743) is fit
  by the *same* low-rank `Ξ_cosmo` rewrite (coherent with E0/E1/E2/E4/E5), and where the data prefer a
  crossing, that crossing is realized by a positive/stable operator (no growing mode forced).

### 1.2 The effective equation of state (LOCKED, `idea.md` §6 E3 / `plan/04` eq. 19)

The single load-bearing formula. With `ρ_eff(z) = ρ_FLRW(z;θ) + R[Ξ_cosmo](z)` (`plan/04` eq. 5):

```
w_eff(z) = −1 + ( (1+z)/3 ) · d/dz [ ln ρ_eff(z) ]                                               (E3.1)
```

Equivalently, in the conservation-equation form used by DESI reconstructions,
`w_eff(a) = −1 − (1/3) d ln ρ_eff / d ln a`, with `a = 1/(1+z)`. The two key facts (both used below):

- **Crossing condition.** `w_eff(z)` crosses `−1` **exactly where `d/dz ln ρ_eff(z)` changes sign**,
  i.e. where the effective energy density has a stationary point in `z`. `w_eff < −1 ⇔
  d ln ρ_eff/dz < 0` (`ρ_eff` decreasing toward higher `z`, i.e. *growing toward the future*).
- **Ontology separation.** `w_eff` is a **derivative readout** of `ρ_eff`; nothing in (E3.1) requires
  `ρ_eff` to come from a kinetic Lagrangian. A standard single-field reading would *infer* a kinetic
  sign from `w_eff`; E3 shows that inference is the over-read (P2/F11 in spirit — `plan/04` §6.2), not
  a fact about the operator.

### 1.3 The live controversy this experiment must engage (mandatory)

`idea.md` §4 frames four published positions E3 must engage **explicitly and adversarially**. The
experiment is designed to **decide which holds for the DESI signal**, not to pre-assume the crossing
is real:

| Source | arXiv | Claim | What it implies for E3 |
|---|---|---|---|
| **DESI DR2 extended DE** | **2503.14743** | data **prefer** a `w(z)` crossing `−1` (esp. low-z); non-crossing "disfavored but not ruled out". | the **primary target**: reconstruct `w(z)`, locate the crossing redshift `z_c`, test whether SBT's positive/stable `R[Ξ]` reproduces it. |
| **Keeley, Shafieloo & Matthewson** | **2506.15091** | even non-phantom fiducial models produce apparent CPL phantom-crossing fits in **≈3.2%** of mocks. | the **false-positive control**: E3 must run a mock campaign and report the apparent-crossing rate of a *non-crossing* null, comparing to the data significance. |
| **Dinda, Maartens & Saito** | **2605.13546** | local goodness-of-fit improvements do **not** persist under global Bayesian model comparison; no statistically consistent evidence for phantom crossing. | the **Bayesian-discipline control**: the crossing claim must be scored by global model comparison (BIC/evidence + OOS), not in-sample `Δχ²` alone. |
| **Antusch, King & Wang** | **2604.08449** | coupled DE+DM can produce an **apparent** phantom crossing **without** a phantom scalar (frozen early, evolves late). | corroborating direction: an explicit *physical* example that the crossing can be effective — SBT's `R[Ξ]` is the **model-agnostic** version of the same statement (the IDE `Q` is one chart of `Ξ`, E6). |

> **`idea.md` §6 Exp3 pass criterion (verbatim intent):** *"construct a positive, stable, audit-closed
> rewrite operator whose induced `w_eff` crosses `−1`."* This is operationalized in §9.3 as the
> **`G-E3-CONSTRUCT` gate** (existence, `[T]`) and in §9.4 as the **`G-E3-DATA` gate** (the data
> crossing is realized by such an operator, `[E]`). Both the existence gate and the false-positive /
> Bayesian-discipline controls are pre-registered.

### 1.4 Foundations grounding (P4)

P4 has **no single named Foundations-IV law** (`plan/04` §6.4, proposition table). It is built from
two corpus ingredients:

- **Operator-rewrite repair (P1's cosmology extension of F2 — NOT a third F2 repair).** The crossing is
  induced by the **operator-rewrite chart**, the P1/cosmology *extension* of the Descent–Repair Normal Form
  (`Foundations_IV` `thm:F2` itself names only source refinement + minimal target coarsening; `plan/04`
  §6.1): `R[Δ_SBT]` is an *admissible* macro-operator correction (`plan/04` eq. 5), not a new fundamental field. (The DESI `w₀wₐ`, IDE `Q`,
  and `(μ,Σ)` are alternative *charts* of the same repair — shadow rows 3, 8, 9.)
- **Spectral/positivity (membrane) discipline of `Emergence IS the Needle Killer`.** The
  stable-readout criterion is operationalized as **spectral positivity / stability**, *not* a
  Lagrangian kinetic sign: a positive native currency (`ρ_eff > 0`) on a stable (**no growing mode**)
  operator (`Adequacy_Residuals` positivity; the layer-dissolving-endpoint membrane positivity of
  `Emergence_IS_the_Needle_Killer`). This certifies a **stable effective finite readout / no growing
  mode**; it does **not** certify the absence of a negative-kinetic (ghost) degree of freedom, which
  is `out_of_scope` here (no Lagrangian/kinetic-metric framework is built — REGISTRY §5). See §4 for
  the exact certificate.

The meta-obligation **F9 No Unstatused Residual** (`Foundations_IV` `thm:F9`; `plan/04` §6.4) applies:
whatever the data verdict, the leftover (e.g. "the real dark sector is/ isn't this operator") must
carry exactly one AOR status (§8). The "Λ not ruled out" / "no microphysical alternative claimed"
disclaimers are registered as `nonclaim` (`plan/04` §8.3; `Dark Energy` precursor non-claims register).

### 1.5 The crucial ontological distinction (LOCKED — this is the crux)

The whole experiment rests on separating two things that single-field cosmology conflates:

| Object | What it is | What it does NOT entail |
|---|---|---|
| `w_eff(z)` (the **readout**, E3.1) | a derivative chart of the macro `ρ_eff(z)` | does **not** entail a fundamental scalar's `ẇφ²/2` sign |
| `R[Ξ]` (the **operator**) | the additive macro-rewrite (`plan/04` eq. 5) | does **not** add a growing mode in the audited norm (we *prove* this — §4); the kinetic-metric/ghost question is `out_of_scope` (no Lagrangian) |

> The "phantom ⇒ ghost" objection arises **only** if one identifies `w_eff(z) < −1` with a
> fundamental scalar-field equation of state `w = (½φ̇² − V)/(½φ̇² + V)` and infers `φ̇² < 0`. E3's
> certificate shows the *macro readout* crosses `−1` while the *operator* is positive and stable
> (**no growing mode**). This is precisely the over-read P2/F11 forbids (`plan/04` §6.2): an inference
> (`w_eff < −1 ⇒ ghost`) that does not descend through the cosmological access quotient. E3 does
> **not** affirmatively certify the absence of a negative-kinetic DOF — that is `out_of_scope` absent
> a Lagrangian/kinetic-metric framework (REGISTRY §5); it certifies a stable effective finite readout.

---

## 2. The construction: a positive, stable, audit-closed rewrite operator (LOCKED)

E3 builds the operator from the **same low-rank `Ξ_cosmo` ansatz** as the rest of the program (no
bespoke phantom machinery — that would be a fudge). From `plan/04` §3.1 eqs. 4–5:

```
Ξ_cosmo(z, ℓ, p) = a₀·φ₀(z)  +  a₁·φ₁(z)·ψ₁(ℓ)·s_p  +  a₂·φ₂(z)·c_p            (plan/04 eq. 4)
ρ_eff(z)         = ρ_FLRW(z; θ)  +  R[Ξ_cosmo](z)                              (plan/04 eq. 5)
```

with the **fixed, probe-shared** shapes `φ₀ ≡ 1`, `φ₁(z)=z/(1+z)`, `φ₂(z)=ln(1+z)` and amplitudes
`(a₀, a₁, a₂[, β])` the only free parameters (`plan/04` §3.1 hard rule; ≤ 3 beyond ΛCDM in the minimal
run). The phantom crossing is induced by the **constant + late-activating staging combination** whose
net `d ln ρ_eff/dz` changes sign once in the DESI window.

### 2.1 Why this ansatz can cross −1 with a *positive* operator (LOCKED)

The matter background `ρ_FLRW ∝ (1+z)³` is monotone increasing in `z`. A positive constant chart `a₀`
alone gives `ρ_eff` with `d ln ρ_eff/dz > 0` everywhere ⇒ `w_eff > −1` (quintessence-like, no
crossing). A crossing requires `d ln ρ_eff/dz` to **pass through zero**, i.e. the *effective DE
component* `ρ_DE,eff(z) ≡ ρ_eff − ρ_m` must have a stationary point. The late-activating staging term
`a₁·φ₁(z) = a₁·z/(1+z)` (which *rises* toward higher `z`) combined with the constant `a₀` produces an
effective DE density that **decreases then increases** (or vice-versa) across `[0, ~1]`, so its log
slope changes sign once — exactly the DESI low-z crossing. Crucially:

- **Positivity is preserved:** `ρ_eff(z) > 0` everywhere (the operator adds a positive native currency;
  no point where the effective density goes negative — the positive-effective-density condition,
  paired with the no-growing-mode condition below). This is *not* automatic for an arbitrary `w(z)`
  parameterization; it is enforced as a constraint on `(a₀, a₁)` (§4.1).
- **The crossing is in the *derivative*, not the *sign*:** `w_eff < −1` happens while `ρ_eff > 0`,
  because `w_eff` reads the *slope* of `ln ρ_eff`, and a positive density can have a region of negative
  log-slope.

> **The operator is the same object everywhere (anti-fudge, `plan/04` §3.1 / §9.2 rank ceiling).** E3
> does **not** introduce a free `w(z)`. It introduces **no new parameters** beyond `(a₀, a₁, a₂[, β])`
> already fitted in E1. The phantom crossing is a *consequence* of the fitted `Ξ`, read through (E3.1).
> If E3 needed a phantom-specific extra parameter, it would fail `G-E3-RANK` (§9.5).

### 2.2 The deterministic finite-witness operator (the existence object, LOCKED)

For the **existence/construction result (A)** the operator is pinned to a deterministic, rational,
finite instance (so it is theorem-grade and Lean-checkable — §7). This is the **lift of E0 Toy 3**
(`plan/experiments/E0-synthetic-demos.md` §4), reused here verbatim and extended to the DESI-preferred
`z_c`:

| Symbol | Meaning | Default (pinned in config) |
|---|---|---|
| `z`-grid | redshift grid (must bracket the crossing) | `n_z = 400`, linear on `[0, 1.5]` (Python) / a coarse rational grid `n ≥ 3` for Lean (T5) |
| `Ω_m` | matter fraction | `0.30` |
| `H₀` | normalization (cancels in `w_eff`) | `70.0` km/s/Mpc |
| `ρ_eff(z)` | effective density from `R[Ξ]` | `ρ_eff(z) = ρ_m(z) + ρ_DE,eff(z)`, `ρ_DE,eff(z) = a₀ + a₁·g(z)` with `g(z)=z/(1+z)` and `(a₀, a₁)` pinned so `d ln ρ_eff/dz` changes sign once in `[0,1.5]` and `ρ_eff > 0` everywhere |

The exact closed form is fixed in `sbt_cosmo/xi/rewrite.py` (shared with E0 Toy 3 and E1); E3 sets
`(a₀, a₁)` for the construction leg to a deterministic value that places `z_c` near the DESI-preferred
crossing (≈ 0.3–0.5; `z_c` is *reported*, not fitted, in leg A). The requirement (not the exact bump
shape) is: **`ρ_eff > 0` everywhere and `d ln ρ_eff/dz` changes sign once.**

---

## 3. Inputs

### 3.1 Datasets (versions and access — from `../GROUNDING_BRIEF.md` §I and `plan/03`)

| Probe | Dataset | Release | Vector | Covariance | Loader (`plan/03`) | Role |
|---|---|---|---|---|---|---|
| **`w(z)` recon (primary)** | **DESI DR2 extended DE** | **arXiv:2503.14743** | `w₀wₐ` posterior + non-parametric `w(z)`/`ρ_DE(z)` reconstruction nodes | published posterior chains / contour | `load_desi_dr2_extended()` | the DESI phantom-crossing signal to reconstruct and reproduce |
| **BAO (geometry leg)** | **DESI DR2 BAO** | arXiv:2503.14738 | `D_M(z)/r_d`, `D_H(z)/r_d` per tracer bin | full analytic+mock | `load_desi_dr2_bao()` | constrains `ρ_eff(z)` via geometry (the `K_M` kernel) |
| **SN (geometry leg)** | **Pantheon+** (primary), **Union3** / **DES-SN5YR** (cross-check) | 2202.04077 / 2401.06956 / Zenodo:13827844 | `μ(z)`, full cov | full stat+sys | `load_pantheon_plus()` etc. | constrains `ρ_eff(z)` via `K_L`; SN-compilation spread is a staging signal |
| **CMB anchor (prior leg)** | Planck 2018 | 1807.06209 | TT/TE/EE compressed (`Ω_m`, `θ*`, `r_d`) | published | `load_planck2018(compressed=True)` | high-z anchor that pins `ρ_eff` at early times (the crossing is a *low-z* effect; the anchor freezes the rewrite early — cf. Antusch et al. 2604.08449 "frozen early") |

> **Why DESI 2503.14743 specifically.** This is the *extended* DESI DR2 analysis whose headline is the
> phantom-crossing preference (`idea.md` §4 ref [13], §6 E3). E3 must reconstruct **its** preferred
> `w(z)`/`ρ_DE(z)` (parametric `w₀wₐ` and, where available, the non-parametric node reconstruction),
> locate the crossing `z_c`, and quantify its significance — *before* asking whether SBT's positive
> operator reproduces it (`idea.md` §10 standard 1, reproduce-first).

> **SN-compilation dependence is a signal, not noise (`idea.md` §6 Exp1; `plan/03`).** Run the data leg
> with Pantheon+, Union3, DES-SN5YR against the same DESI BAO. Any spread in the recovered `z_c` /
> crossing significance across SN compilations is a **packaging (P4 staging) fingerprint** and must be
> recorded, not averaged away.

### 3.2 Parameters and priors

| Parameter | Leg | Prior / value | Notes |
|---|---|---|---|
| `Ω_m` | both | `U(0.1, 0.6)` (data) / `0.30` (construction) | background |
| `H₀ r_d` | data | `U` broad | BAO combination |
| `a₀` (Λ-chart) | both | `U`, `complexity`-penalized; pinned in leg A | constant repair |
| `a₁` (staging chart) | both | `U`, `complexity`-penalized; pinned in leg A | **the crossing-inducing amplitude** |
| `a₂` (gluing chart) | data | `U`, `complexity`-penalized | carried for coherence with E1/E2; usually small in pure geometry |
| `β` (ℓ-response) | optional | `U(0,2)` | fixed unless logged |
| `M_B`, `r_d` | data, with SN/BAO | nuisances (marginalized) | calibration (cf. E2 §3.4) |

> **Ansatz rank ceiling (anti-fudge, `plan/04` §3.1 / §9.2).** The data leg adds **≤ 3** params beyond
> ΛCDM (`a₀, a₁, a₂`); shapes are fixed and probe-shared. **No phantom-specific free parameter.** Any
> extension is a logged statused deviation (`budgeted`).

---

## 4. The stable-readout stability audit (the decision spine, LOCKED — `plan/04` §7)

Following `plan/04` §7 verbatim, the rewrite `R[Ξ]` passes the **stable-readout certificate** (a
stable effective finite readout with **no growing mode**) **iff BOTH** of §4.1–§4.2 hold. The
certificate establishes positivity + no growing mode; it does **not** establish the absence of a
negative-kinetic (ghost) degree of freedom, which is `out_of_scope` absent a Lagrangian/kinetic-metric
framework (REGISTRY §5).

### 4.1 (i) Energy positivity (positive native currency)

> `R[Ξ]` is a **positive operator** on the audit-energy inner product `⟨·, C·⟩` with `C = Σ^{-1}`
> (`plan/04` §4.0, §7): it adds **no negative-norm direction**. Two concrete, reported checks:
> - **Density positivity:** `ρ_eff(z) > 0` for all grid `z` (report `min_z ρ_eff(z)`; require `> 0`).
> - **Operator/adequacy positivity (P-adeq — a *positivity*, NOT a stability, certificate; ADDENDUM §4):**
>   the symmetrized rewrite `sym_C(R[Ξ]) = ½(R + R^†)` in `C`-coordinates is PSD (↔ Schur `Ξ_C ⪰ 0`,
>   `plan/04` §9.1 `G-FORMAL-1`) — report its **minimum eigenvalue** `λ_min^{sym}`; require `≥ 0`
>   (tolerance `≥ −10⁻⁸`). This says the rewrite adds no negative audit-energy direction; it does **not**
>   by itself imply dynamical stability (that is §4.2).

### 4.2 (ii) Spectral stability (no growing mode)

> Linearize the **continuous macro-evolution generator** `J(z) = ∂f/∂(state)` of `dstate/d(ln a)=f(a,ρ_eff)`
> about the trajectory; compute its eigenvalue spectrum `{λ_j(z)}`. **No-growing-mode witness (S-stab):**
> require `Re(λ_j) ≤ 0` for all `j`, all `z` (no exponentially growing mode); equivalently, for the
> discretized one-step integrator, spectral radius `≤ 1`, or a Lyapunov `J^*C+CJ ⪯ 0`. **Report
> `max_z max_j Re(λ_j(z))`; require `≤ 0`** to numerical tolerance. This is the finite **stability**
> statement (distinct from the §4.1 positivity certificates); it does **not** establish the sign of a
> kinetic term (that requires a Lagrangian; `out_of_scope`, REGISTRY §5).

### 4.3 Optional sound-speed-style proxy (recorded, not binding)

> A fixed finite-difference effective sound-speed proxy `c_eff²(z) ≥ 0` where defined. Record
> `c_eff,min²`; the **binding** witness is (i)+(ii). (A negative `c_eff²` would be a *gradient*
> instability — a distinct pathology from a ghost — so it is logged separately and statused if it
> appears.)

### 4.4 Crossing stability

> The crossing redshift `z_c` (root of `d ln ρ_eff/dz = 0`, equivalently `w_eff(z_c) = −1`) must be
> **stable to `< 0.1` in `z` under 1σ parameter jitter** of the fitted `Ξ` (Monte-Carlo over the
> posterior; report the `z_c` distribution std). An unstable crossing (`σ(z_c) ≥ 0.1`) means the
> crossing is not a robust feature and is statused `moduli`/`budgeted` (§8).

> **The certificate IS the result (A).** Passing (i)+(ii) while `w_eff(z) < −1` over an interval is the
> finite, constructive proof that **a positive, stable operator (no growing mode) yields phantom
> crossing** — a stable effective finite readout. The "phantom ⇒ ghost" objection is declared resolved
> only under the over-read of §1.5; an affirmative no-negative-kinetic-DOF claim is `out_of_scope`
> (REGISTRY §5). **Grade:** the certificate is `[T]` for the constructed map as a finite-witness
> stability statement (Lean T5, §7); "the *data* prefer a crossing realized by a positive/stable `R`"
> is `[E]` (the §9.4 data gate).

---

## 5. Method (pipeline)

> **Determinism/provenance (mandatory, `GROUNDING_BRIEF` §III).** Every run pins
> `numpy`/`random`/sampler seeds, writes a run-manifest JSON (`run_id`, date, seeds, datasets+versions,
> software versions, parameters, output files, `audit_status`), and emits `[chain, posterior.hdf5,
> triangle.png]`. `float64` throughout (Python); rationals throughout (Lean T5). The construction leg
> (A) is *fully deterministic* (no RNG); the data leg (B) follows the seed protocol.

### Leg A — the construction / existence result (`[T]`; gate `G-E3-CONSTRUCT`, §9.3)

1. **Build the operator.** Instantiate the pinned `ρ_eff(z) = ρ_m(z) + a₀ + a₁·z/(1+z)` (`xi/rewrite.py`,
   shared with E0 Toy 3) with `(a₀, a₁)` chosen so `d ln ρ_eff/dz` changes sign once in `[0,1.5]` and
   `ρ_eff > 0` everywhere. Place `z_c` near the DESI-preferred crossing.
2. **`w_eff(z)` readout (E3.1).** Compute `w_eff(z) = −1 + (1+z)/3 · d/dz[ln ρ_eff(z)]` analytically
   where possible, else by a fixed central-difference stencil on the pinned grid.
3. **Locate the crossing.** Bisection on the pinned grid ⇒ `z_c`; report `w_eff(0)`, `w_eff(1.5)`
   bracketing `−1`, and the interval where `w_eff < −1`.
4. **Stable-readout certificate (§4).** Run `xi/stability.py`: (i) `min_z ρ_eff > 0` and
   `λ_min^{sym} ≥ 0`; (ii) `max_z max_j Re(λ_j(z)) ≤ 0` (no growing mode); (iii) record `c_eff,min²`.
   Emit the spectrum and the certificate booleans.
5. **Emit artifacts** (§6): `e3_construct_weff.csv`, `e3_operator.npz`, `fig_e3_weff_construct.png`.

> Leg A reproduces and *lifts* E0 Toy 3 to the DESI `z_c`. The only difference from Toy 3 is that the
> operator parameters are placed to match the **data-preferred** crossing (from leg B step B1), making
> the existence result *physically targeted*, not generic. (Toy 3's generic witness still stands as the
> AOR `RefStableAOR`-grade evidence — `plan/00-overview` §7.)

### Leg B — the data result (`[E]`; gates `G-E3-REPRO`, `G-E3-DATA`, controls)

- **B0 — Reproduce baselines (`G-E3-REPRO`, §9.2).** Fit `ΛCDM` (`M₀`) and `w₀wₐ` (`M₁`) jointly to
  DESI DR2 BAO + Pantheon+ (+ Planck prior) with the team stack; **recover the published DESI
  2503.14743 `w₀wₐ` contour and phantom-crossing preference** (`w₀ > −1, wₐ < 0`, crossing at low z)
  *before* any SBT machinery. Convergence: `R̂ < 1.01`, ESS > 400/chain.
- **B1 — Reconstruct `w(z)` / `ρ_DE(z)` and locate `z_c`.** From the `M₁` posterior (and, where
  available, a non-parametric node reconstruction matching 2503.14743's methodology), reconstruct
  `w(z)` and the implied `ρ_DE(z)` on a z-grid; locate the crossing `z_c` and its significance
  (posterior fraction with a crossing in `[0, z_max]`). This fixes the *target* `z_c` for leg A.
- **B2 — Fit the SBT rewrite (`M_Ξ`).** Fit ΛCDM + the low-rank `Ξ` (amplitudes `a₀, a₁[, a₂]`,
  fixed shapes) to the same DESI BAO + SN (+ Planck) data. Compute `ρ_eff(z)` (eq. 5) and `w_eff(z)`
  (E3.1) from the **fitted** `Ξ`. Report `χ², χ²/dof, k, BIC, AIC` vs `M₀, M₁`.
- **B3 — Stable-readout audit on the *fitted* operator (§4).** Run the full §4 certificate on `M_Ξ`
  evaluated at the posterior best-fit and over the posterior (for `z_c` stability §4.4). The decisive
  question: *does the operator that fits the DESI crossing pass (i)+(ii) (positive, no growing mode)?*
- **B4 — False-positive control (Keeley et al. 2506.15091).** Generate seeded mocks from a
  **non-crossing** fiducial (ΛCDM and a non-phantom quintessence `w > −1`); run B1 on each; report the
  fraction that yields an apparent CPL crossing. Compare to the data significance (B1). The crossing
  claim survives only if the data significance exceeds the false-positive rate band (≈3.2% reference).
- **B5 — Bayesian-discipline control (Dinda et al. 2605.13546).** Score the crossing by **global model
  comparison** (ΔBIC / evidence of `M_Ξ` and `M₁` vs `M₀`) and by **out-of-sample** `PPD` (B6), *not*
  by in-sample `Δχ²` alone. Report whether the local goodness-of-fit improvement persists globally.
- **B6 — Out-of-sample / cross-probe predictive audit `PPD` (`plan/04` §4.4).** Leave-one-probe-out:
  fit `M_Ξ` to BAO(+CMB) only, posterior-predict held-out SN `μ(z)`; and SN-only → predict held-out
  BAO. Score `PPD_{p→q}` (whitened, eq. 14). The genuine-`Ξ` test: does `M_Ξ` lower held-out `PPD` vs
  `M₀`/`M₁`, or only in-sample `χ²`? (Anti-fudge.)
- **B7 — Coherence handoff (`plan/04` §9.4).** Export the fitted `(a₀, a₁, a₂)` and the implied
  `K_L/K_M/K_G/K_S` amplitudes + `z_c` to the **coherence ledger** so E1/E2/E4/E5 can check the
  make-or-break cross-amplitude constraint (within **10×**, consistent sign).
- **B8 — AOR statusing (§8).** Type the residual and the crossing claim with exactly one base status.

### Software (from `GROUNDING_BRIEF` §II)
`cobaya ≥3.4` (MCMC/nested), `CLASS ≥3.2` or `CAMB ≥1.5.7` (FLRW distances; pick one, do not mix),
`getdist ≥1.5` + `arviz ≥0.15` (R̂/ESS/posteriors), `numpy/scipy` (`ρ_eff` derivatives, Jacobian
eigenvalues via `scipy.linalg.eig`, Schur/symmetrized-operator PSD via `eigh`), `matplotlib ≥3.5`.
Lean 4 (≥v4.28.0, mathlib-free preferred) for the T5 witness (§7). Modules: `sbt_cosmo/xi/rewrite.py`
(`Δ_H`, `ρ_eff`, `w_eff`), `sbt_cosmo/xi/stability.py` (Jacobian/eigenvalue/stable-readout certificate),
`sbt_cosmo/xi/residual.py` (low-rank `Ξ`), `sbt_cosmo/cosmology/background.py` (`H(z)`, distances),
`sbt_cosmo/aor/{ledger,status}.py`.

---

## 6. Outputs and AOR statusing

### 6.1 Artifacts (committed)

| Artifact | Path (suggested) | Contents |
|---|---|---|
| Run manifests | `results/E3/manifests/*.json` | per-run seeds, datasets+versions, software, params, `audit_status` (`GROUNDING_BRIEF` §III.B) |
| Construction witness (A) | `results/E3/e3_construct_weff.csv` | `z, rho_eff, dln_rho_dz, w_eff`; header: `z_cross`, `w_eff(0)`, `w_eff(1.5)`, `max_Re_eig`, `lambda_min_sym`, `min_rho_eff`, `c_eff2_min`, `no_growing_mode` (bool) |
| Operator dump (A) | `results/E3/e3_operator.npz` | `z`, `rho_eff`, `w_eff`, `Jacobian` (stacked), `eigenvalues`, `Xi_params` |
| Data reconstruction (B1) | `results/E3/e3_wz_reconstruction.hdf5` | reconstructed `w(z)`, `ρ_DE(z)`, `z_c` posterior, crossing significance, per SN compilation |
| Data SBT fit (B2/B3) | `results/E3/e3_data_fit.csv` | `{M₀, M₁, M_Ξ}` × `{χ², χ²/dof, k, BIC, AIC, ΔBIC vs M₁, a₀, a₁, a₂, z_c, max_Re_eig, lambda_min_sym, min_rho_eff, no_growing_mode}` |
| False-positive control (B4) | `results/E3/e3_falsepos_mocks.csv` | per-mock apparent-crossing flag; aggregate false-positive rate; comparison band |
| Bayesian-discipline record (B5) | `results/E3/e3_bayes_discipline.json` | global ΔBIC/evidence vs in-sample `Δχ²`; persistence verdict |
| OOS predictive record (B6) | `results/E3/e3_ppd.json` | `PPD_{BAO→SN}`, `PPD_{SN→BAO}` for `M₀/M₁/M_Ξ` |
| `z_c` stability record (B3) | `results/E3/e3_zc_stability.json` | `σ(z_c)` under 1σ posterior jitter; stability verdict (< 0.1) |
| Posterior triangles | `results/E3/triangle_*.png` | per model (`getdist`) |
| Figures | `results/E3/fig_e3_weff_construct.png`, `fig_e3_weff_data.png` | `w_eff(z)` crossing `−1`, eigenvalue-realpart inset (all ≤ 0), `ρ_eff > 0` panel; data-fit `w(z)`/`w_eff(z)` with crossing |
| AOR status entry | appended to `results/aor_status_table.csv` | the typed residual (§6.2) |
| Coherence handoff | `results/coherence_ledger/E3.json` | `a₀, a₁, a₂`, implied `K_L/K_M/K_G/K_S` amplitudes + sign + `z_c`, for §9.4 cross-check |
| Lean receipt | `lean/.lake` build log + `lean.{toolchain, mathlib_rev, build}` in manifest | green `lake build` of `SbtCosmo.PhantomStableReadout` (§7) |

### 6.2 AOR statusing of the E3 residual (`plan/04` §8; `idea.md` §6 Exp3)

The leftover after E3 must carry **exactly one** AOR base status (F9 No Unstatused Residual). The
status is determined by the §9 verdict:

| E3 verdict | AOR status | Residual type (`plan/04` §8.2) | Payload `π` |
|---|---|---|---|
| Construction (A) passes: positive/stable operator crosses −1 | `bridged` | (operator-rewrite, `Σ_rewrite`) | the explicit `Witness`/operator + the stable-readout certificate (no growing mode); the "phantom ⇒ ghost" objection bridged |
| Data (B): DESI crossing reproduced by positive/stable `R[Ξ]` (no growing mode) | `bridged` | `D_descent` | the fitted `Ξ` + certificate; the apparent `w < −1` is an effective readout |
| Data (B): crossing not robust / not preferred globally (Dinda direction) | `moduli` or `budgeted` | `D_limit`/`D_horizon` | the `z_c` flat direction or the global-evidence-null record |
| If a fit required an operator with a *growing mode* (certificate fails on the data-preferred operator) | `blocked` | (`Σ_rewrite` blocked) | the inadmissibility reason (the growing-mode rewrite is provably blocked, `plan/04` §8.3 `blocked`) — **this is an honest negative result, reported with numbers** |

Plus standing statuses always recorded:
- "Λ not ruled out" → `nonclaim` (`Dark Energy` precursor; `plan/04` §1.2(2), §8.3).
- "Real dark sector not claimed to be this operator" → `nonclaim` (the existence proof is not an
  identity claim — Lean T5 scope line, `plan/05`).
- "No negative-kinetic (ghost) degree of freedom" → `out_of_scope` (REGISTRY §5): E3 builds no
  Lagrangian/kinetic-metric framework, so the ghost-absence claim cannot be made; E3 certifies only a
  stable effective finite readout / no growing mode.
- Out-of-window extrapolation in `z` → `D_horizon` (`budgeted`).
- `c_eff² < 0` gradient-instability proxy, if it appears → logged separately (`budgeted`/`out_of_scope`;
  it is *not* a ghost and must not be conflated with one).
- Any compressed-likelihood fallback → `budgeted`.

This run advances the carrier toward **RefStableAOR** (E1–E3 leg → RefStableAOR per `plan/00-overview`
§7; `plan/04` §8.4); the Toy-3-lifted finite witness is the `RefStableAOR`-grade evidence for P4.

---

## 7. Lean anchor — `SbtCosmo.PhantomStableReadout` (TARGET T5, `[T]`)

The construction result (A) is mechanized exactly as `plan/05` **TARGET T5** specifies (no
re-derivation; this section pins the E3↔Lean correspondence).

> **Module:** `lean/SbtCosmo/PhantomStableReadout.lean`; declaration
> `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness`. Mathlib-free, everything finite +
> rational so it is `decide`/`native_decide`-able (`plan/05` §T5).
>
> **Statement (LOCKED, `plan/04` §6.4 / `plan/05` T5).** There is a finite `Witness` (a rational
> z-grid, a rational `ρ_eff`, and a rational discrete generator `gen`) such that:
> ```
> theorem phantom_stable_readout_witness :
>   ∃ (W : Witness) (i : Fin W.N), NoGrowingMode W.gen ∧ wEff W i < (-1 : ℚ)
> ```
> where `wEff W i = −1 + ((1+z_i)/3)·(Δ ln ρ_eff / Δ z)` (centered, rational) and `NoGrowingMode gen`
> is a **decidable, rational, kernel-checkable sufficient condition** for "all eigenvalues have
> `Re λ ≤ 0`" — preferred form: **Gershgorin** (strict diagonal dominance with non-positive real
> diagonal ⇒ `faithful`/T1 soundness); fallback: a rational **Lyapunov** PSD certificate
> (`narrowed_surrogate`/T2, spectral soundness cited). (`plan/05` T5 options i–iii.) The witness
> certifies a stable effective finite readout (no growing mode), **not** the absence of a
> negative-kinetic (ghost) DOF, which is `out_of_scope` (REGISTRY §5).
>
> **Structural alignment (L8, `plan/05`).** The T5 witness grid + `z_c` must be **structurally
> identical** to the E3 leg-A Python `w_eff` grid and crossing node (same node count ≥ 3, same `z_c`
> node); an `example`/`#eval` prints the witness `w_eff` profile so it can be cross-checked against the
> Python `e3_construct_weff.csv`. Non-vacuity (L6): witness uses ≥ 3 grid nodes; the `∃` is witnessed
> by an explicit term `decide` accepts.
>
> **Scope line (LOCKED, `plan/05` T5).** *"Certifies that a positive, stable (no growing mode) finite
> rewrite operator CAN induce `w_eff < −1` — an existence proof dissolving the 'phantom ⇒ ghost'
> objection by exhibiting a stable effective finite readout. Does NOT claim the real dark sector is
> this operator, nor that the universe's `w_eff` crosses −1 (that is the E3 leg-B empirical fit), nor
> that there is no negative-kinetic (ghost) DOF (that is `out_of_scope` absent a Lagrangian/kinetic-
> metric framework, REGISTRY §5); it certifies that crossing −1 is a property of the effective readout
> of a stable, positive operator."*
>
> **No `sorry`/`admit`/`axiom`/`opaque`/`constant`** (`plan/05` §final checklist). Green `lake build`
> is recorded in the run manifest under `lean.{toolchain, mathlib_rev, build}`.

The Python stable-readout certificate (§4) uses full eigenvalue computation (`scipy.linalg.eig`) as the
**`[E]`-grade numerical** witness on the fine grid / fitted operator; the Lean T5 is the **`[T]`-grade
finite** witness with a decidable sufficient condition on a coarse rational grid. Both must agree on
the sign verdict (no growing mode true) and the crossing (`w_eff < −1` at the witness node).

---

## 8. The AOR ledger entry (LOCKED format)

Per `plan/04` §8, E3 commits one row per residual atom to the AOR Status Table with the triple
`(atom a, status s, payload π)`. Mandatory atoms for E3:

| Atom | Status (verdict-dependent, §6.2) | Type | Payload `π` |
|---|---|---|---|
| "phantom ⇒ ghost" objection | `bridged` (if A passes) | `Σ_rewrite` | the explicit positive/stable operator + stable-readout certificate |
| stable-readout positivity / no-growing-mode constraint | `zero` (certificate holds) / `blocked` (if a growing mode is forced) | `Σ_constraint` | `λ_min^{sym} ≥ 0`, `max Re λ ≤ 0`, `min ρ_eff > 0` witnesses |
| "no negative-kinetic (ghost) DOF" | `out_of_scope` | `Σ_nonclaim` | no Lagrangian/kinetic-metric framework built (REGISTRY §5) |
| DESI data crossing | `bridged` / `moduli` / `budgeted` (per B3–B5) | `D_descent`/`D_limit` | fitted `Ξ` + global evidence + `z_c` stability |
| `z_c` value | `moduli` if `σ(z_c) ≥ 0.1` else `selected` (robust) | `D_limit` | the `z_c` posterior |
| "Λ not ruled out" / "operator ≠ real dark sector" | `nonclaim` | `Σ_nonclaim` | scope reference |
| extrapolation beyond z-grid | `budgeted` | `D_horizon` | sampling-cutoff budget |
| gradient-instability proxy `c_eff² < 0` (if present) | `budgeted`/`out_of_scope` | (logged) | distinct from ghost; never conflated |

Zero `unstatused` entries at phase end (F9, `plan/04` §6.4, §9.5).

---

## 9. Pass / fail gates (quantitative, pre-registered)

> **Pre-registration discipline (`plan/00-overview` §6, `plan/04` §9).** These thresholds are fixed
> **before** seeing results and may not be relaxed afterward; any relaxation is a logged statused
> deviation (`budgeted`). Units are χ²/dof, ΔBIC, whitened distances, eigenvalue real parts, and
> redshift-stability bounds.

### 9.1 Data / metric gates

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E3-COV` | DESI BAO + Pantheon+ covariances PD, condition number `< 10⁸`, all entries finite (else `Σ^†` on legal quotient) | `plan/04` §4.0; `GROUNDING_BRIEF` §VI(1) |
| `G-E3-KERNEL` | `K_L,K_M,K_G,K_S` linear in `(a₀,a₁,a₂)` to `< 1%` (finite-difference check) | `plan/04` §9.2 |

### 9.2 Reproduction gate (must pass first — else the data leg cannot proceed)

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E3-REPRO` | `M₀`/`M₁` joint fit recovers the published **DESI 2503.14743** `w₀wₐ` contour (`w₀>−1, wₐ<0`) and its phantom-crossing preference; `χ²_SN`/`χ²_BAO` within **5%** of published; `R̂<1.01`, ESS>400 | `idea.md` §10.1; `plan/03` reproduce-first |

### 9.3 The construction gate (the centerpiece — `idea.md` §6 Exp3 pass criterion) `[T]`

| Gate | PASS (all required) | FAIL |
|---|---|---|
| **`G-E3-CONSTRUCT`** | The leg-A operator satisfies **all four** — two *positivity* (2,3) and one *stability* (4), which are **distinct** certificates (ADDENDUM §4): (1) **crossing:** `w_eff(z) < −1` over an interval and `> −1` elsewhere (genuine crossing at `z_c ∈ [0,1.5]`); (2) **density positivity (P-dens):** `min_z ρ_eff(z) > 0`; (3) **operator/adequacy positivity (P-adeq — NOT stability, ↔ `Ξ_C⪰0`):** `λ_min^{sym} ≥ −10⁻⁸`; (4) **dynamical stability (S-stab, continuous generator `J`):** `max_z max_j Re(λ_j(z)) ≤ +10⁻⁸` (no growing mode). | any of the four fails ⇒ the existence claim of `idea.md` §6 Exp3 is **not** demonstrated |
| **`G-E3-LEAN`** | `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness` compiles green under `lean --check` (no `sorry`/`axiom`/`opaque`); the `#eval` witness `w_eff` profile matches the Python leg-A `z_c`/sign to the witness node | Lean target does not compile or the witness disagrees with Python |

> **`G-E3-CONSTRUCT` is the gate that satisfies `idea.md` §6 Exp3.** Passing it (with `G-E3-LEAN`) is
> the **theorem-grade resolution of the ghost-instability objection** as a finite-witness stability
> statement: a positive, stable, audit-closed rewrite operator whose induced `w_eff` crosses `−1`
> **with no growing mode** exists and is exhibited (a stable effective finite readout). This is the
> non-negotiable deliverable of E3. The affirmative no-negative-kinetic-DOF (ghost) claim is **not**
> part of this deliverable — it is `out_of_scope` absent a Lagrangian/kinetic-metric framework
> (REGISTRY §5).

### 9.4 The data gate (is the DESI crossing realized by a positive, stable, no-growing-mode operator?) `[E]`

| Gate | PASS | FAIL |
|---|---|---|
| **`G-E3-DATA`** | The `M_Ξ` operator fit to DESI BAO+SN(+CMB) (B2) (a) reproduces the data-preferred crossing `z_c` (B1) within its 1σ, **and** (b) passes the §4 stable-readout certificate (B3): `max Re λ ≤ 0` (no growing mode), `λ_min^{sym} ≥ 0`, `min ρ_eff > 0` on the fitted operator. | the operator that fits the DESI crossing **requires** a violated certificate (a growing mode) — an honest negative, statused `blocked` (§6.2) |
| **`G-E3-ZC-STAB`** | `σ(z_c) < 0.1` in redshift under 1σ posterior jitter (B3, §4.4) | `σ(z_c) ≥ 0.1` ⇒ crossing not robust, statused `moduli` |

### 9.5 SBT-claim / discipline gates

| Gate | PASS | FAIL |
|---|---|---|
| `G-E3-FALSEPOS` (Keeley et al. 2506.15091) | the data crossing significance (B1) **exceeds** the false-positive rate band from non-crossing mocks (B4); report both numbers (reference band ≈ 3.2%) | data significance `≤` false-positive rate ⇒ crossing is consistent with a non-crossing fiducial artifact (statused `probabilistic`/`budgeted`) |
| `G-E3-BAYES` (Dinda et al. 2605.13546) | the crossing preference **persists** under global model comparison: `M_Ξ` (and/or `M₁`) beats `M₀` by ΔBIC/evidence consistently, not only in-sample `Δχ²` (B5) | improvement is in-sample only and **vanishes** under global comparison ⇒ no consistent evidence (statused `budgeted`/`nonclaim`) |
| `G-E3-OOS` (out-of-sample, `plan/04` §4.4) | `M_Ξ` lowers held-out `PPD_{BAO→SN}` and/or `PPD_{SN→BAO}` by **> 3%** vs ΛCDM, and beats every alternative beyond the combined uncertainty band (a `≤`-best / within-3% margin is a floor/tie, not a pass) (B6) | `M_Ξ` improves only in-sample `χ²`, not held-out `PPD` (= fudge) |
| `G-E3-RANK` (anti-fudge, `plan/04` §9.2) | `M_Ξ` uses **≤ 3** extra params (`a₀,a₁,a₂`), shapes probe-shared, **no phantom-specific free parameter**; the crossing is a *consequence* of the fitted `Ξ`, not a tuned `w(z)` | a phantom-specific free parameter was introduced, or rank ceiling exceeded without logged justification |
| `G-E3-COHERE` (coherence handoff, `plan/04` §9.4 / `plan/00-overview` §6.4) | E3's `(a₀,a₁,a₂)` and implied `K_L/K_M/K_G/K_S` amplitudes are within **10×** and consistent sign with the E1 geometry `Ξ` and the E2/E5 charts | E3 `Ξ` amplitude differs from E1 by `>10×` or sign disagrees → **program-phase coherence failure** |

### 9.6 Pre-registered failure modes (honored and reported with numbers; `plan/00-overview` §6.2 std 5)

E3 (as the P4 program leg) **fails the program phase** if any of:
1. `G-E3-CONSTRUCT` fails — **no** positive/stable operator inducing a crossing **with no growing
   mode** can be exhibited (the "phantom ⇒ ghost" objection is *not* dissolved). This is the hard
   failure: `idea.md` §10 standard 5 lists "the phantom crossing requires an actual ghost field" as a
   program-killing outcome (operationalized here as: no stable effective finite readout exists).
2. `G-E3-LEAN` fails — the finite witness does not mechanize (the existence claim lacks its receipt).
3. `G-E3-COHERE` fails — the E3 `Ξ` is mutually inconsistent with E1 (the make-or-break coherence
   gate): the phantom crossing is explained by a *different* `Ξ` than geometry, i.e. a per-probe fudge.
4. `G-E3-RANK` violated — the crossing required a phantom-specific tuned `w(z)`, not the shared `Ξ`.

> **Crucial distinction (LOCKED, `plan/04` §9.6 "failure is acceptable iff statused").** A `FAIL` of the
> *data* gates is **not** a failure of the *program*, provided it is statused:
> - `G-E3-DATA` fail with status `blocked` (a **growing mode** *was* required by the data-preferred
>   operator) is a legitimate, publishable **negative** result that *refutes* the SBT
>   phantom-as-readout reading for the real data — it must be reported with the eigenvalue numbers,
>   not hidden.
> - `G-E3-FALSEPOS`/`G-E3-BAYES` fail (the DESI crossing is a false positive / does not persist
>   globally) is also legitimate: it means **there is no robust crossing to explain**, which *agrees*
>   with Dinda et al. (2605.13546) and Keeley et al. (2506.15091) and is consistent with the program
>   (the `Ξ` simply has no crossing chart active). Status `budgeted`/`nonclaim`.
>
> The program fails at E3 only via §9.6 items 1–4. The unacceptable outcomes are: an unreproduced DESI
> baseline (`G-E3-REPRO` fail), an `unstatused` residual at phase end, or a gate relaxed after the fact.

---

## 10. Dependencies, blocking, and links

- **Blocked by:**
  - `plan/03` data acquisition (DESI DR2 extended DE 2503.14743, DESI DR2 BAO 2503.14738, Pantheon+
    2202.04077 / Union3 2401.06956 / DES-SN5YR, Planck compressed prior).
  - `plan/02` environment (cobaya/CLASS/CAMB/getdist/arviz/numpy/scipy stack; Lean 4 ≥v4.28.0).
  - `plan/04` §3 (rewrite `R[Δ]`, low-rank ansatz, kernels), §4.0 (metric `d`), §4.4 (`PPD`), **§6.4
    (Proposition P4, eq. 19)**, **§7 (the stable-effective-readout stability audit)**, §8 (AOR statuses).
  - `plan/05` **TARGET T5** (`SbtCosmo.PhantomStableReadout`, the finite witness conventions).
  - **E0 Toy 3** (the deterministic stable-operator witness E3 leg A lifts) — `plan/experiments/E0`
    §4; E3 reuses `sbt_cosmo/xi/{rewrite,stability}.py`.
  - **E1** (DESI DR2 reproduction + the fitted geometry `Ξ`, needed for `G-E3-REPRO`, the `z_c` target,
    and the `G-E3-COHERE` cross-check).
  - **E2** (whether the DESI `w(z)`/`Ξ` survives the gluing collapse — E2 §8.4 / §9 hands E3 the
    `F_collapse` so E3 knows whether there is a rewrite residual *to* read as a crossing).
- **Blocks / unblocks:** **E8** (model-competition synthesis — the `{M₀,M₁,M_Ξ}` row + the
  stable-readout certificate + the false-positive/Bayesian-discipline verdicts feed the final matrix);
  the **P4 Lean closure** (`SbtCosmo.PhantomStableReadout`); the **coherence ledger** consumed by
  E4/E5/E6 (the `z_c` and `(a₀,a₁)` are part of the shared `Ξ`).
- **`idea.md` citations:** §3 (shadow map row 5 — the derivative chart), §4 ("Proposition 4: effective
  phantom crossing need not imply ghosts" + the four published positions: DESI 2503.14743, Antusch et
  al. 2604.08449, Keeley et al. 2506.15091, Dinda et al. 2605.13546), §6 **Experiment 3** (the
  `w_eff(z)` formula eq. E3.1, the "construct a positive, stable, audit-closed rewrite operator" pass
  criterion), §7 ("Phantom crossing" — "a ghost appears only if one over-reads `w_eff` as a fundamental
  scalar-field equation of state"), §10 (standards 1, 3, 5).
- **Corpus citations:** `A_Six_Birds_Eye_View_of_Dark_Energy` (the rewrite hypothesis `H(z)²=H_m²+Δ_H`,
  `w_eff` readout, "Λ not ruled out" nonclaim, route-mismatch precursor); `Emergence_IS_the_Needle_
  Killer` (the positive-native-currency / stable-operator membrane discipline = the stable-readout
  certificate basis); `Adequacy_Residuals` (positivity / PSD of the audit-energy form `C=Σ^{-1}`);
  `Foundations_IV` `thm:F2` (Descent–Repair: F2 names source refinement + minimal target coarsening; the operator rewrite is P1's cosmology extension, NOT an F2 repair) +
  `thm:F9` (No Unstatused Residual); `Audited_Operational_Realisability` (the status catalogue,
  `blocked` for a growing-mode rewrite, the `RefStableAOR` carrier grade); `Six_Birds_for_Neutrino_
  Mass` (the cross-lens audit template, here applied to SN-compilation swapping as a packaging signal).
- **arXiv anchors:** **DESI DR2 extended DE 2503.14743** (primary `w(z)` reconstruction); DESI DR2 BAO
  2503.14738; Pantheon+ 2202.04077; Union3 2401.06956; DES-SN5YR Zenodo:13827844 / 2401.02929; Planck
  2018 1807.06209; **Keeley–Shafieloo–Matthewson 2506.15091** (false-positive rate ≈3.2%); **Dinda–
  Maartens–Saito 2605.13546** (global Bayesian discipline); **Antusch–King–Wang 2604.08449** (apparent
  crossing without a phantom scalar).
