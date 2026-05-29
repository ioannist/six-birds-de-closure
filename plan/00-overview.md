# 00 — Master Overview: Dark Energy as the Shadow of a Failed Closure

> **Read this first.** This is the entry point for any implementer joining the Six Birds
> dark-energy closure (`six-birds-de-closure`) program. It states the thesis, fixes the scope
> of *this* implementation phase, reproduces the nine-paradox → one-residual shadow map,
> defines what "done" means with quantitative gates, and points to every other file under `plan/`.
>
> **Authoritative companion:** `GROUNDING_BRIEF.md` (datasets, exact releases, software
> stack, determinism/reproducibility standards, compute budgets, AOR vocabulary). This overview
> is consistent with that brief; where they overlap the brief wins on data/version details and
> this file wins on conceptual framing and the definition of done.
>
> **Source of truth for the science:** `idea.md` (the full research program, including the
> post-section-10 **UPDATE** block on the Hubble readout field, Hubble holonomy, the route matrix,
> and lawful plurality).

---

## 0. Status and hard constraints for implementers

- **This is a build phase, not a writing phase.** Produce experiments + math + Lean +
  committed results. **Do NOT write the manuscript / prose / narrative paper here.** Tables,
  figures, machine-readable result ledgers, and Lean artifacts are in scope; LaTeX section
  drafts are out of scope for this phase.
- **Reproduce before you reinterpret.** Every experiment that touches real data must first
  recover the *published* baseline result to tolerance (see §6) before any Six Birds object is
  introduced. A Six Birds claim built on a pipeline that cannot reproduce DESI DR2 / Planck /
  Pantheon+ is rejected on sight.
- **One residual, not nine fudge functions.** The entire program lives or dies on whether a
  single low-rank closure residual `Ξ_cosmo(z, ℓ, p)` (≤ 5–7 free parameters total, ≤ 3 beyond
  ΛCDM in the minimal ansatz) explains the major anomalies simultaneously. Probe-specific
  free corrections are a failure, not a feature.
- **No unstatused residual.** Every tension that survives must be *typed* using the AOR status
  vocabulary (§7): `zero | budgeted | bridged | hidden | moduli | selected | probabilistic |
  out_of_scope | nonclaim | blocked | approved_other` (plus the four asymptotic variants). Note
  `unstatused` is **NOT** a status — it is a validator-error sentinel; a residual still tagged
  `unstatused` at the end of the phase is a gate failure (F9, No-Unstatused-Residual). Not-claiming
  is represented by `nonclaim`, which is a valid status.
- **Determinism (realistic).** Every run carries a seed-pinned manifest (see GROUNDING_BRIEF §III).
  Likelihood / forward-model evaluations are **deterministic** (bitwise reproducible given fixed
  inputs), and the committed posterior **summaries** are reproducible to a **stated tolerance**.
  MCMC/PolyChord **chains are NOT required to be bitwise-identical** across environments; they are
  validated by **statistical equivalence** — parameter means/covariance within MC error, `R̂ < 1.01`,
  and ESS thresholds. Only the E0 toy demos (no sampler) are bitwise reproducible. Results are
  committed to the repo.

---

## 1. The thesis

The live cosmology debate (May 2026) is not one anomaly but a cluster: DESI DR2 prefers a
time-varying dark-energy equation of state at ~3.1σ (BAO+CMB) to 2.8–4.2σ (with SN); the Hubble
tension persists and is *method-dependent*; the S₈ tension has softened but not vanished; the
cosmological-constant problem, coincidence problem, distance-duality controversy, phantom-crossing
ghost worry, interacting-dark-sector hints, and modified-gravity alternatives all remain open
(`idea.md` §§1–9, Consolidated Assessment table).

The standard reflex is **nine fixes for nine problems** — a new fluid, a new coupling, a new
gravity, a new prior. The Six Birds Theory (SBT) claim is the opposite, and it is the load-bearing
sentence of this whole repository (`idea.md` §0 lead-in, §3):

> **Dark energy is the shadow of a failed closure.**
> The same closure residual appears as Λ, evolving `w(z)`, phantom crossing, distance-duality
> failure, `H₀` mismatch, `S₈` mismatch, interacting-dark-sector terms, or modified-gravity
> parameters, depending on which observational *lens* and *completion* are used.

Formally (`idea.md` §1, §4), cosmological inference is a **closure package**

```
𝔉 = (X, T, {f_p}_{p∈P}, U_θ, A),     P = {CMB, BAO, SN, WL, RSD, local-ladder}
```

where `X` is the underlying world-state, `T` is evolution, `f_p` are probe lenses, `U_θ` is the
homogeneous FLRW completion, and `A` is the audit system. Define packaging `E_{θ,p} = U_θ ∘ f_p`.
Dark energy is **not** posited as a substance; it is the **least audit-closed rewrite** needed when
packaging fails to commute with dynamics:

```
U f_p T ≠ T_FLRW U f_p     ⟹     route mismatch     RM_p(x) = d(E_{θ,p} T x, T_θ E_{θ,p} x) > 0
```

The named object is the **cosmological closure residual**

```
Ξ_cosmo(z, ℓ, p)        indexed by redshift z, staging/scale ℓ, probe p
```

defined as the minimizer of the combined audit cost (`idea.md` §4; grounded in
`Adequacy_Residuals` as a Schur complement, and `AOR` as the closure-completion record):

```
Δ_SBT = argmin_Δ [ Σ_p RM_p(Δ) + Σ_{p,q} LG_{p,q}(Δ) + Σ_{p,q} PPD_{p→q}(Δ) + λ·complexity(Δ) ]
```

The `λ·complexity` term is what defends against the "flexible fudge function" critique: the model
adds the *least* rewrite that closes the audits, not an arbitrary function.

The **four measurable residuals** (`idea.md` §4) that any Six Birds object must reduce:

| Symbol | Name | Definition | Tests |
|---|---|---|---|
| `δ_p` | idempotence defect | `d(E²_{θ,p}, E_{θ,p})` | does the closure stabilize / packaging is a projection |
| `RM_p` | route mismatch | `d(E_{θ,p} T, T_θ E_{θ,p})` | does coarse-graining commute with dynamics |
| `LG_{p,q}` | local-global gluing defect | `d(glue(f_p, f_q), global FLRW)` | do local probes glue to one metric object |
| `PPD_{p→q}` | cross-probe predictive failure | `d(q_obs, q_pred from p)` | out-of-sample predictive closure |

**The minimal empirical ansatz** (`idea.md` §5) keeps the residual low-rank:

```
Ξ_cosmo(z, ℓ, p) = a₀ φ₀(z)              ← constant-like repair          (the Λ-shadow)
                 + a₁ φ₁(z) ψ₁(ℓ) s_p    ← staging/scale-dependent       (growth / WL shadow)
                 + a₂ φ₂(z) c_p           ← calibration/gluing residual   (SN–BAO / H₀ / CDDR shadow)
```

with observable-correction kernels mapping `Ξ` to shifts in SN distance `K_L`, BAO geometry `K_M`,
growth `K_G`, weak-lensing `K_S`, and Hubble readouts `K_{r,ℓ}`. **The same `Ξ` must improve
geometry, growth, and calibration predictions at once.** If each probe needs an unrelated `Ξ_p`,
Six Birds fails.

**The Hubble upgrade (idea.md UPDATE block).** `H₀` is *not* a closure-independent scalar. It is a
route-, lens-, staging-, and calibration-dependent readout of the package:

```
H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo],   r = (probe, anchor, z-depth, lens scale, completion, bridge)
```

So the honest object is a **Hubble readout field** `H_{r,ℓ}(z)`, and the **Hubble tension is the
scalar shadow of Hubble holonomy** `𝔥_γ = B_{γ#}P(H₀^{r₁}) ⊖ P(H₀^{r₁})` — the posterior transported
around a loop of routes does not return unchanged. The prediction is **lawful plurality**: the
disagreements among CMB/BAO, inverse-ladder, Cepheid, TRGB, JAGB, time-delay, and standard-siren
`H₀` are *structured by route and staging*, not random scatter, and the *same* `Ξ_cosmo` that
organizes them must also repair the DESI/SN/BAO/growth audits.

---

## 2. Scope of THIS implementation phase

**In scope (build these):**

1. **Experiments E0–E8** (defined in GROUNDING_BRIEF Part 2; one `plan/experiments/EN-*.md` each).
   Synthetic toy demo, DESI DR2 reproduction + SBT, distance-duality gluing, phantom-crossing
   stability, Hubble route matrix + holonomy, S₈ staging sweep, IDE-as-accounting, MG-as-repair,
   and the model-competition synthesis.
2. **The mathematics**: explicit definitions of `𝔉_cosmo`, `E_{θ,p}`, the four residuals, the
   low-rank `Ξ_cosmo` ansatz, the observable kernels `K_L/K_M/K_G/K_S/K_{r,ℓ}`, and the four
   propositions P1–P4 (§5).
3. **The Lean 4 mechanization** of the propositions and the pass/fail gate conditions, *where
   feasible* (≥ P1 and P4 must have Lean witnesses; P2/P3 mechanized at least as scaffold +
   verified-computation witness). Reuse corpus anchors: `Foundations IV` (`thm:F2`, `thm:F4`,
   `thm:F9`, `thm:F11`), `Adequacy_Residuals`, `AOR`.
4. **Committed results**: per-experiment result ledgers (HDF5/npy + JSON manifests), posterior
   triangle plots, the model-comparison matrix, the AOR status table, and the residual-reuse
   coherence check — all committed to the repository.

**Out of scope (do NOT do in this phase):**

- The prose manuscript / paper sections / abstract / rhetorical framing (that is a later phase;
  `idea.md` §8 is the eventual outline, not a task list for now).
- Running anything via the `ops/` dispatch harness, codex, or any external agent. This is a
  *planning + (later) local-execution* repo; the execution is codex-driven downstream.
- Writing to any memory store.
- Inventing new datasets or new physics beyond the `Ξ_cosmo` ansatz; the ansatz is fixed by
  `idea.md` §5 and the UPDATE block and may only be specialized, not enlarged without a logged
  justification.

---

## 3. The nine-paradox → one-residual shadow map

Reproduced from `idea.md` §3 **with the corrected diagnoses** (and the UPDATE-block refinement of
the Hubble row from "instrument-relative bridge residual / nuisance" to **route-holonomy / lawful
plurality**). Each row is a *projection* of the single residual `Ξ_cosmo`; the right column names
the SBT primitive(s) P1–P6 doing the work. This table is the conceptual spine that experiments
E0–E8 must collectively close.

| # | Paradox | Six Birds diagnosis | How the *same* residual appears | Primitive / chart |
|---|---|---|---|---|
| 1 | **Cosmological-constant problem** | No-overread / cross-layer descent failure | Observed acceleration term is a cosmological closure residual, **not** automatically the QFT vacuum-energy scalar; the 10¹²⁰ mismatch dissolves as an *unbridged cross-layer identification* | **P1 / F11** — Λ is the **constant chart** of `Ξ` |
| 2 | **Hubble tension** *(UPDATE-corrected)* | Route-mismatch **holonomy**; `H₀` is not a closure-independent scalar | CMB→BAO, inverse-ladder, Cepheid→SN, TRGB→SN, JAGB→SN, time-delay, siren `H₀` are **route-indexed readouts** `H₀^{(r,ℓ)}`; disagreement is **lawful plurality** (structured by route + staging), the scalar shadow of nonzero Hubble holonomy `𝔥_γ` | **P3** — `H₀` is the **calibration-currency chart** |
| 3 | **DESI evolving `w(z)`** | P1 rewrite term; redshift-staged closure correction | Homogeneous FLRW completion needs a redshift-dependent operator repair; the `w₀w_a` preference is a *readout* of macro closure failure, not a primitive fluid | **P1 / P4** — `w_a` is the **redshift chart** |
| 4 | **Distance-duality violation (CDDR)** | Local-global obstruction; gluing residual | SN luminosity distances `D_L` and BAO `D_M/r_d`, `D_H/r_d` are locally valid but fail to glue into one global FLRW completion; `η(z)=D_L/[(1+z)²D_A]` deviation is the measured gluing defect | **P5 / F4** — η(z) is the **gluing chart** |
| 5 | **Phantom crossing (`w_eff < −1`)** | Effective-coordinate artifact; readout of a rewrite, not a fundamental field | `w_eff(z)` crosses −1 because it is a macro readout of the (positive, stable) rewrite operator; the witness is a **stable effective readout / no growing mode**, not a ghost-free Lagrangian claim (the latter is `out_of_scope` absent a kinetic-metric framework) | **P1** — phantom crossing is the **derivative chart** |
| 6 | **S₈ / growth tension** | Growth-lens **staging** residual; scale-cut & probe-dependent | Growth (`fσ₈`) and geometry (`Ω_m`) are different closure lenses; scale cuts, z-calibration, baryons, intrinsic alignments move the manifested `Ξ`; the residual is staging-dependent, not universal | **P4 / P6** — S₈ shift is the **growth/staging chart** |
| 7 | **Coincidence problem** | Late-stage activation threshold | Residual turns on when nonlinear structure + coarse-graining failure become cosmologically important (z ≲ 1); "why now?" answered because *closure failure is late* | **P4 / P3** — staging/routing of coarse-graining |
| 8 | **Interacting dark sector (`Q`)** | P6 accounting shadow | The fitted continuity-equation transfer `Q_IDE` is a **ledger representation** of `Ξ_cosmo`, not necessarily a new dark force | **P6** — `Q` is the **continuity-equation chart** |
| 9 | **Modified gravity vs dark energy** | Descent–Repair Normal Form *choice* | `(μ, Σ)`, evolving `w`, IDE `Q`, and backreaction are **alternative repair charts** of the same failed FLRW descent; DESI's `(μ,Σ)≈`GR supports the anomaly living in the *completion* layer, not local gravity | **P1** — MG is the **operator-rewrite chart** (the P1 extension repair; F2 itself names source refinement + minimal target coarsening) |
| (10) | **Anthropic / multiverse retreat** | Closure–reality boundary | If `Λ_obs` is a closure residual rather than a fundamental constant, anthropic selection is no longer the default explanation; it survives only if a true layer-descended Λ passes all audits | **Boundary principle** — what remains when the residual is mistaken for ontology |

> Row count note: `idea.md` §3 lists ten rows (the anthropic row is included). "Nine paradoxes"
> refers to the nine *observational/theory* tensions; the anthropic row is the boundary corollary.
> Experiments cover all of rows 1–9; row 10 is settled by argument (P2/F11 + the boundary
> discipline), not by a dedicated data experiment.

**The one-line headline:** Λ, `w_a`, `Q_IDE`, `η_CDDR`, `μ/Σ`, and `S₈` shifts are **coordinate
charts on the same closure defect.**

---

## 4. The four residuals → experiments map

Each experiment stresses specific residuals and shadow-map rows. (Full charters, inputs, methods,
outputs, and per-experiment gates live in the `plan/experiments/EN-*.md` files; see §8.)

| Exp | Charter (one line) | Residuals exercised | Shadow rows | AOR stratum |
|---|---|---|---|---|
| **E0** | Synthetic null-Λ heterogeneous generator → apparent `Ω_Λ`; refit with `Ξ` rewrite | `δ_p`, `RM_p` | 1, 3, 5 | PreSB → operator-rewrite |
| **E1** | Reproduce DESI DR2 `w₀w_a` (3.1–4.2σ) then add `Ξ_cosmo` | `RM_p`, `PPD_{p→q}` | 1, 3 | RefStableAOR |
| **E2** | Distance-duality `η(z)` as local-global gluing obstruction | `LG_{p,q}` | 4, 3 | local-global |
| **E3** | Phantom crossing with stable effective readout / no growing mode; eigenvalue stability of the rewrite | `RM_p` (+ stability) | 5 | operator-rewrite |
| **E4** | Hubble route matrix + holonomy `𝔥_γ`; lawful plurality test | `RM_p`, `PPD_{p→q}`, holonomy | 2 | CascadeStableAOR / route |
| **E5** | S₈ growth/staging sweep; scale-cut fingerprint vs white noise | `PPD_{p→q}`, `δ_p(ℓ)` | 6 | staging |
| **E6** | IDE `Q(z)` as a P6 accounting chart of `Ξ_cosmo` | `PPD_{p→q}` | 8 | exchange-rate / accounting |
| **E7** | Modified gravity as an alternative descent-repair chart | `RM_p`, stability | 9 | operator-rewrite (alt) |
| **E8** | Model-competition synthesis: ΛCDM / `w₀w_a` / CDDR / IDE / MG / SBT | all | all | AOR |

---

## 5. The four propositions (math + Lean targets)

These are the formal backbone (`idea.md` §4, §8 Section-4). Each is grounded in a named
Foundations-IV law and gets a Lean target. **Definition of "proved" here = a theorem statement
in Lean 4 with either (a) a complete proof reusing the corpus anchor, or (b) a verified-computation
witness for the finite/numerical instance, with the residual obligation explicitly statused.**

| Prop | Statement (informal) | Foundations-IV anchor | Lean target |
|---|---|---|---|
| **P1 — Descent-Repair Normal Form** | When the FLRW descent of a macro law fails, `thm:F2` names the base admissible repairs as **source refinement** and **minimal target coarsening**; P1 extends this normal form with the **operator-rewrite** chart, and `Δ_SBT` (the `Ξ_cosmo` rewrite) is that operator-rewrite repair. | `thm:F2` *Descent-Repair Normal Form* (Lean: `Transport.DescentRepair.descent_repair_normal_form`) | Instantiate F2 with `q = U_θ` (FLRW completion as quotient), `F = f_p T`, `r = ` observable readout; show `splitObs ≠ ∅ ⇒ Ξ`-rewrite is the minimal operator-rewrite repair beyond F2's source-refinement / target-coarsening base. **Full proof feasible** (reuse F2). |
| **P2 — No-Overread / Access Quotient** | QFT vacuum energy does **not** descend automatically to cosmological dark energy; `ρ_vac^QFT ≡ ρ_Λ^cosmo` is rejected unless a bridge descends through the cosmological access quotient. Dissolves the cc-problem as an unbridged cross-layer identification. | `thm:F11` *Adequacy / No-Overread* (access quotient `def:access-quotient`) | State the access quotient `accessQ: H → Q_I` for the cosmological observation signature; prove the identification is an **overread defect** absent a declared bridge. **Scaffold + witness** feasible; full proof reuses F11. |
| **P3 — Local-Global / Distance Duality** | Distance duality is the statement that SN and BAO local sections globalize into one metric-distance object; CDDR failure is a **gluing obstruction**, not automatically new dark energy. | `thm:F4` *Local-Global Obstruction Normal Form* (Lean: `…Topology…`/`local-global`) | Instantiate F4 local-global compatibility with `f_SN`, `f_BAO` sections; `η(z) ≠ 1 ⇔` nonempty gluing obstruction. **Scaffold + numerical witness** on the fitted η(z). |
| **P4 — Phantom Crossing With Stable Readout** | A finite, **positive, stable** rewrite operator can induce `w_eff(z)` crossing −1 with a **stable effective readout / no growing mode** (grade `[T]` finite-witness stability). The stronger "no negative-kinetic (ghost) d.o.f." claim needs a Lagrangian/Hamiltonian/kinetic-metric framework this program does not build, and is therefore `out_of_scope` (statused) unless such a framework is added. | (no single named F-law; uses operator-rewrite + eigenvalue/stability audit; cf. `Emergence IS the Needle Killer` membrane discipline) | Construct the finite macro-evolution map with `Ξ`; **prove** all Jacobian eigenvalues have non-positive real part (no growing mode / stable effective readout) while the induced `w_eff` crosses −1. Lean target `SBTCosmo.PhantomStableReadout` states the finite stability property only. **Full finite proof feasible** (verified computation). |

`No Unstatused Residual` (`thm:F9`) is the meta-obligation enforced across all four: every leftover
tension must carry an AOR status (§7).

---

## 6. Pass / fail gates (quantitative)

These are the **phase-level** gates. They are the conjunction of the per-experiment gates
(GROUNDING_BRIEF Part 2) plus the five hard evidence standards (`idea.md` §10). All thresholds are
**pre-registered**: they may not be relaxed after seeing results; a relaxation must be logged as a
statused deviation.

### 6.1 Reproduction gates (must pass *before* any SBT object is added)

| Gate | Threshold | Source |
|---|---|---|
| Baseline ΛCDM fit | χ²/dof < 1.05 on Planck 2018 TT/TE/EE + DESI DR2 BAO | GROUNDING_BRIEF §I.A/B, §VI(3) |
| DESI DR2 `w₀w_a` recovery | recovered `(w₀, w_a)` contours within ±5% of published (arXiv:2503.14738), e.g. `w₀≈−0.92±0.08`, `w_a≈−0.49±0.23`-class | `idea.md` §6 E1 |
| Likelihood agreement | computed χ²_total within 5% of published reference per probe block | GROUNDING_BRIEF §VI(3) |
| Convergence | Gelman–Rubin `R̂ < 1.01` on all sampled params; ESS > 400/chain | GROUNDING_BRIEF §III.C, §VI(2) |
| Covariance sanity | positive-definite; condition number < 10⁸; all entries finite | GROUNDING_BRIEF §VI(1) |

### 6.2 Six Birds claim gates (the five hard standards, operationalized)

1. **Low-rank residual.** Total SBT free parameters ≤ ΛCDM + 3 in the minimal ansatz (≤ 5–7 across
   the full carrier). No probe-specific free `Ξ_p`. *Fail if* the same dataset requires distinct,
   uncorrelated `Ξ` per probe.
2. **In-sample fit.** SBT (ΛCDM + `Ξ_cosmo`) achieves χ²/dof ≤ best phenomenological model on the
   joint DESI+CMB+SN data, with ΔBIC not worse than +5 vs the best competitor.
3. **Win out-of-sample.** Leave-one-probe-out (BAO+CMB→SN; SN+BAO→growth; WL+RSD→geometry;
   CMB+BAO→local `H₀`). On the primary OOS metric (predictive log-score / Δχ²_OOS), complexity-
   penalized, the verdict is **win / tie / fail** (REGISTRY §8): a **`win`** requires SBT-`Ξ` to beat
   **every** alternative by **more than the combined uncertainty band** AND after the complexity
   penalty, with **no silent loss** on any critical leg (geometry, growth, Hubble); a **`tie`** (within
   the band of the best alternative) is **NOT a pass**; a **`fail`** loses overall or on any critical
   leg. Only a strict `win` satisfies this standard — the old "within 3%" pass wording is removed.
4. **Staging fingerprint.** Parameter trajectories across scale-cut / z-binning sweeps show
   structured (not white-noise) variation: spectral low-frequency power **> 2×** the ΛCDM/null
   trajectory, or BIC(SBT staging model) − BIC(null) **> 10** (strong) / **> 5** (moderate).
5. **Pre-registered failure modes honored.** All E0–E8 failure conditions (GROUNDING_BRIEF Part 2)
   are checked and reported with numbers, pass or fail.

### 6.3 Per-experiment headline gates (summary; full list in EN files)

| Exp | Headline pass condition | Headline failure condition |
|---|---|---|
| E0 | Recover `|Ω_Λ| > 0.5` from null-Λ generator; refit RMSE within 5% using ≤ 2 `Ξ` params; `δ ≈ 0` | `Ξ` needs > 2 params/bin, RMSE gap > 10%, or `δ` > 10% of data variance |
| E1 | SBT χ²/dof ≤ 0.99 with ≤ 3 extra params; OOS SN RMSE ↓ > 10% (a within-MC-error match is a floor/tie, not a pass — the decisive OOS win is judged program-level at `G-E8-OOS-DECISIVE`) | χ² > 5% worse; > 4 extra params; OOS SN > 15% worse |
| E2 | M₂ (`η≠1`, `Ξ≠0`) OOS ΔBIC > 5 vs {M₀,M₁}; gluing explains > 50% of apparent `w_a` | M₂ never beats M₁; gluing explains < 30%; η-shape uncorrelated with residuals (p < 0.05) |
| E3 | `w_eff` crosses −1 at DESI-preferred `z_c`; all Jacobian eigenvalues `Re λ ≤ 0`; `z_c` stable to < 0.1 under 1σ | positive-real eigenvalue (instability); no crossing when DESI prefers it; `z_c` shifts > 0.5 |
| E4 | route clustering ρ(r=r′) > ρ(r≠r′) (Spearman p < 0.05); staging OOS R² > 0.7; holonomy `𝔥_γ` ≫ measurement error (> 0.1 nats); `Ξ`-corrected `std[H₀^{r,ℓ}]` shrinks | route structure absent; staging R² < 0.5; `𝔥_γ` < 0.1 nats on all loops; `Ξ` does not reduce route mismatch |
| E5 | `(S₈)^{ℓ_cut}` shows smooth staging trajectory; ΔBIC(SBT−null) > 10 or > 40% variance explained; `K_S` amplitude within 10× of `K_L`, `K_M` | white-noise scatter; ΔBIC < 5; `K_S` amplitude > 10× off from `K_L`/`K_M` |
| E6 | effective `Q(z)` from `Ξ` matches fitted IDE `Q` to ≤ 20% RMS; SBT RSD reducible to IDE within 10% (comparability, NOT a std-3 OOS win — program OOS decided only at E8/`G-E8-OOS-DECISIVE`); `|μ_SBT−μ_GR| < |μ_IDE−μ_GR|` | `Q` discrepancy > 30%; SBT RSD > 15% worse; same `(μ,Σ)` deviation in both |
| E7 | reproduce DESI `(μ₀,Σ₀)`≈GR; MG-induced `w(z)` inside DESI 2σ; MG growth OOS within 15%; no MG instability | MG growth > 20% worse; MG eigenvalue instability (AOR fail). *(MG simply not preferred is not a failure — it is a logged alternative repair.)* |
| E8 | SBT final composite score ≥ ΛCDM; Bayes factor `log B_{SBT/ΛCDM} > 1` (target > 3); OOS RMSE strictly below every alternative beyond the combined uncertainty band (a within-1.1× margin is a tie/floor, not a pass — decisive only at `G-E8-OOS-DECISIVE`) | SBT BIC ≫ 5 worse than best; OOS > 20% worse; > 4 extra params with no BIC gain; staging fingerprint absent; `log B < 0` |

### 6.4 Coherence gate (the make-or-break constraint)

The **same** low-rank `Ξ_cosmo` is fit in **exactly the seven coherence-ledger members E1–E7**
(geometry E1/E2, phantom E3, Hubble E4, growth E5, accounting E6, MG-compatibility E7), whose
amplitudes enter the frozen ledger `results/xi_cosmo_coherence.csv`. (E0 is excluded — it fits the
synthetic injected `XiToy`, not `Ξ_cosmo`; E8 is the judge that consumes the ledger, not a member.)
**Fail rule (`G-PHASE-COHERENCE`):** if any member's fitted `Ξ_cosmo` is mutually inconsistent with
another — cross-amplitudes outside **10×** or with disagreeing sign (e.g., the E5 `K_S` amplitude
differs from the E1 `K_L`/`K_M`-implied amplitude by > 10×) — the phase resolves to **`PROGRAM_FAIL`**.
The experiments are not independent; they must form one audit closure.

---

## 7. AOR status vocabulary and the result ledger

All results are recorded in an **Audited Operational Realisability (AOR)** carrier
(`docs/papers/…Audited_Operational_Realisability…`). Carrier status progresses:

```
PreSB  →  RefStableAOR  →  CascadeStableAOR  →  AOR
(raw fit)  (E1–E3 pass)     (E4–E7 pass)         (E8 synthesis passes)
```

Every surviving tension is a **statused residual**, typed with exactly one base status:

`zero | budgeted | bridged | hidden | moduli | selected | probabilistic | out_of_scope | nonclaim | blocked | approved_other`

(plus the four asymptotic variants `asymptotic_budgeted | summable | contractive | eventual_zero`
per REGISTRY §1 / the grounding brief). `unstatused` is **NOT** a member of this enum: it is a
validator-error sentinel, and any residual still tagged `unstatused` is a gate failure, not a
status. A mandatory **AOR Status Table** must accompany the final results; an `unstatused` entry at
phase end is a defect (`thm:F9`, No Unstatused Residual). Examples of expected statusing: the
cc-problem cross-layer bridge →
`budgeted`/`out_of_scope`; a CDDR gluing defect repaired by `Ξ` → `bridged`; a genuinely
irreducible systematic → `budgeted`; a parameter the data cannot fix → `moduli`.

---

## 8. Definition of done

The phase is **done** when *all* of the following hold and are committed to the repo:

1. **E0–E8 each implemented and run**, each producing: a seed-pinned run manifest JSON
   (GROUNDING_BRIEF §III.B), a result ledger (HDF5/npy data vector + covariance + diagnostics),
   a posterior triangle plot (where MCMC is used), and a pass/fail report against its
   pre-registered gates (§6.3).
2. **All §6.1 reproduction gates pass** for every experiment touching real data, demonstrated
   *before* SBT objects are introduced.
3. **All five §6.2 hard-standard gates pass** for the Six Birds claim, with numbers.
4. **The §6.4 coherence gate passes**: one low-rank `Ξ_cosmo` reused across E1–E7, with the
   residual-reuse matrix committed and all cross-amplitudes within tolerance.
5. **The four propositions P1–P4 are proved and Lean-mechanized where feasible**: P1 and P4 with
   complete Lean proofs (P1 reusing `thm:F2`; P4 a finite verified-computation/eigenvalue witness),
   P2 and P3 with Lean scaffolds + verified-computation witnesses reusing `thm:F11` and `thm:F4`.
   Each Lean artifact compiles under `lean --check`.
6. **E8 model-competition matrix committed**: rows {ΛCDM, `w₀w_a`, CDDR, IDE, MG, SBT} × columns
   {χ²/dof, ΔBIC, ΔAIC, k, OOS RMSE, staging power, route-closure ratio, `log B`}, with SBT meeting
   its §6.3 E8 gate.
7. **AOR status table committed**, every residual typed, zero `unstatused` entries.
8. **Determinism verified** (per REGISTRY 11.6): likelihood / forward-model evaluations are bitwise
   reproducible given fixed inputs, and committed posterior summaries reproduce to a stated tolerance;
   sampler chains are validated by statistical equivalence (`R̂ < 1.01`, ESS, means/covariance within
   MC error), not bitwise identity. The E0 toy demos (no sampler) reproduce bitwise.

A `PROGRAM_FAIL` (or honest `ACCEPTED_NEGATIVE`) outcome is an acceptable scientific result *if* it
is honestly statused — e.g., "phantom crossing showed a growing mode / no stable effective readout
(P4 fail)" or "`Ξ` fragmented into probe-specific corrections (coherence fail, `G-PHASE-COHERENCE`)"
must be recorded as such, not hidden. What is *not* acceptable is an unreproduced baseline, an
`unstatused` residual, or a relaxed-after-the-fact gate.

---

## 9. Inventory of plan files (what each file specifies)

This overview (`plan/00-overview.md`) is the conceptual entry point and the definition of done.
The remaining plan artifacts are:

- **`GROUNDING_BRIEF.md`** — the authoritative data + environment + audit brief: exact dataset
  releases and access (DESI DR2 BAO `2503.14738`, Planck 2018 `1807.06209`, SPT-3G D1 `2601.16277`,
  ACT DR6 `2509.02945`, Pantheon+ `2202.04077`, Union3 `2401.06956`, DES-SN5YR Zenodo:13827844,
  DES Y6 `2601.14559`, KiDS-Legacy `2503.19441`, HSC Y3 `2511.18134`, DESI full-shape `2411.12026`,
  SH0ES `2509.01667`, CCHP `2408.06153`, TDCOSMO `2110.00517`, GW170817 `1709.05895`), the software
  stack (cobaya ≥ 3.4, CLASS ≥ 3.2 / CAMB ≥ 1.5.7, pyccl/CCL, getdist, arviz, Lean 4 ≥ 4.0),
  determinism/seed/manifest standards, compute budgets, data-format specs, and the full AOR status
  vocabulary + the per-experiment operationalized gates that this overview summarizes in §6.3.
- **`plan/experiments/E0-*.md` … `plan/experiments/E8-*.md`** — one file per experiment (to be
  authored alongside this overview), each containing: charter; `idea.md` + corpus grounding;
  explicit **inputs** (datasets/versions, parameters), **method** (pipeline, models M₀/M₁/M₂…,
  estimators), and **outputs** (ledgers, plots, manifests); the null and alternative models; the
  AOR stratum exercised; the Lean anchor; and the pre-registered quantitative pass/fail gates
  matching §6.3 here. E0 = synthetic toy demo; E1 = DESI DR2 reproduction + SBT; E2 = distance-
  duality gluing; E3 = phantom crossing with stable effective readout / no growing mode; E4 = Hubble route matrix + holonomy
  (the central UPDATE-block diagnostic); E5 = S₈ staging sweep; E6 = IDE-as-accounting; E7 =
  MG-as-repair; E8 = model-competition synthesis.

When in doubt about *data/versions/seeds/AOR vocabulary*, consult the GROUNDING_BRIEF; when in doubt
about *what counts as success and why*, consult this overview (§3 thesis map, §6 gates, §8 done).
When in doubt about *the physics*, consult `idea.md` (and its UPDATE block for the Hubble sector).

---

## 10. Corpus grounding (for implementers who want the proofs)

- **`idea.md`** — full program; §1 closure package, §3 shadow map, §4 carrier + four residuals,
  §5 minimal `Ξ` ansatz + kernels, §6 experiments, §10 five hard standards, **UPDATE** Hubble field /
  holonomy / route matrix / lawful plurality.
- **`docs/papers/INDEX.md`** — corpus map; P1–P6 vocabulary; concept→paper lookup.
- **A Six Birds' Eye View of Dark Energy** (`…A_Six_Birds_Eye_View_of_Dark_Energy…`) — the precursor;
  closure package `(X,T,f,U,A)`, route mismatch 0 in linear regime / > 0 with nonlinearity,
  null-Λ heterogeneous-patch toy → apparent acceleration. Foundation for E0/E1. **Does not rule out
  a cosmological constant.**
- **Adequacy Residuals and Blind-Spot Currency** — `Ξ` as Schur complement of block currencies;
  projection identity; the residual calculus behind `Ξ_cosmo`.
- **Audited Operational Realisability (AOR)** — the carrier, the status strata, the
  `PreSB → RefStableAOR → CascadeStableAOR → AOR` hierarchy, No-Unstatused-Residual discipline.
- **Foundations IV** — named laws: `thm:F2` Descent-Repair (→ P1), `thm:F4` Local-Global Obstruction
  (→ P3), `thm:F9` No Unstatused Residual (meta-obligation), `thm:F11` Adequacy/No-Overread + access
  quotient (→ P2).
- **Holonomy with Memory** + **Protocol Trap** + **To Plot a Stone** — route transport, holonomy vs
  arrow-of-time separation, distance-as-protocol-cost / curvature-as-loop-holonomy. Foundation for
  E4 (Hubble holonomy `𝔥_γ`).
- **Emergence IS the Needle Killer** — layer-dissolving / membrane discipline; framework-bound
  limits; supports the P4 stability argument.
- **Six Birds for Neutrino Mass** — a worked cross-lens audit template (SPT-3G 2018→D1 lens swap);
  the methodological pattern (held-out mismatch, localization, common-staging control) E4/E5 reuse.
