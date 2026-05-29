# E4 — The Hubble Route Matrix and Hubble Holonomy

> **One-line charter.** Build a **Hubble route matrix** `H₀^{(r,ℓ)}` whose rows `r` are
> observational routes (CMB→BAO, BAO→SN, Cepheid→SN, TRGB→SN, JAGB→SN, time-delay, siren) and whose
> columns `ℓ` are staging/bridge choices (redshift/host cuts, SN sample, anchor, BAO compression,
> calibration bridge); fit three nested models — **null** (`K[Ξ]=0`), **per-route nuisance noise**
> (`H₀ + ε_{r,ℓ}`), and a **single low-rank closure residual** (`H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo]`);
> compute **Hubble holonomy** `𝔥_γ` around route loops; and run the **five lawful-plurality
> pass/fail tests** so that the Hubble tension is established as a *route-holonomy measurement*, not
> a nuisance to be bracketed. **Decisive gate (`G-E4-DECISIVE`, the lawful-plurality claim):** the
> single `Ξ_cosmo` must beat **both** null **and** per-route-noise by Bayesian model comparison, be the
> *same* `Ξ_cosmo` reused in E1/E2/E5, **and** all **five lawful-plurality tests LP1–LP5 (T1–T5)** must
> pass. Model comparison + reuse *without* all five LP tests is only the weaker **route-reuse** finding
> (`G-E4-ROUTEREUSE`, `[E]`/partial), not the lawful-plurality claim.

> **Read-order / consistency.** This file implements *one* experiment of the program defined in
> `plan/00-overview.md` (§3 shadow map row 2 "Hubble tension"; §6 gates; §8 done) and
> `../GROUNDING_BRIEF.md` (canonical datasets, software stack, determinism standard, AOR
> vocabulary, audit gates). Every formal object used here is *locked* upstream in
> `plan/04-formal-foundations.md`: the cosmological closure carrier `𝔉_cosmo` and the four residuals
> `δ_p / RM_p / LG_{p,q} / PPD_{p→q}` (§4), the low-rank `Ξ_cosmo` ansatz and observable kernels
> `K_L/K_M/K_G/K_S` (§3), Proposition **P3 (Hubble holonomy / route transport)** and its grounding
> in **F4 local–global obstruction** and **F3/P3 protocol holonomy** (§5), the metric `d` (§4.0),
> and the AOR status catalogue (§8). Data products and access are locked in
> `plan/03-data-acquisition.md` (CMB §B, BAO §A, SN §C, local ladder §F).
> **Science source of truth:** `idea.md` §2 ("Hubble tension"), §6 Experiment 4 ("cross-probe
> posterior-predictive audits", Hubble leg), and — centrally — the entire **UPDATE block after §10**
> ("The Hubble 'constant' is not a closure-independent scalar"; "Hubble readout field"; "Hubble
> holonomy `𝔥_γ`"; "Hubble route matrix"; "lawful plurality"; the five pass/fail conditions). This
> file does **not** re-derive those objects; it specifies the *pipeline, the matrix construction, the
> three models, holonomy computation, outputs, and pre-registered quantitative pass/fail gates*.
>
> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean/finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a gate
> in §10 below).

> **HARD GROUNDING (idea.md UPDATE, central pillar).** The UPDATE block elevates the Hubble sector
> from a "handle carefully" caveat to *one of the central pillars of the paper*. The load-bearing
> claims this file must operationalize, verbatim in intent:
> 1. "`H₀` is **not a closure-independent scalar** across observational routes" — it is a
>    "route-, lens-, staging-, and calibration-dependent readout of the cosmological package."
> 2. "`H₀` is an **illegal over-compression** when the observational package has nonzero route
>    mismatch." The honest object is a **Hubble readout field** `ℋ_{r,ℓ}(z)`, evaluated at `z=0` as
>    `H₀^{(r,ℓ)}`.
> 3. The disagreement is **lawful plurality**: "The disagreements should organize by route, staging,
>    calibration bridge, redshift depth, and lens/completion choice." Not random scatter.
> 4. "**The Hubble tension is the scalar shadow of Hubble holonomy.**"
> 5. Danger to defuse: critics will say "you are just relabeling observational scatter as theory."
>    The five pass/fail conditions exist precisely to forbid that.

---

## 1. Scientific framing and grounding

### 1.1 What this experiment is about

In ordinary FLRW cosmology `H₀` is a single present-day scalar parameter, and all methods are
*supposed* to estimate the same object:

```
H₀^CMB ≈ H₀^BAO ≈ H₀^Cepheid/SN ≈ H₀^TRGB/SN ≈ H₀^time-delay ≈ H₀^siren.
```

Six Birds Theory (SBT) refuses that identity as primitive (`idea.md` UPDATE). Each determination is
a **packaged readout** transported through a lens, a completion, and a calibration bridge:

```
H₀^{(r)} = H_closed(0) + K_r[Ξ_cosmo],        r = (probe, anchor, redshift depth, lens scale, completion, calibration bridge).
```

If the cosmological closure **package is closed**, these currencies exchange *at par* and yield one
`H₀`. If **route mismatch** `RM_p` is present (the central SBT diagnostic, `plan/04` §4.2; Dark
Energy precursor §"Coherence: idempotence and route mismatch"; `RM(x)=d(E·T x, T·E x)`), the
"exchange rates acquire holonomy" and different routes return different effective `H₀`. **That is a
prediction, not a bug.**

E4 is the experiment that turns this prediction into a falsifiable measurement. It is the
operational centerpiece of **Proposition P3 (Hubble holonomy / route transport)** locked in
`plan/04` §5, grounded in:
- **F4 Local–Global Obstruction** (`Foundations_IV` `thm:F4`): the route-indexed `H₀^{(r)}` are
  local sections of a would-be global scalar `H₀`; failure to glue them into one value is a
  *gluing obstruction*, classified by exactly one of four overlap statuses (mirroring E2's CDDR
  treatment). The "global FLRW scalar `H₀`" plays the role of the global object.
- **P3 / F3 Protocol Holonomy** (`Protocol_Trap`; `Holonomy_with_Memory`): composition order of
  bridges matters; transport around a *loop* of routes can fail to return the start posterior. The
  loop residue **is** the holonomy.

### 1.2 The live data this experiment must engage (mandatory)

The Hubble sector disagreement is real and method-dependent (`idea.md` §2; `plan/03` §F). E4 must
ingest the *published* determinations as fixed inputs (this is a planning/blueprint task; we collect
posteriors, we do not re-run distance-ladder pipelines). The canonical anchor values
(`../GROUNDING_BRIEF.md` §I.B, §I.F; `idea.md` §2):

| Route family | Determination | `H₀` [km s⁻¹ Mpc⁻¹] | arXiv / DOI | SBT route label |
|---|---|---|---|---|
| Early / inverse | Planck 2018 base-ΛCDM | `67.4 ± 0.5` | 1807.06209 | `r₁ = CMB→BAO` anchor |
| Early / inverse | DESI DR2 BAO + BBN (inverse ladder) | `≈ 67.5 ± 0.6` (combination-dependent) | 2503.14738 | `r₁ = CMB→BAO`, `r₂ = BAO→SN` |
| Late / Cepheid | SH0ES JWST+HST Cepheid→SN | `73.18 ± 0.88` | 2509.01667 | `r₃ = Cepheid→SN` |
| Late / TRGB | CCHP JWST TRGB→SN | `70.39 ± 1.22_stat ± 1.33_sys ± 0.70_SN` | 2408.06153 | `r₄ = TRGB→SN` |
| Late / TRGB | CCHP JWST-only TRGB→SN | `68.81 ± 1.79 ± 1.32` | 2408.06153 | `r₄ = TRGB→SN` (anchor variant) |
| Late / JAGB | CCHP JWST JAGB→SN | `67.80 ± 2.17 ± 1.64` | 2408.06153 | `r₅ = JAGB→SN` |
| Late / lensing | TDCOSMO + H0LiCOW time delays | `73.3 ± 1.8` (model-dependent; mass-sheet) | 2110.00517 | `r₆ = time-delay` |
| Late / GW | GW170817 standard siren | `70.0 ⁺¹²₋₈` | 1709.05895 | `r₇ = siren` |

> **idea.md UPDATE, decisive framing:** "The disagreements should organize **by route, staging,
> calibration bridge, redshift depth, and lens/completion choice**. So the Six Birds prediction is
> not merely plurality of `H₀`. It is **lawful plurality**." E4's gates (§10) are the discipline that
> turns lawful plurality into a result rather than a relabeling of scatter.

### 1.3 Foundations grounding (P3 ↔ F4, F3; Holonomy_with_Memory; Protocol_Trap)

Three corpus results are the spine of E4. They are *locked* in `plan/04` §5 and re-used here:

- **F4 local–global obstruction normal form** (`Foundations_IV` `thm:F4`; Lean
  `Transport.LocalGlobalObstruction.local_global_obstruction_normal_form`): a compatible local
  family carries **exactly one** of four statuses. For the Hubble field we instantiate:
  ```
  ExactlyOneStatus(H) ⇔ RoutesInconsistent(H) ⊻ RouteCompatibleNonScalar(H)
                         ⊻ ScalarAmbiguous(H) ⊻ ScalarExact(H)
  ```
  - `ScalarExact` — all routes glue to one `H₀` (no tension, null wins).
  - `RouteCompatibleNonScalar` — routes are mutually compatible *as a field* `H₀^{(r,ℓ)}` but do not
    collapse to one scalar: **lawful plurality, the SBT prediction**.
  - `RoutesInconsistent` — routes contradict even as a field (no low-rank `Ξ` reconciles them):
    pure systematics / failure of the framework.
  - `ScalarAmbiguous` — multiple distinct scalars glue equally well (degenerate; statused `moduli`).

- **P3 / F3 protocol holonomy** (`Protocol_Trap`): the **critical control discipline** of this
  experiment. `Protocol_Trap` proves that *route dependence is NOT automatically meaningful* — a
  positive route effect can be a scheduling/bookkeeping artifact (the "protocol trap"), and an
  autonomous, honestly-internalized lift can collapse a holonomy to ~0 (their `EPR_lifted < 10⁻¹⁷`
  under the unbiased clock). **Therefore measuring `𝔥_γ ≠ 0` is necessary but not sufficient.** E4
  must show the holonomy *survives honest internalization of the declared bridges* (test T5, source
  refinement) — exactly the discipline `Protocol_Trap` and `Holonomy_with_Memory` demand.

- **Holonomy with Memory** (route transport, loop action, predictive vs current quotient): supplies
  the formal object for "transport a posterior around a loop." A loop `ℓ ∈ 𝒞_{i→i}` acts on the
  *current quotient* `CurrentQ` and the *predictive quotient* `PredictiveQ`; the loop can act
  trivially on `CurrentQ` while moving `PredictiveQ`. The Hubble analogue: a route loop may return
  the *point estimate* of `H₀` unchanged (current) while moving the *full posterior / predictive
  content* (predictive). E4's holonomy `𝔥_γ` (§5) is measured on the **posterior** precisely to
  catch the predictive-quotient signal, not just the scalar shadow. `Holonomy_with_Memory` also
  fixes the **flattenable** control: some route mismatch is removable by admissible completion and
  must be classified as such, not counted as a positive.

---

## 2. The Hubble route matrix `H₀^{(r,ℓ)}`

### 2.1 Rows — observational routes `r`

The route is the full transport chain `r = (probe, anchor, redshift depth, lens scale, completion,
calibration bridge)`. The seven canonical rows (`idea.md` UPDATE "Rows would be observational
routes"):

| `r` | Route | Lens / completion content | Primary data (locked `plan/03`) |
|---|---|---|---|
| `r₁` | **CMB→BAO** | sound-horizon `r_d` calibration → BAO dilation → inverse-ladder `H₀` | Planck 2018 (1807.06209); DESI DR2 BAO (2503.14738) |
| `r₂` | **BAO→SN** | BAO `r_d` → SN absolute magnitude `M_B` bridge → low-z `H₀` | DESI DR2 BAO (2503.14738) + Pantheon+ (2202.04077) / Union3 (2401.06956) |
| `r₃` | **Cepheid→SN** | Cepheid P–L (anchors: NGC 4258 maser, MW parallax, LMC DEBs) → SN `M_B` → `H₀` | SH0ES JWST+HST (2509.01667) |
| `r₄` | **TRGB→SN** | TRGB tip magnitude → SN `M_B` → `H₀` | CCHP JWST (2408.06153) |
| `r₅` | **JAGB→SN** | JAGB (carbon-AGB) standard candle → SN `M_B` → `H₀` | CCHP JWST (2408.06153) |
| `r₆` | **time-delay** | strong-lens time delays + mass model → `H₀` (no SN bridge) | TDCOSMO+H0LiCOW (2110.00517) |
| `r₇` | **siren** | GW luminosity distance + EM redshift → `H₀` (no ladder) | GW170817 (1709.05895) |

### 2.2 Columns — staging / bridge choices `ℓ`

The column index is the *staging/bridge* coordinate (`idea.md` UPDATE: "`ℓ = redshift cut, host
cut, SN sample, anchor choice, BAO compression, calibration bridge`"). Each column is a discrete
admissible choice; the matrix cell `(r,ℓ)` is populated only where the route+staging combination is
realized by an existing public determination or by a controlled re-analysis of a public likelihood.

| Column axis `ℓ` | Levels (discrete) | Applies to routes |
|---|---|---|
| `ℓ_zcut` redshift cut | `z_min ∈ {0.0, 0.01, 0.023, 0.06}` (Hubble-flow floor) | `r₂,r₃,r₄,r₅` (SN-bridged) |
| `ℓ_host` host-galaxy cut | `{all, high-mass, low-mass, low-extinction}` | `r₃,r₄,r₅` |
| `ℓ_SN` SN sample | `{Pantheon+, Union3, DES-SN5YR}` | `r₂,r₃,r₄,r₅` |
| `ℓ_anchor` anchor choice | `{NGC4258, MW-parallax, LMC-DEB, combined}` (Cepheid); `{tip-cal-A, tip-cal-B}` (TRGB) | `r₃,r₄` |
| `ℓ_BAOcomp` BAO compression | `{full DM/DH per-bin, compressed (α∥,α⊥), iso BAO}` | `r₁,r₂` |
| `ℓ_bridge` calibration bridge | `{r_d-from-BBN, r_d-from-CMB, M_B-external, M_B-internal}` | all |

**Matrix dimensions.** The *full* combinatorial grid is large; the *populated* matrix is sparse and
fixed in advance. Pre-register a target of **N_cells ∈ [25, 60]** populated `(r,ℓ)` cells spanning
all 7 rows and ≥4 distinct column axes, with ≥3 cells per row where the route admits staging
variation (`r₆,r₇` may have 1–2 cells each). Record the exact realized cell list in the run manifest
(`../GROUNDING_BRIEF.md` §III.B). Cells are **pre-registered**; no cell may be added or dropped
after seeing fits.

### 2.3 Cell contents — what each `(r,ℓ)` stores `[E]`

Each cell stores a **posterior over `H₀`** (not just a point estimate), because the holonomy and the
predictive-quotient test (Holonomy with Memory) require the full distribution:

```
cell(r,ℓ) = { H₀_mean, H₀_sigma, P(H₀ | r,ℓ) as samples or Gaussian (μ,σ²),
              covariance with shared nuisances (M_B, r_d) where available,
              provenance: {arXiv, access, recompute_flag}, z_eff, ℓ_levels }
```

Where a public determination provides only a Gaussian summary (most late-ladder points), store
`(μ,σ)` and flag `recompute_flag=false`. Where a public likelihood is re-evaluable (Planck, DESI
BAO via `desilike`, Pantheon+/Union3 distance-modulus + covariance), recompute the cell posterior
under the declared `ℓ` and flag `recompute_flag=true`. **Staging columns are only scientifically
meaningful for `recompute_flag=true` cells** (you cannot vary `z_min` on a published scalar); the
gates in §10 that test *staging structure* (T2) are evaluated **only over recomputed cells**.

A cell whose only public input is a published summary with **no recomputable likelihood** is
additionally tagged `summary_only=true`. Such cells are **excluded from any gate that requires
recomputation** (e.g. the staging-slope gate G-E4-T2 and the reproduction-`χ²` arm of G-E4-0a); they
still contribute to the route-matrix model comparison through their stored posterior.

### 2.4 Model/prior-dependent routes — time-delay (`r₆`) and multi-anchor `H₀` (`[E]`, REGISTRY §9)

The time-delay route (`r₆`, TDCOSMO+H0LiCOW, 2110.00517) and any other **model/prior-dependent**
`H₀` determination (e.g. mass-sheet-transform choice; anchor-dependent late-ladder points) are
**not** ingested as a single Gaussian scalar. They are ingested as **posterior families / model
variants**: each declared modeling choice (mass-sheet prior, lens-mass parametrization, anchor) is a
distinct cell `(r₆, ℓ)` carrying its own posterior, and the spread across the family is the
model-dependence — not collapsed into one `(μ,σ)`. The `73.3 ± 1.8` Gaussian is a *fallback summary
only* (flagged `summary_only=true`), not the primary representation when the family is available.

- **Model-dependence status (AOR).** The leftover from the modeling-choice spread is statused
  `moduli` (multiple choices fit comparably — degenerate) or `selected` (one choice is adopted with a
  declared selection rationale), per REGISTRY §9 / `plan/04` §8. It is **never** left `unstatused`.
- **With-and-without discipline (mandatory).** E4's model comparison and holonomy (§4, §6) are run
  **twice**: once **with** the time-delay route `r₆` included and once **with `r₆` removed**. Both
  runs are reported (`E4_model_comparison.json` carries a `with_timedelay` / `without_timedelay`
  pair), and `G-E4-DECISIVE` must be evaluated on the **without-time-delay** run so the core result does
  not rest on the most model-dependent route. The with-vs-without delta is recorded as the
  time-delay route's marginal influence and statused accordingly.

---

## 3. Inputs

### 3.1 Data inputs (locked in `plan/03`, `../GROUNDING_BRIEF.md` §I)

| Input | Release | Role in E4 | Format | Fallback |
|---|---|---|---|---|
| Planck 2018 TT/TE/EE+lowE | 1807.06209 | `r₁` posterior; `H_closed(0)` anchor prior | native Planck likelihood / Gaussian summary | Gaussian `67.4 ± 0.5` |
| DESI DR2 BAO | 2503.14738 | `r₁,r₂` BAO dilation; `ℓ_BAOcomp` levels | HDF5/text tables; `desilike` | published contours |
| Pantheon+ | 2202.04077 | SN bridge for `r₂,r₃,r₄,r₅`; `ℓ_SN`, `ℓ_zcut`, `ℓ_host` | distance modulus `μ(z)` + full covariance | Gaussian `μ(z)` |
| Union3 | 2401.06956 | alt `ℓ_SN` level | HDF5/fits | compressed 5-bin ladder |
| DES-SN5YR | Zenodo 13827844 | alt `ℓ_SN` level | Zenodo + FITS | fitted `μ(z)` + cov |
| SH0ES JWST+HST | 2509.01667 | `r₃` posterior + anchor/host staging metadata | posterior samples / Gaussian | `73.18 ± 0.88` |
| CCHP JWST TRGB/JAGB | 2408.06153 | `r₄,r₅` posteriors + anchor variants | posterior ensemble / Gaussian | quoted ±stat±sys±SN |
| TDCOSMO+H0LiCOW | 2110.00517 | `r₆` posterior **family** (mass-sheet / lens-model variants; §2.4) | posterior samples per modeling choice | `73.3 ± 1.8` (`summary_only`) |
| GW170817 | 1709.05895 | `r₇` posterior | joint posterior | `70.0 ⁺¹²₋₈` |

### 3.2 Formal / cross-experiment inputs (locked upstream)

- `Ξ_cosmo(z,ℓ,p)` low-rank ansatz with **≤ 5–7 free parameters** (`plan/04` §3; idea.md §5):
  `Ξ_cosmo = a₀φ₀(z) + a₁φ₁(z)ψ₁(ℓ)s_p + a₂φ₂(z)c_p`. **E4 introduces no new free parameters of its
  own**; it uses the *same* `Ξ_cosmo` (same `{a₀,a₁,a₂}` and basis) that E1 (DESI `w(z)`), E2
  (distance duality `η`), and E5 (growth/`S₈`) constrain. This is the residual-reuse requirement
  (test T4) and the decisive cross-experiment gate (§10.D).
- The **Hubble kernel** `K_{r,ℓ}[Ξ_cosmo]` (define in §4) is a *new readout* of the *existing*
  `Ξ_cosmo`, not a new residual.
- Metric `d` for posterior comparison (`plan/04` §4.0): **2-Wasserstein** `W₂` on `H₀` posteriors
  (1-D, closed form for Gaussians) plus **symmetrized KL** `D_sym` as a secondary metric.
- AOR status catalogue (`plan/04` §8; `../GROUNDING_BRIEF.md` §VI): every residual leg gets exactly
  one status.

### 3.3 Determinism / provenance inputs (`../GROUNDING_BRIEF.md` §III)

- Seeds: `numpy`, `python random`, sampler seed — all recorded in the run manifest.
- Run manifest JSON (`../GROUNDING_BRIEF.md` §III.B schema) listing every cell's data release +
  access + `recompute_flag`, software versions (`cobaya ≥3.4`, `CLASS ≥3.2`/`CAMB ≥1.5.7`,
  `getdist ≥1.5`, `arviz ≥0.15`, `numpy/scipy`), and the pre-registered cell list and loop list.
- float64 throughout; positive-definiteness + condition-number checks on every covariance
  (`../GROUNDING_BRIEF.md` §VI.1, cond < 10⁸).

---

## 4. Method

### 4.1 Step 1 — assemble the route matrix `[E]`

1. For each pre-registered cell `(r,ℓ)`, obtain `P(H₀|r,ℓ)`:
   - `recompute_flag=true` cells: re-evaluate the public likelihood under the declared staging
     `ℓ` (e.g. apply `z_min` cut to Pantheon+ before the `M_B`→`H₀` bridge; swap `ℓ_SN`; swap
     `ℓ_anchor` in the Cepheid/TRGB calibration; swap `ℓ_BAOcomp` in `desilike`). Run an MCMC/profile
     and store samples. Enforce `R̂ < 1.01`, ESS > 400 (`../GROUNDING_BRIEF.md` §VI.2).
   - `recompute_flag=false` cells: store the published Gaussian `(μ,σ)`.
2. Assemble the stacked data vector `D = {H₀^{(r,ℓ)}}` of length `N_cells`, with covariance `C_D`:
   - diagonal = per-cell variance;
   - **off-diagonal = shared-nuisance correlations** (cells sharing `M_B`, `r_d`, an anchor, or an SN
     sample are correlated). Build `C_D` from declared shared nuisances; where unknown, set
     correlation 0 and **flag it** (a conservative choice that the gates account for). Verify `C_D`
     positive-definite, cond < 10⁸.
3. Render the matrix as a heatmap (rows `r` × columns `ℓ`) of `H₀^{(r,ℓ)}` and of
   `(H₀^{(r,ℓ)} − H_closed(0))` — the raw "lawful-plurality fingerprint" plot.

### 4.2 Step 2 — define the three competing models `[E]`

All three predict the matrix `D`. They differ only in how the route/staging dependence is generated.

**M_null (no closure residual).** `idea.md` UPDATE "The null model is `K_{r,ℓ}[Ξ_cosmo]=0`":
```
H₀^{(r,ℓ)} = H₀,          one scalar, K[Ξ]=0.
```
Free params: 1 (`H₀`). All disagreement must be absorbed by the published per-cell error bars; any
excess is unmodeled. This is the "FLRW scalar `H₀` is closure-independent" hypothesis.

**M_noise (per-route nuisance noise).** `idea.md` UPDATE "The naive nuisance model is
`H₀^{(r,ℓ)} = H₀ + ε_{r,ℓ}`, where each route gets unrelated noise":
```
H₀^{(r,ℓ)} = H₀ + ε_{r,ℓ},     ε_{r,ℓ} ~ N(0, τ²) i.i.d. (or per-route τ_r²).
```
Free params: 1 (`H₀`) + 1 (`τ`) [variant: + per-route `τ_r`, ≤ 8]. This is the "the disagreement is
**structureless scatter / systematics**" hypothesis — the steel-man of the critic ("you are just
relabeling observational scatter"). **Crucially M_noise has NO route/staging structure**: `ε` is
exchangeable across cells.

**M_SBT (single low-rank closure residual).** `idea.md` UPDATE "The Six Birds model is
`H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo]`":
```
H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo],
```
where `Ξ_cosmo` is the **shared** low-rank residual (≤5–7 params, `plan/04` §3) and `K_{r,ℓ}` is the
Hubble readout kernel (§4.3). Free params: 1 (`H_closed(0)`) + the `Ξ_cosmo` params **that are
shared with / fixed by E1,E2,E5** (so the *marginal* cost of E4 is ≈ the route-coupling structure,
not new amplitudes). The structure is the point: `K_{r,ℓ}` is a *fixed functional* of the route's
(redshift depth, lens scale, calibration bridge), not free per-cell numbers.

### 4.3 Step 3 — the Hubble readout kernel `K_{r,ℓ}[Ξ_cosmo]` `[E]`

`K_{r,ℓ}` maps the closure residual into a route-specific `H₀` offset. It is constructed from the
*declared transport content* of the route, so that the offset is **structured by route, not free**.
Concretely, for a route that infers `H₀` from data over an effective redshift window `[z_lo, z_hi]`
at lens scale `ℓ_scale` through a calibration bridge `b`:

```
K_{r,ℓ}[Ξ_cosmo] = ∂H₀/∂(distance) · ∫_{z_lo}^{z_hi} W_r(z) · Ξ_cosmo(z, ℓ_scale, p_r) dz
                   + B_b[Ξ_cosmo]      (calibration-bridge term)
```

- `W_r(z)` — the route's redshift response (e.g. inverse-ladder routes weight high `z` via `r_d`;
  local ladder routes weight `z → 0`; time-delay weights the lens/source redshifts). Fixed from the
  route definition.
- `p_r` — the probe label entering the `s_p`, `c_p` factors of `Ξ_cosmo`.
- `B_b[Ξ_cosmo]` — the **calibration-bridge holonomy term**: the `a₂φ₂c_p` ("gluing/calibration")
  component of `Ξ_cosmo` read through the bridge `b`. This is the term that ties E4 to E2's
  distance-duality `η(z)` (same `a₂` amplitude → residual reuse).

**Implementation:** `K_{r,ℓ}` is a deterministic linear functional of `Ξ_cosmo` evaluated by
`pyccl`/`CLASS` distance computations along each route; verify it reduces to `0` identically when
`a₀=a₁=a₂=0` (so `M_SBT → M_null` in that limit — nested models, clean model comparison). `[T]`
finite-precision check: `|K_{r,ℓ}[0]| < 10⁻⁸` for all cells.

### 4.4 Step 4 — fit and compare `[E]`

Fit M_null, M_noise, M_SBT to `D` with covariance `C_D` (`cobaya`; Polychord for evidences). Compute:
- `χ²_min`, `χ²/dof` per model;
- **Bayesian evidence** `ln Z` per model (Polychord), and pairwise `ln B = ln Z_SBT − ln Z_X`;
- **information criteria** as a robustness cross-check: `BIC`, `AIC`, and `WAIC`/`LOO` via `arviz`;
- per-cell standardized residuals `(H₀^{(r,ℓ)} − model)/σ` for residual structure tests.

### 4.5 Step 5 — Hubble holonomy `𝔥_γ` `[E]`

Operationalize the named diagnostic (`idea.md` UPDATE "Hubble holonomy"):

```
𝔥_γ = d( B_{γ#} P(H₀ | r₁),  P(H₀ | r₁) ),
```

where `γ` is a **loop** of routes `r₁ → r₂ → … → r₁` and `B_{γ#}` is the composed declared
bridge-transport of the posterior around the loop. Procedure (Holonomy with Memory route transport):

1. Start with the posterior `P(H₀|r₁)` at one route's interface.
2. Transport it to the next route via the **declared calibration bridge** `B_{r₁→r₂}` (e.g. carry
   `r_d` / `M_B` / anchor information forward; this is a deterministic, declared map on the
   posterior, *not* a refit). Repeat around the loop.
3. Transport back to the start.
4. Measure the loop residue with the metric `d` (`W₂` primary, `D_sym` secondary).

`𝔥_γ = 0` ⇒ the Hubble currency is globally consistent on `γ` (route-compatible, `ScalarExact` or
flattenable). `𝔥_γ ≠ 0` ⇒ **route holonomy**: the scalar `H₀` does not exist globally on `γ`.

**Loop catalogue (pre-registered).** At minimum:
- `γ_AB` = CMB→BAO→SN→(M_B bridge)→Cepheid→(anchor bridge)→CMB (early↔late macro-loop);
- `γ_late` = Cepheid→SN→TRGB→SN→JAGB→SN→Cepheid (late-ladder calibrator loop);
- `γ_geom` = BAO→SN→time-delay→BAO (geometric loop, no stellar calibrators);
- one **null/flat control loop** (Holonomy with Memory `flat`/`flattenable` regime): a loop built
  entirely from cells that *share the same bridge and anchor*, where the declared transport is the
  identity-by-construction; this loop **must** return `𝔥_γ ≈ 0` (T-control).

> **Protocol-trap discipline (mandatory, `Protocol_Trap`).** For every loop with `𝔥_γ ≠ 0`, run the
> **honest-internalization control**: replace the externally-scheduled bridge composition by the
> autonomous lift that internalizes the bridge bookkeeping (carry the shared nuisances as explicit
> state, as `Protocol_Trap`'s `Z = X×Φ` lift does). If `𝔥_γ` collapses toward 0 under honest
> internalization, the holonomy was a **protocol-trap artifact** and is *demoted* (does not count as
> a positive). If `𝔥_γ` survives internalization, it is a genuine route holonomy. This is the exact
> false-positive guard `Protocol_Trap` was written to provide (their unbiased-clock lift drives
> `EPR_lifted < 10⁻¹⁷`).

### 4.6 Step 6 — the five lawful-plurality tests `[E]`

Run the five pass/fail tests from `idea.md` UPDATE ("For example: 1. Route structure … 5. Source
refinement"). Thresholds are pre-registered in §10.

- **T1 Route structure.** Cepheid/SN, TRGB/SN, JAGB/SN, inverse-ladder, time-delay offsets are *not*
  random: they organize by bridge route. Test: M_SBT (route-structured `K`) beats M_noise
  (exchangeable `ε`) by model comparison; and a permutation test that scrambles route labels
  destroys the M_SBT fit.
- **T2 Staging structure.** Changing `ℓ` (z-cut, host, anchor, SN sample, BAO compression) moves
  `H₀^{(r,ℓ)}` **predictably** — i.e. along the `Ξ_cosmo`-predicted direction `∂K_{r,ℓ}/∂ℓ`.
  Evaluated on `recompute_flag=true` cells only. Test: measured staging slopes correlate with
  predicted slopes; sign agreement.
- **T3 Closure transport / holonomy.** At least one pre-registered loop has `𝔥_γ` significantly ≠ 0
  **after** the protocol-trap internalization control, and the flat-control loop has `𝔥_γ ≈ 0`.
- **T4 Residual reuse.** The **same** `Ξ_cosmo` (same `{a₀,a₁,a₂}`) that fits the Hubble matrix also
  fits E1 (DESI `w(z)`), E2 (`η(z)` distance duality), E5 (growth/`S₈`) within their joint
  posterior. Test: joint fit `Ξ_cosmo` amplitudes overlap across experiments (no >Nσ tension, no
  >10× amplitude mismatch).
- **T5 Source refinement.** Adding *genuine* hidden-variable / heterogeneity proxies (the kind that
  feed `Ξ_cosmo`) **reduces** the matrix residual; adding *unrelated route-specific nuisance
  parameters* (more `ε_{r,ℓ}` freedom) does **not** improve out-of-sample predictive closure. This
  is the anti-overfitting discipline: success must come from structure, not from added freedom.

### 4.7 Step 7 — F4 status assignment and AOR ledger `[E]`/`[C]`

Assign the route field exactly one F4 status (`ScalarExact` / `RouteCompatibleNonScalar` /
`RoutesInconsistent` / `ScalarAmbiguous`) per §1.3, with the decision rule in §10.E. Record every
residual leg (per-route leftover, unmodeled off-diagonal correlations, internalized-away holonomies)
with exactly one AOR status (`plan/04` §8): `zero`, `budgeted`, `bridged`, `hidden`, `moduli`,
`selected`, `probabilistic`, `out_of_scope`, `nonclaim`, `blocked`, `approved_other`. `unstatused` is
**not** a status: any leg left `unstatused` at end of phase is a gate failure (F9 No Unstatused
Residual). Emit the mandatory **AOR Status Table**.

---

## 5. Outputs (artifacts the implementation must produce)

All under `results/E4/` with a run manifest (`../GROUNDING_BRIEF.md` §III.B).

| Artifact | File | Content |
|---|---|---|
| Route matrix table | `E4_route_matrix.csv` / `.hdf5` | per-cell `(r, ℓ, H₀_mean, H₀_sigma, z_eff, recompute_flag, provenance)` |
| Route matrix covariance | `E4_matrix_covariance.npy` | `C_D` with shared-nuisance off-diagonals; PD + cond report |
| Matrix heatmaps | `E4_matrix_heatmap.png`, `E4_residual_heatmap.png` | `H₀^{(r,ℓ)}` and `H₀^{(r,ℓ)} − H_closed(0)` |
| Model fits | `E4_model_fits.json` | `χ²`, `χ²/dof`, `ln Z`, `BIC`, `AIC`, `WAIC/LOO`, params per model |
| Model comparison | `E4_model_comparison.json` | `ln B_{SBT vs null}`, `ln B_{SBT vs noise}`, `ΔBIC`, `ΔWAIC` — reported as a `with_timedelay` / `without_timedelay` pair (§2.4) |
| Holonomy report | `E4_holonomy.json` | per-loop `𝔥_γ` (W₂ and `D_sym`), pre- and post-internalization, with the protocol-trap verdict per loop |
| Lawful-plurality tests | `E4_lawful_plurality.json` | T1–T5 numeric results + pass/fail flags |
| Residual-reuse cross-check | `E4_residual_reuse.json` | joint `Ξ_cosmo` amplitudes E1/E2/E4/E5 + tension metrics |
| F4 status + AOR ledger | `E4_status_table.md`/`.json` | F4 verdict + AOR Status Table (every residual leg statused) |
| Posterior triangle | `E4_triangle.png` | M_SBT posterior (`getdist`) |
| Run manifest | `E4_run_manifest.json` | seeds, datasets+versions+access, software versions, cell list, loop list, audit-gate results |

**Unblocks:** E4's fitted/holonomy-confirmed `Ξ_cosmo` route-coupling feeds the **synthesis /
model-competition** experiment (`plan/00` §model competition; "E8"), and its `B_b`/`a₂` calibration
term must be *consistent with* E2's `η(z)` fit. The shared `Ξ_cosmo` is the binding object across
E1/E2/E4/E5.

---

## 6. Pass/fail gates (quantitative; pre-registered)

> **All thresholds below are pre-registered and may not be changed after seeing fits**
> (`idea.md` §10 "Pre-register failure modes"; `../GROUNDING_BRIEF.md` §VI). The convention for
> Bayesian evidence is the Jeffreys/Kass–Raftery scale: `ln B > 5` = strong, `> 2.5` = moderate.

### 6.A Reproduction gate (must pass first — `idea.md` §10 standard 1)

- **G-E4-0a.** Each `recompute_flag=true` cell reproduces its published `H₀` to within `1σ_pub` and
  within **5%** on `χ²` of the published reference (`../GROUNDING_BRIEF.md` §VI.3). The non-recomputed
  cells reproduce the published `(μ,σ)` exactly.
- **G-E4-0b.** Every cell posterior is converged: `R̂ < 1.01`, ESS > 400 (`../GROUNDING_BRIEF.md` §VI.2).
  `C_D` positive-definite, cond < 10⁸, all finite (`../GROUNDING_BRIEF.md` §VI.1).
- **FAIL** ⇒ pipeline error; E4 does not proceed to model comparison.

### 6.B Decisive model-comparison gate (the core of E4)

`idea.md` UPDATE: the single `Ξ_cosmo` must beat **both** null **and** per-route-noise.

- **G-E4-1 (SBT beats null).** `ln B_{SBT vs null} ≥ 5` (strong) **and** `ΔBIC = BIC_null − BIC_SBT ≥ 10`
  **and** `χ²/dof_SBT < χ²/dof_null`. (M_null failing is expected if a tension exists at all; this
  gate confirms the matrix carries real structure.)
- **G-E4-2 (SBT beats per-route noise — the hard one).** `ln B_{SBT vs noise} ≥ 5` **and**
  `ΔBIC = BIC_noise − BIC_SBT ≥ 6` **and** `ΔWAIC` favors SBT. This is the gate that distinguishes
  *structured lawful plurality* from *structureless scatter*. **If M_noise fits as well as or better
  than M_SBT, E4 FAILS its core claim** — the disagreement is statistically indistinguishable from
  unrelated systematics.
- **G-E4-2-permutation.** Scrambling route labels (recompute `K_{r,ℓ}` with permuted `r`) must **destroy**
  the SBT advantage: permuted-`ln B_{SBT vs noise}` must drop below `2.5` in ≥ 95% of 1000
  permutations. (Guards against the kernel accidentally being flexible enough to fit any assignment.)

### 6.C Lawful-plurality gates (T1–T5, `idea.md` UPDATE five conditions)

- **G-E4-T1 Route structure.** G-E4-2 passes **and** the permutation control G-E4-2-permutation passes.
- **G-E4-T2 Staging structure.** Over `recompute_flag=true` cells, the correlation between measured
  staging slopes `ΔH₀/Δℓ` and `Ξ_cosmo`-predicted slopes `∂K_{r,ℓ}/∂ℓ` has Pearson `ρ ≥ 0.5` with
  `p < 0.05`, and sign agreement in ≥ 70% of staging pairs. (If routes do not respond to staging in
  the predicted direction, the staging structure claim fails.)
- **G-E4-T3 Holonomy.** At least one pre-registered loop has `𝔥_γ` (in `W₂`) exceeding **2× the loop's
  propagated posterior width** (i.e. `𝔥_γ / σ_γ ≥ 2`) **after** the protocol-trap internalization
  control, **and** the flat-control loop has `𝔥_γ / σ_γ < 0.5`. **A holonomy that vanishes under
  honest internalization is a protocol-trap artifact and does not satisfy G-E4-T3** (`Protocol_Trap`).
- **G-E4-T4 Residual reuse (binds to G-decisive, §6.D).** The `Ξ_cosmo` amplitudes `{a₀,a₁,a₂}` fit on
  the Hubble matrix agree with those fit in E1/E2/E5: pairwise tension `< 2σ` on each amplitude
  **and** no amplitude differs by `> 10×` across experiments (`idea.md` §3 "If each probe needs an
  unrelated `Ξ_p`, Six Birds fails"; `../GROUNDING_BRIEF.md` cross-experiment failure rule).
- **G-E4-T5 Source refinement.** Adding genuine heterogeneity proxies improves out-of-sample predictive
  closure (leave-one-route-out predictive `χ²` improves by ≥ 20% vs M_noise), while adding the same
  number of *unrelated* per-route nuisance params does **not** (≤ 5% improvement, and `WAIC` does not
  favor the nuisance-augmented model). Structure must beat freedom.

### 6.D Decisive cross-experiment gate (program-level)

> The single overriding gate (`idea.md` UPDATE final paragraph; §10 standards 2–3):

- **G-E4-DECISIVE (the POSITIVE Hubble-holonomy / lawful-plurality result).** The decisive positive
  result — *lawful plurality confirmed, the Hubble tension established as a route-holonomy
  measurement* — requires **all five lawful-plurality tests LP1–LP5** (`idea.md` UPDATE; mapped here
  to T1–T5) to pass, on top of the model-comparison and reuse gates. Formally, `G-E4-DECISIVE`
  succeeds **iff** all of:
  - (G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation) — SBT beats **both** null and per-route noise; **and**
  - **G-E4-T1 (LP1 route structure) ∧ G-E4-T2 (LP2 staging structure) ∧ G-E4-T3 (LP3 holonomy) ∧
    G-E4-T4 (LP4 residual reuse) ∧ G-E4-T5 (LP5 source refinement)** — all five lawful-plurality
    tests pass.

  Only this full conjunction may be reported as **the lawful-plurality claim** (F4 verdict
  `RouteCompatibleNonScalar`, §6.E). `G-E4-DECISIVE` is evaluated on the **without-time-delay** run
  (§2.4) so the core verdict does not rest on the most model-dependent route; the **with-time-delay**
  run is reported alongside as corroboration.

- **G-E4-ROUTEREUSE (the weaker "route-reuse" finding — `[E]`/partial, NOT lawful plurality).** A
  result that passes mainly on the **single-`Ξ_cosmo` low-rank route-reuse** model comparison —
  i.e. (G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation ∧ G-E4-T4) holds (the single low-rank `Ξ_cosmo` beats
  both null and per-route noise and is reused in E1/E2/E5 within tolerance) but **not all** of
  LP1–LP5 (T1–T5) hold — is reported as the weaker **route-reuse** finding, graded **`[E]`/partial**.
  It records that a single low-rank closure residual is favored by model comparison and is reused
  across experiments, and **must NOT be reported as the lawful-plurality claim** nor as
  `G-E4-DECISIVE`; the F4 verdict in this case is not yet `RouteCompatibleNonScalar` (the
  not-yet-satisfied LP tests are statused, §4.7). It is also evaluated on the **without-time-delay**
  run.

### 6.E F4 status decision rule

- `ScalarExact` ⇐ G-E4-1 fails to favor any structure over a single scalar (M_null adequate;
  `ln B_{SBT vs null} < 2.5`): **no Hubble tension at the field level; null wins.**
- `RouteCompatibleNonScalar` ⇐ `G-E4-DECISIVE` passes (all of G-E4-1, G-E4-2, G-E4-2-permutation and
  **all five** LP tests G-E4-T1…G-E4-T5): **lawful plurality confirmed — the SBT prediction.** Status
  of the leftover after `K_{r,ℓ}[Ξ_cosmo]`: `budgeted` or `bridged`.
- **Route-reuse (intermediate, NOT lawful plurality)** ⇐ `G-E4-ROUTEREUSE` passes but `G-E4-DECISIVE`
  does **not** (a single low-rank `Ξ_cosmo` is favored by model comparison and reused in E1/E2/E5, but
  not all of LP1–LP5 hold): reported as the weaker **`[E]`/partial route-reuse** finding; the F4 field
  verdict stays **un-promoted** (no `RouteCompatibleNonScalar` claim yet) and the not-yet-satisfied LP
  legs are statused (`budgeted`/`hidden`/`nonclaim` as appropriate, §4.7).
- `RoutesInconsistent` ⇐ G-E4-2 fails (M_noise ≈ M_SBT) **and** no low-rank `Ξ` reconciles the routes:
  **pure systematics / framework does not apply here.** Leftover status: `blocked` or `out_of_scope`,
  and E4 reports a *negative* Hubble-pillar result honestly.
- `ScalarAmbiguous` ⇐ multiple distinct `H_closed(0)` fit equally well (evidence-degenerate):
  leftover status `moduli`.

### 6.F Pre-registered failure modes (E4 FAILS if any of these)

Operationalizing `idea.md` §10 standard 5 + UPDATE's anti-relabeling discipline:

1. **Indistinguishable from scatter.** M_noise fits as well as or better than M_SBT (G-E4-2 fails):
   the disagreement is structureless. ⇒ `RoutesInconsistent`, negative result.
2. **No residual reuse.** The Hubble `Ξ_cosmo` is incompatible with E1/E2/E5 `Ξ_cosmo` (G-E4-T4 fails,
   >10× amplitude mismatch or >2σ tension): the matrix needs an unrelated probe-specific fudge. ⇒
   Six Birds fails the "one residual, many shadows" claim for the Hubble sector.
3. **Holonomy is a protocol-trap artifact.** Every nonzero `𝔥_γ` collapses under honest
   internalization (G-E4-T3 fails): the loop residue was scheduling/bookkeeping, not closure failure.
4. **No staging structure.** Staging slopes uncorrelated with predictions (G-E4-T2: `ρ < 0.5` or sign
   agreement < 70%): the field is not lawfully organized by staging.
5. **Permutation not destroyed.** G-E4-2-permutation fails (`K_{r,ℓ}` fits permuted route labels nearly
   as well): the kernel is an over-flexible fudge, not a structured readout.

---

## 7. Corpus and idea.md grounding (citations)

- **idea.md** — §2 ("Hubble tension"; Planck/SH0ES/CCHP values), §6 Experiment 4 (cross-probe PPD,
  Hubble leg, the explicit `73.18`, `68.81`, `67.80`, `67.4` numbers), and the **entire UPDATE block
  after §10** (Hubble readout field `ℋ_{r,ℓ}`; `H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo]`; null
  `K[Ξ]=0`; nuisance `H₀ + ε_{r,ℓ}`; Hubble holonomy `𝔥_γ = B_{γ#}P(H₀^{r₁}) ⊘ P(H₀^{r₁})`; route
  matrix rows `r₁…r₇` and columns `ℓ`; "lawful plurality"; the five pass/fail conditions; "The Hubble
  tension is the scalar shadow of Hubble holonomy").
- **Holonomy with Memory** (`Tsiokos_2026_Holonomy_with_Memory…`) — route-transport package, loop
  action on current vs predictive quotients, the flat/protocol-trap/flattenable/explicit-latent
  regime taxonomy, and the discipline that route dependence alone is *diagnostically informative but
  insufficient*. Grounds §4.5 (measure holonomy on the **posterior**, not the point estimate) and the
  flat/flattenable controls.
- **Protocol Trap** (`Tsiokos_2026_Six_Birds_Protocol_Trap…`) — holonomy ≠ arrow; route dependence
  can be a scheduling artifact that vanishes under an autonomous, honestly-internalized lift
  (`EPR_lifted < 10⁻¹⁷`). Grounds the **mandatory internalization control** in §4.5 and gate G-E4-T3 /
  failure mode 3 — the false-positive guard that defuses "relabeling scatter."
- **A Six Birds' Eye View of Dark Energy** (precursor) — the route-mismatch diagnostic
  `RM(x)=d(E·T x, T·E x)`, lens/completion/packaging `E=U∘f`, and the closure-rewrite framing that
  `H₀^{(r)}` is a packaged readout.
- **Foundations IV** — F4 local–global obstruction normal form (four exclusive statuses), grounding
  §1.3 / §4.7 / §6.E; F3/P3 protocol holonomy; F9 No Unstatused Residual (§4.7).
- **Adequacy Residuals** — the Schur-complement reading of `Ξ_cosmo` as what the joint multi-route
  family measures beyond a single FLRW scalar; the calibration-bridge term `B_b` as a blind-spot
  currency.
- **AOR** — the status vocabulary and the carrier-completion record level for §4.7 / §6.E.
- **Six Birds for Neutrino Mass** — the working cross-lens audit template (held-out mismatch `δχ`,
  localization, common-staging control) that E4's route/staging audit mirrors for the Hubble sector.

---

## 8. Compute / runtime budget (`../GROUNDING_BRIEF.md` §IV)

- Cell recomputation (per `recompute_flag=true` cell): single-likelihood profile/MCMC, ~minutes to a
  few hours on 16 CPU; total for ~20–40 recomputed cells ≈ the "extended scan" tier (12–48 h, 16–32
  GB).
- Model comparison (3 models, Polychord evidences over `N_cells`): the matrix likelihood is cheap
  (Gaussian in `N_cells ≤ 60`); evidences are fast — minutes to ~1 h per model.
- Holonomy transport: deterministic posterior transport, < 1 h total; internalization controls add a
  comparable pass.
- Residual-reuse cross-check (G-E4-T4): consumes the *already-fit* `Ξ_cosmo` posteriors from E1/E2/E5;
  marginal cost is a joint-overlap computation, minutes.
- Total E4 budget intuition: ~1–3 days wall on a 16–32 CPU node, dominated by cell recomputation.

---

## 9. Non-claims register

- E4 does **not** claim to resolve the Hubble tension by producing a single corrected `H₀`; it claims
  the tension is a **route-holonomy measurement** and tests whether it is *lawful* (G-E4-DECISIVE).
- E4 does **not** re-run any distance-ladder pipeline from raw photometry; it ingests published
  posteriors and re-evaluates only public likelihoods under declared staging.
- E4 does **not** assert that any particular determination (SH0ES / CCHP / Planck) is "right";
  every route is a packaged readout, and the framework is *agnostic* about which scalar (if any) is
  fundamental.
- A globally valid scalar `H₀` (`ScalarExact`) is **not ruled out a priori** — it is an admissible
  verdict (§6.E) if M_null wins, consistent with the precursor's "a cosmological constant is not
  ruled out" discipline.
- The five lawful-plurality tests are **gates, not assumptions**: a nonzero holonomy that fails the
  protocol-trap control is reported as an artifact, not a discovery.
