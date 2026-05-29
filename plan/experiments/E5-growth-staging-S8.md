# E5 — Growth / Staging Sweep for S₈ (the staging-fingerprint experiment)

> **One-line charter.** Run **scale-cut and staging sweeps** across the modern growth probes
> (DES Y6 3×2pt, KiDS-Legacy, HSC Y3, DESI DR2 full-shape RSD, ACT/SPT CMB lensing) using a **REAL
> physical 3×2pt / growth likelihood via CCL/`pyccl`** (NOT a surrogate template basis), and test the
> **staging fingerprint** `∂Ξ_cosmo/∂ℓ ≠ 0`: a *fundamental* Λ must be (statistically) flat under
> reasonable scale-cut / smoothing / redshift-binning changes beyond known systematics, whereas a
> *closure residual* has structured staging dependence. The make-or-break gate: the **same low-rank
> `Ξ_cosmo`** that improves geometry (E1/E2) must also predict the growth-sector residuals (`K_G`,
> `K_S`) with a cross-amplitude consistent within **10×** and consistent sign — or the Six Birds
> growth explanation is incomplete.

> **Read-order / consistency.** This file implements *one* experiment of the program defined in
> `plan/00-overview.md` (§3 shadow map row 6 — the growth/S₈ chart; §6 gates; §8 done) and
> `../GROUNDING_BRIEF.md` (datasets §I.D/§I.E, stack §II.A, determinism §III, AOR §VI). Every
> formal object used here is *locked* in `plan/04-formal-foundations.md`: the carrier and four
> residuals (§4), the low-rank ansatz **term 1 = the staging chart** `a₁·φ₁(z)·ψ₁(ℓ)·s_p` (§3.1),
> the growth/WL kernels **`K_G` (RSD `fσ₈`) and `K_S` (WL `S₈`)** (§3.3 eqs. 8–9), the staging-defect
> atlas type **`D_scale`** = `∂Ξ/∂ℓ ≠ 0` (§8.2), the coherence gate (§9.4), and the metric `d`
> (§4.0). Data products / loaders / fallbacks are locked in `plan/03-data-acquisition.md` (growth-probe
> table §"weak-lensing & LSS", RSD §"BAO/RSD"). Environment + the CCL backend + the pyccl↔CLASS
> agreement gate G-ENV-4 are locked in `plan/02-environment-and-deps.md` (§1.4, §6.G-ENV-4). **Science source
> of truth:** `idea.md` §5 ("the same `Ξ` must improve geometry, growth, and calibration"; ansatz term
> 1; kernels `K_G`,`K_S`), §6 **Experiment 5** (the `∂Ξ_cosmo/∂ℓ` test), §3 shadow map **row 6**
> ("`S₈` tension = growth-lens staging residual"), §10 (five hard standards, esp. **standard 4**
> staging fingerprints and **standard 2** one low-rank residual). **Precursor weakness this file
> exists to fix:** `A_Six_Birds_Eye_View_of_Dark_Energy` §"Public LSS vectors and surrogate audit
> backend" (Limitation box: *surrogate LSS backend*) + App. *DES Y3 scale-cut staging sweep* — the
> precursor's growth/S₈ claims were **protocol-level under a surrogate backend**; E5 replaces that with
> a physical CCL forward model so the staging fingerprint is a *physics* result, not a backend artifact.
>
> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean / finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a gate
> in §9 below).

---

## 1. Scientific framing and grounding

### 1.1 What this experiment is about

`idea.md` §3 (shadow map, **row 6**) and §6 **Experiment 5** state the thesis precisely:

> *"Growth and geometry are different lenses; weak-lensing scale cuts, redshift calibration, and
> baryonic/intrinsic-alignment modeling change the closure. … The key question is not 'is `S₈` low?'
> but `∂Ξ_cosmo/∂ℓ ≠ 0`? A fundamental Λ should not care about weak-lensing scale cuts except through
> known systematics. A closure residual should have a structured staging fingerprint."* — `idea.md`
> §3 row 6 + §6 Exp5.

The **headline of the program** (`idea.md` §3; `plan/00-overview` §3): `Λ`, `w_a`, `Q_IDE`, `η_CDDR`,
`μ/Σ`, and **`S₈` shifts** are *coordinate charts on the same closure defect* `Ξ_cosmo(z,ℓ,p)`. E5 is
the experiment that isolates the **growth/staging chart** (`S₈`, `fσ₈`) — formally the **term-1**
piece `a₁·φ₁(z)·ψ₁(ℓ)·s_p` of the ansatz (`plan/04` §3.1), the only term carrying explicit `ℓ`
(staging/scale) dependence — and asks two questions:

1. **Is the growth residual `ℓ`-structured?** I.e. does the fitted closure residual *vary with the
   weak-lensing scale cut* `ℓ_cut` (and the redshift-binning / smoothing / photo-z-calibration
   staging axes) in a way that is reproducible and *not* explained by the survey's own declared
   systematics? `∂Ξ_cosmo/∂ℓ ≠ 0` is the F8.2 `D_scale` (stage-law) defect signature.
2. **Does the *same* `Ξ` reused from geometry predict the growth sector?** I.e. does the `a₁`/`a₀`
   amplitude inherited from E1/E2 geometry, mapped through `K_G`/`K_S`, land within the modern
   probe-dependent `S₈` spread (DES Y6 low; KiDS/HSC closer to Planck) — the **coherence test** that
   is the program's make-or-break gate.

### 1.2 Why this is the experiment that addresses the precursor's central weakness (mandatory)

`idea.md` §2 ("What to keep and what to upgrade") names this explicitly:

> *"Second, replace the surrogate LSS backend with a real physical likelihood or a clearly staged
> two-paper plan. The `S₈` claim cannot be convincing using only a surrogate backend."* — `idea.md` §2.

The precursor (`A_Six_Birds_Eye_View_of_Dark_Energy`) was explicit about this limitation:

| Precursor statement (verbatim intent) | Source | What E5 must do differently |
|---|---|---|
| *"our LSS demonstrations are protocol-level under a surrogate backend pending physical 3×2pt likelihoods"* | abstract | Use a **physical CCL/`pyccl` 3×2pt + RSD + CMB-lensing forward model**; no template-basis surrogate `y^th = y^ref + Tφ`. |
| *"we do not present a full physical 3×2pt likelihood reproduction … we use probe-splitting and staging audits on the public vectors as a closure-consistency demonstration"* | §intro | Reproduce the **published `S₈`** of each survey first (G-E5-REPRO) before any `Ξ`. |
| *Limitation box "Surrogate LSS backend": "uses a surrogate theory backend rather than a physical 3×2pt forward model … does not constitute a physical reproduction"* | §results LSS | The CCL model **is** the physical forward model (transfer functions, nonlinear `P(k)` via Halofit/HMcode, IA, baryons, tomographic kernels). |
| *App.: "identical optima across models are plausibly an artifact of the surrogate degeneracy and should not be interpreted as a physical staging signature"* | App. scale-cut sweep | E5's staging fingerprint must be a **physical** dependence: the surrogate produced degenerate optima; a real backend cannot. The G-E5-STAGE-NULL control distinguishes the two. |
| *"the staging machinery is in place (block map → scale-cut mask → refit → held-out metrics), while deferring physical interpretation of staging dependence to a future backend-enabled analysis"* | App. | E5 **is** that backend-enabled analysis; the block map + scale-cut mask machinery is reused, the surrogate template is **replaced**. |

> **The honesty rule (LOCKED).** Any leg of E5 that *cannot* be run with a physical CCL likelihood
> (e.g. a survey whose official likelihood is unavailable and whose covariance is not separable) is
> run under an **explicit staged fallback** (§3.3) and its result is **statused** (`budgeted` /
> `out_of_scope`, never `unstatused`; F9, `plan/04` §8.3) and **excluded from the headline staging
> fingerprint**. A surrogate template basis (`y^ref + Tφ`) is **forbidden** as a headline result and
> may appear only as a clearly labeled protocol-continuity cross-check vs the precursor (§3.4, G-E5-NOSURR).

### 1.3 Foundations grounding (the staging chart and the `D_scale` defect)

- **F4 / P4 Staging (`plan/04` §3.1 term 1; §8.1 `Σ_stage`; §8.2 `D_scale`).** The ansatz's only
  `ℓ`-dependent term is `a₁·φ₁(z)·ψ₁(ℓ)·s_p`, with `ψ₁(ℓ)=(ℓ/ℓ₀)^{-β}` a smoothing/scale kernel and
  `φ₁(z)=z/(1+z)` (activates late — the "coincidence" row 7 reading). A nonzero, *reproducible*
  `∂Ξ_cosmo/∂ℓ` is exactly the `Σ_residual` atom of primary type **`D_scale`** ("stage-law failure":
  staging fingerprint `∂Ξ/∂ℓ ≠ 0`, `plan/04` §8.2). The whole experiment funnels to typing the growth
  residual as either `D_scale` (a genuine staging fingerprint → `Ξ` is real and packaging-induced) or
  to a `budgeted` systematic (the staging dependence is a known IA/baryon/photo-z effect, *not* a
  closure signature).
- **The cross-lens audit template (`Six_Birds_for_Neutrino_Mass`).** E5 reuses the directional
  held-out mismatch `δχ_{B|A}` and the **common-staging control** of the neutrino-mass paper, applied
  to *growth surveys as lenses*: DES Y6, KiDS-Legacy, HSC Y3 are three lenses on (overlapping) sky; the
  question is not "which `S₈` is right" but whether the packaged growth inference is **stable** under
  the lens swap and the scale-cut staging change. The `δχ` localization-by-`ℓ-bin` map is the growth
  analog of the neutrino paper's TT-high-`ℓ` heatmap.
- **`K_G`, `K_S` kernels (`plan/04` §3.3 eqs. 8–9).** `K_G` maps `Ξ` to a shift of RSD `fσ₈(z)` (a
  `∂_z`-linearized growth response to the rewrite `R[Ξ]`); `K_S` is the scale-integrated `K_G` over
  the WL kernel with `ψ₁(ℓ)` weighting, mapping `Ξ` to a shift of `S₈`. Both are **linear functionals
  of the same `Ξ`** with fixed probe-shared shapes (anti-fudge, `plan/04` §3.1 hard rule).
- **Coherence gate (`plan/04` §9.4 / §5 LP4; `plan/00-overview` §6.4).** The `Ξ`-amplitude implied by
  `K_S` must lie within **10×** of the amplitude implied by E1's `K_L`/`K_M`, with consistent sign.
  This is the program-level make-or-break gate that E5 stress-tests hardest (geometry vs growth is the
  cleanest "one residual, two charts" check).
- **F9 No Unstatused Residual / AOR (`plan/04` §8).** Every surviving growth tension (residual `S₈`
  offset, IA/baryon degeneracy, photo-z calibration shift, surrogate fallback) carries **exactly one**
  AOR base status.

### 1.4 The live `S₈` picture this experiment must engage (mandatory, adversarial)

`idea.md` §5 (and the §3 row-6 reading) frame the *softened, probe-dependent* `S₈` situation. E5 must
**not** assume "the universe is too smooth"; it must treat the spread across surveys as the signal:

| Survey | Release | `S₈` (published) | Offset from Planck | What it implies for the staging test |
|---|---|---|---|---|
| **DES Y6** 3×2pt | arXiv:2601.14559 | `S₈ = 0.789 ± 0.012` | ~**1.8σ** below Planck+ACT+SPT | the residual leg: lowest `S₈`; the staging sweep asks whether the offset *moves* with `ℓ_cut`. |
| **KiDS-Legacy** shear | arXiv:2503.19441 | `S₈ = 0.815^{+0.016}_{−0.021}` | ~**0.73σ** from Planck | the recalibrated leg: near-consistent after redshift-calibration + sims update (a staging change). |
| **HSC Y3** (+DESI recal) | arXiv:2511.18134 | `S₈ = 0.805 ± 0.018` | mild | the photo-z-recal staging axis: `original→DESI-recal` shifted `S₈` from ~0.769 up to 0.805. |
| **DESI DR2 full-shape RSD** | arXiv:2411.12026 | `fσ₈(z)` 6–8 bins; `μ₀=0.04±0.22, Σ₀=0.044±0.047` | GR-consistent | the RSD growth-rate leg (independent of WL IA/baryon systematics); feeds `K_G`. |
| **ACT/SPT CMB lensing** | arXiv:2509.02945 | `C_ℓ^{κκ}` ℓ~100–3000 | high-`z` growth | the high-redshift growth cross-check; least affected by low-`z` baryon/IA staging. |

> **The packaging reading (`idea.md` §3 row 6, §5).** The *spread itself* — DES Y6 low, KiDS/HSC
> closer to Planck after a redshift-calibration / methodology (i.e. **staging**) change — is the P4
> signal. The KiDS-Legacy and HSC-Y3 recalibrations are *literal staging changes that moved `S₈`*.
> SBT's contribution is to **type** this: is the survey-to-survey spread an `ℓ`/staging-structured
> residual (`D_scale`, the `Ξ` reading) or a `budgeted` collection of independent systematics
> (the null reading)? E5 is designed to decide this with a physical backend, **not** to force `S₈` low.

---

## 2. The models (LOCKED)

E5 fits a small model ladder to the *same* growth data with a **physical CCL forward model**, sharing
background + growth parameters with E1's verified geometry fit:

| Model | Growth physics | Closure term | Extra free params beyond ΛCDM | Reads as | F-law |
|---|---|---|---|---|---|
| **`G₀`** (null) | ΛCDM growth (GR; `μ=Σ=1`), full CCL nonlinear `P(k)` | none | 0 (only IA/baryon/photo-z nuisances) | a fundamental Λ — *staging-flat by hypothesis* | baseline |
| **`G₁`** (geometry-only `Ξ`) | ΛCDM growth | term-0 `a₀` only (Λ-chart), **fixed to E1's fitted value** | 0 new (inherited) | "geometry `Ξ` does nothing for growth" null-for-coherence | reused E1 `Ξ` |
| **`G₂`** (staging `Ξ`, the SBT model) | ΛCDM growth + growth/WL shift via `K_G`,`K_S` | term-1 `a₁` (+ `ψ₁` exponent `β` optional) staging chart, **with `a₀` from E1** | `+1…2` (`a₁`[,`β`]) | the SBT growth reading: one residual, staging chart | term-1 staging (`plan/04` §3.1) |
| **`G_MG`** (MG comparator, → E7) | `(μ₀,Σ₀)` modified-growth, CCL `μΣ` parameterization | none | `+2` (`μ₀,Σ₀`) | the modified-gravity repair chart (E7 owns this; run here only as a growth comparator) | F2 alt repair |

> **`G₂` construction detail (LOCKED).** `G₂` does **not** add a free per-probe growth fudge. It keeps
> the background `Ξ` term-0 amplitude `a₀` **pinned to E1's fitted value** (read from the coherence
> ledger `results/xi_cosmo_coherence.csv`, `plan/04` §9.4) and lets **only** the staging-chart
> amplitude `a₁` (and optionally the scale exponent `β` of `ψ₁(ℓ)=(ℓ/ℓ₀)^{-β}`) be fit to growth.
> The induced observable shifts use the *same* probe-shared kernels everywhere:
> ```
> (fσ₈)^obs(z)  = (fσ₈)^GR(z; θ)  + K_G[Ξ](z)        (plan/04 eq. 8; RSD)
> S₈^obs        = S₈^GR(θ)        + K_S[Ξ]           (plan/04 eq. 9; WL, ψ₁(ℓ)-weighted)
> ```
> Because `K_G`/`K_S` are driven by the **same** `Ξ` whose `a₀` came from geometry, `G₂` is the
> operational realization of `idea.md` §5's key rule: *the same `Ξ` must improve geometry AND growth*.
> The **only** freedom unique to E5 is `a₁` (staging amplitude) and `β` (scale shape) — the thing that
> the staging fingerprint `∂Ξ/∂ℓ` measures. There is **no** per-probe free `Ξ_p` (G-E5-RANK).

> **Auxiliary baselines (declared, for comparison only):**
> - **`G_sys`** (systematics-saturated null): `G₀` with *expanded* IA + baryon-feedback + photo-z
>   nuisance freedom (the survey's own maximal systematics model). This is the "the staging dependence
>   is a known systematic" hypothesis. If `G_sys` absorbs the staging fingerprint as well as `G₂`,
>   the fingerprint is `budgeted`, not `D_scale` (decision gate §9.4).
> - **`G_surr`** (precursor surrogate replica, **non-headline**): the precursor's `y^th = y^ref + Tφ`
>   template basis, run *only* on DES Y3 vectors to reproduce the precursor's protocol-level sweep and
>   to demonstrate (G-E5-NOSURR) that the physical CCL result differs from the surrogate degeneracy.

---

## 3. Inputs

### 3.1 Datasets (versions, access, real-vs-surrogate decision — from `GROUNDING_BRIEF` §I.D/§I.E, `plan/03`)

| Probe | Dataset | Release | Vector | Physical CCL likelihood? | Loader (`plan/03`) | Role | Fallback (statused) |
|---|---|---|---|---|---|---|---|
| **WL/3×2pt (PRIME)** | **DES Y6** | arXiv:2601.14559 | shear+clustering+GGL, n_z=4, ℓ_max~5000 (or ξ±(θ)); full analytic+sim cov; **scale cuts per bin pair**; `S₈=0.789±0.012` | **YES** — official `DESLikelihood`/cosmosis-style + CCL forward model | `load_des_y6(scale_cut=…)` | the prime growth probe; the `ℓ_cut` sweep target | Gaussian approx on published vector+cov w/ official cuts baked in → **`budgeted`**, *excluded from headline staging fingerprint* |
| **WL shear** | **KiDS-Legacy** | arXiv:2503.19441 | cosmic shear only, n_z=5, ℓ~30–1500 (bandpowers/COSEBIs); sim+analytic cov; `S₈=0.815^{+0.016}_{−0.021}` | **YES** — CCL shear forward model on published bandpowers | `load_kids_legacy(statistic=…)` | the recalibrated cross-check leg | shear-only `P(κ)` Gaussian, no RSD coupling → **`budgeted`** |
| **WL shear+clustering** | **HSC Y3** | arXiv:2511.18134 | shear+clustering, n_z=5–6, ℓ~200–10000; mock cov; **two photo-z calibrations** (original / DESI-recal); `S₈=0.805±0.018` | **YES** — CCL forward model; both photo-z calibrations exposed | `load_hsc_y3(photoz=…)` | the **photo-z-recal staging axis** (a literal staging swap) | original (pre-DESI-recal) prior as comparison leg → **`budgeted`**; recal-vs-original swap **is** a staging diagnostic |
| **RSD (growth rate)** | **DESI DR2 full-shape** | arXiv:2411.12026 | `fσ₈(z)` 6–8 bins z∈[0.1,1.5]; mock cov; `(μ₀,Σ₀)` MG inputs | **YES** — `desilike` full-shape, or compressed `(fσ₈, D_M/r_d, D_H/r_d)` per bin via CCL | `load_desi_rsd_fs(compressed=…)` | the WL-systematics-independent growth leg; feeds `K_G` | compressed `fσ₈(z)`+geometry Gaussian (loses full-shape `P(k)`) → **`budgeted`** |
| **CMB lensing** | **ACT/SPT** | arXiv:2509.02945 | `C_ℓ^{κκ}` ℓ~100–3000; analytic cov | **YES** — CCL `C_ℓ^{κκ}` forward model | `load_cmb_lensing(source=…)` | high-`z` growth cross-check; least low-`z` IA/baryon staging | Planck-only lensing (lower S/N) → **`budgeted`** |
| **WL/3×2pt (FALLBACK)** | DES Y3 3×2pt | arXiv:2212.00091 | shear+clustering+GGL, n_z=4, ℓ_max~4000; public `DESLikelihood` | **YES** — fully public official likelihood | `load_des_y3_3x2pt()` | substitute prime probe if Y6 likelihood unavailable; also the `G_surr` surrogate-replica host | published compressed 3×2pt likelihood → **`budgeted`**; **`approved_other`** if substituting for Y6 |
| **CMB anchor** | Planck 2018 | arXiv:1807.06209 | TT/TE/EE + lensing native | YES (`clik`) | `load_planck_2018(...)` | the `S₈`-from-CMB anchor the offset is measured against | compressed distance priors → `budgeted` |

> **The real-vs-surrogate decision (LOCKED — the heart of why E5 exists).** For every growth leg, the
> backend selection follows a strict precedence, recorded per-run in the manifest:
> 1. **Official survey likelihood** (e.g. DES Y6 `DESLikelihood`) wrapped to drive CCL — *preferred*;
>    result is a **headline physics** result (status `zero`/`bridged` on the backend axis).
> 2. **CCL physical forward model on the published data vector + covariance** (Gaussian likelihood
>    with the survey's official scale cuts, IA model, baryon model, photo-z `n(z)`) — *acceptable
>    headline* (the forward model is physical even if we supply the Gaussian likelihood wrapper);
>    status `budgeted` only on the *likelihood-approximation* axis, not on the physics axis.
> 3. **Surrogate template basis** (`y^ref + Tφ`) — **forbidden as headline**; permitted only as the
>    `G_surr` precursor-continuity cross-check (§3.4). Any leg that can *only* run as a surrogate is
>    **`out_of_scope`** for the headline staging fingerprint and is reported separately.
>
> Decision rule per leg: *use the highest-precedence backend that builds and passes the pyccl↔CLASS
> agreement gate G-ENV-4 (`plan/02` §6.G-ENV-4: `P(k)` agree <1%, `σ8` <0.5%)*. Record the chosen tier in
> `meta.json`. The headline staging fingerprint (§5, §9) is computed **only** from tier-1/tier-2 legs.

### 3.2 The staging axes (LOCKED — what "`ℓ`" means in E5)

`Ξ_cosmo(z,ℓ,p)` has `ℓ` = "scale or staging" (`idea.md` §1, `plan/04` §3.1). E5 sweeps **five concrete
staging axes**, each a declared P4 refinement axis (`plan/04` §8.1 `Σ_stage`):

| Staging axis `ℓ` | Concrete control | Probes it applies to | Default sweep grid |
|---|---|---|---|
| **`ℓ_cut` (scale cut)** | min-scale / max-`ℓ` cut on the 2pt vector (or `θ_min` for ξ±) | DES Y6, KiDS, HSC, CMB-lensing | `ℓ_max ∈ {1000, 1500, 2000, 3000, 5000}` (survey-appropriate); `θ_min ∈ {2.5′…}` for ξ± |
| **`z-bin` (tomographic)** | drop / split tomographic source bins; high-`z`-only vs all | DES Y6, KiDS, HSC | all bins; drop-lowest-`z`; drop-highest-`z`; 2-bin coarse vs full |
| **`smoothing`** | nonlinear-`P(k)` prescription / smoothing scale (Halofit vs HMcode; `k_max`) | all WL + RSD | `{Halofit, HMcode2020}` × `k_max ∈ {0.5, 1.0, 3.0} h/Mpc` |
| **`photo-z calibration`** | HSC original vs DESI-recal `n(z)`; KiDS calibration variants | HSC Y3 (primary), KiDS | `{original, DESI-recal}` (HSC); KiDS calibration set |
| **`probe-block split`** | shear-only vs shear+clustering+GGL; RSD-only vs WL-only | DES Y6, HSC, DESI RSD | shear-only / clustering+GGL / full 3×2pt; growth-only vs geometry-anchored |

> **Common-staging control (from `Six_Birds_for_Neutrino_Mass` §"common-staging").** When comparing two
> survey lenses (DES Y6 vs KiDS vs HSC) the surveys differ in native `ℓ`-support. A **common-staging**
> run restricts all compared lenses to a shared `ℓ`-range (the intersection of supports) and repeats
> the audit. If the `S₈` spread / staging fingerprint **persists under common-staging**, it points
> *away* from a pure support/cut explanation (the neutrino-paper conclusion logic). This is required
> before any staging dependence is read as a `D_scale` closure fingerprint.

### 3.3 The staged fallback ladder (LOCKED — explicit, statused, never silent)

For each leg, if the preferred backend is unavailable the run *descends one tier* and the descent is
recorded as a statused residual. The ladder and statuses:

| Tier | Backend | Headline-eligible? | AOR status of the descent |
|---|---|---|---|
| **T1** | Official survey likelihood + CCL | YES (physics) | `zero` on the backend axis |
| **T2** | CCL physical forward model + Gaussian likelihood on published vector/cov (official cuts/IA/baryon/`n(z)`) | YES (physics) | `budgeted` (likelihood-approximation axis only) |
| **T3** | CCL forward model + Gaussian, but with a *reduced* systematics model (e.g. IA fixed, baryons fixed) | cross-check only | `budgeted` + flagged `D_source` (un-modeled systematic freedom) |
| **T4** | DES Y3 (fallback) substituting for DES Y6 | YES with caveat | `approved_other` (external substitute) |
| **T5** | Surrogate template `y^ref + Tφ` | **NO** (precursor-continuity only) | `out_of_scope` for headline; `budgeted` as protocol cross-check |

> A leg that cannot reach **T2** for the prime probe (DES Y6) blocks the *headline* fingerprint but not
> the experiment: E5 then runs the fingerprint on whichever T1/T2 legs survive (KiDS/HSC/RSD/CMB-lens)
> and records DES-Y6 as `blocked` with the block reason (F9 `blocked`, `plan/04` §8.3). The experiment
> is **not** allowed to silently substitute a surrogate and call it a growth result.

### 3.4 The precursor-surrogate cross-check (`G_surr`, non-headline, LOCKED)

To make the surrogate-weakness fix *auditable*, E5 explicitly **reproduces** the precursor's surrogate
sweep on DES Y3 (the precursor's host) and **contrasts** it with the physical CCL result:

1. Run `G_surr` (`y^th = y^ref + Tφ`, `p∈{1,2}`) probe-split PPD + scale-cut sweep on DES Y3 vectors,
   reproducing the precursor App. result (identical optima across models, `x_min ≈ 25.41` in the
   precursor config) — confirming the surrogate **degeneracy** the precursor warned about.
2. Run the **physical CCL** `G₀`/`G₂` on the *same* DES Y3 vectors with the *same* scale-cut sweep.
3. **Demonstrate** (G-E5-NOSURR) that the physical backend does **not** produce the surrogate's
   degenerate identical optima — the physical staging curve has structure the surrogate cannot, which
   is exactly why the precursor deferred physical interpretation. This is the auditable receipt that
   E5's staging fingerprint is a physics result, not a backend artifact.

### 3.5 Parameters and priors

| Parameter | Model(s) | Prior | Notes |
|---|---|---|---|
| `Ω_m, Ω_b, H₀, n_s, ln(10¹⁰A_s)` (→ `σ8`) | all | standard broad priors (match E1) | background+primordial; shared with geometry fit |
| `a₀` (Λ-chart) | `G₁,G₂` | **fixed to E1's fitted value** (coherence ledger) | NOT re-fit in E5 — it is inherited (this is the coherence test) |
| `a₁` (staging chart) | `G₂` | `U`, `complexity`-penalized | **the E5 control parameter** (the growth/WL amplitude) |
| `β` (`ψ₁(ℓ)` exponent) | `G₂` optional | `U(0, 2)` | the scale-shape; if fitted, it is the explicit `∂Ξ/∂ℓ` slope |
| IA amplitude `A_IA` (+ z-slope `η_IA`) | all WL legs | survey-default prior (NLA/TATT) | intrinsic-alignment nuisance — a *known systematic*, must be marginalized |
| baryon feedback (`HMcode A_baryon`/`Ω_b`-feedback or `T_AGN`) | all WL legs | survey-default prior | baryonic systematic — must be marginalized; part of "known systematics" |
| photo-z shifts `Δz_i` per bin | all WL legs | survey-default `N` priors | redshift-calibration systematic; the HSC recal axis sweeps this structurally |
| shear calibration `m_i` | all WL legs | survey-default `N` priors | multiplicative-bias systematic |
| `μ₀, Σ₀` | `G_MG` only | `U` broad | MG comparator (E7 owns) |

> **Ansatz rank ceiling (anti-fudge, `plan/04` §3.1 / §9.2).** `G₂` adds **≤ 2** *closure* free params
> beyond ΛCDM (`a₁`[,`β`]) — and `a₀` is **inherited, not free**. The growth/WL shapes
> `φ₁(z), ψ₁(ℓ), s_p` are **fixed and probe-shared**: *no per-probe free `Ξ_p`*. IA / baryon / photo-z
> / shear-calibration nuisances are **survey-standard systematics** (the "known systematics" Λ is
> allowed to depend on), not closure parameters, and are marginalized in *every* model including the
> null `G₀` — so they cannot be charged to the closure residual.

---

## 4. The staging-fingerprint object (the decision spine) (LOCKED)

The central measured object is the **staging derivative** `∂Ξ_cosmo/∂ℓ`, operationalized as the
dependence of the fitted closure amplitude (and the held-out mismatch) on the staging axis. Following
the `D_scale` defect type (`plan/04` §8.2) and `idea.md` §6 Exp5:

### 4.1 The fingerprint statistic

For each staging axis `ℓ` (§3.2) with sweep values `{ℓ_1, …, ℓ_K}`:

```
Fit G₂ at each ℓ_k  →  fitted staging amplitude  a₁(ℓ_k)   and   residual S₈-offset  ΔS₈(ℓ_k)         (E5.1)
Staging slope:        s_Ξ := d a₁ / d ℓ   (or d ΔS₈ / d ℓ_cut), estimated by weighted linear regression
Staging fingerprint:  the null hypothesis  s_Ξ = 0  (a fundamental Λ)  vs  s_Ξ ≠ 0  (a closure residual)
```

The **physical-vs-systematic discrimination** (the crux, from `idea.md` §6 Exp5 "except through known
systematics") is enforced by comparing the *same* slope under `G₂` vs the systematics-saturated null
`G_sys`:

```
Residual staging slope:  s_Ξ^resid := s_Ξ(G₂)  −  s_Ξ(G_sys)                                          (E5.2)
```

`s_Ξ^resid ≈ 0` ⇒ the staging dependence is fully a *known systematic* (IA/baryon/photo-z) → the
fingerprint is `budgeted`, **not** a closure signature. `s_Ξ^resid ≠ 0` at significance ⇒ a genuine
staging fingerprint not absorbed by the survey's own systematics → `D_scale` (the `Ξ` reading).

### 4.2 The directional cross-lens held-out mismatch (growth analog of the neutrino template)

Treating DES Y6 / KiDS / HSC as lenses `A, B`, compute the directional held-out mismatch
(`Six_Birds_for_Neutrino_Mass` eq. `δχ_def`), under each model and under common-staging:

```
δχ_{B|A} = χ²_B(θ̂_A) − χ²_B(θ̂_B)   ≥ 0     (how poorly the A-packaged growth object predicts B)      (E5.3)
```

localized by `ℓ-bin` and tomographic-bin (the heatmap "where to look"). The audit asks: does `G₂`'s
single `Ξ` **reduce** the cross-lens `δχ` (the closure repair works across survey lenses), and does the
residual mismatch *persist under common-staging* (pointing away from a pure support/cut artifact)?

### 4.3 The `D_scale` / `budgeted` status assignment (the verdict)

| Verdict | Operational condition | AOR status (`plan/04` §8.2–8.3) | Reads as |
|---|---|---|---|
| **`D_scale` (staging fingerprint = closure)** | `s_Ξ^resid ≠ 0` at **>2σ**, reproducible across ≥2 probes and surviving common-staging; **and** the same `Ξ` lowers cross-lens `δχ` | `bridged` (repaired by `Ξ`), typed `D_scale` | growth `S₈` is a closure/staging chart of the *same* `Ξ` (the row-6 thesis) |
| **`budgeted` (staging = known systematic)** | `s_Ξ^resid ≈ 0` (`<2σ`): `G_sys` absorbs the staging dependence as well as `G₂` | `budgeted`, typed `D_source` | the spread is IA/baryon/photo-z systematics; SBT does **not** claim a growth `Ξ` (a valid, honest outcome) |
| **`out_of_scope` (cannot decide physically)** | only surrogate/T5 backend available for the deciding leg | `out_of_scope` for headline | physics-grade decision deferred (precursor state, explicitly flagged) |

---

## 5. Method (pipeline)

> **Determinism / provenance (mandatory, `GROUNDING_BRIEF` §III; `plan/02` §determinism).** Every run
> pins `numpy`/`random`/sampler seeds and `OMP_NUM_THREADS=1` for the determinism gate, writes a
> run-manifest JSON (`run_id`, date, seeds, datasets+versions, software versions incl.
> **pyccl-internal vs standalone CLASS version**, backend tier per leg, parameters, output files,
> `audit_status`), and emits `[chain, posterior.hdf5, triangle.png]`. `float64` throughout.

### Step 0 — Environment + backend gate (must pass first)
- Confirm `plan/02` T0/T1 build gates: `import pyccl` succeeds; **G-ENV-4 pyccl↔CLASS agreement** passes
  (`P(k)` <1%, `σ8` <0.5%). *Fail → E5 is blocked* (`plan/02` §6.G-ENV-4: "fail → block growth experiments
  E5/E7"). This is the precondition that the precursor never met (its pyccl import failed in the
  baseline env, forcing the surrogate).
- Verify CCL computes `σ8`, one `fσ₈(z)`, one shear `C_ℓ`, one `C_ℓ^{κκ}` vs stored references <0.5%.

### Step 1 — Reproduce published `S₈`/`fσ₈` baselines (gate `G-E5-REPRO`, §9.1)
- For each tier-1/tier-2 probe, fit `G₀` (ΛCDM, GR growth) with the **physical CCL forward model** and
  the survey's official scale cuts + IA + baryon + photo-z model, and **recover the published `S₈`**
  (or `fσ₈(z)` for DESI RSD; `C_ℓ^{κκ}` amplitude for CMB lensing) within the survey's quoted
  uncertainty: DES Y6 `S₈≈0.789±0.012`, KiDS `0.815`, HSC `0.805`, GR `μ₀≈0.04, Σ₀≈0.044`.
  **No `Ξ` is introduced until this passes** (`idea.md` §10 standard 1; this is the literal fix of the
  precursor's surrogate limitation — we now reproduce real survey constraints).
- Convergence: `R̂ < 1.01` all params; ESS > 400/chain.

### Step 2 — The scale-cut / staging sweeps
- For each staging axis (§3.2) and each probe, re-run the inference at every sweep value, holding the
  survey systematics model fixed at its default. Record `a₁(ℓ_k)`, `ΔS₈(ℓ_k)`, `fσ₈`-residuals,
  per-`ℓ-bin` `χ²` contributions, and full posteriors.
- Run the **common-staging control** across the WL survey lenses (§3.2): restrict to the shared
  `ℓ`-support and repeat.

### Step 3 — Fit the model ladder with the same `Ξ`
- Fit `G₀, G₁, G₂` (and `G_sys`, `G_MG`) to each probe and to the **joint growth vector** (3×2pt + RSD
  + CMB-lensing), with `a₀` **pinned from E1's coherence ledger** and **only** `a₁`[,`β`] free in `G₂`.
- The `K_G`/`K_S` kernels (`plan/04` §3.3) are implemented as linear functionals of `Ξ`; verify
  kernel linearity to <1% (finite-difference, `plan/04` §9.2) and positivity/stability of `R[Ξ]`
  (`plan/04` §7, stable-readout — shared with E3).
- Record per model: `χ²`, `χ²/dof`, `k`, `BIC = χ² + k ln N`, `AIC`, posteriors, fitted `a₁`, `S₈`,
  `σ8`, derived `fσ₈(z)`.

### Step 4 — The staging-fingerprint test (the central question)
- Estimate the staging slope `s_Ξ` (E5.1) per axis by weighted regression with full posterior
  covariance; estimate the residual slope `s_Ξ^resid` (E5.2) by differencing against `G_sys`.
- Test `s_Ξ = 0` and `s_Ξ^resid = 0` (the `∂Ξ_cosmo/∂ℓ ≠ 0` question of `idea.md` §6 Exp5). Report
  significance, reproducibility across probes, and persistence under common-staging.

### Step 5 — Cross-lens held-out mismatch + cross-probe PPD audit
- Directional `δχ_{B|A}` (E5.3) across DES Y6 / KiDS / HSC, localized by `ℓ-bin` and tomographic bin
  (the heatmap); under each model and common-staging. Does `G₂`'s single `Ξ` lower the cross-lens
  `δχ`?
- Leave-one-probe-out PPD (`plan/04` §4.4): fit to **geometry (E1 BAO+SN+CMB) → predict growth `fσ₈`/`S₈`**
  (the canonical "train geometry, predict growth" of `idea.md` §6 E4 / §10 standard 3); and the reverse
  **growth → geometry**. Score `PPD` (whitened). The genuine-`Ξ` test: does `G₂` lower held-out
  `PPD_{geom→growth}` vs `G₀`, or only in-sample `χ²`?

### Step 6 — `D_scale` / `budgeted` status assignment + AOR ledger
- Assign the §4.3 verdict; emit the AOR status for the growth residual and for every systematic /
  backend-tier descent (F9, no `unstatused`).

### Step 7 — The precursor-surrogate cross-check (`G_surr`, §3.4)
- Run the surrogate replica on DES Y3 and the physical CCL on the same vectors; produce the
  side-by-side that demonstrates the physical backend breaks the surrogate degeneracy (G-E5-NOSURR).

### Step 8 — Coherence handoff (the make-or-break)
- Read E1's `a₀` and `K_L`/`K_M` amplitudes from `results/xi_cosmo_coherence.csv`. Compute E5's
  implied `K_S`/`K_G` amplitude from the fitted `Ξ`. **Check the coherence gate**: E5's `K_S` amplitude
  within **10×** and consistent sign with E1's `K_L`/`K_M` (`plan/04` §9.4; `plan/00-overview` §6.4).
  Append E5's `(a₁, β, K_G, K_S)` amplitudes to the coherence ledger for E4/E8.

### Software (from `GROUNDING_BRIEF` §II.A; `plan/02` §1.4)
`pyccl ≥3.0,<3.2` (CCL; **the physical 3×2pt/RSD/CMB-lensing forward model — the core of E5**),
`cobaya ≥3.5,<3.6` (MCMC/likelihood interface; official survey likelihoods `DESLikelihood`/cosmosis
adapters where available), `CLASS ≥3.2`/`CAMB ≥1.5.7` (transfer functions/background; reconcile with
pyccl-internal CLASS via G-ENV-4), `desilike` (DESI full-shape RSD), `getdist ≥1.5` + `arviz ≥0.15`
(`R̂`/ESS/posteriors), `numpy<2.0`/`scipy` (regression, whitened distances), `matplotlib ≥3.5`.
Optional Lean 4 (`v4.28.0`) for the `D_scale` / staging-defect scaffold (§6).

---

## 6. Outputs and AOR statusing

### 6.1 Artifacts (committed)

| Artifact | Path (suggested) | Contents |
|---|---|---|
| Run manifests | `results/E5/manifests/*.json` | per-run seeds, datasets+versions, **backend tier per leg**, pyccl/CLASS versions, params, audit_status (`GROUNDING_BRIEF` §III.B) |
| Reproduction record | `results/E5/repro_S8.csv` | published-vs-recovered `S₈`/`fσ₈`/`μ₀,Σ₀` per probe (G-E5-REPRO) |
| Staging-sweep ledger | `results/E5/staging_sweep.hdf5` | `a₁(ℓ_k)`, `ΔS₈(ℓ_k)`, `fσ₈` residuals, per-`ℓ-bin` `χ²`, all axes × probes, common-staging variants |
| Staging-slope record | `results/E5/staging_slope.json` | `s_Ξ`, `s_Ξ^resid` (E5.1–E5.2) with credible intervals, per axis, the `∂Ξ/∂ℓ` verdict |
| Cross-lens `δχ` heatmap | `results/E5/cross_lens_dchi.{npy,png}` | directional `δχ_{B|A}` localized by `ℓ-bin`/tomographic bin (neutrino-template analog) |
| Model-comparison table | `results/E5/model_comparison.csv` | rows `{G₀,G₁,G₂,G_sys,G_MG}` × cols `{χ²,χ²/dof,k,BIC,AIC,ΔBIC vs G₀, a₁, β, S₈, σ8, OOS PPD_{geom→growth}}` |
| PPD record | `results/E5/ppd_geom_growth.json` | held-out `PPD_{geom→growth}` and `PPD_{growth→geom}` per model |
| `D_scale` verdict | `results/E5/d_scale_status.json` | the §4.3 verdict + evidence (`s_Ξ^resid`, common-staging, cross-lens `δχ` reduction) + AOR status |
| Surrogate cross-check | `results/E5/surrogate_vs_physical.{csv,png}` | `G_surr` (DES Y3) vs physical CCL; demonstrates degeneracy break (G-E5-NOSURR) |
| Posterior triangles | `results/E5/triangle_*.png` | per model/probe (`getdist`) |
| AOR status entry | appended to `results/aor_status_table.csv` | the typed growth residual + every systematic/backend descent (§6.2) |
| Coherence handoff | `results/coherence_ledger/E5.json` (+ append `results/xi_cosmo_coherence.csv`) | `a₁, β`, implied `K_G/K_S` amplitudes + sign, for §9.4 cross-check |

### 6.2 AOR statusing of the E5 residuals (`plan/04` §8; `idea.md` §6 Exp5)

Every surviving growth tension carries **exactly one** AOR base status (F9). Determined by §4.3:

| E5 residual | AOR status | Residual type (`plan/04` §8.2) | Payload `π` |
|---|---|---|---|
| growth staging fingerprint (verdict `D_scale`) | `bridged` | `D_scale` | the `Ξ` term-1 `a₁` that repairs the growth sector + the explicit `s_Ξ^resid` slope |
| growth staging fingerprint (verdict `budgeted`) | `budgeted` | `D_source` | the IA/baryon/photo-z systematic budget absorbing the dependence |
| residual `S₈` offset not explained by `Ξ` or systematics | `budgeted` | `D_target` | the finite bound on the unexplained offset |
| HSC original-vs-recal photo-z shift | `selected` | `D_presentation` | the declared photo-z calibration selection rule (a staging choice) |
| IA / baryon / shear-calibration nuisances | `budgeted` | `D_source` | survey-standard systematic priors (known-systematics) |
| any Gaussian-likelihood approximation (tier-2) | `budgeted` | `D_presentation` | the likelihood-approximation budget |
| DES-Y6 official likelihood unavailable (tier-2 used) | `budgeted` | `D_interface` | the bridging to the published vector+cov |
| a leg only runnable as surrogate (tier-5) | `out_of_scope` | `D_horizon` | the physics-grade-decision deferral (precursor state) |
| DES-Y6 below tier-2 (blocked) | `blocked` | `D_interface` | the block reason; fingerprint run on surviving legs |

Plus standing statuses always recorded:
- "growth and geometry are different lenses; we do not claim the universe is universally too smooth" →
  `nonclaim` (`idea.md` §3 row 6, §5; precursor "Λ not ruled out").
- the MG comparator `G_MG` `(μ₀,Σ₀)` is owned by E7 → `approved_other` here (cross-reference E7).

This run advances the carrier; combined with E4–E7 it targets **CascadeStableAOR** (`plan/00-overview`
§7; E1–E3 → RefStableAOR, E4–E7 → CascadeStableAOR).

### 6.3 Lean anchor (optional this experiment, target for the staging-defect scaffold)

`SBTCosmo.Staging` (`plan/04` §8.2 `D_scale`; §10 Lean map): a scaffold encoding the staging-defect
predicate (the carrier has a declared refinement axis `Σ_stage`, and the residual is typed `D_scale`
iff `∂Ξ/∂ℓ ≠ 0`), plus a **numerical witness** that the fitted staging slope `s_Ξ^resid` carries the
assigned status. The `Σ_stage`/`D_scale` typing is `[T]` (reused from `AOR`); the data slope is `[E]`.

---

## 7. Pass / fail gates (quantitative, pre-registered)

> **Pre-registration discipline (`plan/00-overview` §6, `plan/04` §9).** Thresholds are fixed
> **before** seeing results and may not be relaxed afterward; any relaxation is a logged statused
> deviation (`budgeted`). Units: `S₈` in σ of the survey quote, `χ²/dof`, `ΔBIC`, regression-slope σ,
> whitened distances, fractional `PPD` improvement.

### 7.1 Backend + reproduction gates (must pass first — else blocked)

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E5-BACKEND` | `pyccl` imports; **G-ENV-4 pyccl↔CLASS agreement** passes (`P(k)`<1%, `σ8`<0.5%); CCL reference checks (`σ8`, `fσ₈`, shear `C_ℓ`, `C_ℓ^{κκ}`) <0.5% | `plan/02` §6.G-ENV-4, T1 |
| `G-E5-REPRO` | physical-CCL `G₀` recovers each survey's published `S₈`/`fσ₈`/`(μ₀,Σ₀)` within the survey's quoted 1σ (DES Y6 0.789±0.012; KiDS 0.815; HSC 0.805; GR `μ₀≈0.04`); `R̂<1.01`, ESS>400 | `idea.md` §10.1; the precursor-surrogate fix |
| `G-E5-NOSURR` | the headline staging fingerprint is computed **only** from tier-1/tier-2 (physical-CCL) legs; the `G_surr` surrogate replica reproduces the precursor degeneracy *and* the physical CCL breaks it (distinct, non-degenerate staging curve) | §1.2, §3.4; precursor App. |

### 7.2 Data / metric / ansatz gates

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E5-COV` | each probe `Σ` PD, cond `<10⁸`, finite (else `Σ^†` on legal quotient) | `plan/04` §4.0; `GROUNDING_BRIEF` §VI |
| `G-E5-RANK` | `G₂` adds `≤2` closure params (`a₁`[,`β`]); `a₀` **inherited from E1, not re-fit**; `φ₁,ψ₁,s_p` probe-shared; **no per-probe free `Ξ_p`** | `plan/04` §3.1, §9.2 |
| `G-E5-KERNEL` | `K_G,K_S` linear in `(a₀,a₁)` to `<1%` (finite-difference); `R[Ξ]` positive+stable (stable-readout, `plan/04` §7) | `plan/04` §3.2–3.3, §9.2 |
| `G-E5-SYS` | IA/baryon/photo-z/shear-calibration nuisances marginalized in **every** model incl. `G₀`; not charged to `Ξ` | §3.5 anti-fudge |

### 7.3 The staging-fingerprint gates (the heart of E5)

These operationalize `∂Ξ_cosmo/∂ℓ ≠ 0` (`idea.md` §6 Exp5) and the §4.3 verdict:

| Gate | Verdict / condition |
|---|---|
| **`D_scale` (staging fingerprint = closure)** | residual staging slope `s_Ξ^resid ≠ 0` at **>2σ** (E5.2), **reproducible across ≥2 physical-CCL probes**, and **persisting under common-staging** (>1σ after support-matching), **and** `G₂`'s single `Ξ` lowers the cross-lens `δχ` (E5.3) by **>5%** vs `G₀` |
| **`budgeted` (staging = known systematic)** | `s_Ξ^resid` consistent with 0 (`<2σ`): `G_sys` absorbs the staging dependence as well as `G₂` (their staging curves agree within 1σ) |
| **must be exclusive** | report the evidence triple `(s_Ξ, s_Ξ^resid, common-staging persistence)`; assign exactly one verdict; an ambiguous assignment is itself a `moduli`/`D_source` statused defect |

### 7.4 SBT-claim gates (the `G₂`/`Ξ` value test)

| Gate | PASS | FAIL |
|---|---|---|
| `G-E5-OOS` (out-of-sample, `plan/04` §4.4; `idea.md` §6 E4, §10 std 3) | strict **win** (`plan/REGISTRY` §8): `G₂` lowers held-out `PPD_{geom→growth}` (train on E1 geometry, predict `fσ₈`/`S₈`) beyond the **>3% floor** vs `G₀` (floor, not a pass on its own) **and** beats **every** competitor (`G_sys`,`G_MG`) by more than the combined uncertainty band — a **tie is NOT a pass** | `G₂` ties or loses to a competitor on held-out `PPD`, or improves only in-sample `χ²` not held-out `PPD` (= fudge) |
| `G-E5-DUAL` (one residual, two charts) | the **same** inherited `a₀` (+ fitted `a₁`) improves **both** geometry (already shown E1) **and** growth, with neither block worsened to buy the other | growth improves only by a free `a₁` *unrelated* to geometry (per-probe fudge) |
| `G-E5-COHERE` (coherence, the make-or-break, `plan/04` §9.4 / LP4) | E5's `K_S`/`K_G` amplitude within **10×** and **consistent sign** with E1's `K_L`/`K_M` amplitude (coherence ledger) | E5 growth `Ξ` amplitude differs from E1 geometry `Ξ` by `>10×` or sign disagrees → **program-phase coherence failure** (`plan/00-overview` §6.4) |
| `G-E5-BIC` (model competition) | when the `D_scale` verdict holds, `G₂` beats `G₀` by **ΔBIC > 5** on the joint growth vector | `G₂` never beats `G₀` by ΔBIC in any physical-CCL leg |

### 7.5 Pre-registered failure modes (honored and reported with numbers; `plan/00-overview` §6.3, §6.2 std 5; `idea.md` §10 std 5)

E5 (as a growth-`Ξ` claim) **fails** if **all** of:
1. `s_Ξ^resid` is consistent with 0 across all physical-CCL probes (no staging fingerprint beyond
   known systematics — the `budgeted` verdict), **and**
2. `G₂` does not lower held-out `PPD_{geom→growth}` by `>3%` (`G-E5-OOS` fail), **and**
3. `G₂` never beats `G₀` by `ΔBIC>5` (`G-E5-BIC` fail).

> **Crucial distinctions.**
> - A clean **`budgeted` verdict** (the growth `S₈` spread is fully a known-systematics effect) is a
>   *valid, honest, publishable* E5 outcome (`idea.md` §3 row 6 / §5 explicitly refuse the "universe is
>   too smooth" slogan): SBT then declares it does **not** claim a growth `Ξ`, which *strengthens* the
>   program's credibility. The growth-`Ξ` claim failing is **not** the program failing.
> - The **program** fails at E5 only if (a) `G-E5-BACKEND`/`G-E5-REPRO` fails (cannot reproduce real
>   survey constraints with a physical backend — i.e. we never escaped the precursor's surrogate
>   limitation), (b) **`G-E5-COHERE` fails** (E5 growth `Ξ` is mutually inconsistent with E1 geometry
>   `Ξ` — the make-or-break coherence gate; this is the sharpest possible refutation of "one residual,
>   many shadows"), or (c) `G-E5-RANK`/`G-E5-NOSURR` is violated (the growth `Ξ` is a per-probe fudge,
>   or a surrogate masquerading as a physics result).

---

## 8. Dependencies, blocking, and links

- **Blocked by:**
  - `plan/03` data acquisition: DES Y6 (prime) + KiDS-Legacy + HSC Y3 (both photo-z calibrations) +
    DES Y3 (fallback) + DESI DR2 full-shape RSD + ACT/SPT CMB lensing + Planck anchor (the growth-probe
    table); each loader must expose a mutable `scale_cut` argument for the sweep.
  - `plan/02` environment: the **CCL/`pyccl` backend** (the dependency the precursor lacked) + official
    survey likelihoods (`DESLikelihood`/cosmosis adapters, `desilike`) + the **G-ENV-4 pyccl↔CLASS agreement
    gate** (E5 is explicitly blocked if G-ENV-4 fails).
  - `plan/04` §1–§9: carrier + four residuals; ansatz **term-1 staging chart**; kernels `K_G`/`K_S`;
    `D_scale` defect; AOR statuses; coherence gate; metric `d`.
  - **E1** (DESI DR2 reproduction): provides the **fitted geometry `Ξ` (`a₀`, `K_L`/`K_M` amplitudes)**
    via `results/xi_cosmo_coherence.csv` — *required* to pin `a₀` in `G₁`/`G₂` and to run the
    make-or-break coherence gate. E5 cannot run its headline coherence test until E1-B has written the
    coherence ledger.
  - (soft) **E2** geometry/gluing `Ξ` for a second coherence anchor; **E3** the stable-readout positivity of
    `R[Ξ]` (shared stability audit).
- **Blocks / unblocks:**
  - **E4** (Hubble route matrix): E5's staging-chart `a₁` is one input to the lawful-plurality
    residual-reuse test (LP4, `plan/04` §5.3) — the same `Ξ` that organizes `H₀^{(r,ℓ)}` must also
    repair growth/staging.
  - **E7** (modified gravity as repair chart): E5 provides the GR-growth baseline and the `G_MG`
    `(μ₀,Σ₀)` comparator; E7 decides whether MG is a viable alternative repair of the *same* growth
    residual.
  - **E8** (model-competition synthesis): the `{G₀,G₁,G₂,G_sys,G_MG}` row + the `D_scale`/`budgeted`
    verdict + the cross-lens `δχ` feed the final model-competition matrix and the residual-reuse matrix.
  - the **coherence ledger** consumed by E4/E8; the **AOR status table** advancing toward
    CascadeStableAOR.
- **`idea.md` citations:** §2 ("replace the surrogate LSS backend with a real physical likelihood" —
  the reason E5 exists); §3 shadow map **row 6** ("`S₈` tension = growth-lens staging residual"); §5
  (ansatz **term 1** `a₁·φ₁·ψ₁·s_p`; kernels **`K_G`,`K_S`**; "the same `Ξ` must improve geometry,
  growth, and calibration"); §6 **Experiment 5** (the `∂Ξ_cosmo/∂ℓ ≠ 0` staging-fingerprint test;
  "a fundamental Λ should not care about scale cuts except through known systematics"); §10 (standard 1
  reproduce-first, standard 2 one low-rank residual, standard 3 win out-of-sample, standard 4 staging
  fingerprints, standard 5 pre-register failure modes).
- **Corpus citations:** `A_Six_Birds_Eye_View_of_Dark_Energy` — the **surrogate-backend Limitation box**
  + the DES Y3 scale-cut staging-sweep appendix (the precise weakness E5 fixes) + the P4 staging-
  fingerprint discussion (§"Staging predictions") + the block-map → scale-cut-mask → refit machinery
  (reused, surrogate replaced); `Six_Birds_for_Neutrino_Mass` — the directional cross-lens `δχ_{B|A}`
  audit + spectrum/`ℓ` localization heatmap + **common-staging control** (the template E5 mirrors for
  growth-survey lens swaps); `Foundations_IV` `thm:F4` (Local–Global, the WL cross-survey gluing) +
  the P4 staging law + `thm:F9` (No Unstatused Residual); `Audited_Operational_Realisability`
  (the `D_scale` residual type, the `Σ_stage` stratum, the eleven base statuses, the carrier hierarchy);
  `Adequacy_Residuals` (the Schur-complement `Ξ_C(D|L)` = the joint growth content one GR/Λ family
  cannot explain).
- **arXiv anchors:** DES Y6 3×2pt 2601.14559 (`S₈=0.789±0.012`); KiDS-Legacy 2503.19441
  (`S₈=0.815^{+0.016}_{−0.021}`); HSC Y3 + DESI recal 2511.18134 (`S₈=0.805±0.018`); DES Y3 3×2pt
  fallback 2212.00091; DESI DR2 full-shape RSD / MG 2411.12026 / 2411.12022 (`μ₀=0.04±0.22,
  Σ₀=0.044±0.047`); ACT DR6 CMB lensing 2509.02945; Planck 2018 1807.06209.
