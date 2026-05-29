# E1 — DESI DR2 Reproduction Before Six Birds (the gate)

> **Status of this file.** Implementation-ready plan for experiment **E1**. It is the *reproduction
> gate* for the entire program: a from-scratch, public-likelihood reproduction of the standard
> DESI DR2 dark-energy results — `ΛCDM`, `wCDM`, `w₀w_aCDM` over `DESI DR2 BAO + CMB + SN`
> combinations — that must **pass before any Six Birds (`Ξ_cosmo`) object is introduced anywhere
> in the program**. E1 produces the published `w₀>−1, w_a<0` contour and the dynamical-dark-energy
> significances (`3.1σ` BAO+CMB; `2.8–4.2σ` +SN) within a stated tolerance, plus the parameter
> tables, `Δχ²`/evidence ledger, and the baseline chains that E2–E8 consume.
>
> **Grounding.** `idea.md` §6 **Experiment 1** ("DESI DR2 reproduction before Six Birds";
> *Pass criterion: your pipeline recovers the published contours before adding any Six Birds
> variables*); `idea.md` §10 **test 1** ("Reproduce standard results first"); `idea.md` §2 upgrade 1
> ("move from DES-only public probes to DESI DR2 as the central battleground … reproduce the DESI DR2
> `w₀w_a` signal before introducing Six Birds. Otherwise reviewers will not trust the new
> machinery"). The post-§10 **UPDATE** block supplies the inverse-ladder route this experiment
> *produces* for E4. Corpus: `A_Six_Birds_Eye_View_of_Dark_Energy` (lens/completion/route-mismatch
> framing of cosmological inference, the precursor whose *compressed* DES likelihoods E1 upgrades to
> *full* DESI DR2 likelihoods); `Audited_Operational_Realisability` (every degradation = a *statused*
> residual); `Adequacy_Residuals` (the block currencies the baseline chains later feed). Shared
> conventions: `SHARED GROUNDING BRIEF` §§I–VI; `plan/03-data-acquisition.md` (dataset keys,
> loaders, fallbacks, gates `G-DATA-*`); `plan/02-environment-and-deps.md` (cobaya/CLASS install);
> `plan/01-repo-structure.md` (run layout, manifest schema, `results/`); `plan/00-overview.md`
> §6.1/§6.3 (reproduction + headline gates this file expands); `plan/04-formal-foundations.md`
> (the `Ξ_cosmo` objects that are *forbidden* in E1).

---

## 0. Charter (one sentence)

Reproduce, from public data and public likelihoods with our own `cobaya + CLASS` pipeline, the
standard DESI DR2 `ΛCDM`/`wCDM`/`w₀w_aCDM` results and their dynamical-dark-energy significances to
within a pre-registered tolerance, **with zero Six Birds machinery**, thereby earning the right for
the rest of the program (E2–E8) to add `Ξ_cosmo`.

### 0.1 Why E1 exists (the gate logic)

- **The reproduction is the credential.** Six Birds' headline claim ("dark energy is the shadow of a
  failed closure") is only interesting if the standard analysis is reproduced *first*, on the same
  data, with an independent pipeline. If E1 fails, every downstream `Ξ_cosmo` result is unfalsifiable
  and the program is dead at the gate (`idea.md` §10 test 1; `plan/00-overview.md` §6.1).
- **E1 is a NULL experiment for Six Birds.** No `a₀,a₁,a₂`, no `R[Ξ]`, no `K_L/K_M/K_G/K_S`, no
  `Δ_SBT`, no route-readout field. E1's job is exactly to establish what the *standard* models say so
  that the SBT addition in E1-B (and E2–E8) is a measured *improvement over a verified baseline*, not
  a number compared against an unverified guess.
- **E1 emits the substrate the rest of the program consumes.** The verified ΛCDM/`w₀w_a` chains, the
  baseline `χ²` per probe block, and the derived inverse-ladder `H₀` posterior are all *outputs* of
  E1 that E2 (gluing baseline), E3 (phantom-crossing reference `w(z)`), E4 (inverse-ladder route),
  E5 (geometry baseline for the growth comparison), E6/E7 (IDE/MG baselines), and E8 (model
  competition) read as fixed inputs.

### 0.2 Two stages — hard ordering

| Stage | Name | Contents | Gate |
|-------|------|----------|------|
| **E1-A** | **Reproduction (this gate)** | `ΛCDM`, `wCDM`, `w₀w_aCDM` fits over DESI+CMB+SN combinations; recover published contours + significances | **Must pass G-E1-REPRO-* before E1-B or any other experiment** |
| **E1-B** | **First SBT add-on (post-gate only)** | Add the §3.1 low-rank `Ξ_cosmo` (`a₀,a₁,a₂`) to the *verified* E1-A pipeline; test in-sample fit + out-of-sample SN prediction | Runs **only after** E1-A passes; gated by G-E1-SBT-* |

> **HARD CONSTRAINT (locked).** No file, run, or table in E1-B may be produced until `summary.json`
> for the E1-A reproduction run records all `G-E1-REPRO-*` gates as `PASS`. The gate verifier
> (`tests/test_gates.py`, `plan/01` §6) enforces this by refusing to score E1-B if the E1-A
> manifest is absent or its reproduction gates are not green.

---

## 1. Inputs

### 1.1 Datasets (exact releases; from `plan/03` and Brief §I)

All dataset keys, loaders, fetch URLs, formats, licenses, and fallbacks are fixed in
`plan/03-data-acquisition.md`. E1 consumes the following and **only** the following:

| Role | Dataset key | Release (arXiv/DOI) | Product used in E1 | Loader (`io/datasets.py`) | Fallback (AOR status) |
|------|-------------|---------------------|--------------------|---------------------------|-----------------------|
| **BAO (PRIMARY)** | `DESI_DR2_BAO` | arXiv:2503.14738 | Joint `D_M(z)/r_d`, `D_H(z)/r_d` (+`D_V/r_d` isotropic bins), ~13–15-element vector + full covariance, per-bin `z_eff` | `load_desi_dr2_bao()` | compressed BAO-only Gaussian likelihood (`budgeted`) |
| **CMB (ANCHOR)** | `PLANCK_2018` | arXiv:1807.06209 | Native `clik`: TT(ℓ2–2500), TE/EE(ℓ2–2300), low-ℓ TT/EE, lensing | `load_planck_2018(...)` → `ClikLikelihood` | compressed CMB distance priors `(R, ℓ_A, ω_b, n_s)` + covariance (`budgeted`) |
| **SN (PRIMARY)** | `PANTHEON_PLUS` | arXiv:2202.04077 | `μ(z_hel,z_cmb)` for 1550 SN + full `C_μμ` | `load_pantheon_plus(z_min=0.01)` | binned `μ(z̄)` 10–20 bins + binned cov (`budgeted`; full = `zero`) |
| **SN (variant)** | `UNION3` | arXiv:2401.06956 | Standardized `μ` for 1258 SN + systematic block cov | `load_union3()` | compressed 5-bin distance–redshift (`budgeted`) |
| **SN (variant / precursor)** | `DES_SN5YR` | Zenodo:13827844 / arXiv:2401.02929 | `μ(z)` for 1470 SN + calibration covariance | `load_des_sn5yr()` | fitted `μ(z)` polynomial + cov (`budgeted`) — precursor cross-check |

- **SN-dataset dependence is the point, not a nuisance.** The published significance is a *range*
  (`2.8–4.2σ`) precisely because it depends on the SN compilation. E1 runs each SN compilation
  separately (and the SN-free `BAO+CMB` combination), and the *spread across SN choice* is recorded
  as a Six Birds packaging signal — logged, never hidden (`idea.md` §6 Exp1; `plan/03` §4 method).
- **No weak-lensing / RSD / local-ladder data in E1.** Those enter E4–E7. E1 is geometry + CMB + SN
  only. (`DESI_RSD_FS`, `DES_Y6`, `KIDS_LEGACY`, `HSC_Y3`, `SH0ES`, `CCHP_TRGB_JAGB`, `TDCOSMO`, `SIRENS_GW170817` are
  out of E1 scope.)

### 1.2 Data-integrity preconditions (must hold before any fit)

Inherited from `plan/03` gates `G-DATA-1` (covariance PD), `G-DATA-7` (sha256 vs manifest),
`G-DATA-8` (no undocumented fallback). For E1 specifically, the run script asserts, per probe block,
before sampling:

- Covariance symmetric, positive-definite (Cholesky succeeds), condition number `κ < 10⁸`
  (Brief §VI.1). Record `λ_min`, `κ`, `chol_success`, `chol_jitter_used` in `summary.json`.
- All data-vector and covariance entries finite (no NaN/Inf).
- sha256 of every loaded raw file matches the tracked `data/manifests/<key>.json`.
- Any fallback invoked ⇒ `access ≠ official_likelihood` and `aor_status ∈ {budgeted, …}` recorded in
  both dataset manifest and run manifest (`plan/03` §8).

### 1.3 What is FORBIDDEN in E1 (anti-leakage of SBT)

E1-A must contain **none** of the following (a lint check in `tests/test_gates.py` scans the E1-A
config + code path for these symbols and fails the run if present):

- The closure residual `Ξ_cosmo`, its ansatz coefficients `a₀,a₁,a₂[,β]`, shapes `φ₀,φ₁,φ₂,ψ₁`, the
  rewrite `R[·]`, the kernels `K_L,K_M,K_G,K_S,K_{r,ℓ}`, the least-rewrite objective `Δ_SBT`
  (`plan/04` §3, eqs. (4)–(9)).
- Any route-indexed Hubble readout `H₀^{(r,ℓ)}` or holonomy `𝔥_γ` (those are E4).
- Any per-probe free correction function added to a theory prediction.

`w₀w_aCDM` (CPL) is **not** an SBT object — it is a *standard* phenomenological dark-energy model and
is the central reproduction target. Reproducing CPL is the gate; *interpreting* CPL's `(w₀,w_a)` as a
chart of `Ξ_cosmo` is E8's job, not E1's.

---

## 2. Method

### 2.1 Software stack (Brief §II; `plan/02`)

| Tool | Min version | Role in E1 |
|------|-------------|------------|
| `cobaya` | ≥3.4 | Inference driver, likelihood orchestration, native Planck likelihood interface, MCMC + (optional) PolyChord, BOBYQA minimizer |
| `CLASS` (`classy`) | ≥3.2 | Boltzmann backend: `C_ℓ`, `D_M(z)`, `D_H(z)`, `r_d(θ)`, background `H(z)` |
| `CAMB` | ≥1.5.7 | **Cross-check backend only** (§2.7); never mixed with CLASS in one chain |
| `getdist` | ≥1.5 | Posterior summaries, triangle/contour figures, marginal stats |
| `arviz` | ≥0.15 | MCMC health: `R̂`, ESS, trace/energy checks |
| `numpy/scipy` | latest | Cholesky whitening, `Δχ²`, significance arithmetic |

- **Backend choice is locked per program (Brief §II.A): CLASS is primary.** Do not mix CLASS and
  CAMB inside a single chain. CAMB is used *only* in the §2.7 cross-check to bound backend-induced
  scatter.
- **Float64 everywhere** (Brief §III.D). CLASS/CAMB precision settings pinned in the config and
  recorded in the manifest.

### 2.2 Models (exact parameterizations)

Three nested background dark-energy models. `w₀w_aCDM` is the CPL parameterization used by DESI DR2.

| Model | Free DE params | `w(a)` | Notes |
|-------|----------------|--------|-------|
| **`ΛCDM`** | none (`w≡−1`) | `−1` | Baseline / null for dynamical DE |
| **`wCDM`** | `w₀` | `w₀` (constant) | One-parameter constant-`w` |
| **`w₀w_aCDM`** (CPL) | `w₀, w_a` | `w₀ + w_a (1−a) = w₀ + w_a · z/(1+z)` | **PRIMARY reproduction target** |

Background dark-energy density (CPL, for the CLASS fluid):
`ρ_DE(a)/ρ_DE,0 = a^{−3(1+w₀+w_a)} · exp(−3 w_a (1−a))`. Use CLASS's `Omega_fld` / `w0_fld`,
`wa_fld` fluid with PPF (`use_ppf = yes`) so the phantom-divide crossing (`w` through `−1`) is handled
without numerical blow-up. This is a *standard* DESI-pipeline choice — **not** an SBT statement about
ghosts (that interpretation is E3).

### 2.3 Sampled parameters and priors (locked)

Cosmological parameters (flat priors unless noted), matching the DESI DR2 baseline analysis
conventions (arXiv:2503.14738) so contours are directly comparable:

| Parameter | Symbol | Prior | Notes |
|-----------|--------|-------|-------|
| Baryon density | `Ω_b h²` | `U(0.005, 0.1)` | |
| Cold dark matter density | `Ω_c h²` | `U(0.001, 0.99)` | |
| Acoustic angular scale | `100 θ_MC` | `U(0.5, 10)` | sampled instead of `H₀` for CMB efficiency |
| Reionization optical depth | `τ` | `U(0.01, 0.8)` | with Planck low-E |
| Scalar amplitude | `ln(10¹⁰ A_s)` | `U(1.61, 3.91)` | |
| Scalar tilt | `n_s` | `U(0.8, 1.2)` | |
| DE eq. of state today | `w₀` | `U(−3, 1)` | `wCDM`, `w₀w_aCDM` only |
| DE eq. of state evolution | `w_a` | `U(−3, 2)` | `w₀w_aCDM` only |

Derived: `H₀`, `Ω_m`, `σ_8`, `S_8`, `r_d`, `Age`. Neutrinos: one massive eigenstate fixed at
`Σm_ν = 0.06 eV` (DESI/Planck baseline); `N_eff = 3.044`. (A `Σm_ν`-free variant is *out of E1
scope* — that is the neutrino-mass lens-swap territory, E4/E5 staging axis, per `plan/03` §3 and the
`Six_Birds_for_Neutrino_Mass` template.)

Nuisance parameters: all Planck `clik` nuisances (calibration, foregrounds) sampled with their
recommended priors; Pantheon+ absolute magnitude `M_B` marginalized analytically (or sampled with a
wide flat prior) — **E1 uses SN without the SH0ES `M_B` calibration prior** (SN as *uncalibrated*
relative distances), exactly as in the DESI DR2 + SN combination. The SH0ES `M_B` / `H₀` prior is an
E4 route ingredient, deliberately excluded here to match the published DESI DR2 contour.

### 2.4 Data combinations (the reproduction matrix)

Run every model over every combination. The combinations and their expected headline results:

| ID | Combination | Models | What it must reproduce |
|----|-------------|--------|------------------------|
| `C1` | **Planck 2018** (CMB only) | ΛCDM, wCDM, w₀w_a | CMB-only baseline; `H₀≈67.4±0.5` @ ΛCDM (arXiv:1807.06209) |
| `C2` | **DESI DR2 BAO + Planck** (`BAO+CMB`) | ΛCDM, wCDM, w₀w_a | **`3.1σ` dynamical-DE preference**; `w₀>−1, w_a<0` |
| `C3` | `BAO+CMB+`**Pantheon+** | ΛCDM, wCDM, w₀w_a | DE significance in `2.8–4.2σ` band (Pantheon+ leg) |
| `C4` | `BAO+CMB+`**Union3** | ΛCDM, wCDM, w₀w_a | DE significance in `2.8–4.2σ` band (Union3 leg; typically higher) |
| `C5` | `BAO+CMB+`**DES-SN5YR** | ΛCDM, wCDM, w₀w_a | DE significance in `2.8–4.2σ` band (DES-SN5YR leg; typically highest) |

> The published DESI DR2 statement: `BAO+CMB` prefers `w₀w_a` over `ΛCDM` at **3.1σ**; adding SN
> raises this to **2.8–4.2σ** depending on the SN sample (Pantheon+ lower, DES-SN5YR higher), with a
> best-fit in the `w₀ > −1, w_a < 0` quadrant (arXiv:2503.14738; `idea.md` §6 Exp1, §0). E1 must land
> in this quadrant and band.

### 2.5 Inference protocol (per combination × model)

1. **Minimize first.** Run `cobaya` BOBYQA minimizer from ≥4 dispersed starts to locate the MAP and
   the `χ²_min` per combination/model. Record `χ²_min` *per probe block* (CMB, BAO, SN separately) and
   total. This is the spine of the `Δχ²` significance computation (§2.6) and the E2–E8 baselines.
2. **Sample.** Run `cobaya` Metropolis MCMC, ≥4 chains, until `R̂ − 1 < 0.01` on all sampled
   parameters (Brief §VI.2; `plan/01` §9). Drop burn-in via `getdist` defaults. Target ESS `> 400`
   per chain (Brief §III.C). For the headline `C2`/`C3` `w₀w_a` runs, additionally run **PolyChord**
   nested sampling to obtain the **Bayesian evidence** `ln Z` for `w₀w_a` vs `ΛCDM` (§2.6).
3. **Seeds.** Pin `{numpy, python, sampler}` seeds in `config.yaml` (`plan/01` §9.1). Re-run with the
   same seed reproduces the likelihood/forward-model evaluations bitwise and committed summaries to tolerance; chains by statistical equivalence, not bitwise samples (Brief §III.A; REGISTRY §11.6); verified by G-E1-REPRO-DET.
4. **Determinism of the backend.** CLASS precision params fixed in config; record CLASS/CAMB version
   + precision hash in the manifest.

### 2.6 Significance computation (two independent estimators)

The published DESI significance is reported via both `Δχ²` and Bayesian model comparison; E1 computes
both and reports both so neither can be cherry-picked.

- **(a) Frequentist `Δχ²` → Gaussian-equivalent σ.** For nested models with `Δk` extra parameters,
  `Δχ² = χ²_min(ΛCDM) − χ²_min(w₀w_a)`. For `w₀w_a` vs `ΛCDM`, `Δk = 2`; convert via the
  survival function of `χ²` with 2 dof to a two-sided Gaussian-equivalent number of σ
  (`n_σ = sqrt(Φ⁻¹-based mapping)`; report the exact mapping used in `summary.json`). DESI's own
  number is constructed this way; E1 must match it within tolerance.
- **(b) Bayesian evidence.** From PolyChord, `ln B = ln Z(w₀w_a) − ln Z(ΛCDM)` with its sampling
  error. Report Jeffreys-scale interpretation. (DESI reports this as supplementary; E1 records it for
  the E8 model-competition matrix and as a cross-check that the `Δχ²` significance is not an artifact
  of volume effects.)
- **Significance per SN leg.** Compute (a) and (b) for `C2` (no SN), and for each of `C3/C4/C5`. The
  *spread* of `n_σ` across `{Pantheon+, Union3, DES-SN5YR}` must fall in `[2.8, 4.2]` and is recorded
  as the SN-dependence signal (§1.1).

### 2.7 Controls (built into E1, not optional)

| Control | Purpose | Recorded as |
|---------|---------|-------------|
| **Backend cross-check** | Re-run `C2`/`C3` `w₀w_a` MAP + 1 MCMC with **CAMB** instead of CLASS; the `(w₀,w_a)` MAP and `χ²_min` must agree within the pipeline tolerance | `tables/backend_crosscheck.csv` |
| **Prior-sensitivity** | Re-run `C2` `w₀w_a` with the `w_a` prior widened to `U(−3.5, 2.5)`; the contour must not move beyond its 1σ width (rules out prior-driven detection) | `tables/prior_sensitivity.csv` |
| **`Σm_ν` fixed-value control** | Confirm baseline `Σm_ν=0.06` reproduces published; *do not* free it in E1 (logged as out-of-scope, deferred to neutrino-lens experiments) | `summary.json` note |
| **Compressed-vs-full BAO** | If the full DESI likelihood path is used, also run the compressed BAO-only Gaussian fallback for `C2` and confirm the contour shift is within the `budgeted` tolerance (bounds the fallback information loss) | `tables/bao_full_vs_compressed.csv` |
| **SN-leg spread** | The `[2.8,4.2]σ` band reproduced as a *spread* across SN compilations, not a single number | `tables/significance_by_sn.csv` |

### 2.8 E1-B (post-gate only) — first Six Birds add-on

Runs **only after E1-A passes**. Adds the §3.1 low-rank `Ξ_cosmo` from `plan/04` (eqs. (4)–(9)) to
the *verified* E1-A pipeline, with at most 3 amplitude parameters `(a₀,a₁,a₂)`:

1. **Geometry-only SBT fit.** Replace the CPL background by `ρ_eff(z) = ρ_FLRW(z;θ) + R[Ξ_cosmo](z)`
   (eq. (5)) with the kernels `K_L` (SN `D_L`, `c_SN=+1`) and `K_M` (BAO `D_M/r_d`, `c_BAO=−1`) from
   `plan/04` §3.3. Fit `C3` (`BAO+CMB+Pantheon+`). The same `Ξ` must improve **both** the SN block
   and the BAO block (the anti-fudge rule, `plan/04` §3.4).
2. **In-sample gate.** SBT achieves `χ²/dof ≤ 0.99` of the E1-A `w₀w_a` baseline with `≤3` extra
   parameters (`plan/00` §6.3 E1 row).
3. **Out-of-sample gate.** Train on `BAO+CMB`, predict the held-out SN block; SBT improves SN OOS
   RMSE by `>10%` over the ΛCDM baseline, or matches the `w₀w_a` baseline within `3%`. A genuine
   `Ξ_cosmo` lowers the cross-probe `PPD`; a per-probe fudge does not.
4. **Coherence handoff.** Record the fitted `(a₀,a₁,a₂)` and the implied `K_L/K_M` amplitudes to
   `results/xi_cosmo_coherence.csv` so the §6.4 cross-experiment coherence gate (`plan/00`) can check
   that E5's `K_S` amplitude lands within `10×` of E1's `K_L/K_M` amplitude.

> E1-B is intentionally minimal — it only proves "the same `Ξ` improves SN and BAO geometry and wins
> out-of-sample." The richer shadows (gluing, phantom, Hubble, growth) are E2–E7.

---

## 3. Outputs (exact artifacts)

All artifacts live under `runs/E1/<run_id>/` (E1-A) and `runs/E1B/<run_id>/` (E1-B), following the
`plan/01` §7 run layout (`config.yaml`, `manifest.json`, `summary.json`, `tables/`, `figures/`,
`chains/`, `aor_ledger.json`). Cross-experiment publication artifacts are also written to `results/`.

### 3.1 Chains and posteriors

| Artifact | Path | Content |
|----------|------|---------|
| MCMC chains | `runs/E1/<run_id>/chains/{C1..C5}_{lcdm,wcdm,w0wa}.txt` | getdist-format chains, one per combination×model |
| Posterior samples (HDF5) | `runs/E1/<run_id>/chains/*.hdf5` | cobaya-native, for getdist reload |
| PolyChord evidence | `runs/E1/<run_id>/chains/evidence_{C2,C3,C4,C5}.json` | `ln Z ± err` for ΛCDM and w₀w_a |

### 3.2 Figures (publication-grade, committed)

| Figure | Path | Must show |
|--------|------|-----------|
| **`w₀–w_a` contour** | `results/figs/E1_w0wa_contour.{png,pdf}` | 68%/95% contours for `C2` (BAO+CMB) and `C3/C4/C5` (+SN), overlaid with the published DESI DR2 contour for visual comparison; the `w₀>−1, w_a<0` quadrant marked; `ΛCDM` point `(−1,0)` marked |
| Triangle (w₀w_a) | `runs/E1/<run_id>/figures/E1_triangle_C3_w0wa.{png,pdf}` | full parameter triangle for the headline `C3` w₀w_a fit (getdist, `viz/triangle.py`) |
| `H₀` comparison | `results/figs/E1_H0_by_model.{png,pdf}` | derived `H₀` posterior per model×combination, incl. the inverse-ladder posterior (§3.5) vs Planck-ΛCDM band |
| Hubble diagram residual | `runs/E1/<run_id>/figures/E1_sn_residual.{png,pdf}` | SN `μ(z)` residual vs best-fit ΛCDM and w₀w_a, with covariance band |
| MCMC health | `runs/E1/<run_id>/figures/E1_convergence.{png,pdf}` | `R̂` and ESS per parameter (arviz) |

### 3.3 Parameter tables (CSV, committed)

| Table | Path | Columns |
|-------|------|---------|
| **Parameter constraints** | `results/tables/E1_parameters.csv` | `combination, model, param, mean, std, MAP, 68%_low, 68%_high` for all sampled+derived params |
| **`(w₀,w_a)` headline** | `results/tables/E1_w0wa.csv` | `combination, w0_mean, w0_std, wa_mean, wa_std, in_quadrant(bool)` |
| **Significance ledger** | `results/tables/E1_significance.csv` | `combination, dchi2_w0wa_vs_lcdm, n_sigma_dchi2, lnB_w0wa_vs_lcdm, lnB_err, n_sigma_band_ok(bool)` |
| **Per-block χ²** | `results/tables/E1_chi2_blocks.csv` | `combination, model, chi2_CMB, chi2_BAO, chi2_SN, chi2_total, dof, chi2_per_dof` |
| Significance by SN | `results/tables/E1_significance_by_sn.csv` | `sn_dataset, n_sigma, in_band[2.8,4.2](bool)` |
| Backend cross-check | `runs/E1/<run_id>/tables/backend_crosscheck.csv` | `model, w0_class, w0_camb, wa_class, wa_camb, dchi2` |
| Prior sensitivity | `runs/E1/<run_id>/tables/prior_sensitivity.csv` | `prior_width, w0, wa, contour_shift_sigma` |

### 3.4 `Δχ²` / evidence ledger

`results/tables/E1_significance.csv` (above) **is** the `Δχ²`/evidence ledger. It must contain, for
each combination `C2..C5`: `Δχ²(ΛCDM − w₀w_a)`, the Gaussian-equivalent `n_σ` from `Δχ²` (2 dof), the
Bayes factor `ln B`, and a boolean `n_sigma_band_ok` flagging whether the value lands in the published
band (`3.1±tol` for C2; `[2.8,4.2]` for C3/C4/C5).

### 3.5 Derived products for downstream experiments (the substrate)

| Product | Path | Consumed by |
|---------|------|-------------|
| **Verified ΛCDM + w₀w_a chains** | `runs/E1/<run_id>/chains/*` | E2 (gluing baseline), E3 (reference `w(z)`), E5 (geometry baseline), E6/E7, E8 |
| **Baseline per-block χ²** | `results/tables/E1_chi2_blocks.csv` | E1-B & all OOS comparisons (the number SBT must beat) |
| **Inverse-ladder `H₀` posterior** | `results/tables/E1_inverse_ladder_H0.csv` + `runs/E1/<run_id>/chains/inverse_ladder.hdf5` | **E4** route `r = (CMB+BAO→H₀)` (`plan/03` §3 `INVERSE_LADDER`; idea.md UPDATE block). Produced by fitting ΛCDM/w₀w_a to `BAO+CMB` and propagating SN calibration; `derive_inverse_ladder(chains)` |
| **E1-B coherence record** | `results/xi_cosmo_coherence.csv` | §6.4 cross-experiment coherence gate |

### 3.6 Manifest + AOR ledger

- `runs/E1/<run_id>/manifest.json` — full run manifest (`plan/01` §9.3 / Brief §III.B): `run_id`,
  date, seeds, datasets[] (name, version, access, manifest_path, verified, aor_status), software
  versions (cobaya/CLASS/CAMB/getdist/arviz), CLASS precision hash, model, combination, nsamples,
  output files, gate results.
- `runs/E1/<run_id>/aor_ledger.json` — AOR status table (Brief §VI; `plan/04` AOR vocabulary). E1
  target stratum: **`RefStableAOR`** (`plan/00` §4). Every residual typed: e.g. the SN-leg spread is
  `budgeted` (bounded, accounted); any invoked compressed-likelihood fallback is `budgeted`; the
  excluded SH0ES `M_B` prior and free `Σm_ν` are `out_of_scope` (deferred to E4/E5). No
  `unstatused` residual permitted.

---

## 4. Pass/fail gates (quantitative)

Gate IDs use the program convention `G-E1-*`. **All `G-E1-REPRO-*` gates are blocking for the entire
program** (`plan/00` §6.1). `G-E1-SBT-*` gate E1-B only and run after the reproduction passes.

### 4.1 Reproduction gates — E1-A (BLOCKING, must all PASS before any SBT)

| Gate | Quantitative threshold | Fail condition | Source |
|------|------------------------|----------------|--------|
| **G-E1-REPRO-QUAD** | The `C2..C5` `w₀w_a` MAP and 68% region lie in the `w₀ > −1, w_a < 0` quadrant | best-fit outside that quadrant | idea.md §6 Exp1; arXiv:2503.14738 |
| **G-E1-REPRO-CONTOUR** | Recovered `(w₀,w_a)` means within **±5%** of published DESI DR2 values, and 68% interval widths within **±15%** of published; e.g. `C2`-class `w₀≈−0.92, w_a≈−0.4..−0.5`-region overlapping published contour | mean off by `>10%` or interval width off by `>30%` | `plan/00` §6.1, §6.3 E1 |
| **G-E1-REPRO-SIG-BAOCMB** | `C2` (BAO+CMB) dynamical-DE significance recovered as **3.1σ ± 0.4σ** (both `Δχ²`-σ and consistent `ln B` sign) | `n_σ < 2.5` or `> 3.7` for C2 | idea.md §0/§6 Exp1; arXiv:2503.14738 |
| **G-E1-REPRO-SIG-SN** | `C3/C4/C5` significances span and stay within the **`[2.8, 4.2]σ`** band (per-SN-leg), reproducing the SN-dependence | any SN leg outside `[2.5, 4.5]σ`, or the spread collapses to a single value (indicating SN systematics mishandled) | idea.md §6 Exp1 |
| **G-E1-REPRO-CMBONLY** | `C1` ΛCDM recovers `H₀ = 67.4 ± 0.5` (within `1σ`) and Planck `χ²` within **5%** of the published Planck-2018 baseline | `H₀` off by `>1.5σ`; CMB `χ²` off by `>5%` | arXiv:1807.06209; Brief §VI.3 |
| **G-E1-REPRO-CHI2** | Total `χ²` per combination within **5%** of the published reference where available; `χ²/dof` reported per block | block `χ²/dof` implausible (`>1.3` or `<0.7`) without explanation | Brief §VI.3 |
| **G-E1-REPRO-CONV** | `R̂ − 1 < 0.01` all params; ESS `> 400` per chain; for headline runs PolyChord `ln Z` error `< 0.3` | non-convergence; `R̂ − 1 ≥ 0.02` | Brief §VI.2 |
| **G-E1-REPRO-PD** | All probe covariances PD; `κ < 10⁸`; finite | non-PD or `κ ≥ 10⁸` | Brief §VI.1; `plan/03` G-DATA-1 |
| **G-E1-REPRO-DET** | Re-run from `manifest.json` reproduces `(w₀,w_a)` MAP and `χ²_min` (summary scalars) to `< 1e-10` relative; chains by statistical equivalence (not bitwise) | non-reproducible | Brief §III.A; `plan/00` §6 determinism |
| **G-E1-REPRO-BACKEND** | CLASS vs CAMB MAP `(w₀,w_a)` agree within **±2%** and `Δχ²` within `0.5`; prior-widening shifts contour `< 1σ` | backend disagreement `>5%`; prior-driven shift `>1σ` | §2.7 controls |
| **G-E1-REPRO-NO-SBT** | Lint confirms zero SBT symbols (§1.3) in the E1-A code path/config | any `Ξ_cosmo`/`a₀..a₂`/`K_*`/`Δ_SBT`/`H₀^{(r,ℓ)}` reference in E1-A | §1.3 anti-leakage |
| **G-E1-REPRO-AOR** | `aor_ledger.json` present, every residual statused, stratum `RefStableAOR`, no `unstatused` | any unstatused residual; missing ledger | Brief §VI; `plan/04` AOR |

> **GATE FOR THE PROGRAM (locked).** If **any** `G-E1-REPRO-*` gate fails, the program stops at the
> reproduction gate. No E1-B, no E2–E8. This realizes `idea.md` §10 test 1 and §6 Exp1's
> *"Pass criterion: your pipeline recovers the published contours before adding any Six Birds
> variables."* (`plan/00` §6.1, §6.5).

### 4.2 First-SBT gates — E1-B (post-gate; non-blocking for E1-A but blocking for the E1 *headline*)

| Gate | Quantitative threshold | Fail condition |
|------|------------------------|----------------|
| **G-E1-SBT-FIT** | SBT geometry fit (`C3`) reaches `χ²/dof ≤ 0.99 ×` the E1-A `w₀w_a` baseline with `≤3` extra params | SBT `χ²` `>5%` worse than baseline; `>3` extra params used (`plan/00` §6.3 E1) |
| **G-E1-SBT-OOS** | Train `BAO+CMB`, predict SN: SBT SN OOS RMSE ↓ `>10%` vs ΛCDM, **or** matches w₀w_a within `3%` | SN OOS `>15%` worse than baseline (`plan/00` §6.3 E1) |
| **G-E1-SBT-DUAL** | The *same* `(a₀,a₁,a₂)` improves **both** the SN block and the BAO block (each block `χ²` not worsened) | one block improves only by worsening the other (per-probe fudge) (`plan/04` §3.4 anti-fudge) |
| **G-E1-SBT-COHERENCE** | Fitted `K_L/K_M` amplitudes written to `results/xi_cosmo_coherence.csv` for the §6.4 program coherence check | amplitudes not recorded / inconsistent sign with the rewrite definition |

### 4.3 Pre-registered failure modes (cannot be moved after execution)

E1 (and thus the whole program) is **rejected** if, after honest execution:

1. The pipeline cannot recover the published DESI DR2 `w₀w_a` contour or the `3.1σ`/`2.8–4.2σ`
   significances within §4.1 tolerances (reproduction failure ⇒ program stops; `idea.md` §10.5).
2. The recovered significance is *prior-driven* (G-E1-REPRO-BACKEND prior-widening moves the contour
   `> 1σ`) or *backend-driven* (CLASS↔CAMB disagree `> 5%`) — i.e., the "detection" is a pipeline
   artifact, not in the data.
3. E1-B's `Ξ_cosmo` improves SN only by worsening BAO (or vice versa) — a per-probe fudge, not one
   residual (`idea.md` §10.5; `plan/00` §6.3 E1 fail column; `plan/04` §3.4).
4. E1-B uses `>3` extra parameters with no `χ²/dof` gain, or worsens SN OOS by `>15%`.
5. Any SBT symbol leaks into E1-A (G-E1-REPRO-NO-SBT) — the gate is contaminated and the
   reproduction is void.

---

## 5. Compute / runtime budget (Brief §IV)

| Task | Hardware | Wall time | Memory | Notes |
|------|----------|-----------|--------|-------|
| Single ΛCDM fit (`C1`) | 16 CPU | 4–6 h | 8 GB | first-run pipeline validation |
| `wCDM`/`w₀w_aCDM` MCMC per combination | 16–32 CPU | 6–12 h each | 8–16 GB | `C2..C5` × {wcdm, w0wa} |
| PolyChord evidence (`C2`,`C3` w₀w_a) | 32 CPU | 12–24 h each | 16 GB | for `ln Z` |
| CAMB backend cross-check | 16 CPU | 4–6 h | 8 GB | control |
| E1-B SBT geometry fit + OOS | 16 CPU | 6–12 h | 8 GB | post-gate |

Pragmatic order: run `C1` ΛCDM first to validate the pipeline and convergence machinery (Brief §IV
"first run"), then `C2` (the headline BAO+CMB significance), then `C3/C4/C5`, then controls, then —
**only if the gate passes** — E1-B.

---

## 6. Step-by-step implementation checklist

1. Confirm `plan/03` loaders return PD covariances for `DESI_DR2_BAO`, `PLANCK_2018`,
   `PANTHEON_PLUS`, `UNION3`, `DES_SN5YR`; verify sha256 vs manifests (G-DATA-7).
2. Install Planck native likelihoods via `cobaya-install` (per `plan/02` §2.1); wrap DESI BAO and SN
   as cobaya likelihoods; pin CLASS precision in `configs/`.
3. Write `configs/experiments/E1.yaml` (models, combinations `C1..C5`, priors §2.3, seeds, sampler
   targets). Add the §1.3 SBT-symbol lint to `tests/test_gates.py`.
4. Run `C1` ΛCDM → validate pipeline, convergence, CMB `χ²`, `H₀` (G-E1-REPRO-CMBONLY).
5. Run `C2..C5` × {ΛCDM, wCDM, w₀w_a}: minimize → MCMC → (headline) PolyChord. Record per-block `χ²`.
6. Compute significances (§2.6); build `E1_significance.csv` ledger; build `E1_w0wa.csv`,
   `E1_parameters.csv`, `E1_chi2_blocks.csv`.
7. Run controls §2.7 (backend, prior, compressed-vs-full, SN-leg spread).
8. Generate figures §3.2 (overlay published DESI contour on `E1_w0wa_contour`).
9. Derive and emit the inverse-ladder `H₀` posterior (§3.5) for E4.
10. Write `manifest.json` + `aor_ledger.json`; evaluate **all** `G-E1-REPRO-*` gates into
    `summary.json`. **Stop here unless all green.**
11. (Post-gate) Run E1-B SBT geometry add-on; evaluate `G-E1-SBT-*`; emit
    `results/xi_cosmo_coherence.csv`.

---

## 7. Cross-experiment links

- **Feeds E2** (distance-duality gluing): E1's verified ΛCDM/w₀w_a chains are the baseline against
  which the gluing model `M₂` (`η≠1`, `Ξ≠0`) is compared.
- **Feeds E3** (phantom crossing): E1's `w₀w_a` `w(z)` and DESI-preferred crossing redshift `z_c` are
  the reference E3's `w_eff(z)` from `Ξ_cosmo` must reproduce.
- **Feeds E4** (Hubble route matrix): E1 *produces* the inverse-ladder `H₀` route
  `r = (CMB+BAO→H₀)` (§3.5; idea.md UPDATE block, `plan/03` §3 `INVERSE_LADDER`).
- **Feeds E5/E6/E7**: E1's geometry baseline and per-block `χ²` are the fixed reference for the
  growth, IDE, and MG comparisons.
- **Feeds E8** (model competition): E1 contributes the ΛCDM, wCDM, w₀w_a rows (fit, `Δχ²`, `ln Z`,
  per-block `χ²`) of the competition matrix; E1-B contributes the SBT-geometry row's seed.
- **Coherence**: E1-B's `K_L/K_M` amplitude is the anchor the §6.4 program coherence gate uses to
  bound E5's `K_S` amplitude (within `10×`).
