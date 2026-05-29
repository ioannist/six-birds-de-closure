# 06 — Results Manifest: The Authoritative Deliverable Inventory

**Program:** Dark Energy as Closure — a Six Birds resolution of the cosmological paradoxes
**Status:** PLANNING / BLUEPRINT. To be executed later by a separate codex-driven process. Nothing here is run, built, or proved now.

> **Read order.** Read `plan/00-overview.md` (thesis, scope, definition of done), `GROUNDING_BRIEF.md`
> (datasets/stack/determinism/AOR vocabulary), `plan/01-repo-structure.md` (`results/` vs
> `experiments/<E>/outputs/` layout, tracked-vs-ignored policy, gates G-REPO-1…G-REPO-16), and the per-experiment
> files `plan/experiments/E0…E8.md`, `plan/04-formal-foundations.md`, and `plan/05-lean-mechanization.md`
> first. **This file is the single canonical inventory of EVERY result artifact the implementation must
> produce**, aggregated across E0–E8, the formal-foundations math, and the Lean track. It is the
> *results-deliverable spec*: the executor is done with the phase iff every row below exists at its
> committed path, is schema/format-valid, and passes its acceptance check.

> **Scope of THIS file.** It enumerates and types artifacts and gives each a committed path and an
> acceptance check. It does **not** redefine the math (that is `plan/04`), the pipelines (the `E#.md`
> files), or the gate thresholds (those live in `plan/00` §6, `plan/04` §9, and each `E#.md`); it
> *references* them. Where a gate decides an artifact's acceptance, the acceptance check cites the gate
> ID verbatim so there is exactly one source of truth for the threshold.

---

## 0. Conventions used in every table below

### 0.1 Artifact `type`

| `type` | Meaning | Example |
|---|---|---|
| **figure** | a committed `.png` (and `.pdf` for publication-grade) plot | `E1_w0wa_contour.png` |
| **table** | a committed `.csv` (columnated, header row) | `model_competition.csv` |
| **number** | a scalar (or small scalar set) recorded as a key in a `summary.json` / `*.json` | `summary.json:toy2.OmegaLambda_LCDM` |
| **array** | a committed numeric blob (`.npy`/`.npz`/`.hdf5`) holding data vectors / covariances / chains-derived posteriors | `e3_operator.npz` |
| **proof** | a paper-grade mathematical result locked in `plan/04` (graded `[T]`/`[C]`/`[E]`) whose Lean realization, if any, is a separate `Lean` row | Reconciliation Lemma |
| **Lean** | a Lean 4 declaration whose acceptance is `lake build` green + axiom-audit pass | `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness` |
| **manifest** | a per-run provenance JSON (`GROUNDING_BRIEF` §III.B schema) | `runs/E1/<run_id>/manifest.json` |
| **ledger** | an AOR status JSON/CSV (`plan/04` §8) | `aor_status.json` / `aor_status_table.csv` |

### 0.2 Path conventions (from `plan/01` §7–§8)

- **`experiments/<E>/outputs/`** — per-run, per-experiment committed summaries (manifest, `summary.json`,
  `aor_status.json`, tables, figures). **Raw chains under `**/outputs/chains/` are gitignored** (G-REPO-9).
- **`results/`** — cross-experiment, program-level committed artifacts (headline figures, the master
  tables, the coherence ledger, the AOR status master). These survive even if a run dir is pruned.
- **`runs/<E>/<run_id>/`** — E1/E6/E8-style run trees (chains gitignored; manifest/summary/tables tracked).
- **`results/coherence_ledger/E#.json`** + **`results/xi_cosmo_coherence.csv`** — the make-or-break
  cross-experiment coherence record (`plan/04` §9.4, `plan/00` §6.4).
- **`lean/SbtCosmo/*.lean`** + **`lean/manifests/`** — the certified-receipt track (`plan/05`).

> **Tracked-vs-ignored (authoritative, `plan/01` §8 / G-REPO-9).** Every artifact below marked TRACKED is
> committed to git. Chains (`outputs/chains/`, `runs/**/chains/`) and `data/raw/**`, `data/processed/**`,
> `.lake/` are gitignored; their *derived* summaries (posterior_summary, summary.json, tables, figures)
> are tracked so every gate is re-derivable **without re-running** (G-REPO-8 "reproduce-without-rerun").

### 0.3 Universal per-run artifacts (apply to E0–E8 unless noted)

Every experiment run **must** emit these three; they are not repeated in each section's table but are
required for that experiment to count as delivered:

| Artifact | type | Path (per-run) | Acceptance check |
|---|---|---|---|
| Run manifest | manifest | `<run dir>/manifest.json` | schema-valid per `GROUNDING_BRIEF` §III.B / `plan/01` §9.3: `run_id`, ISO `date`, `seeds{}`, `datasets[]{name,version,access,manifest_path,verified,aor_status}`, `software[]{name,version}` (incl. CLASS commit, compiler, container digest where used), `parameters{}`, `output_files[]`, `audit_status ∈ {AOR_certified, recognized_grade, unaudited}`, `lean{toolchain,mathlib_rev,build,axiom_audit}`. G-REPO-6 (100% schema-valid), G-REPO-7 (dataset sha256 match) |
| Gate summary | number/table | `<run dir>/summary.json` | one key per pre-registered gate of that experiment with its scalar value **and** a `pass`/`fail` flag; `tests/test_gates.py` re-checks every gate from this file **without re-running** (G-REPO-8). Determinism: rerun reproduces scalars to ≤1e-12 relative (G-REPO-4) |
| AOR status ledger | ledger | `<run dir>/aor_status.json` (E0/E8) or `<run dir>/aor_ledger.json` (E1/E6) | every residual carries exactly one base status; **zero `unstatused`** (G-REPO-10, `plan/04` §6.4 F9). Carrier stratum recorded (`PreSB`→`RefStableAOR`→`CascadeStableAOR`→`AOR`) |

---

## 1. E0 — Synthetic demonstrations (`experiments/E0_synthetic/outputs/`)

Data-free sanity layer. All paths relative to `experiments/E0_synthetic/outputs/`. Source:
`plan/experiments/E0-synthetic-demos.md` §3, §6.

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E0-1 | Toy-1 RM-vs-β table | table | `tables/toy1_rm_vs_beta.csv` | columns `β, RM_max, RM_mean, δ_max`; **G-E0-1.2** `RM_max(β=0) ≤ 1e-10`, **G-E0-1.3** monotone↑ in β, **G-E0-1.5** `RM_max(2.0)/RM_max(0.5) ∈ [2.0,8.0]` |
| E0-2 | Toy-1 RM-vs-β figure | figure | `figures/fig_toy1_rm_vs_beta.png` | reproduces DE-precursor RM_max curve; β=0 point at zero, monotone rise |
| E0-3 | Toy-2 Q summary | table | `tables/toy2_Q_summary.csv` | cols `A_het, Q_peak, late_time_pos_fraction, max_abs_Q_homogeneous`; **G-E0-2.2** `Q_peak∈[1.0,2.5]` (precursor ≈1.74), **G-E0-2.3** late-time pos-accel fraction ≥0.95 |
| E0-4 | Toy-2 fit summary | table | `tables/toy2_fit_summary.csv` | per-model `{χ²_min,k,AIC,BIC,H₀,Ω_m,Ω_Λ,A,RMSE_{B\|A}}`; **G-E0-2.4** apparent `Ω_Λ∈[0.4,0.75]` & >0.2, **G-E0-2.5** homogeneous control `Ω_Λ<0.1`, **G-E0-2.7** OOS RMSE ratio M1/M2 ≥10 |
| E0-5 | Toy-2 mock distances | array | `arrays/toy2_mock_distances.npz` | keys `z, D_obs, σ, a_𝒟(t), H_𝒟(t), Var(H_i)(z), Q(t)`; finite, monotone `a_𝒟` |
| E0-6 | Toy-2 Q(t) figure | figure | `figures/fig_toy2_Q_vs_time.png` | homogeneous `Q≈0` vs heterogeneous `Q>0` overlay |
| E0-7 | Toy-2 distance-fit figure | figure | `figures/fig_toy2_distance_fit.png` | mock `D_L(z)` with matter-only / ΛCDM / rewrite overlays |
| E0-8 | Toy-3 w_eff-crossing table | table | `tables/toy3_weff_crossing.csv` | cols `z, rho_eff, dln_rho_dz, w_eff` + header `z_cross, eigenvalue spectrum`; **G-E0-3.1** w_eff crosses −1 (min<−1<max), **G-E0-3.3** `min ρ_eff>0`, **G-E0-3.4** `max Re(λ) ≤ +1e-10` |
| E0-9 | Toy-3 operator dump | array | `arrays/toy3_operator.npz` | keys `Ξ params, ρ_eff(z), w_eff(z), Jacobian, eigenvalues` |
| E0-10 | Toy-3 w_eff figure | figure | `figures/fig_toy3_weff.png` | `w_eff(z)` crossing −1 with eigenvalue inset (all Re λ ≤ 0) |
| E0-11 | Toy-4 route-recovery table | table | `tables/toy4_route_recovery.csv` | injected vs recovered `Ξ` params + rel-errors per model; **G-E0-4.1** rel-err ≤0.15 for `a0,a2,H_closed`, **G-E0-4.2** `BIC_null−BIC_SBT ≥10`, **G-E0-4.3** `BIC_nuisance−BIC_SBT ≥6`, **G-E0-4.5** holonomy_truth>0.3 & rel-err ≤0.25, **G-E0-4.6** null-control holonomy ≤0.05 |
| E0-12 | Toy-4 route-matrix dump | array | `arrays/toy4_route_matrix.npz` | `H₀^{(r,ℓ)}` true/noisy/SBT-fit/null-fit/nuisance-fit; loadings; holonomy loop |
| E0-13 | Toy-4 route-matrix figure | figure | `figures/fig_toy4_route_matrix.png` | 7×6 heatmap: null / noise / SBT-Ξ recovery |
| E0-14 | E0 gate summary | number | `summary.json` | all G-E0-1.*–G-E0-4.* scalars + flags; **G-E0-0.1** rerun reproduces scalars to `\|Δrel\|<1e-12` & arrays bitwise |
| E0-15 | E0 run manifest | manifest | `manifest.json` | **G-E0-0.2** `datasets == []` (data-free, asserted in `run.py`) |
| E0-16 | E0 AOR status | ledger | `aor_status.json` | **G-E0-0.3** zero `unstatused` entries (F9) |

---

## 2. E1 — DESI DR2 reproduction + minimal SBT geometry (`runs/E1/<run_id>/`, `results/`)

Blocking reproduction gate (E1-A) + first SBT add-on (E1-B). Source: `plan/experiments/E1-desi-dr2-reproduction.md` §4–§5.

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E1-1 | w₀–wₐ contour figure | figure | `results/figs/E1_w0wa_contour.{png,pdf}` | 68/95% contours C2–C5 overlaid on published DESI DR2; ΛCDM `(−1,0)` marked; **G-E1-REPRO-QUAD** MAP+68% region in `w0>−1, wa<0` quadrant, **G-E1-REPRO-CONTOUR** means within ±5%, widths within ±15% |
| E1-2 | H₀-by-model figure | figure | `results/figs/E1_H0_by_model.{png,pdf}` | derived H₀ per model×combination incl. inverse-ladder vs Planck-ΛCDM band |
| E1-3 | Parameter constraints | table | `results/tables/E1_parameters.csv` | `combination,model,param,mean,std,MAP,68%_low,68%_high`; **G-E1-REPRO-CONV** R̂−1<0.01, ESS>400 |
| E1-4 | (w₀,wₐ) headline | table | `results/tables/E1_w0wa.csv` | `combination,w0_mean,w0_std,wa_mean,wa_std,in_quadrant(bool)` |
| E1-5 | Significance/evidence ledger | table | `results/tables/E1_significance.csv` | `combination,dchi2_w0wa_vs_lcdm,n_sigma_dchi2,lnB_w0wa_vs_lcdm,lnB_err,n_sigma_band_ok(bool)`; **G-E1-REPRO-SIG-BAOCMB** C2 = 3.1σ±0.4, PolyChord lnZ err<0.3 |
| E1-6 | Per-block χ² | table | `results/tables/E1_chi2_blocks.csv` | `combination,model,chi2_{CMB,BAO,SN},chi2_total,dof,chi2_per_dof`; **G-E1-REPRO-CHI2** total within 5% of published, per-block χ²/dof∈[0.7,1.3] |
| E1-7 | Significance by SN compilation | table | `results/tables/E1_significance_by_sn.csv` | `sn_dataset,n_sigma,in_band[2.8,4.2](bool)`; **G-E1-REPRO-SIG-SN** each leg in 2.8–4.2σ, spread not collapsed (also `plan/03` G-DATA-9) |
| E1-8 | Inverse-ladder H₀ posterior | array+table | `results/tables/E1_inverse_ladder_H0.csv` + `results/E1/posteriors/inverse_ladder.npz` (mean, cov, optional thinned samples, each `sha256`) | route `r=(CMB+BAO→H₀)` for E4; committed compact posterior summary (NOT the ignored chain) consumed by E4's inverse-ladder; **G-E1-REPRO-CMBONLY** C1 H₀=67.4±0.5 within 1σ |
| E1-9 | Backend cross-check | table | `runs/E1/<run_id>/tables/backend_crosscheck.csv` | `model,w0_class,w0_camb,wa_class,wa_camb,dchi2`; **G-E1-REPRO-BACKEND** CLASS vs CAMB MAP within ±2% (and `plan/02` G-ENV-2) |
| E1-10 | Prior-sensitivity | table | `runs/E1/<run_id>/tables/prior_sensitivity.csv` | `prior_width,w0,wa,contour_shift_sigma`; widened-prior shift < 1σ |
| E1-11 | Compressed-vs-full BAO control | table | `runs/E1/<run_id>/tables/bao_full_vs_compressed.csv` | contour shift within `budgeted` tolerance (bounds fallback info loss; `plan/03` G-DATA-5) |
| E1-12 | Posterior triangles | figure | `runs/E1/<run_id>/figures/triangle_*.png` (+ `sn_residual`, `convergence`) | getdist triangles per combination×model |
| E1-13 | PolyChord evidence | number | `results/E1/posteriors/evidence_{C2,C3,C4,C5}.json` (each `sha256`) | `ln Z ± err` for ΛCDM and w₀wₐ; committed evidence summary backing **G-E1-REPRO-SIG-BAOCMB** (raw nested-sampler chains stay gitignored) |
| E1-14 | Posterior chains | array (ignored) | `runs/E1/<run_id>/chains/*.{txt,hdf5}` | gitignored byproduct (G-REPO-9), **no gate depends on it** (REGISTRY §7); getdist-reloadable |
| E1-15 | E1 run manifest | manifest | `runs/E1/<run_id>/manifest.json` | §0.3; **G-E1-REPRO-DET** rerun reproduces (w₀,wₐ) MAP + χ²_min to <1e-10 rel |
| E1-16 | E1 AOR ledger | ledger | `runs/E1/<run_id>/aor_ledger.json` | **G-E1-REPRO-AOR** all residuals statused, stratum `RefStableAOR`, no `unstatused` |
| E1-17 | E1 gate summary | number | `runs/E1/<run_id>/summary.json` | all `G-E1-REPRO-*` (+ `G-E1-SBT-*` for E1-B); covariance PD/cond<1e8 (**G-E1-REPRO-PD**); **G-E1-REPRO-NO-SBT** lint = zero SBT symbols in E1-A |
| E1-18 | E1-B coherence record | table | `results/xi_cosmo_coherence.csv` (E1 row) | fitted `K_L/K_M` amplitudes recorded; **G-E1-SBT-FIT** SBT χ²/dof ≤0.99× w₀wₐ with ≤3 extra params, **G-E1-SBT-OOS** SN OOS RMSE down >10% (a within-3% match is a floor/tie, not a pass — strict program OOS win is judged at `G-E8-OOS-DECISIVE`), **G-E1-SBT-DUAL** same (a0,a1,a2) improves both SN and BAO |

> **BLOCKING (locked).** No E1-B or E2–E8 artifact may be produced until every `G-E1-REPRO-*` flag in
> `runs/E1/<run_id>/summary.json` is green (`plan/experiments/E1` §0; `plan/00` §6).

---

## 3. E2 — Distance duality / local-global obstruction (`results/E2/`)

Source: `plan/experiments/E2-distance-duality.md` §6.

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E2-1 | η(z) audit ledger | array | `results/E2/eta_audit.hdf5` | `η(z), η(z)/η₀`, full cov, both calibration regimes, per SN compilation; **G-E2-CALIB** headline test on η(z) *shape* with `(M_B,r_d)` marginalized, amplitude reported separately |
| E2-2 | LG gluing defect | array+number | `results/E2/lg_gluing.npy` + json | `LG_{SN,BAO}` whitened value with F4 status |
| E2-3 | Model comparison | table | `results/E2/model_comparison.csv` | rows `{M₀,M₁,M₂,M₁₊₂,M_AM}` × `{χ²,χ²/dof,k,BIC,AIC,ΔBIC,w₀,wₐ,ε₀,a₂,OOS PPD}`; **G-E2-BIC** winning gluing/mixture OOS ΔBIC>5 vs {M₀,M₁}, **G-E2-RANK** M₂ ≤3 extra probe-shared params |
| E2-4 | Collapse-fraction record | number | `results/E2/w_a_collapse.json` | `F_collapse` + credible interval per SN compilation/regime (decision-verdict input) |
| E2-5 | F4 status verdict | ledger | `results/E2/f4_status.json` | exactly-one-of-four status (`OverlapInconsistent ⊻ CompatibleNonGlobal ⊻ GloballyAmbiguous ⊻ GloballyExact`) + `(Comp,image,fiber)` evidence + decision verdict (gluing/rewrite/mixture) |
| E2-6 | Posterior triangles | figure | `results/E2/triangle_*.png` | per-model getdist |
| E2-7 | E2 run manifests | manifest | `results/E2/manifests/*.json` | §0.3; **G-E2-REPRO** M₀/M₁ recover published DESI w₀wₐ + 2.8–4.2σ band, χ² within 5%, R̂<1.01/ESS>400 (must pass before any Ξ/η machinery) |
| E2-8 | AOR status entry | ledger | append `results/aor_status_table.csv` | typed E2 residual; **G-E2-SHAPE** η(z) shape correlated with SN-BAO residual (Spearman p<0.05) or rejects gluing reading; **G-E2-OOS** M₂/M₁₊₂ lowers held-out PPD by >3% |
| E2-9 | Coherence handoff | table+number | `results/coherence_ledger/E2.json` (+ `results/xi_cosmo_coherence.csv` E2 row) | `a₀,a₂` + implied `K_L/K_M` amplitudes+sign; **G-E2-COHERE** within 10× & consistent sign vs E1 (make-or-break) |

---

## 4. E3 — Phantom crossing with stable readout (`results/E3/`, `lean/`)

Formal centerpiece for P4. Source: `plan/experiments/E3-phantom-crossing.md` §6–§7.

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E3-1 | Construction witness (Leg A) | table | `results/E3/e3_construct_weff.csv` | cols `z, rho_eff, dln_rho_dz, w_eff`; header `z_cross, w_eff(0), w_eff(1.5), max_Re_eig, lambda_min_sym, min_rho_eff, c_eff2_min, stable_readout`; **G-E3-CONSTRUCT** w_eff<−1 over interval, crossing z_c∈[0,1.5], `min ρ_eff>0`, `lambda_min_sym≥−1e-8`, `max Re λ ≤ +1e-8` |
| E3-2 | Operator dump (Leg A) | array | `results/E3/e3_operator.npz` | `z, rho_eff, w_eff, Jacobian, eigenvalues, Xi_params` |
| E3-3 | Data reconstruction (B1) | array | `results/E3/e3_wz_reconstruction.hdf5` | reconstructed `w(z), ρ_DE(z)`, `z_c` posterior, crossing significance per SN compilation; **G-E3-REPRO** recovers published 2503.14743 w₀wₐ + crossing, χ² within 5% |
| E3-4 | Data SBT fit (B2/B3) | table | `results/E3/e3_data_fit.csv` | rows `{M₀,M₁,M_Ξ}` × `{χ²,χ²/dof,k,BIC,AIC,ΔBIC,a₀,a₁,a₂,z_c,max_Re_eig,lambda_min_sym,min_rho_eff,stable_readout}`; **G-E3-DATA** M_Ξ reproduces data z_c within 1σ + stable-readout cert, **G-E3-RANK** ≤3 extra params, no phantom-specific free param |
| E3-5 | False-positive control (B4) | table | `results/E3/e3_falsepos_mocks.csv` | per-mock crossing flag + aggregate false-positive rate; **G-E3-FALSEPOS** (Keeley 2506.15091) data significance exceeds non-crossing-mock band (~3.2% ref) |
| E3-6 | Bayesian-discipline record (B5) | number | `results/E3/e3_bayes_discipline.json` | global ΔBIC/evidence vs in-sample Δχ²; **G-E3-BAYES** (Dinda 2605.13546) crossing persists under global model comparison |
| E3-7 | OOS predictive record (B6) | number | `results/E3/e3_ppd.json` | `PPD_{BAO→SN}, PPD_{SN→BAO}` for M₀/M₁/M_Ξ; **G-E3-OOS** M_Ξ lowers ≥1 held-out PPD by >3% & beats every alternative beyond the combined uncertainty band (`≤`-best / within-3% is a floor/tie, not a pass; program OOS win at `G-E8-OOS-DECISIVE`) |
| E3-8 | z_c stability record (B3) | number | `results/E3/e3_zc_stability.json` | `σ(z_c)` under 1σ jitter; **G-E3-ZC-STAB** `σ(z_c)<0.1` |
| E3-9 | Posterior triangles | figure | `results/E3/triangle_*.png` | per-model getdist |
| E3-10 | w_eff figures | figure | `results/E3/fig_e3_weff_construct.png`, `fig_e3_weff_data.png` | crossing −1, eigenvalue-realpart inset (all ≤0), `ρ_eff>0` panel; data-fit w(z)/w_eff(z) |
| E3-11 | E3 run manifests | manifest | `results/E3/manifests/*.json` | §0.3; covariances PD/cond<1e8 (**G-E3-COV**); kernels linear in (a₀,a₁,a₂) to <1% (**G-E3-KERNEL**) |
| E3-12 | AOR status entry | ledger | append `results/aor_status_table.csv` | typed residual; carrier reaches `RefStableAOR` at E1–E3 leg, zero `unstatused` (F9). Honest negative (data require a ghost) statused `blocked` |
| E3-13 | Coherence handoff | table+number | `results/coherence_ledger/E3.json` (+ `results/xi_cosmo_coherence.csv` E3 row) | `a₀,a₁,a₂` + implied `K_L/K_M/K_G/K_S` amplitudes+sign + `z_c`; **G-E3-COHERE** within 10× & consistent sign vs E1 (make-or-break) |
| E3-14 | Lean P4 receipt | Lean | `lean/SbtCosmo/PhantomStableReadout.lean` + `lean.{toolchain,mathlib_rev,build}` in manifest | **G-E3-LEAN** `phantom_stable_readout_witness` compiles green under `lean --check` (no sorry/axiom/opaque); `#eval` witness matches Python z_c/sign at witness node (also Lean row T5, §8) |

---

## 5. E4 — Hubble route matrix and holonomy (`results/E4/`)

Central pillar per the idea.md UPDATE block. All paths under `results/E4/`. Source: `plan/experiments/E4-hubble-route-matrix.md` §(outputs).

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E4-1 | Route matrix table | table+array | `results/E4/E4_route_matrix.csv` / `.hdf5` | per-cell `(r,ℓ,H₀_mean,H₀_sigma,z_eff,recompute_flag,provenance)`; ≥7 routes × staging cols; **G-E4-0a** recomputed cells within 1σ_pub & 5% χ², non-recomputed match published (μ,σ); `plan/03` G-DATA-6 (≥6 routes, ≥1 closed loop) |
| E4-2 | Route matrix covariance | array | `results/E4/E4_matrix_covariance.npy` | `C_D` with shared-nuisance off-diagonals; **G-E4-0b** PD, cond<1e8, finite |
| E4-3 | Matrix heatmaps | figure | `results/E4/E4_matrix_heatmap.png`, `E4_residual_heatmap.png` | `H₀^{(r,ℓ)}` and `H₀^{(r,ℓ)}−H_closed(0)` |
| E4-4 | Model fits | number | `results/E4/E4_model_fits.json` | `χ²,χ²/dof,lnZ,BIC,AIC,WAIC/LOO`, params per model (null / per-route noise / SBT-Ξ) |
| E4-5 | Model comparison | number | `results/E4/E4_model_comparison.json` | `lnB_{SBT vs null}, lnB_{SBT vs noise}, ΔBIC, ΔWAIC`; **G-E4-1** SBT beats null (lnB≥5 ∧ ΔBIC≥10), **G-E4-2** SBT beats per-route noise (lnB≥5 ∧ ΔBIC≥6 ∧ ΔWAIC favors SBT), **G-E4-2-permutation** label-scramble drops lnB<2.5 in ≥95% of 1000 perms |
| E4-6 | Holonomy report | number | `results/E4/E4_holonomy.json` | per-loop `𝔥_γ` (KL nats **and** W₂), pre/post bridge internalization, protocol-trap verdict per loop; **G-E4-T3** ≥1 loop `𝔥_γ/σ_γ≥2` after internalization AND flat-control loop <0.5 (`plan/04` LP3 `𝔥_γ>0.1` nats) |
| E4-7 | Lawful-plurality tests | number | `results/E4/E4_lawful_plurality.json` | T1–T5 numeric results + pass/fail; **G-E4-T2** staging Pearson ρ≥0.5 (p<0.05) & sign agreement ≥70%, **G-E4-T5** leave-one-route-out predictive χ² improves ≥20% with genuine proxies vs ≤5% unrelated (LP1/LP2/LP5) |
| E4-8 | Residual-reuse cross-check | number | `results/E4/E4_residual_reuse.json` | joint `Ξ_cosmo` amplitudes E1/E2/E4/E5 + tension metrics; **G-E4-T4** amplitudes agree <2σ AND none differs >10× (LP4 / make-or-break) |
| E4-9 | F4 status + AOR ledger | ledger | `results/E4/E4_status_table.md` / `.json` | F4 verdict + AOR Status Table, every leg statused, zero `unstatused` |
| E4-10 | Posterior triangle | figure | `results/E4/E4_triangle.png` | M_SBT posterior (getdist) |
| E4-11 | E4 run manifest | manifest | `results/E4/E4_run_manifest.json` | §0.3 + cell list, loop list, audit-gate results; R̂<1.01/ESS>400 per cell (**G-E4-0b**) |
| E4-12 | Decisive (lawful-plurality) + route-reuse results | number | (in `summary.json` / `E4_model_comparison.json`) | **G-E4-DECISIVE** = (G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation) ∧ (G-E4-T1 ∧ G-E4-T2 ∧ G-E4-T3 ∧ G-E4-T4 ∧ G-E4-T5) — model-comparison ∧ **all five LP1–LP5** — all hold for the lawful-plurality positive result; the weaker **G-E4-ROUTEREUSE** (…∧ G-E4-T4 only, not all LP) is the `[E]`/partial route-reuse finding, NOT the lawful-plurality claim |
| E4-13 | Coherence handoff | table+number | `results/coherence_ledger/E4.json` (+ `results/xi_cosmo_coherence.csv` E4 row) | Hubble-route `Ξ_cosmo` `(a₀,a₁,a₂)` + implied kernel amplitudes+sign (from `E4_residual_reuse.json`); **G-E4-T4** within 10× & consistent sign vs E1/E2/E5 (REGISTRY §3 coherence member, make-or-break) |

---

## 6. E5 — Growth/staging sweep for S₈ (`results/E5/`)

Source: `plan/experiments/E5-growth-staging-S8.md` §(outputs).

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E5-1 | Reproduction record | table | `results/E5/repro_S8.csv` | published-vs-recovered `S₈/fσ₈/(μ₀,Σ₀)` per probe; **G-E5-REPRO** physical-CCL G₀ within quoted 1σ, R̂<1.01/ESS>400; **G-E5-BACKEND** pyccl-CLASS agreement (`plan/02` G-ENV-4: P(k)<1%, σ8<0.5%) — E5 blocked if fails |
| E5-2 | Staging-sweep ledger | array | `results/E5/staging_sweep.hdf5` | `a₁(ℓ_k), ΔS₈(ℓ_k), fσ₈` residuals, per-ℓ-bin χ², all axes×probes, common-staging variants |
| E5-3 | Staging-slope record | number | `results/E5/staging_slope.json` | `s_Ξ, s_Ξ^resid` + CIs per axis, `∂Ξ/∂ℓ` verdict; **D_scale verdict** `s_Ξ^resid≠0` at >2σ, reproducible across ≥2 physical-CCL probes, persists under common-staging |
| E5-4 | Cross-lens δχ heatmap | array+figure | `results/E5/cross_lens_dchi.{npy,png}` | directional `δχ_{B\|A}` localized by ℓ-bin/tomographic bin; model `G₂` (single Ξ) lowers cross-lens δχ by >5% vs `G₀` |
| E5-5 | Model comparison | table | `results/E5/model_comparison.csv` | rows `{G₀,G₁,G₂,G_sys,G_MG}` × `{χ²,χ²/dof,k,BIC,AIC,ΔBIC,a₁,β,S₈,σ8,OOS PPD}`; **G-E5-BIC** G₂ beats G₀ ΔBIC>5 when D_scale holds, **G-E5-RANK** ≤2 closure params, a₀ inherited (not refit), no per-probe Ξ_p |
| E5-6 | PPD record | number | `results/E5/ppd_geom_growth.json` | held-out `PPD_{geom→growth}` & reverse per model; **G-E5-OOS** G₂ lowers by >3% vs G₀ & beats every alternative beyond the combined uncertainty band (`≤`-best / within-3% is a floor/tie, not a pass; program OOS win at `G-E8-OOS-DECISIVE`); **G-E5-DUAL** inherited a₀+fitted a₁ improves both geometry & growth |
| E5-7 | D_scale verdict + status | ledger | `results/E5/d_scale_status.json` | §4.3 verdict + evidence + AOR status (valid honest `budgeted` vs true failure distinguished) |
| E5-8 | Surrogate cross-check | table+figure | `results/E5/surrogate_vs_physical.{csv,png}` | **G-E5-NOSURR** headline computed only from tier-1/2 physical-CCL legs; `G_surr` (DES Y3) reproduces precursor degeneracy AND physical CCL breaks it |
| E5-9 | Posterior triangles | figure | `results/E5/triangle_*.png` | per model/probe getdist |
| E5-10 | E5 run manifests | manifest | `results/E5/manifests/*.json` | §0.3 + backend tier per leg, pyccl/CLASS versions; kernels `K_G,K_S` linear in (a₀,a₁) to <1% & R[Ξ] positive+stable (**G-E5-KERNEL**) |
| E5-11 | AOR status entry | ledger | append `results/aor_status_table.csv` | typed growth residual + every systematic/backend descent |
| E5-12 | Coherence handoff | table+number | `results/coherence_ledger/E5.json` (+ append `results/xi_cosmo_coherence.csv` E5 row) | `a₁,β` + implied `K_G/K_S` amplitudes+sign; **G-E5-COHERE** within 10× & consistent sign vs E1 `K_L/K_M` (make-or-break) |

---

## 7. E6 — IDE as accounting shadow (`results/E6/`, `lean/`)

Source: `plan/experiments/E6-ide-accounting.md` §(outputs).

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E6-1 | IDE baseline chains + contours | array+figure | `results/E6/E6A_ide_chains.hdf5`, `E6A_contours.png` | `IDE_xiDE`/`SIDE` posteriors: `ξ,H₀,S₈,Q(z)` band |
| E6-2 | Reproduction table | table | `results/E6/E6A_repro_table.csv` | recovered vs published (2503.23225 / 2504.00994) `ξ,H₀`-tension σ, `S₈` + pass flags; **G-E6-REPRO-XI** ξ within 1σ (fail >2σ), **G-E6-REPRO-H0** tension→≈2.7σ within ±0.3σ, **G-E6-REPRO-CHI2** per-block χ² within 5% |
| E6-3 | Chart map + bg equivalence | array+figure | `results/E6/E6B_chartmap.hdf5`, `E6B_bg_overlay.png` | `Q_IDE(z)` vs `Q_Ξ(z)`; H(z)/distances overlay incl. CC points; `Δ_bg`; span defect; **G-E6-BG-Q** Q_Ξ matches Q_IDE RMS ≤20% (fail >30%), **G-E6-BG-HZ** within CC errors, **G-E6-BG-SPAN** out-of-span <20% (fail >50% ⇒ out_of_scope) |
| E6-4 | Growth-split decision | table+figure | `results/E6/E6C_growth.csv`, `E6C_fsigma8.png`, `E6C_S8.png` | `fσ₈^{IDE/Ξ}`/data, S₈ comparison, reducibility verdict, `(μ₀,Σ₀)`; **G-E6-GROWTH-RED** (Verdict A bridged) vs **G-E6-GROWTH-INT** (Verdict B real interaction); **G-E6-MUSIGMA** `\|μ_SBT−μ_GR\|<\|μ_IDE−μ_GR\|` |
| E6-5 | PPD held-out ledger | table | `results/E6/E6C_ppd.csv` | per-split held-out `δχ²` for SBT_Ξ/IDE/LCDM/w0wa; **G-E6-PPD** (reducibility / comparability to IDE — NOT a std-3 OOS win) SBT RSD within 10% of IDE on geometry→growth split (fail >15% worse); the strict program-level OOS win is judged only at `G-E8-OOS-DECISIVE` |
| E6-6 | Adequacy residual | number | `results/E6/E6C_adequacy.json` | `Ξ_C(Q\|Ξ)` value + blind-spot witness |
| E6-7 | E6 summary | number | `results/E6/summary.json` | all gate verdicts; **G-E6-COH** a₁ within 10× & consistent sign vs E1/E5 (violation ⇒ program fails phase), **G-E6-RANK** ≤3 free Ξ params, a₁ not refit; R̂<1.01/ESS>400, cov PD/cond<1e8, IDE continuity conserved to machine precision |
| E6-8 | AOR status entry | ledger | append `results/aor_status_table.csv` | **G-E6-STATUS** every residual+verdict exactly one base status (F9, none unstatused) |
| E6-9 | E6 run manifests | manifest | `results/E6/manifests/*.json` | §0.3, one per run |
| E6-10 | Lean chart-map receipt | Lean | `lean/SbtCosmo/IdeChartMap.lean` (target T-E6) | **G-E6-BG-LEAN [T]** continuity chart reproduces `ρ_de^eff` on grid; kernel linearity <1%; green `lake build`, no sorry/axiom |
| E6-11 | Coherence handoff | table+number | `results/coherence_ledger/E6.json` (+ `results/xi_cosmo_coherence.csv` E6 row) | coherence-locked `a₁` (+ implied `K_G/K_S` amplitude+sign) used in the reducibility test, NOT refit; **G-E6-COH** within 10× & consistent sign vs E1/E5 (REGISTRY §3 coherence member, make-or-break) |

---

## 8. E7 — Modified gravity as repair chart (`results/E7/`)

Source: `plan/experiments/E7-modified-gravity.md` §(outputs).

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E7-1 | MG reproduction record | table | `results/E7/repro_mg.csv` | published-vs-recovered `(μ₀,Σ₀), log₁₀\|f_R0\|` bound, `(w₀,wₐ)` per model; **G-E7-REPRO** μ₀=0.04±0.22, Σ₀=0.044±0.047 within 1σ, f(R) log₁₀\|fR0\|<−4.59 (95%), M_w w₀wₐ within ±5%, R̂<1.01/ESS>400; **G-E7-BACKEND** pyccl-CLASS (`plan/02` G-ENV-4) — E7 blocked if fails |
| E7-2 | Where-modification-lives record | number | `results/E7/musigma_prediction.json` | `M_Ξ`-inferred `(μ₀^SBT,Σ₀^SBT)` + CIs, GR-consistency test, M_Ξ-vs-M_w bg match; **G-E7-MUSIGMA (central)** M_Ξ reproduces DESI w(z) AND `\|μ₀^SBT\|<2σ_μ, \|Σ₀^SBT\|<2σ_Σ` |
| E7-3 | Shared-obstruction (F2) record | number | `results/E7/f2_repair_classification.json` | `RM_p, splitObs` overlap `\|△\|/\|splitObs\|` per MG model; **G-E7-F2** overlap <0.15 (M_Ξ and MG repair same obstruction) |
| E7-4 | MG stability certificates | number | `results/E7/mg_stability.json` | per-MG `max_λ Re λ`, min symmetrized eigenvalue; **G-E7-STABILITY** every admitted MG `max Re λ ≤0` (tol 1e-6) & min symm eig ≥−1e-8; failures logged `blocked` |
| E7-5 | MG-vs-Ξ necessity (OOS) | number | `results/E7/ppd_geom_growth.json` | held-out `PPD_{geom→growth}` per model; **G-E7-NECESSITY** MG required iff lowers OOS PPD by >15% (either direction logged); **G-E7-OOS** M_Ξ growth OOS within 15% of best MG (fail >20% worse) |
| E7-6 | Model comparison | table | `results/E7/model_comparison.csv` | rows `{M₀,M_w,M_Ξ,M_μΣ,M_fR,M_ST}` × `{χ²,χ²/dof,k,BIC,ΔBIC,AIC,w₀,wₐ,μ₀,Σ₀,f_R0,S₈,OOS PPD,stable?}`; **G-E7-RANK** M_Ξ ≤2 closure params, (μ,Σ)=(1,1) held, no per-probe Ξ_p |
| E7-7 | Repair-classification verdict | ledger | `results/E7/repair_verdict.json` | §4.5 verdict + evidence + AOR statuses (approved_other/blocked/moduli/nonclaim). MG not-preferred is logged, NOT a failure |
| E7-8 | Posterior triangles | figure | `results/E7/triangle_*.png` | per-model getdist; `(μ₀,Σ₀)` contour with GR `(0,0)` marked |
| E7-9 | E7 run manifests | manifest | `results/E7/manifests/*.json` | §0.3 + backend tier, pyccl/CLASS/MGCAMB versions; **G-E7-KERNEL** K_M,K_G,K_S linear <1% & R[Ξ] positive+stable; **G-E7-COV** each Σ PD/cond<1e8/finite |
| E7-10 | AOR status entry | ledger | append `results/aor_status_table.csv` | typed MG/SBT residuals + every blocked model/systematic/backend descent |
| E7-11 | Coherence handoff | table+number | `results/coherence_ledger/E7.json` (+ append `results/xi_cosmo_coherence.csv` E7 row) | `a₂`, MG `(μ₀,Σ₀,f_R0)`→effective-Ξ amplitude+sign, F2 verdict; **G-E7-COHERE** within 10× & consistent sign vs E1/E5 (make-or-break) |

> **Program-fail conditions (E7).** G-E7-MUSIGMA fail (Ξ forces non-GR (μ,Σ)), OR G-E7-COHERE fail, OR
> G-E7-OOS fail (>20% worse), OR an instability not logged `blocked`. MG simply not preferred is NOT a failure.

---

## 9. E8 — Global model competition (`results/tables/`, `results/figures/`, `experiments/E8_model_competition/outputs/`)

Strictly last. Source: `plan/experiments/E8-model-competition.md` §5, §8.

| # | Artifact | type | Committed path | Acceptance check |
|---|---|---|---|---|
| E8-1 | Master competition matrix | table | `results/tables/model_competition.csv` | 6 contenders `{M_Λ,M_w,M_η,M_Q,M_μΣ,M_Ξ}` × `{χ²,per-block-χ²,BIC,AIC,DIC,lnZ,lnB,per-leg-OOS,OOS_composite,PPC,staging,plurality,verdict}`; **G-E8-RANK** single Ξ_cosmo, ≤+3 minimal/≤+5–7 full params, kernels probe-shared & linear <1%; **G-E8-BIC** SBT-Ξ ΔBIC_vs_LCDM not worse than +5 vs best competitor |
| E8-2 | OOS battery | table | `results/tables/oos_battery.csv` | per (contender×leg): PPD, N_q, OOS_RMSE, fold/seed provenance + per-cell `verdict ∈ {win,tie,fail}`; **G-E8-OOS-DECISIVE (BINDING/std3, REGISTRY §8)** passes ONLY on a strict OOS **win** — SBT-Ξ better than **every** alternative on the primary OOS metric **beyond the combined uncertainty band AND after the complexity penalty**, with **no silent loss** on any critical leg (geometry/growth/Hubble); a **tie** (within the best alternative's uncertainty band) is **NOT a pass**, **fail** = loses overall or on any critical leg; **in-sample-only win = FAIL** |
| E8-3 | One-residual-nine-shadows | table | `results/tables/one_residual_nine_shadows.csv` | shadow map populated with measured per-row residuals (each row's specialist model vs SBT-Ξ) |
| E8-4 | AOR status master | ledger | `results/tables/aor_status_master.csv` | consolidated statuses across E0–E8, **zero `unstatused`** (F9); carrier reaches AOR target (CascadeStableAOR floor) |
| E8-5 | Decisive OOS figure | figure | `results/figures/model_competition_oos.{pdf,png}` | OOS_composite bar with E1-ΛCDM-baseline line + combined-uncertainty band of the best alternative, SBT-Ξ highlighted with its win/tie/fail verdict (the decisive figure; a strict OOS win is the only pass, REGISTRY §8) |
| E8-6 | Evidence vs complexity figure | figure | `results/figures/model_competition_evidence.{pdf,png}` | `lnB_{M/Λ}±err` vs Δk per contender, Jeffreys bands; **G-E8-EVID** `lnB_{Ξ/Λ}>1` (target >3) with σ_lnB, evidence ≥ ΛCDM & within 2σ of best |
| E8-7 | Per-leg OOS heatmap | figure | `results/figures/oos_battery_heatmap.{pdf,png}` | contender×leg OOS_RMSE color-scaled |
| E8-8 | PPC discrepancy heatmap | figure | `results/figures/ppc_discrepancy.{pdf,png}` | contender×(probe,z/ℓ-bin) standardized PPC residuals; **G-E8-PPC** reproduced-block p-values ∈[0.01,0.99], no catastrophic in-sample failure |
| E8-9 | Nine-shadows-closed figure | figure | `results/figures/nine_shadows_closed.{pdf,png}` | shadow map populated visually |
| E8-10 | E8 per-run outputs | manifest+number+ledger | `experiments/E8_model_competition/outputs/{manifest.json,summary.json,aor_status.json}` + `tables/`,`figures/`,`chains/` | §0.3; **G-E8-CONV** R̂−1<0.01/ESS>400, PolyChord lnZ err<0.3 & run-to-run scatter<0.3; **G-E8-COV** every block PD/cond<1e8/finite; **G-E8-DET** rerun reproduces likelihood/forward-model evaluations bitwise + committed summaries to a stated tolerance; chains validated by statistical equivalence (`R̂<1.01`, ESS, means/cov within MC error), NOT bitwise table identity across environments (REGISTRY §11.6) |
| E8-11 | Frozen-Ξ / stable-readout / deps assertions | number | (keys in `summary.json`) | **G-E8-FROZEN** SBT-Ξ read from coherence ledger, not re-tuned; **G-E8-STABLEREADOUT** phantom column carries E3's stable-readout certificate — at E8 the **no-growing-mode (S-stab)** component `max Re λ ≤0` is re-verified for the winner (P-dens/P-adeq established at E3; REGISTRY §11.2); **G-E8-COHERENCE** (make-or-break) cross-amplitudes within 10×, consistent sign; **G-E8-DEPS** all blockedBy artifacts present, every upstream `summary.json.terminal_state ∈ terminal_accepted = {PASS, ACCEPTED_NEGATIVE}` (REGISTRY §2; `BLOCKED`/`PROGRAM_FAIL` upstream ⇒ E8 cannot run), coherence gate green; **G-E8-REPRO** every contender χ²/dof<1.05 on reproduced blocks; **G-E8-STAGING & G-E8-PLURALITY** E5 staging + E4 plurality columns populated |

---

## 10. Cross-experiment program-level artifacts (`results/`)

These are written incrementally by E1–E8 and are the binding objects of the phase. They are the
make-or-break coherence and AOR record.

| # | Artifact | type | Committed path | Producing experiments | Acceptance check |
|---|---|---|---|---|---|
| X-1 | Coherence ledger | table | `results/xi_cosmo_coherence.csv` | E1-B, E2, E3, E4, E5, E6, E7 (one row each — all seven coherence members, REGISTRY §3); E8 reads | one row per contributing experiment with `(a₀,a₁,a₂[,β])` + implied kernel amplitudes + sign; **coherence gate (`plan/04` §9.4, `plan/00` §6.4)**: cross-amplitudes within 10×, signs agree, else **whole phase fails** |
| X-2 | Per-experiment coherence handoffs | number | `results/coherence_ledger/E{2,3,4,5,6,7}.json` | E2, E3, E4, E5, E6, E7 | each present with the experiment's `Ξ` amplitudes+sign (E4 from `E4_residual_reuse.json`/G-E4-T4; E6 the coherence-locked `a₁` reading, G-E6-COH); consumed by E4 (LP4) and E8 |
| X-3 | AOR status table (running) | ledger | `results/aor_status_table.csv` | E2, E3, E5, E6, E7 (append); E8 consolidates | every typed residual; carrier progression `RefStableAOR`→`CascadeStableAOR`; zero `unstatused` (G-REPO-10/F9) |
| X-4 | Residual-reuse coherence matrix | number/table | `results/E4/E4_residual_reuse.json` (+ `model_competition.csv` cols) | E4 (build), E8 (synthesize) | same Ξ reused across E1–E7; G-E4-T4 amplitudes <2σ & none >10× (`plan/01` G-REPO-15: per-probe kernel amplitudes agree within factor 10) |
| X-5 | Inverse-ladder H₀ handoff | array+table | `results/tables/E1_inverse_ladder_H0.csv` + `results/E1/posteriors/inverse_ladder.npz` (mean, cov, optional thinned samples, each `sha256`) | E1 (build), E4 (consume) | committed compact posterior summary (NOT an ignored chain) present and route-tagged `r=(CMB+BAO→H₀)` for E4 (`plan/03` G-DATA-6) |

---

## 11. Formal-foundations (math) deliverables — `plan/04`

These are **proof**-type artifacts: paper-grade results locked in `plan/04`, each graded `[T]`/`[C]`/`[E]`.
They are "produced" in the sense that the phase commits the locked statements (in `plan/04`) and the
numerical witnesses that discharge their empirical lift; their Lean realizations (where any) are §12 rows.
Acceptance for a `proof` row = the cited `plan/04` §9 gate holds on committed data.

| # | Result | type | Locked in | Acceptance check (`plan/04` §9 gate) |
|---|---|---|---|---|
| F-1 | Reconciliation Lemma (Schur ⇒ least-rewrite) | proof `[T]`/`[C]` | `plan/04` §1.2 | Schur identity sanity `Ξ_C⪰0` (min eig ≥−1e-8); reconciliation numerical check `J(Δ)=Schur energy` to <1% |
| F-2 | Exact-adequacy ⇒ no rewrite | proof `[T]` | `plan/04` §1.2(2) | FLRW-exact synthetic ⇒ `Ξ_C` Frobenius <1e-6 AND fit selects `Δ_SBT=0` (all `\|a_i\|<1e-3`) [verified in E0] |
| F-3 | Low-rank ansatz + kernel linearity | proof `[E]` | `plan/04` §3 | rank ceiling ≤ΛCDM+3 (minimal)/≤5–7 (full), no per-probe Ξ_p; kernels linear in (a₀,a₁,a₂) to <1% (finite-difference) |
| F-4 | Four-residual finite operational defs + metric d | proof `[T]`/`[E]` | `plan/04` §4 | every probe Σ PD/cond<1e8/finite; linear-control nulls `RM_p,δ_p<1e-6` of data variance (E0); nonlinear positivity `RM_p>0` |
| F-5 | P1 Descent-Repair (↔F2) | proof `[T]` | `plan/04` §6.1 | `RM_p>0 ⇒ splitObs≠∅` (unconditional) and the biconditional `splitObs≠∅ ⇔ RM_p>0` under (H-faithful); Lean row §12 T2/DescentRepair |
| F-6 | P2 No-Overread (↔F11) | proof `[C]` | `plan/04` §6.2 | numerical witness separates an `accessQ` fiber; cc-residual statused (`out_of_scope`/`bridged`); Lean row §12 (NoOverread scaffold) |
| F-7 | P3 Local-Global / CDDR (↔F4) | proof `[T]`/`[C]` | `plan/04` §6.3 | fitted η(z) carries exactly one of four F4 statuses (decided in E2); Lean row §12 T4 |
| F-8 | P4 Phantom stable-readout + stability audit | proof `[T]`/`[E]` | `plan/04` §6.4, §7 | three certificates P-dens (`ρ_eff>0`) ∧ P-adeq (`sym_C(R)⪰0↔Ξ_C⪰0`, = `lambda_min_sym≥0`) ∧ S-stab (`max Re λ(J)≤0`, no growing mode) AND `∃z w_eff<−1`; z_c stable <0.1 under 1σ (decided in E3); Lean row §12 T5 |
| F-9 | Hubble readout field, route models, holonomy 𝔥_γ, LP1–LP5 | proof `[T]`/`[E]` | `plan/04` §5 | LP1–LP5 gates (decided in E4); Lean row §12 T6 |
| F-10 | F9 No-Unstatused (meta) | proof `[T]` | `plan/04` §6.4, §8 | committed AOR status table has zero `unstatused`; carrier reaches CascadeStableAOR; Lean row §12 T7 |

---

## 12. Lean track deliverables — `plan/05` (`lean/`)

**Lean**-type artifacts. Acceptance is uniform: `lake build` green under pinned `lean-toolchain`
(`leanprover/lean4:v4.28.0`) + pinned `lake-manifest.json`, axiom-audit pass (closure ⊆ trust base),
**zero `sorry`/`admit`/`axiom`/`opaque`/`constant`**, and a coverage-table row with tier + scope line
(`plan/05` §6–§7 gates L1–L9). Each target is recorded in run manifests as `lean.{toolchain,mathlib_rev,build,axiom_audit}`.

| # | Lean declaration | Committed path | Tier | Mathlib? | Acceptance check (gate) |
|---|---|---|---|---|---|
| L-0a | toolchain pin | `lean/lean-toolchain` | — | — | exact `leanprover/lean4:v4.28.0` |
| L-0b | lakefile | `lean/lakefile.lean` | — | — | declares `SbtCosmo` (mathlib-free) + `SbtCosmoSchur` (mathlib) libs; `warningAsError`, `autoImplicit false` |
| L-0c | manifest pin | `lean/lake-manifest.json` | — | — | pins exact mathlib commit compatible with v4.28.0 |
| L-0d | trust base | `lean/manifests/trust_base.txt` | — | — | `{propext,Classical.choice,Quot.sound,choice,funext}`; **L4** every theorem closure ⊆ allowlist (mathlib-free ⊆ `{propext,Quot.sound}`) |
| L-0e | coverage table | `lean/manifests/coverage_table.md` | — | — | **L7** one row per declaration, tier + narrowing + scope disclaimer; 0 undisclosed narrowings |
| L-1 | T1 `SbtCosmo.Idempotence.{image_eq_fixedSet,delta_zero_iff_fixed}` | `lean/SbtCosmo/Idempotence.lean` | faithful | no | green; δ-defect packaging fixed points; non-vacuous E0 instance |
| L-2 | T2 `SbtCosmo.RouteMismatch.{route_mismatch_nonneg,…_zero_iff_commutes,…_pos_witness}` | `lean/SbtCosmo/RouteMismatch.lean` | faithful | no | green; **L6** RM>0 witness ≥2 states; structurally identical to E0 toy (P1) |
| L-3 | T3 `SbtCosmo.Schur.{adequacy_residual_psd,exact_adequacy_trivial_chain}` | `lean/SbtCosmo/Schur.lean` | PSD faithful / exact narrowed | **yes (only T3)** | green; PSD = `faithful`; exact-adequacy hard cycle deferred to paper-proof (`narrowed_surrogate` row) |
| L-4 | T4 `SbtCosmo.LocalGlobal.{globalizes_iff_in_image,four_status_classification}` | `lean/SbtCosmo/LocalGlobal.lean` | faithful (or narrowed if delegated) | no | green; F4 four-status, cosmological gluing-record instance (P3/E2) |
| L-5 | T5 `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness` | `lean/SbtCosmo/PhantomStableReadout.lean` | faithful (Gershgorin)/narrowed (Lyapunov) | no | green; **L6** witness ≥3 grid nodes, `S-stab (no-growing-mode) ∧ w_eff<−1` (the Lean witness proves the S-stab component + crossing; the full stable-readout certificate incl. P-dens/P-adeq is the E3 numerical check, REGISTRY §11.2); matches E3 z_c/sign (P4) |
| L-6 | T6 `SbtCosmo.Holonomy.{route_holonomy_nonzero,holonomy_current_trivial_predictive_nontrivial}` | `lean/SbtCosmo/Holonomy.lean` | faithful | no | green; **L6** ≥3 routes; route labels match E4 registry |
| L-7 | T7 `SbtCosmo.AORStatus.no_unstatused_residual` | `lean/SbtCosmo/AORStatus.lean` | faithful (or narrowed if delegated) | no | green; F9 well-formedness; instantiated on program residual registry |
| L-8 | Common base | `lean/SbtCosmo/Common.lean` | — | no | finite-carrier + `Defect` vocabulary; all targets compile against it |
| L-9 | T-E6 `SbtCosmo.IdeChartMap` (chart-map soundness) | `lean/SbtCosmo/IdeChartMap.lean` | faithful/narrowed | no | green; continuity chart reproduces `ρ_de^eff` on finite grid (E6 G-E6-BG-LEAN) |
| L-10 | README + receipts | `lean/README.md` | — | — | what each receipt certifies, scope disclaimers, target→P→E map |
| L-11 | Axiom-audit + CI T5 | (script + workflow) | — | — | **L1** build green both libs, **L2** zero sorry/admit + no `sorryAx`, **L3** zero project-local escapes, **L9** manifest records lean.{…}; CI T5 <15 min for mathlib-free set |

> **`SbtCosmo.Adequacy.reconciliation`** (the §1.2 Reconciliation Lemma Lean target, `plan/04` §1.2) is
> an **optional** stretch receipt that reuses the adequacy Schur lemmas; if delivered it is a `Lean`
> row analogous to L-3 (mathlib, faithful-PSD/narrowed for the hard direction). If not delivered, F-1
> remains a `proof`-grade paper result and its empirical lift is the E0/E1 reconciliation numerical check.

---

## 13. Master acceptance gate for the phase (the "definition of done" for this file)

The results-deliverable spec is satisfied iff **all** of the following hold (cross-checked against
`plan/00` §8, `plan/01` G-REPO-1…G-REPO-16, `plan/04` §9, `plan/05` L1–L9):

1. **Existence + format.** Every TRACKED row in §1–§12 exists at its committed path, is schema/format-valid
   for its `type` (figure renders; table has the declared header; number/array keys present; manifest
   schema-valid; ledger statused; Lean declaration present).
2. **Per-experiment gates.** Every `summary.json` (E0–E8) records every pre-registered gate of that
   experiment with a `pass`/`fail` flag, and every flag is re-derivable from committed artifacts **without
   re-running** (G-REPO-8). E1-A reproduction gates are green before any E1-B/E2–E8 artifact exists.
3. **Determinism.** Re-running from a manifest reproduces deterministic likelihood/forward-model evaluations
   bitwise and committed `summary.json` scalars to ≤1e-12 relative; MCMC/PolyChord chains are validated by
   statistical equivalence (`R̂<1.01`, ESS, means/cov within MC error), NOT bitwise identity across
   environments (only the E0 toy demos, no sampler, reproduce arrays bitwise) (`plan/00` determinism,
   REGISTRY §11.6; E0 G-E0-0.1, E8 G-E8-DET).
4. **Coherence (make-or-break).** `results/xi_cosmo_coherence.csv` and `results/coherence_ledger/E*.json`
   are populated; cross-amplitudes within 10× with consistent sign (`plan/04` §9.4 / `plan/00` §6.4 /
   `plan/01` G-REPO-15). A coherence break is a `PROGRAM_FAIL` (**whole-phase failure**), and must itself be statused.
5. **Out-of-sample decisive (std 3, REGISTRY §8).** `results/tables/oos_battery.csv` + `model_competition.csv` show
   `G-E8-OOS-DECISIVE` resolved to a strict OOS **win**: SBT-Ξ better than **every** alternative on the primary
   OOS metric **beyond the combined uncertainty band AND after the complexity penalty**, with **no silent loss**
   on any critical leg (geometry/growth/Hubble). A **tie** (within the best alternative's band) is NOT a pass;
   a loss overall or on any critical leg is a **fail**. An in-sample-only win is an explicit FAIL.
6. **AOR closure (F9).** `results/tables/aor_status_master.csv` has **zero `unstatused`** entries; the
   carrier reaches CascadeStableAOR (AOR target). Every pre-registered honest negative (P4 needs a ghost,
   holonomy flattens to artifact, MG not preferred) resolves to terminal state `ACCEPTED_NEGATIVE`
   (REGISTRY §2), is typed with a base status, and is reported with numbers; a coherence break is a
   `PROGRAM_FAIL` (whole-phase failure) that must itself be statused.
7. **Lean track.** L1–L9 all green: `lake build` green for both libraries under the pinned toolchain;
   zero `sorry`/`admit`/`axiom`/`opaque`/`constant`; axiom closures ⊆ trust base; P1(T2)+P4(T5) faithful;
   coverage table complete; structural alignment with `sbt_cosmo/` witnesses (L8).
8. **Unacceptable outcomes (always FAIL, never statusable).** An unreproduced published baseline; an
   `unstatused` residual at phase end; a gate relaxed after seeing results; a tracked chains blob under
   `**/outputs/chains/`; a dataset whose sha256 does not match its manifest (G-REPO-7).

---

## 14. Provenance crosswalk (where each row's spec comes from)

| Section | Source plan file(s) | Notes |
|---|---|---|
| §0 conventions | `plan/01` §7–§9, `GROUNDING_BRIEF` §III/V/VI | path layout, manifest schema, tracked-vs-ignored |
| §1 E0 | `plan/experiments/E0-synthetic-demos.md` §3, §6, §7 | data-free; verbatim output tree + G-gates |
| §2 E1 | `plan/experiments/E1-desi-dr2-reproduction.md` §4–§5 | runs/ tree + results/ headline artifacts; BLOCKING |
| §3 E2 | `plan/experiments/E2-distance-duality.md` §(outputs), §(gates) | F4 status + F_collapse + coherence handoff |
| §4 E3 | `plan/experiments/E3-phantom-crossing.md` §6–§7 | Leg A construction + Leg B data fit + Lean P4 |
| §5 E4 | `plan/experiments/E4-hubble-route-matrix.md` §(outputs) | route matrix + holonomy + LP tests + G-E4-DECISIVE |
| §6 E5 | `plan/experiments/E5-growth-staging-S8.md` §(outputs) | staging sweep + D_scale + surrogate cross-check |
| §7 E6 | `plan/experiments/E6-ide-accounting.md` §(outputs) | E6-A/B/C + Lean IdeChartMap |
| §8 E7 | `plan/experiments/E7-modified-gravity.md` §(outputs) | 6-model ladder + F2 + stability + necessity |
| §9 E8 | `plan/experiments/E8-model-competition.md` §5, §8 | master matrix + OOS battery + shadow map + AOR master |
| §10 cross-experiment | E1–E8 + `plan/04` §9.4 | coherence ledger, AOR running table, residual-reuse matrix |
| §11 formal | `plan/04-formal-foundations.md` §1–§9 | proof-grade results + their §9 gates |
| §12 Lean | `plan/05-lean-mechanization.md` §2–§8 | seven targets + T-E6 + manifests + CI |
| §13–§14 | `plan/00` §8, `plan/01` G-REPO-1…G-REPO-16, `plan/04` §9, `plan/05` L1–L9 | master done-criteria + crosswalk |
