# 07 — Consolidated Pass / Fail Gate Register

> **What this file is.** The single, consolidated, machine-readable register of *every* quantitative
> pass/fail gate in the Six Birds dark-energy-as-closure program. It aggregates the per-experiment
> gates from `plan/experiments/E0…E8-*.md`, restates the **five hard evidence standards** of
> `idea.md` §10 (operationalized into program-level gates), and enumerates the **pre-registered
> failure modes** (`idea.md` §10 standard 5). For every gate it gives: the **gate ID**, the **metric**,
> the **threshold**, the **experiment(s) it governs**, and the **source** (the plan file / `idea.md`
> section / GROUNDING_BRIEF section it is locked to).
>
> **Authority and consistency.** This file is *derived*, not *original*: it must remain byte-for-byte
> consistent with the thresholds locked in the experiment plans and the SHARED GROUNDING BRIEF. Where
> any future edit creates a discrepancy, **the per-experiment plan file and the GROUNDING_BRIEF win on
> the number** and this register must be reconciled. No threshold here may be relaxed after results are
> seen; a relaxation is a logged `budgeted` statused deviation in the run manifest (`plan/00` §6;
> `plan/04` §9). This register is the contract `tests/test_gates.py` (`plan/01` §6) checks against the
> committed `summary.json` of each experiment.
>
> **Read-order.** Locked upstream by: `plan/00-overview.md` (§6 phase gates, §6.2 five standards, §6.3
> per-experiment headline gates, §6.4 coherence gate, §8 done), `GROUNDING_BRIEF.md` (§I datasets,
> §III determinism, §VI audit gates), `plan/04-formal-foundations.md` (§9 quantitative gates, §3.1 rank
> ceiling, §9.4 coherence, §8 AOR), `plan/05-lean-mechanization.md` (L1–L9 Lean gates). Aggregates:
> all of `plan/experiments/E0…E8-*.md` §-gate sections. Science source of truth: `idea.md` §10.

---

## 0. How to read this register

- **Gate ID convention** (namespaced per REGISTRY §4). `G-<Exp>-<NAME>` for per-experiment gates
  (e.g. `G-E1-REPRO-QUAD`), `G-E0-0.x`/`G-E0-1.x`… for E0's local IDs (kept verbatim from the E0 plan,
  E0-namespaced here), `L1…L9` for Lean (`plan/05`), `G-REPO-1…G-REPO-16` for repo-structure (`plan/01`),
  `G-ENV-1…G-ENV-9` for environment (`plan/02`). Program-level standards are `STD-1…STD-5`. The single
  program-deciding gate is `G-E8-OOS-DECISIVE`.
- **Grade.** `[E]` empirical (decided by data), `[T]` theorem-grade (Lean / finite verified computation),
  `[C]` conditional/recognition-grade (`plan/04` §0).
- **Blocking semantics.** A gate marked **BLOCKING** must pass before downstream work proceeds; a
  failed blocking gate stops the relevant scope (an experiment, a leg, or the whole program). A gate
  marked **make-or-break** is the §6.4 coherence constraint: its failure fails the *entire phase*.
- **"FAIL is acceptable iff statused."** Per `plan/00` §8 and `plan/04` §9.6, an honest negative result
  (e.g. "phantom crossing required a ghost", "ΛCDM wins out-of-sample", "growth spread is a known
  systematic") is a *valid scientific outcome* provided it is reported with numbers and carries an AOR
  status. The *unacceptable* outcomes are: an unreproduced baseline, an `unstatused` residual at phase
  end (`thm:F9`), or a gate relaxed after the fact.

---

## 1. The five hard evidence standards (`idea.md` §10 → program gates STD-1…STD-5)

These are the program-level standards every experiment is measured against (`idea.md` §10; restated in
`plan/00` §6.2). Each is operationalized into a concrete, pre-registered, quantitative gate.

| ID | Standard (`idea.md` §10) | Operational metric | Threshold | Governs | Source |
|---|---|---|---|---|---|
| **STD-1** | **Reproduce standard results first** | published baseline `χ²`/contour recovered with *zero* SBT machinery, before any `Ξ` object is added | per-block `χ²` within **5%** of published; `χ²/dof < 1.05` on baseline blocks; recovered contours within E1 tolerance; `R̂−1<0.01`, ESS>400 | E1 (gate), E2/E3/E5/E6/E7 reproduction legs, E8 floor | `idea.md` §10.1; `plan/00` §6.1; GB §VI(2,3) |
| **STD-2** | **Use one low-rank residual** | total SBT free parameters; per-probe correction check | `≤ ΛCDM+3` (minimal ansatz), `≤ +5–7` (full carrier); **no probe-specific free `Ξ_p`**; kernels probe-shared and linear in `(a₀,a₁,a₂)` to `<1%` | all SBT legs (E1-B…E8); enforced by every `G-*-RANK` and `G-*-KERNEL` | `idea.md` §10.2; `plan/00` §6.2; `plan/04` §3.1, §9.2 |
| **STD-3** | **Win out-of-sample** | leave-one-probe-out BIC-penalized whitened OOS RMSE / `PPD_{p→q}` | a **strict `win`** on the primary OOS metric — SBT-`Ξ` better than **every** alternative by **more than the combined uncertainty band** and after the complexity penalty, with **no silent loss** on any critical leg (geometry, growth, Hubble). A **`tie`** (within the band of the best alternative) is **NOT a pass**; an in-sample-only win is a **FAIL** | E1-B, E2, E3, E5, E6, E7 OOS legs; **decisive at E8** (`G-E8-OOS-DECISIVE`) | `idea.md` §10.3; `plan/00` §6.2; `plan/04` §4.4, §9.3 |
| **STD-4** | **Show staging fingerprints** | structured (not white-noise) parameter variation across scale-cut / z-binning / route sweeps | low-frequency spectral power **>2×** the null trajectory **OR** `ΔBIC(SBT staging − null) > 10` (strong) / `> 5` (moderate); E4 lawful-plurality + E5 `D_scale` verdicts populated and structured | E4 (lawful plurality), E5 (staging fingerprint); corroboration at E8 | `idea.md` §10.4; `plan/00` §6.2; `plan/04` §8.2 |
| **STD-5** | **Pre-register failure modes** | all E0–E8 failure conditions (§7 here) checked and reported with numbers, pass or fail | 100% of pre-registered failure modes evaluated and recorded in `summary.json`; none relaxed post-hoc | all experiments | `idea.md` §10.5; `plan/00` §6.2 |

---

## 2. Phase-level gates (`plan/00` §6.1, §6.4)

### 2.1 Reproduction gates (BLOCKING — must pass *before* any SBT object is added)

| Gate | Metric | Threshold | Governs | Source |
|---|---|---|---|---|
| `G-PHASE-LCDM` | baseline ΛCDM fit quality | `χ²/dof < 1.05` on Planck 2018 TT/TE/EE + DESI DR2 BAO | E1 (and every reproduction leg) | `plan/00` §6.1; GB §VI(3) |
| `G-PHASE-W0WA` | DESI DR2 `(w₀,w_a)` recovery | recovered contours within **±5%** of published (arXiv:2503.14738) | E1, E2, E3 reproduction | `plan/00` §6.1; `idea.md` §6 E1 |
| `G-PHASE-CHI2` | likelihood agreement | computed `χ²_total` within **5%** of published reference per probe block | all real-data experiments | `plan/00` §6.1; GB §VI(3) |
| `G-PHASE-CONV` | MCMC convergence | Gelman–Rubin `R̂ < 1.01` on all sampled params; ESS `> 400`/chain | all MCMC experiments | GB §III.C, §VI(2) |
| `G-PHASE-COV` | covariance sanity | symmetric, positive-definite, condition number `< 10⁸`, all entries finite | all experiments with a covariance | GB §VI(1) |
| `G-PHASE-DET` | determinism | (a) deterministic likelihood / forward-model evaluations (bitwise reproducible given fixed inputs); (b) committed posterior summaries reproduced to a stated tolerance (`<1e-12` rel scalar ε). Sampler chains are **not** required bitwise-identical across environments — they are validated by **statistical equivalence** (parameter means/covariance within MC error; `R̂ < 1.01`; ESS thresholds). Only the E0 toy demos (no sampler) are bitwise reproducible | ≥1 experiment per phase | GB §III.A; `plan/00` §8(8) |

### 2.2 The coherence gate (make-or-break — failure fails the **entire phase**)

| Gate | Metric | Threshold | Governs | Source |
|---|---|---|---|---|
| **`G-PHASE-COHERENCE`** | cross-experiment consistency of the *single* `Ξ_cosmo` | the same `Ξ` reused across E1–E7; cross-amplitudes within **10×** and **consistent sign** (e.g. E5 `K_S` vs E1 `K_L/K_M`; E2 `a₂`; E3 `(a₀,a₁,a₂)`; E4 `{a₀,a₁,a₂}`; E6 `a₁`; E7 effective-`Ξ`). **If any experiment's fitted `Ξ` is mutually inconsistent with another (>10× amplitude or sign disagreement), the whole program fails the phase.** | E1↔E2↔E3↔E4↔E5↔E6↔E7↔E8 (residual-reuse) | `plan/00` §6.4; `plan/04` §9.4; `idea.md` §3 ("if each probe needs an unrelated `Ξ_p`, Six Birds fails") |

### 2.3 AOR / Lean phase gates

| Gate | Metric | Threshold | Governs | Source |
|---|---|---|---|---|
| `G-PHASE-AOR` | No Unstatused Residual (`thm:F9`) | every surviving tension typed with exactly one base status; **zero `unstatused`** entries at phase end | all experiments; consolidated at E8 | `plan/00` §7; `plan/04` §8; GB §VI |
| `G-PHASE-CARRIER` | AOR carrier progression | `PreSB → RefStableAOR (E1–E3) → CascadeStableAOR (E4–E7) → AOR (E8)`; phase-end floor = CascadeStableAOR | E1–E8 | `plan/00` §7; `plan/04` §8.4 |
| `G-PHASE-LEAN` | Lean mechanization compiles | P1–P4 Lean artifacts compile under `lean --check`; no `sorry`/`admit`/`axiom`/`opaque`/`constant`; trust base within allowlist | P1–P4 (E0/E1/E2/E3 anchors) | `plan/00` §8(5); `plan/05` L1–L9 |

---

## 3. E0 — Synthetic data-free demonstrations (BLOCKING for E1/E3/E4)

> E0 passes **iff all G-gates pass**. Gate IDs verbatim from `plan/experiments/E0-synthetic-demos.md` §8.
> All are `[E]`/`[T]` deterministic (no sampler). `plan/04` P4 finite witness lives here (Toy 3).

### 3.1 Toy 1 — route mismatch vs nonlinearity

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E0-1.1` | idempotence defect `δ_max` (all β) | `≤ 1e-10` | E0 §8.1 |
| `G-E0-1.2` | route mismatch `RM_max` at `β=0` (linear control) | `≤ 1e-10` (numerically zero) | E0 §8.1 |
| `G-E0-1.3` | `RM_max` monotone in β | strictly increasing across β-grid | E0 §8.1 |
| `G-E0-1.4` | `RM_max` at `β∈{0.5,2.0}` | both `> 1e-3` | E0 §8.1 |
| `G-E0-1.5` | nonlinearity scaling | `RM_max(2.0)/RM_max(0.5) ∈ [2.0, 8.0]` (precursor ≈3.99) | E0 §8.1 |

### 3.2 Toy 2 — null-Λ generator → apparent `Ω_Λ`

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E0-2.1` | homogeneous control `max|Q|` (`A_het=0`) | `≤ 1e-6` | E0 §8.2 |
| `G-E0-2.2` | heterogeneous `Q_peak` (`A_het=0.6`) | `> 1.0`, band `[1.0, 2.5]` (precursor ≈1.74) | E0 §8.2 |
| `G-E0-2.3` | late-time positive-acceleration fraction | `≥ 0.95` (precursor ≈0.988) | E0 §8.2 |
| `G-E0-2.4` | apparent `Ω_Λ` from null-Λ ΛCDM mis-fit | `∈ [0.4, 0.75]` **and** `> 0.2` (precursor ≈0.60) | E0 §8.2 |
| `G-E0-2.5` | ΛCDM control on homogeneous generator | recovered `Ω_Λ < 0.1` (no spurious DE) | E0 §8.2 |
| `G-E0-2.6` | rewrite (M2) in-sample vs ΛCDM (M1) | `|χ²_M2−χ²_M1|/n_z ≤ 0.1` with `k_M2 ≤ k_M1+1` | E0 §8.2 |
| `G-E0-2.7` | out-of-sample heterogeneity-proxy prediction | `RMSE_{B|A}(M1)/RMSE_{B|A}(M2) ≥ 10` (precursor ~100×) | E0 §8.2 |

### 3.3 Toy 3 — phantom crossing with stable readout (P4 witness)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E0-3.1` | `w_eff` genuine crossing | `min(w_eff) < −1 < max(w_eff)`; endpoints on opposite sides | E0 §8.3 |
| `G-E0-3.2` | single crossing | sign-change count of `(w_eff+1)` over grid `= 1`; `z_cross ∈ (0, z_max)` | E0 §8.3 |
| `G-E0-3.3` | positive native currency | `min_z ρ_eff(z) > 0` | E0 §8.3 |
| `G-E0-3.4` | stable operator (no growing mode) | `max_z max_j Re(λ_j(z)) ≤ 0` (tol `+1e-10`) | E0 §8.3 |
| `G-E0-3.5` | perturbation proxy (advisory) | `c_eff²_min ≥ −1e-8` (recorded, non-blocking) | E0 §8.3 |
| `G-E0-3.6` | crossing robust to grid refinement | doubling `n_z` keeps `z_cross` stable to `|Δ|≤1e-2`, preserves `G-E0-3.4` | E0 §8.3 |

### 3.4 Toy 4 — Hubble route matrix + holonomy recovery (E4 rehearsal)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E0-4.1` | `Ξ_inj` parameter recovery | each of `a0_relerr, a2_relerr, Hclosed_relerr ≤ 0.15` | E0 §8.4 |
| `G-E0-4.2` | null model rejected | `BIC_null − BIC_SBT ≥ 10` | E0 §8.4 |
| `G-E0-4.3` | low-rank beats per-route nuisance | `BIC_nuisance − BIC_SBT ≥ 6` (lawful plurality) | E0 §8.4 |
| `G-E0-4.4` | SBT residual vs injected noise | reduced `χ²_SBT ∈ [0.5, 1.5]` | E0 §8.4 |
| `G-E0-4.5` | Hubble holonomy nonzero & recovered | `holonomy_truth > 0.3` km/s/Mpc; `|holonomy_SBT−truth|/truth ≤ 0.25` | E0 §8.4 |
| `G-E0-4.6` | holonomy null control | `Ξ_inj=0` run: `holonomy_null ≤ 0.05` km/s/Mpc | E0 §8.4 |

### 3.5 E0 cross-cutting

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E0-0.1` | determinism | rerun reproduces scalars to `|Δrel|<1e-12`, arrays bitwise | E0 §8.5 |
| `G-E0-0.2` | data-free | `manifest.datasets == []` | E0 §8.5 |
| `G-E0-0.3` | AOR completeness (F9) | zero `unstatused` entries | E0 §8.5 |
| `G-E0-0.4` | runtime budget | wall `< 2 h` on 8 CPU, peak mem `< 4 GB` | E0 §8.5 |
| `G-E0-0.5` | artifacts emitted | the 5 figures + 5 tables exist and are non-empty | E0 §8.5 |

---

## 4. E1 — DESI DR2 reproduction + first SBT add-on

> `G-E1-REPRO-*` are **BLOCKING for the entire program** (`plan/00` §6.1): no E1-B, no E2–E8 until all
> are green. Gate IDs verbatim from `plan/experiments/E1-desi-dr2-reproduction.md` §4.

### 4.1 Reproduction gates — E1-A (BLOCKING for the whole program)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E1-REPRO-QUAD` | `(w₀,w_a)` quadrant | C2–C5 MAP + 68% region in `w₀>−1, w_a<0` | E1 §4.1 |
| `G-E1-REPRO-CONTOUR` | contour recovery | `(w₀,w_a)` means within **±5%** of published; interval widths within **±15%** | E1 §4.1 |
| `G-E1-REPRO-SIG-BAOCMB` | C2 dynamical-DE significance | **3.1σ ± 0.4σ** (fail if `<2.5` or `>3.7`) | E1 §4.1 |
| `G-E1-REPRO-SIG-SN` | C3/C4/C5 per-SN-leg significance | spread within **[2.8, 4.2]σ** (fail if any outside [2.5,4.5] or spread collapses) | E1 §4.1 |
| `G-E1-REPRO-CMBONLY` | C1 ΛCDM CMB-only | `H₀ = 67.4 ± 0.5` within 1σ; Planck `χ²` within 5% | E1 §4.1 |
| `G-E1-REPRO-CHI2` | total / per-block `χ²` | total within **5%** of published; per-block `χ²/dof ∈ [0.7, 1.3]` | E1 §4.1 |
| `G-E1-REPRO-CONV` | convergence | `R̂−1 < 0.01` all params; ESS `>400`/chain; PolyChord `ln Z` err `< 0.3` | E1 §4.1 |
| `G-E1-REPRO-PD` | covariance | PD, condition `<1e8`, finite | E1 §4.1 |
| `G-E1-REPRO-DET` | determinism | rerun reproduces `(w₀,w_a)` MAP + `χ²_min` to `<1e-10` rel | E1 §4.1 |
| `G-E1-REPRO-BACKEND` | backend / prior robustness | CLASS vs CAMB MAP within **±2%**, `Δχ²<0.5`; prior-widening shifts contour `<1σ` | E1 §4.1 |
| `G-E1-REPRO-NO-SBT` | anti-leakage lint | **zero** SBT symbols (`Ξ_cosmo`/`a₀–a₂`/`K_*`/`Δ_SBT`/`H₀^{(r,ℓ)}`) in E1-A code path | E1 §4.1, §1.3 |
| `G-E1-REPRO-AOR` | AOR ledger | present, all residuals statused, stratum `RefStableAOR`, no `unstatused` | E1 §4.1 |

### 4.2 First-SBT gates — E1-B (post-gate; blocking for the E1 headline)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E1-SBT-FIT` | SBT in-sample fit (C3) | `χ²/dof ≤ 0.99 ×` the w₀w_a baseline with `≤3` extra params | E1 §4.2 |
| `G-E1-SBT-OOS` | SBT out-of-sample (train BAO+CMB, predict SN) | **win/tie/fail** on SN OOS RMSE vs the best alternative; **win** = SN OOS RMSE ↓ `>10%` vs ΛCDM beyond the combined uncertainty band (matching w₀w_a within **3%** is a **floor**, not a pass — a **tie**) | E1 §4.2 |
| `G-E1-SBT-DUAL` | anti-fudge dual improvement | same `(a₀,a₁,a₂)` improves **both** SN and BAO blocks (neither worsened) | E1 §4.2 |
| `G-E1-SBT-COHERENCE` | coherence handoff | fitted `K_L/K_M` amplitudes written to `results/xi_cosmo_coherence.csv` | E1 §4.2 |

---

## 5. E2 — Distance duality as local–global obstruction

> Gate IDs verbatim from `plan/experiments/E2-distance-duality.md` §8. F4 status assignment is the
> verdict; the gluing reading *failing* yields a valid **rewrite-residual** verdict (not a program fail).

### 5.1 Reproduction / data / metric

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E2-REPRO` | DESI reproduction (BLOCKING) | M₀/M₁ recover published `w₀w_a` contour + 2.8–4.2σ DE band; `χ²_SN`/`χ²_BAO` within **5%**; `R̂<1.01`, ESS>400 | E2 §8.1 |
| `G-E2-COV` | covariances | Pantheon+ `C_μμ` + DESI BAO cov PD, cond `<1e8`, finite | E2 §8.2 |
| `G-E2-RECON` | section reconstruction | reproduces each probe's distances within 1σ on native grid before shared-grid mapping | E2 §8.2 |
| `G-E2-CALIB` | calibration handling | headline CDDR test on `η(z)` **shape** with `(M_B,r_d)` marginalized; `η₀` amplitude reported separately, never as a violation | E2 §8.2 |

### 5.2 Four-status / decision gates (the heart of E2)

| Gate / status | Metric | Threshold | Source |
|---|---|---|---|
| `OverlapInconsistent` | `η=η₀(1+ε₀g(z))` slope | `ε₀ ≠ 0` at **>2σ**, robust across `g(z)∈{z, ln(1+z)}` | E2 §8.3 |
| `Comp(a)` holds (flat) | `|ε₀|/σ(ε₀)` | `< 2` for both `g(z)` forms | E2 §8.3 |
| `GloballyExact` | single-FLRW joint fit | `χ²/dof ≤ 1.05` and unique completion (`|R⁻¹(a)|=1`) | E2 §8.3 |
| `CompatibleNonGlobal` | flat `η`, no global FLRW | no single FLRW gives `χ²/dof ≤ 1.05` | E2 §8.3 |
| `GloballyAmbiguous` | fiber cardinality | multiple completions within `Δχ²<1` (`|R⁻¹(a)|>1`) | E2 §8.3 |
| Decision: gluing-residual | collapse fraction `F_collapse` (eq. E2.2) | `F_collapse > 0.5` **and** F4 ∈ {OverlapInconsistent, CompatibleNonGlobal} | E2 §8.4 |
| Decision: rewrite-residual | `F_collapse` | `F_collapse < 0.3` **and** F4 ∈ {GloballyExact, CompatibleNonGlobal} | E2 §8.4 |
| Decision: mixture | `F_collapse` / model comparison | `0.3 ≤ F_collapse ≤ 0.5`, **or** M₁₊₂ beats both M₁ and M₂ by `ΔBIC>5` | E2 §8.4 |

### 5.3 SBT-claim gates

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E2-OOS` | out-of-sample | **win/tie/fail** vs the best competitor; **win** = M₂/M₁₊₂ lowers held-out `PPD_{BAO→SN}`/`PPD_{SN→BAO}` by **>3%** vs ΛCDM and beats every alternative beyond the combined uncertainty band (being `≤` best competitor / within 3% of it is a **floor**, scored a **tie**, not a pass) | E2 §8.5 |
| `G-E2-BIC` | model competition | winning gluing/mixture model OOS `ΔBIC > 5` vs {M₀,M₁} when gluing verdict holds | E2 §8.5 |
| `G-E2-SHAPE` | residual correlation | `η(z)` shape correlated with SN–BAO joint residual (Spearman `p<0.05`); uncorrelated (`p>0.05`) rejects gluing reading | E2 §8.5 |
| `G-E2-RANK` | anti-fudge rank | M₂ uses `≤3` extra params, probe-shared shapes, no per-probe free `Ξ_p` | E2 §8.5 |
| **`G-E2-COHERE`** | coherence (make-or-break) | E2 `a₂` and `K_L/K_M` amplitudes within **10×** and consistent sign with E1 geometry `Ξ` | E2 §8.5; `plan/00` §6.4 |

---

## 6. E3 — Phantom crossing with stable readout (P4 centerpiece)

> Gate IDs verbatim from `plan/experiments/E3-phantom-crossing.md` §9. `G-E3-CONSTRUCT` + `G-E3-LEAN`
> are the **theorem-grade centerpiece** satisfying `idea.md` §6 Exp3.

| Gate | Metric | Threshold | Grade | Source |
|---|---|---|---|---|
| `G-E3-COV` | covariances | DESI BAO + Pantheon+ PD, cond `<1e8`, finite | [E] | E3 §9.1 |
| `G-E3-KERNEL` | kernel linearity | `K_L,K_M,K_G,K_S` linear in `(a₀,a₁,a₂)` to `<1%` (finite-difference) | [E] | E3 §9.1 |
| `G-E3-REPRO` | DESI reproduction (BLOCKING) | M₀/M₁ recover published DESI 2503.14743 `w₀w_a` contour + phantom-crossing preference; `χ²` within **5%**; `R̂<1.01`, ESS>400 | [E] | E3 §9.2 |
| **`G-E3-CONSTRUCT`** | **the construction (centerpiece)** | leg-A operator satisfies **all four**: (1) `w_eff<−1` over an interval, genuine crossing `z_c∈[0,1.5]`; (2) `min_z ρ_eff > 0`; (3) `λ_min^{sym} ≥ −1e-8`; (4) `max_z max_j Re(λ_j) ≤ +1e-8` | [T] | E3 §9.3 |
| **`G-E3-LEAN`** | finite witness compiles | `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness` compiles green (`lean --check`, no `sorry`/`axiom`/`opaque`); `#eval` matches Python `z_c`/sign at witness node | [T] | E3 §9.3; `plan/05` T5 |
| `G-E3-DATA` | data crossing realized by stable-readout operator | fitted `M_Ξ` reproduces data-preferred `z_c` within 1σ **and** passes stable-readout certificate (`max Re λ ≤ 0`, `λ_min^{sym} ≥ 0`, `min ρ_eff > 0`) | [E] | E3 §9.4 |
| `G-E3-ZC-STAB` | crossing-redshift stability | `σ(z_c) < 0.1` in z under 1σ posterior jitter | [E] | E3 §9.4 |
| `G-E3-FALSEPOS` | Keeley false-positive control (2506.15091) | data crossing significance **exceeds** non-crossing-mock false-positive band (≈3.2% reference) | [E] | E3 §9.5 |
| `G-E3-BAYES` | Dinda global-Bayesian control (2605.13546) | crossing preference persists under global `ΔBIC`/evidence, not in-sample `Δχ²` alone | [E] | E3 §9.5 |
| `G-E3-OOS` | out-of-sample | **win/tie/fail** vs the best competitor; **win** = `M_Ξ` lowers held-out `PPD_{BAO→SN}`/`PPD_{SN→BAO}` by **>3%** vs ΛCDM and beats every alternative beyond the combined uncertainty band (being `≤` best competitor / within 3% of it is a **floor**, scored a **tie**, not a pass) | [E] | E3 §9.5 |
| `G-E3-RANK` | anti-fudge rank | `M_Ξ` uses `≤3` extra params, probe-shared shapes, **no phantom-specific free parameter** | [E] | E3 §9.5 |
| **`G-E3-COHERE`** | coherence (make-or-break) | E3 `(a₀,a₁,a₂)` + implied `K_L/K_M/K_G/K_S` within **10×** and consistent sign with E1 geometry `Ξ` | [E] | E3 §9.5; `plan/00` §6.4 |

---

## 7. E4 — Hubble route matrix and Hubble holonomy

> Gate IDs from `plan/experiments/E4-hubble-route-matrix.md` §6 (namespaced `G-E4-*` per REGISTRY §4).
> The decisive positive (lawful-plurality) result is `G-E4-DECISIVE = (G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation) ∧ (G-E4-T1 ∧ G-E4-T2 ∧ G-E4-T3 ∧ G-E4-T4 ∧ G-E4-T5)` — model-comparison **∧ all five LP1–LP5** (E4 §6.D, REGISTRY §11.5). The weaker `G-E4-ROUTEREUSE = (G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation ∧ G-E4-T4)` is the `[E]`/partial route-reuse finding, **not** the lawful-plurality claim.

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E4-0a` | reproduction (BLOCKING) | each recomputed cell within `1σ_pub` and 5% `χ²` of published; non-recomputed cells match published `(μ,σ)` | E4 §6.A |
| `G-E4-0b` | convergence + covariance | `R̂<1.01`, ESS>400/cell; `C_D` PD, cond `<1e8`, finite | E4 §6.A |
| `G-E4-1` | SBT beats null | `ln B_{SBT vs null} ≥ 5` **and** `ΔBIC(null−SBT) ≥ 10` **and** `χ²/dof_SBT < χ²/dof_null` | E4 §6.B |
| `G-E4-2` | SBT beats per-route noise (core) | `ln B_{SBT vs noise} ≥ 5` **and** `ΔBIC(noise−SBT) ≥ 6` **and** `ΔWAIC` favors SBT | E4 §6.B |
| `G-E4-2-permutation` | permutation control | scrambling route labels drops `ln B_{SBT vs noise}` below 2.5 in `≥95%` of 1000 permutations | E4 §6.B |
| `G-E4-T1` | route structure | `G-E4-2` ∧ `G-E4-2-permutation` pass | E4 §6.C |
| `G-E4-T2` | staging structure | measured vs predicted staging slopes Pearson `ρ ≥ 0.5` (`p<0.05`); sign agreement `≥70%` (recomputed cells only) | E4 §6.C |
| `G-E4-T3` | holonomy | `≥1` loop has `𝔥_γ/σ_γ ≥ 2` **after** protocol-trap internalization; flat-control loop `𝔥_γ/σ_γ < 0.5` | E4 §6.C |
| `G-E4-T4` | residual reuse | `{a₀,a₁,a₂}` agree across E1/E2/E5 within `<2σ` **and** no amplitude differs by `>10×` | E4 §6.C |
| `G-E4-T5` | source refinement | leave-one-route-out predictive `χ²` improves `≥20%` with genuine proxies vs `≤5%` with unrelated nuisance params | E4 §6.C |
| **`G-E4-DECISIVE`** | lawful-plurality (decisive positive) | `(G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation) ∧ (G-E4-T1 ∧ G-E4-T2 ∧ G-E4-T3 ∧ G-E4-T4 ∧ G-E4-T5)` — model-comparison ∧ **all five LP1–LP5** | E4 §6.D |
| `G-E4-ROUTEREUSE` | weaker route-reuse (`[E]`/partial, NOT lawful plurality) | `(G-E4-1 ∧ G-E4-2 ∧ G-E4-2-permutation ∧ G-E4-T4)` hold but not all of LP1–LP5 | E4 §6.D |

---

## 8. E5 — Growth / staging sweep for S₈

> Gate IDs verbatim from `plan/experiments/E5-growth-staging-S8.md` §7. A `budgeted` (known-systematic)
> verdict is a valid outcome; only backend/repro, coherence, or rank/no-surrogate failures fail the program.

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E5-BACKEND` | physical backend (BLOCKING) | `pyccl` imports; `G-ENV-4` pyccl↔CLASS agreement passes (`P(k)<1%`, `σ8<0.5%`); CCL reference checks `<0.5%` | E5 §7.1 |
| `G-E5-REPRO` | reproduction (BLOCKING) | physical-CCL `G₀` recovers each survey's published `S₈`/`fσ₈`/`(μ₀,Σ₀)` within quoted 1σ (DES Y6 0.789±0.012; KiDS 0.815; HSC 0.805); `R̂<1.01`, ESS>400 | E5 §7.1 |
| `G-E5-NOSURR` | no surrogate as headline | headline fingerprint from tier-1/tier-2 physical-CCL legs only; `G_surr` reproduces precursor degeneracy **and** physical CCL breaks it | E5 §7.1 |
| `G-E5-COV` | covariances | each `Σ` PD, cond `<1e8`, finite | E5 §7.2 |
| `G-E5-RANK` | anti-fudge rank | `G₂` adds `≤2` closure params (`a₁[,β]`); `a₀` inherited not re-fit; probe-shared shapes; no per-probe `Ξ_p` | E5 §7.2 |
| `G-E5-KERNEL` | kernel linearity + stability | `K_G,K_S` linear in `(a₀,a₁)` to `<1%`; `R[Ξ]` positive + stable (stable-readout) | E5 §7.2 |
| `G-E5-SYS` | systematics handling | IA/baryon/photo-z/shear-cal nuisances marginalized in **every** model incl. `G₀`; not charged to `Ξ` | E5 §7.2 |
| `D_scale` verdict (staging fingerprint) | residual staging slope `s_Ξ^resid` (eq. E5.2) | `≠ 0` at **>2σ**, reproducible across `≥2` physical-CCL probes, persisting under common-staging (`>1σ`), **and** `G₂`'s single `Ξ` lowers cross-lens `δχ` by `>5%` vs `G₀` | E5 §7.3 |
| `budgeted` verdict | `s_Ξ^resid` | consistent with 0 (`<2σ`); `G_sys` absorbs the dependence as well as `G₂` | E5 §7.3 |
| `G-E5-OOS` | out-of-sample | **win/tie/fail** vs the best competitor; **win** = `G₂` lowers held-out `PPD_{geom→growth}` by **>3%** vs `G₀` and beats every alternative beyond the combined uncertainty band (being `≤` best competitor / within 3% of it is a **floor**, scored a **tie**, not a pass) | E5 §7.4 |
| `G-E5-DUAL` | one residual, two charts | same inherited `a₀` (+ fitted `a₁`) improves **both** geometry and growth, neither block worsened | E5 §7.4 |
| **`G-E5-COHERE`** | coherence (make-or-break) | E5 `K_S/K_G` amplitude within **10×** and consistent sign with E1 `K_L/K_M` | E5 §7.4; `plan/00` §6.4 |
| `G-E5-BIC` | model competition | when `D_scale` holds, `G₂` beats `G₀` by `ΔBIC > 5` on the joint growth vector | E5 §7.4 |

---

## 9. E6 — Interacting dark sector as accounting shadow

> Gate IDs verbatim from `plan/experiments/E6-ide-accounting.md` §8. `G-E6-REPRO-*` BLOCK E6-B/E6-C.
> Verdicts A (bridged) / B (real interaction) / C (undecidable) are all valid findings.

### 9.1 Data / metric / reproduction

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E6-COV` | covariances | every probe cov PD, cond `<1e8`, finite | E6 §8.1 |
| `G-E6-CONV` | convergence | `R̂ < 1.01` all params; ESS > 400/chain | E6 §8.1 |
| `G-E6-DET` | determinism | deterministic likelihood / forward-model evaluations; committed posterior summaries reproduced to stated tolerance; chains validated by statistical equivalence (means/covariance within MC error, `R̂<1.01`, ESS thresholds) — **not** bitwise-identical; manifest recorded | E6 §8.1 |
| `G-E6-CONS` | continuity sanity | IDE total continuity (E6-2) conserved to machine precision | E6 §8.1 |
| `G-E6-REPRO-XI` | IDE coupling (BLOCKING) | recovered `ξ` agrees with 2503.23225/2504.00994 within **1σ** (fail `>2σ`) | E6 §8.2 |
| `G-E6-REPRO-H0` | `H₀`-tension reproduction (BLOCKING) | reduced toward **≈2.7σ** within ±0.3σ; S-IDE lowers `S₈` in published direction | E6 §8.2 |
| `G-E6-REPRO-CHI2` | per-block `χ²` (BLOCKING) | within **5%** of published; baselines match E1 | E6 §8.2 |

### 9.2 Background equivalence (chart map)

| Gate | Metric | Threshold | Grade | Source |
|---|---|---|---|---|
| `G-E6-BG-Q` (headline) | `Q_Ξ` vs fitted `Q_IDE` | RMS **≤ 20%** of `Q` posterior amplitude (fail `>30%`) | [E] | E6 §8.3 |
| `G-E6-BG-HZ` | `H(z)` + distances | `H(z)` within CC error bars; distances whitened `d ≤ 1`/dof | [E] | E6 §8.3 |
| `G-E6-BG-SPAN` | out-of-span fraction of `ΔρQ` | `< 20%` (clean chart); `>50%` ⇒ `out_of_scope` finding | [E] | E6 §8.3 |
| `G-E6-BG-LEAN` | continuity chart-map | T-E6 reproduces `ρ_de^eff` on grid; kernel linearity `<1%` | [T] | E6 §8.3 |

### 9.3 Growth-split decision + discipline

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E6-GROWTH-RED` (Verdict A) | growth reducibility at coherence-locked `a₁` | `Δχ²_growth(Ξ→IDE) ≤ 4` **and** `|μ_SBT−μ_GR| < |μ_IDE−μ_GR|` **and** `Ξ_C(Q|Ξ) ≈ 0` ⇒ **bridged** | E6 §8.4 |
| `G-E6-GROWTH-INT` (Verdict B) | interaction indicated | `Δχ²_growth(Ξ→IDE) ≥ 9` **or** nonzero adequacy residual with growth blind-spot ⇒ real interaction (`out_of_scope`/`approved_other`) | E6 §8.4 |
| `G-E6-PPD` (reducibility / comparability to IDE — NOT a std-3 OOS win) | held-out `δχ²` | SBT RSD within **10%** of IDE on geometry→growth (S1); within 15% on S2/S3 (fail `>15%` worse). This certifies `Q_IDE` is reducible to a chart of `Ξ` (comparability), it is NOT an out-of-sample victory; the strict program-level OOS win is decided only at `G-E8-OOS-DECISIVE` | E6 §8.4 |
| `G-E6-MUSIGMA` (headline) | `(μ,Σ)` deviation | `|μ_SBT−μ_GR| < |μ_IDE−μ_GR|` (same deviation in both ⇒ Verdict C undecidable) | E6 §8.4 |
| **`G-E6-COH`** | coherence (make-or-break) | `a₁` within **10×** cross-amplitude band, consistent sign with E1/E5 | E6 §8.4; `plan/00` §6.4 |
| `G-E6-RANK` | anti-fudge | `≤3` free `Ξ` params; no IDE-specific `Ξ_p`; `a₁` not refit to chase growth | E6 §8.5 |
| `G-E6-OOS` | reducibility / comparability (NOT a std-3 OOS win) | `G-E6-PPD` met and improves ΛCDM OOS baseline on `≥1` split; this is a comparability/reducibility verdict only — the strict program-level out-of-sample win (std-3) is judged solely at `G-E8-OOS-DECISIVE` | E6 §8.5 |
| `G-E6-NOFUDGE` | anti-fudge span | reproducing IDE background did not require shapes outside `𝒜`; extensions logged | E6 §8.5 |
| `G-E6-STATUS` | F9 | every residual + verdict carries exactly one base status; none `unstatused` | E6 §8.5 |
| `G-E6-FAILREPORT` | std 5 | §8.6 pre-registered failure modes all checked and reported with numbers | E6 §8.5 |

---

## 10. E7 — Modified gravity as another descent-repair chart

> Gate IDs verbatim from `plan/experiments/E7-modified-gravity.md` §7. **MG simply not being preferred
> is NOT a failure** — it is a logged alternative repair. Program fails only on REPRO/BACKEND, MUSIGMA,
> COHERE, OOS(>20% worse), or an unstatused instability.

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E7-BACKEND` | physical backend (BLOCKING) | `pyccl` imports; `G-ENV-4` pyccl↔CLASS agreement (`P(k)<1%`, `σ8<0.5%`); CCL `(μ,Σ)`/`f(R)`/shear ref checks `<0.5%` | E7 §7.1 |
| `G-E7-REPRO` | DESI MG reproduction (BLOCKING) | recover `μ₀=0.04±0.22, Σ₀=0.044±0.047` within 1σ; `f(R)` `log₁₀|f_R0|<−4.59` (95%); `M_w` `w₀w_a` within ±5%; `R̂<1.01`, ESS>400 | E7 §7.1 |
| `G-E7-COV` | covariances | each `Σ` PD, cond `<1e8`, finite | E7 §7.1 |
| `G-E7-RANK` | anti-fudge rank | `M_Ξ` adds `≤2` closure params (`a₂`[, optional]); `a₀` inherited; `(μ,Σ)=(1,1)` held at GR; probe-shared shapes; no per-probe `Ξ_p` | E7 §7.2 |
| `G-E7-KERNEL` | kernel linearity + stability | `K_M,K_G,K_S` linear to `<1%`; `R[Ξ]` positive + stable | E7 §7.2 |
| `G-E7-STABILITY` | MG no-instability certificate | every admitted MG model `max_λ Re λ ≤ 0` (tol `1e-6`) **and** min symmetrized eigenvalue `≥ −1e-8`; failures logged `blocked` | E7 §7.2 |
| `G-E7-SYS` | systematics handling | bias/IA/baryon/photo-z/shear-cal nuisances marginalized in every model incl. `M₀`; not charged to `Ξ`/`(μ,Σ)` | E7 §7.2 |
| **`G-E7-MUSIGMA`** (central SBT prediction) | where-modification-lives | `M_Ξ` background rewrite (`μ=Σ=1`) reproduces DESI `w(z)` **and** inferred `|μ₀^SBT| < 2σ_μ`, `|Σ₀^SBT| < 2σ_Σ` | E7 §7.3 |
| `G-E7-F2` | shared obstruction | split-pair overlap `|△|/|splitObs| < 0.15` (M_Ξ and MG repair the same obstruction) | E7 §7.3 |
| `G-E7-NECESSITY` | is MG demanded? | MG required beyond `Ξ` **iff** it lowers OOS `PPD_{geom→growth}` by **>15%** (either direction logged) | E7 §7.3 |
| **`G-E7-COHERE`** | coherence (make-or-break) | MG-implied effective `Ξ` amplitude within **10×** and consistent sign with E1/E5 `Ξ` | E7 §7.4; `plan/00` §6.4 |
| `G-E7-OOS` | out-of-sample | `M_Ξ` growth OOS within **15%** of best MG model (fail if `>20%` worse) | E7 §7.4 |
| `G-E7-BIC` | model competition (informational) | record `ΔBIC` vs `M₀`; flag if any MG model beats `M_Ξ` by `ΔBIC>5` for E8 | E7 §7.4 |

---

## 11. E8 — Global model competition (the decisive synthesis)

> Gate IDs verbatim from `plan/experiments/E8-model-competition.md` §7. **`G-E8-OOS-DECISIVE` is the
> single binding program-verdict gate** (`idea.md` §10 std 3). An in-sample-only win is a FAIL.

### 11.1 Reproduction-floor + precondition (BLOCKING — else no winner can be scored)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E8-DEPS` | dependency assertion | every `BLOCKED_BY` artifact present; every upstream `terminal_state ∈ {PASS, ACCEPTED_NEGATIVE}` (a `BLOCKED`/`PROGRAM_FAIL` upstream means E8 cannot run); coherence ledger (E1–E7) consistent and §6.4 green | E8 §7.1 |
| `G-E8-REPRO` | reproduction floor | every contender keeps `χ²/dof < 1.05` on reproduced baseline blocks; ΛCDM/w₀w_a within E1 tolerance | E8 §7.1 |
| `G-E8-COV` | covariances | every block `Σ` PD, cond `<1e8`, finite | E8 §7.1 |
| `G-E8-CONV` | convergence + evidence stability | `R̂−1 < 0.01`, ESS > 400/chain; PolyChord `ln Z` err `< 0.3` and run-to-run scatter `< 0.3` | E8 §7.1 |
| `G-E8-DET` | determinism | rerun from manifest reproduces likelihood/forward-model evaluations bitwise and committed posterior summaries to a stated tolerance; MCMC/PolyChord chains validated by statistical equivalence (`R̂<1.01`, ESS, means/cov within MC error), NOT bitwise table identity across environments (REGISTRY §11.6) | E8 §7.1 |

### 11.2 Contender discipline (anti-fudge on SBT-Ξ)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E8-RANK` | rank ceiling | single coherence-checked `Ξ_cosmo`, `≤ +3` (minimal) / `≤ +5–7` (full); no per-probe `Ξ_p`; kernels probe-shared and linear (`<1%`); disqualify if `>+4` params with no BIC gain | E8 §7.2 |
| `G-E8-FROZEN` | no re-tuning | SBT-Ξ form/kernels read from coherence ledger, not re-tuned; no new physics/data | E8 §7.2 |
| `G-E8-STABLEREADOUT` | imported P4 certificate | SBT-Ξ phantom-crossing column carries E3 stable-readout certificate (`max Re λ ≤ 0`) | E8 §7.2 |

### 11.3 The decisive verdict gates

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| **`G-E8-OOS-DECISIVE`** (BINDING, std 3) | out-of-sample composite `OOS^{(M)}` (eqs. E8.1–E8.3) | a strict **`win`**: `OOS_composite(SBT-Ξ)` beats **every** alternative by **more than the combined uncertainty band** and after the complexity penalty, **AND** improves the E1 ΛCDM baseline OOS by **>3%** on `≥1` held-out leg, **AND** has **no silent loss** on any critical leg (geometry, growth, Hubble). A **`tie`** (within the best alternative's uncertainty band) **does NOT pass**; a `fail` is an overall loss or a loss on any critical leg. **In-sample-only win = FAIL** | E8 §7.3, §6 |
| `G-E8-EVID` | Bayesian evidence | `ln B_{Ξ/Λ} > 1` (target `>3`) with `σ_{lnB}`; SBT-Ξ evidence `≥` ΛCDM and within `2σ_{lnB}` of best | E8 §7.3 |
| `G-E8-BIC` | complexity penalty | SBT-Ξ `ΔBIC_vs_LCDM` not worse than `+5` vs the best competitor; SBT-Ξ `≥` ΛCDM composite | E8 §7.3 |
| `G-E8-PPC` | posterior-predictive calibration | every contender has reproduced-block posterior-predictive p-values in `[0.01, 0.99]`; SBT-Ξ no catastrophic in-sample block failure | E8 §7.3 |

### 11.4 Corroboration (std 4 — non-binding, required to be reported)

| Gate | Metric | Threshold | Source |
|---|---|---|---|
| `G-E8-STAGING` | E5 staging-fingerprint column | populated; if SBT-Ξ wins, verdict is `D_scale` (or explicitly statused `budgeted`), not white noise | E8 §7.4 |
| `G-E8-PLURALITY` | E4 lawful-plurality column | populated and structured (LP1–LP5 / holonomy verdict reported) | E8 §7.4 |
| **`G-E8-COHERENCE`** | coherence (make-or-break, re-assertion) | single `Ξ_cosmo` cross-amplitudes within **10×**, consistent sign | E8 §7.4; `plan/00` §6.4 |

---

## 12. Cross-cutting structural / environment / Lean gates

> These govern the *infrastructure* that all experiments depend on. Locked in `plan/01`
> (`G-REPO-1…G-REPO-16`), `plan/02` (`G-ENV-1…G-ENV-9`), `plan/05` (L1–L9). Listed here so the
> consolidated register is complete; the per-file numbering is preserved (namespaced per REGISTRY §4).

### 12.1 Repository structure (`plan/01` §`G-REPO-1`–`G-REPO-16`, selected load-bearing)

| Gate | Metric | Threshold |
|---|---|---|
| `G-REPO-1` | install/import | `pip install -e .` succeeds; `import sbt_cosmo` works |
| `G-REPO-3` | single `Ξ` source | exactly **1** `Ξ_cosmo`/rewrite definition (in `sbt_cosmo/xi/`); 0 redefinitions under `experiments/` |
| `G-REPO-4` | determinism | identical config+lockfile+seeds: deterministic likelihood/forward-model evaluations bitwise reproducible, posterior-summary scalars to `≤1e-12` rel; chains validated by statistical equivalence (means/covariance within MC error, `R̂<1.01`, ESS), **not** bitwise across environments (E0 toy demos, no sampler, are bitwise) |
| `G-REPO-8` | reproduce-without-rerun | every E0–E8 commits manifest/summary/tables/figures/aor_status/posterior_summary; every gate re-derivable from committed artifacts |
| `G-REPO-10` | no unstatused (F9) | every run has `aor_status.json`; 0 residuals with status `unstatused` |
| `G-REPO-13` | reproduction floor | E1 reproduces published baseline total `χ²` within 5% before adding `Ξ` |
| `G-REPO-15` | one `Ξ` serves all probes | E8 per-probe kernel amplitudes agree within factor **10** |

### 12.2 Environment (`plan/02` §`G-ENV-1`–`G-ENV-9`, selected)

| Gate | Metric | Threshold |
|---|---|---|
| `G-ENV-2` | CLASS↔CAMB backend agreement | `D_M/r_d`, `D_H/r_d` agree `<0.1%` for `z∈[0.1,2.3]`; `C_ℓ^TT` `<0.2%` for `ℓ∈[30,2000]`; excess statused as tooling route-mismatch before any physical `Ξ` claim |
| `G-ENV-4` | pyccl↔CLASS agreement (the E5/E7 gate) | `P(k)` agree `<1%` for `k∈[1e-3,1] h/Mpc` at z=0; `σ8` `<0.5%` — **fail blocks E5/E7** |
| `G-ENV-5` | convergence + evidence | `R̂<1.01` all params, ESS>400/chain; nested `ln Z` stable to `<0.2` across two seeds |
| `G-ENV-6` | reproduce-before-rewrite | `χ²_total` for ΛCDM/w₀w_a within 5% of published; 1σ contour widths within 10% |
| `G-ENV-9` | Lean track | `lake build` succeeds under pinned toolchain; P1–P4 + δ/RM certificates compile with no `sorry` |

### 12.3 Lean mechanization (`plan/05` §L1–L9)

| Gate | Metric | Threshold | Targets |
|---|---|---|---|
| `L1` | build green | `lake build` exits 0 for both `SbtCosmo` and `SbtCosmoSchur` libs under pinned toolchain/manifest | T1–T7 |
| `L2` | zero `sorry` | grep returns 0 matches; no `sorryAx` in any `#print axioms` closure | all |
| `L3` | zero escapes | 0 `axiom`/`opaque`/`constant` declarations | all |
| `L4` | trust-base closure | every theorem axiom closure ⊆ `{propext, Classical.choice, Quot.sound, choice, funext}`; mathlib-free targets ⊆ `{propext, Quot.sound}` | all |
| `L5` | required-target coverage | all 7 targets present and green; P1(T2) and P4(T5) faithful complete proofs; P2(T3a PSD) faithful; P3(T4) delivered | T1–T7 |
| `L6` | non-vacuity | committed witnesses `decide`-accepted with `≥2` states / `≥3` routes / `≥3` grid nodes | T2/T5/T6 |
| `L8` | structural alignment | T2 RM witness, T5 `w_eff` grid + `z_c`, T6 route labels structurally identical to E0 toy / E3 grid / E4 route registry | T2/T5/T6 |
| `L9` | manifest recording | every run manifest records `lean.{toolchain, mathlib_rev, build}` and `axiom_audit`; `AOR_certified` requires green+pass | all |

---

## 13. Pre-registered failure modes (`idea.md` §10 standard 5)

> These are the program's named, pre-registered failure modes. They **may not be moved after execution**.
> Each maps to the experiment(s) that detect it and the gate(s) whose failure triggers it. The first five
> are the `idea.md` §10.5 headline failure modes; the remainder are their per-experiment operationalizations.

### 13.1 The five headline failure modes (`idea.md` §10.5)

| # | Failure mode (`idea.md` §10.5) | Detecting metric / gate | Threshold that triggers FAIL | Detected by |
|---|---|---|---|---|
| **F-A** | **`Ξ_cosmo` degenerates to unrelated per-probe fudge terms** | the coherence gate `G-PHASE-COHERENCE` / `G-*-COHERE` / `G-*-RANK` | any experiment's fitted `Ξ` differs from another by **>10×** amplitude or sign disagreement; **or** distinct uncorrelated `Ξ_p` required per probe; **or** `>+4` extra params with no BIC gain | E1-B, E2, E3, E4 (`G-E4-T4`), E5, E6, E7, **E8 (G-E8-RANK/COHERENCE)** |
| **F-B** | **Cannot reproduce DESI DR2** | `G-E1-REPRO-*` (program-blocking) | recovered `(w₀,w_a)` outside published quadrant/contour by `>10%`; C2 significance `<2.5σ` or `>3.7σ`; SN-leg significances outside [2.5,4.5]σ; total `χ²` off by `>5%` | **E1 (blocks everything)**; re-checked in E2/E3/E8 reproduction legs |
| **F-C** | **Worsens growth predictions** | `G-E5-OOS`, `G-E5-COHERE`, `G-E6-PPD`, `G-E7-OOS` | SBT does not lower held-out `PPD_{geom→growth}` by `>3%` (E5); SBT RSD OOS `>15%` worse than IDE (E6); `M_Ξ` growth OOS `>20%` worse than best MG (E7); E5/E6/E7 growth `Ξ` amplitude inconsistent with E1 geometry | E5, E6, E7 |
| **F-D** | **Phantom crossing requires a real ghost** | `G-E3-CONSTRUCT`, `G-E3-DATA` | **no** positive/stable operator inducing a crossing can be exhibited (`G-E3-CONSTRUCT` fails any of: crossing, `ρ_eff>0`, `λ_min^{sym}≥0`, `max Re λ ≤ 0`); **or** the data-preferred operator requires a violated certificate (status `blocked`) | E0 (Toy 3 `G-E0-3.3`/`G-E0-3.4`), **E3 (P4 centerpiece)** |
| **F-E** | **Hubble plurality is unstructured noise** | `G-E4-2` (SBT vs per-route noise), `G-E4-2-permutation`, `G-E4-T2`, `G-E4-T3` | per-route noise `M_noise` fits as well as or better than `M_SBT` (`ln B_{SBT vs noise} < 5` or `ΔBIC < 6`); permutation control not destroyed (perm `ln B ≥ 2.5` in `>5%` of permutations); staging slopes uncorrelated (`ρ<0.5` or sign agreement `<70%`); every nonzero `𝔥_γ` collapses under honest internalization | E0 (Toy 4 `G-E0-4.2`/`G-E0-4.3`), **E4 (F4 verdict `RoutesInconsistent`)** |

### 13.2 Per-experiment pre-registered failure conditions (operationalizations)

| Experiment | FAIL condition (with numbers) | Gate(s) |
|---|---|---|
| **E0** | linear `RM` not zero (`G-E0-1.2` fail); no apparent `Ω_Λ>0.2` from null-Λ generator (`G-E0-2.4`) or spurious DE in homogeneous control (`G-E0-2.5`); rewrite loses OOS (`G-E0-2.7`); crossing needs negative `ρ_eff` or positive-Re-λ eigenvalue (`G-E0-3.3`/`G-E0-3.4`); injected `Ξ` unrecoverable (`G-E0-4.1`) or nuisance preferred by BIC (`G-E0-4.3`); any `unstatused` (`G-E0-0.3`) | E0 §8 |
| **E1** | cannot recover DESI `w₀w_a`/significances (F-B); detection prior-driven (`>1σ` shift) or backend-driven (`>5%`); E1-B `Ξ` improves SN only by worsening BAO (per-probe fudge); `>3` extra params with no `χ²/dof` gain or SN OOS `>15%` worse; SBT symbol leaks into E1-A | E1 §4.3 |
| **E2** | program-fail only if `G-E2-REPRO`, `G-E2-COHERE`, or `G-E2-RANK` fails. Gluing-reading failure (NOT program fail → valid rewrite verdict): M₂ never beats M₁ by `ΔBIC` **and** `F_collapse<0.3` **and** η-shape uncorrelated (`p>0.05`) | E2 §8.6 |
| **E3** | program-fail: `G-E3-CONSTRUCT` fail (F-D), `G-E3-LEAN` fail, `G-E3-COHERE` fail, or `G-E3-RANK` violated. Data-gate fail with status `blocked` (ghost required by data) or `G-E3-FALSEPOS`/`G-E3-BAYES` fail (no robust crossing) are valid statused negatives, NOT program fails | E3 §9.6 |
| **E4** | indistinguishable from scatter (`G-E4-2` fail → `RoutesInconsistent`); no residual reuse (`G-E4-T4` `>10×`/`>2σ`); holonomy a protocol-trap artifact (`G-E4-T3` collapses under internalization); no staging structure (`G-E4-T2` `ρ<0.5`); permutation not destroyed | E4 §6.F |
| **E5** | growth-`Ξ` claim fails (valid `budgeted` outcome) iff `s_Ξ^resid≈0` across all CCL probes **and** no `>3%` PPD gain **and** no `ΔBIC>5`. PROGRAM fails only on `G-E5-BACKEND`/`G-E5-REPRO`, `G-E5-COHERE`, or `G-E5-RANK`/`G-E5-NOSURR` | E5 §7.5 |
| **E6** | program-fail: background not reproducible by `Ξ` within `𝒜` (`G-E6-BG-Q>30%` or span `>50%`); coherence violation (`G-E6-COH`); reproduction skipped/failed (`G-E6-REPRO-*`). Verdict B (real interaction, `G-E6-GROWTH-INT`) or C (undecidable) are valid findings, reported with growth `Δχ²` numbers | E6 §8.6 |
| **E7** | program-fail: `G-E7-BACKEND`/`G-E7-REPRO` fail; `G-E7-MUSIGMA` fail (`Ξ` forces non-GR `(μ,Σ)`); `G-E7-COHERE` fail; `G-E7-OOS` `>20%` worse; an instability not logged `blocked`. **MG simply not preferred is NOT a failure** (logged `approved_other`) | E7 §7.5 |
| **E8** | (1) `G-E8-OOS-DECISIVE` not a strict `win` — an overall loss, a loss on any critical leg, **or a `tie` within the best alternative's uncertainty band** (a tie does not pass), or no leg beats ΛCDM by `>3%`; (2) fudge/over-parameterization (`>+4` params no BIC gain or per-probe `Ξ_p`); (3) coherence failure (`>10×`/sign); (4) reproduction failure; (5) in-sample-only win; (6) `ln B_{Ξ/Λ} < 0` beyond `2σ` **and** OOS loss. Each is a *valid, statused* outcome | E8 §7.5 |

### 13.3 What is NOT a program failure (LOCKED — honesty discipline)

- **SBT-Ξ tying a specialist on that specialist's own leg while winning the composite** is a **win**
  (E8 §7.5).
- **A specialist (`M_w`/`M_Q`/`M_μΣ`) winning a single OOS leg** is expected and fine, provided SBT-Ξ
  wins the composite (E8 §7.5).
- **MG not preferred** (E7) is a logged alternative repair (`approved_other`), not a failure.
- **E2 gluing-reading failure** yields a valid `rewrite-residual` verdict (E2 §8.6).
- **E5 `budgeted` verdict** (growth spread is a known systematic) is a valid, publishable outcome
  (E5 §7.5).
- **E6 Verdict B/C** (real interaction / undecidable) are findings, not failures (E6 §5).
- **An honest E8 FAIL** that is correctly statused (e.g. "ΛCDM remains the audited best closure
  out-of-sample"; Λ **not** ruled out — the precursor non-claim) is a legitimate scientific result.
- **The unacceptable outcomes** (program-invalidating regardless of the science verdict): an
  unreproduced baseline; an `unstatused` residual at phase end (`thm:F9`); a gate relaxed after the fact.

---

## 14. Gate summary index (quick lookup)

| Scope | Count | Blocking / decisive gates |
|---|---|---|
| Program standards | STD-1…STD-5 | STD-1 (reproduce), STD-3 (OOS win) |
| Phase | G-PHASE-* (9) | `G-PHASE-COHERENCE` (make-or-break), `G-PHASE-AOR` (F9) |
| E0 | `G-E0-1.1`–`G-E0-4.6` + `G-E0-0.x` (24) | all (E0 blocks E1/E3/E4) |
| E1 | G-E1-REPRO-* (12), G-E1-SBT-* (4) | all `G-E1-REPRO-*` block the program |
| E2 | G-E2-* (8 + status/decision) | `G-E2-REPRO`, `G-E2-COHERE`, `G-E2-RANK` |
| E3 | G-E3-* (11) | `G-E3-CONSTRUCT`, `G-E3-LEAN`, `G-E3-COHERE` |
| E4 | `G-E4-0a`/`G-E4-0b`, `G-E4-1`/`G-E4-2`/`G-E4-2-perm`, `G-E4-T1`…`G-E4-T5`, `G-E4-DECISIVE`, `G-E4-ROUTEREUSE` (13) | `G-E4-DECISIVE` = model-comp ∧ LP1–LP5 (`G-E4-1`∧`G-E4-2`∧`G-E4-2-perm`∧`G-E4-T1`…`G-E4-T5`); weaker `G-E4-ROUTEREUSE` (…∧`G-E4-T4`) |
| E5 | G-E5-* (12) | `G-E5-BACKEND`, `G-E5-REPRO`, `G-E5-COHERE`, `G-E5-RANK`/NOSURR |
| E6 | G-E6-* (18) | `G-E6-REPRO-*`, `G-E6-COH`, headlines BG-Q/PPD/MUSIGMA |
| E7 | G-E7-* (13) | `G-E7-BACKEND`/REPRO, `G-E7-MUSIGMA`, `G-E7-COHERE`, `G-E7-OOS` |
| E8 | G-E8-* (15) | **`G-E8-OOS-DECISIVE`** (the program verdict), `G-E8-COHERENCE` |
| Infra | `G-REPO-1`–`G-REPO-16` (repo), `G-ENV-1`–`G-ENV-9` (env), L1–L9 (Lean) | `G-ENV-4` (blocks E5/E7), L1/L2 (Lean build) |

> **The single program verdict.** Subject to all reproduction floors and the make-or-break coherence
> gate, the program *succeeds* iff **`G-E8-OOS-DECISIVE` passes**: the single low-rank `Ξ_cosmo`,
> coherence-checked across E1–E7 and never re-tuned, scores a strict **`win`** over the field's best
> specialist models **out-of-sample** on the leave-one-probe-out battery — better than every alternative
> by more than the combined uncertainty band (after the complexity penalty) with no silent loss on any
> critical leg — improving the ΛCDM baseline by `>3%` on `≥1` held-out leg. A `tie` (within band) does
> **not** pass. Everything else is supporting evidence or a statused finding.
