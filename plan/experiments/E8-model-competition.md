# E8 — Global Model Competition and the Decisive Out-of-Sample Gate

> **One-line charter.** Run the **global model competition** of `idea.md` §9: fit the six contenders
> — **ΛCDM, w₀w_aCDM, CDDR-only, IDE, MG, and SBT-Ξ** — on the *same* joint cosmological data with the
> *same* verified pipeline, then rank them by three independent yardsticks: **Bayesian evidence**
> (`ln Z` via PolyChord nested sampling), **leave-one-probe-out out-of-sample prediction** (`PPD_{p→q}`,
> the held-out battery), and **posterior-predictive checks** (PPC). Emit the **master
> model-competition matrix**. **The decisive gate is evidence standard 3 (`idea.md` §10): SBT-Ξ must
> WIN out-of-sample — not merely in-sample — using a *single low-rank* `Ξ_cosmo` reused across E1–E7.
> The win is a strict one (REGISTRY §8): SBT-Ξ must be better than *every* alternative beyond the
> combined uncertainty band AND after the complexity penalty, with no silent loss on any critical leg
> (geometry, growth, Hubble); a tie is NOT a pass.** A model that only wins in-sample, or merely ties
> the best alternative, fails E8.

> **Read-order / consistency.** This file implements the *final synthesis* experiment of the program
> defined in `plan/00-overview.md` (§3 shadow map *all rows*; §4 the four-residuals→experiments map row
> **E8 = "Model-competition synthesis … all residuals … AOR"**; §6.2 the five hard standards; §6.3 the
> E8 headline gate; §6.4 the make-or-break coherence gate; §8 definition-of-done items 6/7) and
> `../GROUNDING_BRIEF.md` (datasets §I, software stack §II — *the sampler/estimator named there*,
> determinism §III, compute budgets §IV, AOR vocabulary §VI, the audit gates §VI). Every formal object
> used here is *locked* in `plan/04-formal-foundations.md`: the carrier `𝔉_cosmo` and the four
> residuals `δ_p / RM_p / LG_{p,q} / PPD_{p→q}` (§4, esp. **§4.4** the cross-probe predictive defect =
> the out-of-sample machinery), the low-rank `Ξ_cosmo` ansatz and kernels `K_L/K_M/K_G/K_S/K_{r,ℓ}`
> (§3), the least-rewrite objective `Δ_SBT` and its `λ·complexity` anti-fudge term (§2 eq. 1), the
> coherence gate (§9.4 / §3.3, the LP4 residual-reuse constraint §5.3), and the AOR carrier hierarchy
> (§8, target **AOR** at E8 synthesis). Data products/loaders/fallbacks are locked in
> `plan/03-data-acquisition.md`; the run layout, the committed `results/tables/model_competition.csv`,
> the coherence ledger `results/xi_cosmo_coherence.csv`, and the experiment dir
> `experiments/E8_model_competition/` are locked in `plan/01-repo-structure.md` (§7, §8). Environment
> and the PolyChord/cobaya stack are locked in `plan/02-environment-and-deps.md`.
>
> **Science source of truth:** `idea.md` **§9 "Model competition"** (verbatim: *"ΛCDM, w₀w_a,
> CDDR-only, IDE, MG, and SBT-Ξ. Use evidence, leave-one-probe-out prediction, and posterior
> predictive checks."*); **§10 "The standard of evidence to aim for"**, *especially standard 3*
> (*"Win out-of-sample. Train on geometry and predict growth; train on growth and predict geometry;
> train on BAO+CMB and predict SN."*), standard 1 (reproduce-first), standard 2 (one low-rank
> residual), standard 4 (staging fingerprints), standard 5 (pre-register failure modes); §6 Exp 4
> (the leave-one-probe-out PPD battery this file aggregates); the post-§10 **UPDATE** block (the Hubble
> routes that enter the competition via E4).
>
> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean / finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a gate in
> §7 below). E8 is overwhelmingly `[E]`: it is the experiment whose pass/fail *is* the program verdict.

> **HARD CONSTRAINT (locked).** E8 is a **synthesis** experiment: it introduces **no new physics, no
> new `Ξ` freedom, and no new data** beyond what E1–E7 already fit. The `Ξ_cosmo` used in the SBT-Ξ
> contender is the **single, already-fitted, coherence-checked** residual from E1–E7 (read from
> `results/xi_cosmo_coherence.csv`), specialized but **never enlarged** (`plan/00` §2 out-of-scope;
> `idea.md` §5 / §10 std 2). E8's job is to *compete and decide*, not to re-tune.

---

## 0. Charter and gate logic

### 0.1 What E8 is (one sentence)

E8 takes the six standard + Six Birds contenders, fits each to the *same* joint dataset with the *same*
verified pipeline, and decides — by **Bayesian evidence**, **leave-one-probe-out out-of-sample
prediction**, and **posterior-predictive checks** — whether the single low-rank `Ξ_cosmo` (the SBT-Ξ
model) is the best *audited closure* of the dark-energy data, with the **out-of-sample win** as the
non-negotiable decisive gate (`idea.md` §9, §10 std 3).

### 0.2 Why E8 exists (the gate logic)

- **E8 is where "one residual, many shadows" is adjudicated against the field's own best models.** The
  program's headline (`idea.md` §0, §3; `plan/00` §1) is that Λ, `w_a`, `η_CDDR`, `Q_IDE`, `μ/Σ`, and
  `S₈` shifts are *coordinate charts on one closure defect*. E8 puts each chart's *own dedicated model*
  (w₀w_a for the `w_a` chart, CDDR-only for the gluing chart, IDE for the accounting chart, MG for the
  operator chart) in head-to-head competition with the *single* `Ξ_cosmo` that is supposed to subsume
  them all. If `Ξ_cosmo` cannot at least match each specialist on its own turf while winning the joint
  out-of-sample test with fewer effective parameters, the unification claim is refuted.
- **The decisive test is out-of-sample, not in-sample (`idea.md` §10 std 3).** A flexible fudge can
  always lower in-sample `χ²`. The discriminating evidence is *held-out cross-probe prediction*: the
  leave-one-probe-out `PPD_{p→q}` battery (`plan/04` §4.4). E8 makes the out-of-sample win the spine of
  the verdict; in-sample fit and evidence are *supporting* yardsticks, not the decision.
- **E8 advances the AOR carrier to its terminal target.** Per `plan/00` §7 and `plan/04` §8.4, the
  carrier progresses `PreSB → RefStableAOR (E1–E3) → CascadeStableAOR (E4–E7) → AOR (E8 synthesis)`. E8
  is the synthesis whose passing certifies the carrier and writes the consolidated AOR status master.

### 0.3 Hard ordering — E8 is strictly last

E8 **depends on every prior experiment** and may not run until E1–E7 have each produced their committed
`summary.json`, their fitted-`Ξ` coherence-ledger entry, and their per-block `χ²` / chain artifacts.

| Upstream | What E8 consumes from it | If missing |
|---|---|---|
| **E1** | verified ΛCDM / wCDM / w₀w_a chains, per-block `χ²`, baseline `ln Z`, the inverse-ladder `H₀`; the E1-B SBT-geometry `Ξ` seed (`a₀`, `K_L/K_M`) | E8 cannot establish the reproduced baselines (std 1) or seed SBT-Ξ — **blocked** |
| **E2** | the CDDR-only model `M₂` fit + the gluing `η(z)` and its `Ξ` gluing-chart amplitude (`a₂`, `K_L/K_M`) | the **CDDR-only contender** has no fitted form — **blocked** |
| **E3** | the phantom-crossing rewrite operator + the stable-readout certificate (used to certify SBT-Ξ's `w_eff(z)` is a stable readout (no growing mode) in the competition) | SBT-Ξ phantom-crossing row uncertified — **degrade SBT-Ξ stability flag** |
| **E4** | the Hubble route matrix, holonomy `𝔥_γ`, the route-`H₀` posteriors per route, the lawful-plurality verdict | the Hubble-route OOS leg + the lawful-plurality column missing — **blocked** for the Hubble part of the matrix |
| **E5** | the growth/staging fit, `K_G/K_S` amplitudes, the `D_scale`/`budgeted` verdict | the **growth OOS leg** + staging-fingerprint column missing — **blocked** for the growth part |
| **E6** | the fitted **IDE** model (the `Q(z)` chart) + the SBT-vs-IDE `Q`-equivalence result | the **IDE contender** has no fitted form — **blocked** |
| **E7** | the fitted **MG** model (`(μ₀,Σ₀)`) + the MG-as-repair viability/instability result | the **MG contender** has no fitted form — **blocked** |

> **Locked precondition.** The E8 run script asserts, before any competition scoring, that every file
> in `BLOCKED_BY` (§8.1) exists, every upstream experiment is in `terminal_accepted` —
> `summary.json.terminal_state ∈ {PASS, ACCEPTED_NEGATIVE}` (REGISTRY §2, §11.4); a `BLOCKED` or
> `PROGRAM_FAIL` upstream means E8 cannot run — and the coherence ledger
> `results/xi_cosmo_coherence.csv` contains one entry per coherence member **E1–E7** (REGISTRY §3)
> with consistent `Ξ` amplitudes (the §6.4 coherence gate must already be green). If the coherence gate
> failed upstream, **E8 records the program-phase coherence FAIL and stops** (it does not attempt to
> rescue it by re-tuning).

---

## 1. The six contenders (LOCKED)

All six are fit to the **same joint data combination** (§3) with the **same** background/primordial
priors (matching E1, `plan/04` §3) and the **same** systematics/nuisance treatment, so the only
differences are the dark-energy / closure degrees of freedom. `Δk` is the count of *extra* free
parameters beyond ΛCDM. The "owner" column names the upstream experiment that fixed the model's form.

| ID | Contender | DE / closure d.o.f. | `Δk` | Reads as (shadow chart) | Owner / form fixed by | F-law |
|---|---|---|---|---|---|---|
| **`M_Λ`** | **ΛCDM** | `w ≡ −1`, `η ≡ 1`, `Q ≡ 0`, `μ=Σ=1` | 0 | the null / baseline; "Λ is a fundamental constant" | E1 (`plan/04` §3 baseline) | — |
| **`M_w`** | **w₀w_aCDM (CPL)** | `w(a)=w₀+w_a(1−a)`, PPF fluid | +2 | the **redshift chart** `w_a` (DESI's preferred dynamical-DE form) | E1 (CPL, arXiv:2503.14738) | — |
| **`M_η`** | **CDDR-only** | `η(z)=D_L/[(1+z)²D_A] ≠ 1` (`η₀`[,`η₁`] deformation), `w≡−1` | +1…2 | the **gluing chart** `η_CDDR` (SN–BAO inconsistency, Afroz–Mukherjee) | E2 (`M₂`, arXiv:2504.16868) | F4 |
| **`M_Q`** | **IDE** | dark-sector transfer `Q(z)` (e.g. `Q = ξ H ρ_DE`, sign-switching variant allowed) | +1…2 | the **accounting/continuity chart** `Q_IDE` | E6 (arXiv:2503.23225) | P6 |
| **`M_μΣ`** | **MG** | scale-/time-dep `(μ₀, Σ₀)` modified growth + lensing | +2 | the **operator-rewrite chart** `μ/Σ` (modified gravity) | E7 (arXiv:2411.12026 / 2411.12022) | P1 op-rewrite ext. of F2 (alt) |
| **`M_Ξ`** | **SBT-Ξ** | the single low-rank `Ξ_cosmo(z,ℓ,p)` ansatz, `(a₀,a₁,a₂)` (+ optional `β`), shared kernels | +3 (≤ +5–7 full) | **all charts at once** — the unification claim | E1–E7 (`plan/04` §3.1; **reused, not re-tuned**) | P1 op-rewrite ext. of F2 + F4 + F11 + P6 |

> **SBT-Ξ is the only contender that must serve all six rows simultaneously.** Each of `M_w, M_η, M_Q,
> M_μΣ` is a *specialist* tuned to one anomaly. `M_Ξ` uses **one** residual with **probe-shared shapes**
> (no per-probe free `Ξ_p`, `plan/04` §3.1 hard rule) and at most 3 amplitudes in the minimal ansatz.
> The whole point of E8 is whether the generalist beats the specialists *out-of-sample*.

### 1.1 Parameter-budget discipline (anti-fudge, LOCKED)

The decisive comparison is **complexity-penalized**. E8 records, for every contender:

- `k` = total free parameters (cosmology + DE/closure + nuisances).
- `Δk` = free parameters beyond ΛCDM.
- `BIC = χ²_min + k·ln N`, `AIC = χ²_min + 2k`, `DIC` (deviance information criterion from the chain),
  and the Bayesian evidence `ln Z` (§2.1) which penalizes volume automatically.

`M_Ξ` is **disqualified** (program fail, `plan/00` §6.3 E8 fail column) if it uses **> 4 extra
parameters with no BIC gain** over the best competitor, or if it requires distinct uncorrelated `Ξ_p`
per probe (that is the §6.2-std-2 / `plan/04` §3.1 anti-fudge violation, caught upstream and re-asserted
here). The `λ·complexity` term of `Δ_SBT` (`plan/04` eq. 1) is the formal embodiment of this rule.

---

## 2. The comparison machinery (LOCKED — three independent yardsticks)

E8 ranks the six contenders by **three** independent yardsticks so that no single estimator can be
cherry-picked (`idea.md` §9 names all three explicitly). The yardsticks and the named tools follow the
SHARED GROUNDING BRIEF §II and `plan/02`.

### 2.1 Yardstick A — Bayesian evidence (the sampler/estimator, named)

- **Estimator:** the **Bayesian evidence** `ln Z = ln ∫ ℒ(d|θ,M) π(θ|M) dθ` for each contender `M`.
- **Sampler:** **PolyChord nested sampling**, driven through **cobaya** (Brief §II.A; `plan/02`;
  matching E1 §2.5 which already runs PolyChord for the headline `w₀w_a` vs ΛCDM evidence). PolyChord is
  chosen (over MultiNest) because it is robust to the moderate dimensionality and curving degeneracies
  of `(w₀,w_a)` / `(μ₀,Σ₀)` / `Ξ` posteriors and reports a calibrated `ln Z ± err`.
- **Bayes factors:** `ln B_{M/Λ} = ln Z(M) − ln Z(M_Λ)`, with the combined PolyChord sampling error
  `σ_{lnB} = sqrt(σ_lnZ(M)² + σ_lnZ(M_Λ)²)`. The headline number is `ln B_{Ξ/Λ}` (`idea.md` §9; `plan/00`
  §6.3 E8 wants `log B_{SBT/ΛCDM} > 1`, target `> 3`).
- **Interpretation scale:** the Jeffreys/Kass–Raftery scale recorded in `summary.json`
  (`|ln B| < 1` inconclusive; `1–2.5` substantial; `2.5–5` strong; `> 5` decisive). Every reported
  `ln B` carries its sampling error; a Bayes factor within `2σ_{lnB}` of zero is reported as
  **inconclusive**, never spun as a win.
- **Evidence determinism / robustness:** each `ln Z` is computed from **≥ 2 PolyChord runs with distinct
  seeds**; the run-to-run `ln Z` scatter must be `< 0.3` (else increase `n_live` and re-run). Seeds are
  pinned in `config.yaml` (Brief §III.A; `plan/01` §9.1).

> **Why evidence alone is not the decision.** Bayesian evidence is prior-sensitive (volume effects). The
> evidence column is reported with a **prior-sensitivity control** (§4.4) and is *one* of three
> yardsticks. The *decision* (§0.2) rests on the **out-of-sample** yardstick (B), which is
> prior-robust because it scores *held-out* prediction. Evidence and PPC are the supporting columns.

### 2.2 Yardstick B — Leave-one-probe-out out-of-sample prediction (THE DECISIVE yardstick)

This operationalizes `idea.md` §10 standard 3 and §6 Experiment 4, and reuses the `PPD_{p→q}` residual
locked in `plan/04` §4.4 (eq. 14). For each contender and each held-out block, fit to the *complement*
of one probe block and score the *held-out* block's posterior-predictive distance.

**The leave-one-probe-out battery (LOCKED, from `idea.md` §6 E4):**

| Leg | Train on | Predict (held-out) `q` | Tests shadow row(s) | Source experiment leg |
|---|---|---|---|---|
| `L1` | BAO + CMB | **SN** (`μ(z)`) | geometry → distance (1, 3) | E1 / E8 |
| `L2` | SN + BAO | **growth** (`fσ₈`, `S₈`) | geometry → growth (6) | E5 |
| `L3` | WL + RSD | **geometry** (`D_M/r_d`, `D_H/r_d`) | growth → geometry (6, 4) | E5 |
| `L4` | local ladder (Cepheid/TRGB/JAGB→SN) | **inverse ladder** (`H₀` from CMB+BAO) | route → route (2) | E4 |
| `L5` | CMB + BAO | **local `H₀`** (SH0ES/CCHP_TRGB_JAGB route readouts) | early → late `H₀` (2) | E4 |

**The scored statistic per leg (whitened, `plan/04` §4.0 / §4.4):**

```
PPD^{(M)}_{p→q} = || y_q^obs − E_{q | p}[ y_q | θ ~ posterior(M | data_p) ] ||_{Σ_q^{-1}}      (E8.1)
```

i.e. the Mahalanobis (covariance-whitened) distance between the held-out observed block `q` and the
posterior-predictive mean of `q` propagated from a fit to the *complement* block(s) `p`, under model
`M`. For reporting we use the **out-of-sample, BIC-penalized RMSE** per leg:

```
OOS_RMSE^{(M)}_{leg} = sqrt( PPD^{(M)}_{leg} / N_q )    (per-d.o.f. whitened residual; N_q = dim(y_q))   (E8.2)
```

and the **out-of-sample composite** across legs (weighted by held-out d.o.f.):

```
OOS^{(M)} = Σ_legs w_leg · OOS_RMSE^{(M)}_leg ,   w_leg = N_q(leg) / Σ N_q                              (E8.3)
```

> **The win condition (the spine of E8).** SBT-Ξ wins out-of-sample iff it is a **strict `win`** in the
> REGISTRY §8 sense: on the composite `OOS^{(M)}`, SBT-Ξ is **better than *every* alternative beyond the
> combined uncertainty band** AND **after the complexity penalty**, with **no silent loss on any critical
> leg** (geometry, growth, Hubble). A `tie` — within the uncertainty band of the best alternative — is
> **NOT a pass** of the out-of-sample standard. (The leg-level `OOS RMSE within 1.1× of best`, `plan/00`
> §6.3 E8, is a *floor* only — a necessary leg-level guard, **not** the program decision.) In addition,
> SBT-Ξ must improve the **E1 ΛCDM baseline OOS by > 3% on ≥ 1 held-out block** (`plan/04` §9.3
> "Out-of-sample win"). A model that wins in-sample (yardstick C / `χ²`) but loses out-of-sample (B)
> **fails** — this is the explicit anti-fudge decision rule (`idea.md` §10 std 3; REGISTRY §8).

> **Cross-fit honesty (LOCKED).** Each OOS leg is a *bona fide* held-out fit: the held-out block `q`
> contributes **zero** information to the training posterior (its likelihood term is removed, its
> nuisances marginalized only over the training-informed prior). The PPD is the *predictive* distance,
> not a residual at the joint MAP. The cross-fit folds, seeds, and which blocks are held are pinned in
> `config.yaml` and recorded in the manifest, so the OOS scores are reproducible (Brief §III.A).

### 2.3 Yardstick C — Posterior-predictive checks (PPC, in-sample calibration + discrepancy)

Following `idea.md` §9 ("posterior predictive checks") and Brief §IV ("Posterior-predictive checks
(PPD)"), for each contender fit to the **full joint** data, draw `N_pp` posterior-predictive
realizations of each probe block and compute:

- **Posterior-predictive p-values** for per-block discrepancy statistics `T(y)` (e.g. block `χ²`,
  the SN Hubble-residual run statistic, the BAO radial/transverse split, the high-`ℓ` CMB tail used in
  the neutrino-mass template). A well-calibrated model has `p` in `[0.05, 0.95]`; `p < 0.01` or
  `p > 0.99` flags a block the model *cannot* reproduce even in-sample.
- **Per-block in-sample `χ²/dof`** and total `χ²/dof` (the §7.1 reproduction-floor check: every
  contender must keep `χ²/dof < 1.05` on the reproduced baseline blocks, `plan/00` §6.1).
- **The discrepancy heatmap** (probe × `z`/`ℓ`-bin) of standardized posterior-predictive residuals —
  the program-wide analog of the `Six_Birds_for_Neutrino_Mass` localization heatmap — so a model's
  failures are *localized*, not just scalar-summarized.

> PPC is the **calibration** yardstick: it certifies that each contender (including SBT-Ξ) is not merely
> winning a number but actually *reproduces the data distributionally* in-sample, and it localizes where
> each model strains. PPC does not by itself decide the competition (yardstick B does), but a contender
> with a catastrophic PPC failure (`p < 0.01` on a reproduced block) is flagged as not-reproducing and
> cannot be declared the winner.

### 2.4 The verdict rule (LOCKED — how the three yardsticks combine)

The decision is **lexicographic with an anti-fudge guard**, in this strict order:

1. **Reproduction floor (std 1).** Every contender must pass the §7.1 reproduction gates (`χ²/dof <
   1.05` on baseline blocks; recovered baseline contours within E1 tolerance). A contender failing this
   is `unreproduced` and excluded from "winner" eligibility (but still listed in the matrix).
2. **Out-of-sample (std 3) — DECISIVE.** Rank eligible contenders by `OOS^{(M)}` (E8.3). SBT-Ξ must
   satisfy §2.2's win condition — a **strict `win`** (REGISTRY §8): better than *every* alternative
   beyond the combined uncertainty band AND after the complexity penalty, with no silent loss on any
   critical leg. A `tie` is **not** a pass.
3. **Complexity / evidence (std 2) — TIE-BREAK + guard.** Among out-of-sample-comparable models, prefer
   lower `Δk` and higher `ln Z`. SBT-Ξ must not exceed +4 extra params with no BIC gain (§1.1).
4. **Staging fingerprint (std 4) — corroboration.** SBT-Ξ's win is *corroborated* (not gated) by E5's
   staging-fingerprint column and E4's lawful-plurality column being non-null and structured.

A composite score is also reported for transparency (a single ordering), but the **binding** verdict is
the lexicographic rule above; the composite never overrides a failed out-of-sample test.

```
CompositeScore(M) = z(−OOS^{(M)}) + z(ln Z(M)) + z(−ΔBIC_{M/Λ}) + z(PPC_calibration(M))                (E8.4)
```

(`z(·)` = standardize across contenders; higher is better). `CompositeScore` is a *sorting aid* only;
§2.4 steps 1–3 are the decision.

---

## 3. Inputs

### 3.1 Datasets (the full joint combination; from Brief §I, `plan/03`)

E8 fits the **maximal joint combination** the program supports — the union of every probe block used in
E1–E7 — because the unification claim is precisely that one residual closes *all* of them at once. All
keys, loaders, fallbacks, and integrity gates are locked in `plan/03`.

| Block | Dataset key(s) | Release | Product | Enters legs | Owner |
|---|---|---|---|---|---|
| **CMB** | `PLANCK_2018` (+ optional `ACT_DR6`/`SPT_3G` cross-check) | 1807.06209 / 2509.02945 / 2506.20707 | TT/TE/EE + lensing | all; `L1`,`L4`,`L5` train | E1 |
| **BAO** | `DESI_DR2_BAO` | 2503.14738 | `D_M/r_d`, `D_H/r_d` | all; `L1`,`L3`,`L4`,`L5` | E1 |
| **SN** | `PANTHEON_PLUS` (primary); `UNION3`, `DES_SN5YR` (variants) | 2202.04077 / 2401.06956 / Zenodo:13827844 | `μ(z)` + full cov | `L1` held-out; `L2`,`L3` train | E1/E2 |
| **WL / 3×2pt** | `DES_Y6` (prime); `KIDS_LEGACY`, `HSC_Y3` | 2601.14559 / 2503.19441 / 2511.18134 | shear (+clustering) `S₈` | `L2` held-out; `L3` train | E5 |
| **RSD** | `DESI_RSD_FS` | DR2 compressed `fσ₈` (DR1 FS method 2411.12026) | `fσ₈(z)` 6–8 bins | `L2` held-out; `L3` train | E5 |
| **CMB lensing** | `CMB_LENSING` | 2509.02945 | `C_ℓ^{κκ}` | growth cross-check | E5 |
| **Local ladder** | `SH0ES`, `CCHP_TRGB_JAGB` (TRGB/JAGB), `TDCOSMO`, `SIRENS_GW170817` | 2509.01667 / 2408.06153 / 2110.00517 / 1709.05895 | route-`H₀` posteriors | `L4`,`L5` | E4 |
| **Inverse ladder** | derived in E1 (CMB+BAO→`H₀`) | — | `H₀^inv` posterior | `L4` held-out | E1/E4 |

> **SN-compilation and WL-survey spread are recorded, not hidden** (`idea.md` §6 E1, §5): the
> competition is run with `PANTHEON_PLUS` as the headline SN and with the DES Y6 prime growth probe; the
> Union3 / DES-SN5YR and KiDS / HSC legs are reported as a *spread* row in the matrix (a packaging
> signal), per E1 §2.7 and E5 §1.4.

### 3.2 Fitted-model inputs from E1–E7 (the contenders' forms; LOCKED)

E8 does **not** re-derive any contender's functional form; it reads each from its owner experiment.

| Contender | Read from (artifact) | What is read |
|---|---|---|
| `M_Λ`, `M_w` | `experiments/E1.../outputs/` chains + `summary.json` | verified ΛCDM/wCDM/w₀w_a fits, per-block `χ²`, `ln Z`, MAP |
| `M_η` | `experiments/E2.../outputs/` (the `M₂` model) | the `η(z)` deformation parameterization + fit |
| `M_Q` | `experiments/E6.../outputs/` | the IDE `Q(z)` model + fit + SBT↔IDE equivalence result |
| `M_μΣ` | `experiments/E7.../outputs/` | the MG `(μ₀,Σ₀)` model + fit + viability/instability flag |
| `M_Ξ` | `results/xi_cosmo_coherence.csv` (one entry per coherence member **E1–E7**, REGISTRY §3) + `plan/04` §3.1 ansatz | the single fitted `Ξ_cosmo` `(a₀,a₁,a₂[,β])`, the kernels, the stable-readout certificate (E3) |

> **The SBT-Ξ contender is assembled from the *coherence-checked* `Ξ`, not re-fit freely.** E8 reads the
> coherence ledger (whose entries already passed the §6.4 coherence gate upstream), assembles the single
> `Ξ_cosmo`, and the *only* fitting E8 does on `M_Ξ` is the joint posterior over the **already-declared**
> `(a₀,a₁,a₂[,β])` + standard cosmology/nuisances — for the evidence (A) and the cross-fit OOS (B). The
> ansatz form and the probe-shared kernel shapes are frozen (`plan/04` §3.1).

### 3.3 Determinism / provenance (mandatory; Brief §III; `plan/01` §9)

Every E8 run pins `{numpy, python, sampler}` seeds, sets `OMP_NUM_THREADS` deterministically for the
PolyChord-determinism check, uses **float64** throughout, and writes the run manifest
(`run_id`, date, seeds, datasets+versions, software versions incl. cobaya/CLASS/PolyChord/getdist/arviz,
the upstream `summary.json` hashes consumed, parameters, output files, `audit_status`). Re-running an
identical config reproduces the likelihood/forward-model evaluations bitwise and the committed `summary.json`/tables to a stated tolerance (chains by statistical equivalence, not bitwise) (Brief §III.A;
verified by `G-E8-DET`).

---

## 4. Method (pipeline)

### Step 0 — Precondition / dependency assertion (must pass first)
- Assert every `BLOCKED_BY` artifact (§8.1) exists; each upstream experiment is in `terminal_accepted` —
  `summary.json.terminal_state ∈ {PASS, ACCEPTED_NEGATIVE}` (REGISTRY §2, §11.4), never universal `PASS`;
  a `BLOCKED`/`PROGRAM_FAIL` upstream means E8 cannot run. The coherence ledger has consistent `Ξ` entries
  from all of **E1–E7** (REGISTRY §3) and the §6.4 coherence gate is green. Fail any ⇒ E8 **stops** with
  the precise missing/failed dependency logged (no partial competition is scored). If the coherence gate
  failed upstream, record the program-phase coherence FAIL (§7.5) and stop.

### Step 1 — Assemble contenders + joint likelihood
- Build the joint cobaya likelihood over the full §3.1 combination (CMB native `clik` + DESI BAO + SN +
  CCL 3×2pt/RSD + CMB-lensing + the E4 route-`H₀` posteriors as Gaussian priors per route).
- Instantiate the six contenders (§1) with frozen forms (§3.2). Assert the `Ξ_cosmo` ansatz rank
  ceiling (`G-E8-RANK`) and kernel linearity (re-checked from `plan/04` §9.2) before any fit.

### Step 2 — In-sample joint fits + PPC (yardstick C)
- For each contender: minimize (BOBYQA from ≥4 starts) → MCMC (cobaya Metropolis, ≥4 chains) to
  `R̂ − 1 < 0.01`, ESS > 400/chain. Record per-block + total `χ²`, `χ²/dof`, `k`, `BIC`, `AIC`, `DIC`.
- Run the §2.3 posterior-predictive checks: `N_pp` realizations per block, posterior-predictive
  p-values, the discrepancy heatmap.
- **Reproduction floor check** (`G-E8-REPRO`, std 1): every contender keeps `χ²/dof < 1.05` on the
  reproduced baseline blocks; ΛCDM/w₀w_a recover the E1 contours within tolerance.

### Step 3 — Bayesian evidence (yardstick A)
- For each contender: **PolyChord** nested sampling (≥2 seeds), `ln Z ± err`; compute `ln B_{M/Λ}` and
  `σ_{lnB}`. Verify run-to-run `ln Z` scatter `< 0.3` (`G-E8-EVID-DET`); else raise `n_live` and re-run.
- Record the Jeffreys-scale interpretation per contender.

### Step 4 — Leave-one-probe-out out-of-sample (yardstick B — DECISIVE)
- For each contender and each leg `L1…L5` (§2.2): fit to the training complement (held-out block's
  likelihood removed), draw the posterior-predictive of the held-out block, compute `PPD^{(M)}_{leg}`
  (E8.1), `OOS_RMSE^{(M)}_leg` (E8.2), and the composite `OOS^{(M)}` (E8.3).
- For `L2/L3` use the E5 CCL growth forward model; for `L4/L5` use the E4 route posteriors + the E1
  inverse-ladder. These legs are *imported* from E4/E5 where already computed and *re-scored uniformly*
  here so all contenders are on one footing (record provenance per leg).
- **The win check:** evaluate §2.2's condition for `M_Ξ` against `min_M OOS^{(M)}` and against the E1
  ΛCDM baseline OOS.

### Step 5 — Verdict (§2.4 lexicographic rule)
- Apply the four-step lexicographic decision (reproduction floor → out-of-sample → complexity/evidence →
  staging corroboration). Compute `CompositeScore` (E8.4) as a transparency sort.
- Pull in the E5 staging-fingerprint verdict and the E4 lawful-plurality verdict as the std-4
  corroboration columns.

### Step 6 — Master matrix + figures + AOR synthesis
- Emit `results/tables/model_competition.csv` (§5.1), the competition figures (§5.2), and the
  consolidated AOR status master (`results/tables/aor_status_master.csv`), advancing the carrier to the
  **AOR** target (§5.3).

### Software (Brief §II; `plan/02`)
`cobaya ≥3.4` (driver + likelihood orchestration + **PolyChord** interface + BOBYQA), `CLASS ≥3.2`
(Boltzmann; one backend per program), `pyccl ≥3.0` (3×2pt/RSD/CMB-lensing forward model for `L2/L3`),
`PolyChord` (the named evidence estimator), `getdist ≥1.5` (posteriors/contours), `arviz ≥0.15`
(`R̂`/ESS/PPC diagnostics), `numpy<2.0`/`scipy` (whitening, BIC/AIC arithmetic, composite z-scores),
`matplotlib ≥3.5`. Optional Lean 4 (`v4.28.0`) only to re-check the imported P4 stable-readout certificate
flag for the SBT-Ξ stability column (the certificate itself is produced in E3).

---

## 5. Outputs (exact artifacts)

Per-experiment artifacts live under `experiments/E8_model_competition/outputs/` (`plan/01` §7 layout:
`config.yaml`, `manifest.json`, `summary.json`, `tables/`, `figures/`, `chains/`, `aor_status.json`).
The cross-experiment publication deliverables are written to `results/` (`plan/01` §8).

### 5.1 The master model-competition matrix (THE headline deliverable)

`results/tables/model_competition.csv` — rows = the six contenders; columns (matching `plan/00` §8
done-item 6 and `plan/01` §8):

| Column | Meaning |
|---|---|
| `model` | `LCDM, w0waCDM, CDDR_only, IDE, MG, SBT_Xi` |
| `k`, `delta_k` | total / extra-beyond-ΛCDM free parameters |
| `chi2_total`, `chi2_per_dof` | in-sample joint fit (yardstick C) |
| `chi2_CMB, chi2_BAO, chi2_SN, chi2_WL, chi2_RSD, chi2_ladder` | per-block in-sample `χ²` |
| `dBIC_vs_LCDM`, `dAIC_vs_LCDM`, `DIC` | complexity-penalized in-sample comparison |
| `lnZ`, `lnZ_err`, `lnB_vs_LCDM`, `lnB_err`, `jeffreys` | **yardstick A** (PolyChord evidence) |
| `OOS_L1_SN, OOS_L2_growth, OOS_L3_geom, OOS_L4_invladder, OOS_L5_localH0` | **yardstick B** per-leg OOS RMSE (E8.2) |
| `OOS_composite` | **yardstick B** composite (E8.3) — the decisive number |
| `OOS_vs_LCDM_pct` | OOS improvement vs E1 ΛCDM baseline (signed %) |
| `PPC_min_pvalue`, `PPC_worst_block` | **yardstick C** calibration (worst posterior-predictive p-value + which block) |
| `staging_fingerprint` | E5 corroboration: `D_scale` / `budgeted` / `n_a` (SBT-Ξ only meaningfully) |
| `lawful_plurality` | E4 corroboration: holonomy verdict / `n_a` |
| `reproduces_baseline` | bool (std-1 floor) |
| `composite_score` | E8.4 transparency sort |
| `verdict_eligible` | bool (passed reproduction floor) |
| `is_winner` | bool (exactly one `true` if a winner is declared; all `false` if inconclusive) |

A companion `results/tables/oos_battery.csv` records, per (contender × leg), the train/held-out block
spec, `PPD` (E8.1), `N_q`, `OOS_RMSE`, and the cross-fit fold/seed provenance.

### 5.2 Figures (publication-grade, committed)

| Figure | Path | Must show |
|---|---|---|
| **Out-of-sample composite bar** | `results/figures/model_competition_oos.{pdf,png}` | `OOS_composite` per contender with the E1-ΛCDM-baseline line and the **combined uncertainty band of the best competitor** (the strict-`win` discriminator, REGISTRY §8 — SBT-Ξ must clear it to pass; a tie inside the band is not a pass); SBT-Ξ highlighted — **the decisive figure** |
| **Evidence vs complexity** | `results/figures/model_competition_evidence.{pdf,png}` | `ln B_{M/Λ} ± err` vs `Δk` per contender; Jeffreys bands; inconclusive zone shaded |
| **Per-leg OOS heatmap** | `results/figures/oos_battery_heatmap.{pdf,png}` | contender × leg matrix of `OOS_RMSE`, color-scaled; reveals *which* prediction each model wins/loses |
| **PPC discrepancy heatmap** | `results/figures/ppc_discrepancy.{pdf,png}` | contender × (probe,`z`/`ℓ`-bin) standardized posterior-predictive residuals (the neutrino-template analog) |
| **One-residual-nine-shadows (closed)** | `results/figures/nine_shadows_closed.{pdf,png}` | the §3 shadow map populated: each row's specialist model vs SBT-Ξ on that row's residual |

Also populate `results/tables/one_residual_nine_shadows.csv` (the `plan/01` §8 shadow map table) with
the measured per-row residuals from each contender, so the unification claim is auditable row-by-row.

### 5.3 AOR synthesis (the terminal carrier status)

- `experiments/E8_model_competition/outputs/aor_status.json` + the consolidated
  `results/tables/aor_status_master.csv` — every surviving tension across E0–E8 carries **exactly one**
  AOR base status (`zero | budgeted | bridged | hidden | moduli | selected | probabilistic |
  out_of_scope | blocked | approved_other`; **no `unstatused`**, `thm:F9`). Examples expected at E8:
  - the dark-energy "detection" itself, *if* SBT-Ξ wins out-of-sample → `bridged` (the apparent
    acceleration is a repaired closure residual, not an unbridged fundamental constant).
  - any contender that wins one leg but loses another (specialist over-fit) → its leg-loss is
    `budgeted` (bounded predictive cost).
  - the SN-compilation / WL-survey spread → `budgeted` (packaging signal, accounted).
  - the cc-problem QFT↔cosmology cross-layer identification → `out_of_scope`/`budgeted` (P2/F11,
    unbridged; never claimed solved).
  - a contender excluded by the reproduction floor → `blocked` with reason.
- **Carrier status target:** E8 synthesis aims for **AOR** (`Ξ_SB = 0`, all strata discharged) per
  `plan/04` §8.4 / `plan/00` §7; if a residual remains it is discharged at **CascadeStableAOR** (finite
  cascade, base statuses only) — the phase-end floor (`plan/04` §8.4, LOCKED).

### 5.4 Manifest + summary

`experiments/E8_model_competition/outputs/manifest.json` (Brief §III.B schema) + `summary.json` with all
`G-E8-*` gate evaluations as booleans + the numeric thresholds achieved. The summary records the
**single binding verdict** (`is_winner`, `verdict_reason`) and the AOR carrier status reached.

---

## 6. The decisive out-of-sample standard (evidence standard 3) — operationalized

This section isolates the program's load-bearing requirement (`idea.md` §10 std 3; §0.2 here) so it
cannot be diluted by the in-sample yardsticks.

### 6.1 Statement (LOCKED)

> **SBT-Ξ must WIN out-of-sample, not just in-sample.** Using the *single low-rank* `Ξ_cosmo` reused
> across E1–E7 (no per-probe fudge, ≤ +4 extra params), on the leave-one-probe-out battery `L1…L5`,
> SBT-Ξ must be a **strict `win`** (REGISTRY §8): its out-of-sample composite must be **better than
> *every* alternative beyond the combined uncertainty band** AND **after the complexity penalty**, with
> **no silent loss on any critical leg** (geometry, growth, Hubble), **and** it must **improve the E1
> ΛCDM baseline by > 3% on ≥ 1 held-out block**. A `tie` (within the best alternative's uncertainty
> band) is **NOT a pass**. A model that achieves a lower in-sample `χ²` or a higher `ln Z` but a *worse*
> out-of-sample composite does **not** win.

### 6.2 Why this is the discriminating test

- In-sample `χ²` and even evidence can reward flexibility on the *training* data. The closure claim is
  specifically that one residual *predicts across probes* — that geometry predicts growth and vice
  versa (`idea.md` §10 std 3, §6 E4). Only the held-out `PPD_{p→q}` (`plan/04` §4.4) measures that.
- A *specialist* model (e.g. `M_w` tuned to BAO+CMB+SN geometry) is expected to do well on `L1`
  (geometry→SN) but to gain nothing on `L2` (geometry→growth) or `L4/L5` (the Hubble routes) — its
  out-of-sample composite is dragged down by the legs it does not address. SBT-Ξ's claim is that *one*
  residual lifts *all* legs at once. The per-leg OOS heatmap (§5.2) makes this visible.

### 6.3 The explicit anti-fudge decision

`G-E8-OOS-DECISIVE` (the binding gate, §7.3) encodes §2.4 step 2: **out-of-sample is evaluated before
and dominates in-sample.** If `M_Ξ` is the best in-sample but not out-of-sample, `is_winner = false` and
the verdict is recorded as "SBT-Ξ in-sample only — out-of-sample FAIL (std 3)", a statused FAIL
(`budgeted` on the predictive axis, honestly reported, `plan/00` §8).

---

## 7. Pass / fail gates (quantitative, pre-registered)

> **Pre-registration discipline (`plan/00` §6, `plan/04` §9).** Thresholds are fixed **before** seeing
> results; any relaxation is a logged statused deviation (`budgeted`). Units: `χ²/dof`, `ΔBIC`/`ΔAIC`,
> `ln B ± σ_{lnB}`, whitened OOS RMSE (per-d.o.f. Mahalanobis), signed % vs baseline, posterior-predictive
> p-values. Gate IDs use the program convention `G-E8-*`.

### 7.1 Reproduction-floor + precondition gates (must pass first — else E8 cannot score a winner)

| Gate | Threshold | Fail condition | Source |
|---|---|---|---|
| `G-E8-DEPS` | every `BLOCKED_BY` artifact present; every upstream `summary.json.terminal_state ∈ {PASS, ACCEPTED_NEGATIVE}` (`terminal_accepted`, REGISTRY §2/§11.4 — never universal `PASS`); coherence ledger from all of E1–E7 consistent and §6.4 gate green | any missing dependency, an upstream `terminal_state` of `BLOCKED`/`PROGRAM_FAIL`, or upstream coherence FAIL | §0.3, §4 step 0; REGISTRY §2, §3, §11.4 |
| `G-E8-REPRO` | every contender keeps `χ²/dof < 1.05` on reproduced baseline blocks; ΛCDM/w₀w_a recover E1 contours within E1 tolerance | a contender cannot reproduce its baseline | `plan/00` §6.1; `idea.md` §10 std 1 |
| `G-E8-COV` | every block `Σ` PD, cond `< 10⁸`, finite (else `Σ^†` on legal quotient) | non-PD / ill-conditioned covariance | `plan/04` §4.0; Brief §VI.1 |
| `G-E8-CONV` | all contenders: `R̂ − 1 < 0.01`, ESS > 400/chain; PolyChord `ln Z` err `< 0.3` and run-to-run scatter `< 0.3` | non-convergence / unstable evidence | Brief §VI.2; §2.1 |
| `G-E8-DET` | re-run reproduces likelihood/forward-model bitwise + committed `summary.json`/tables to tolerance; chains by statistical equivalence (`R̂<1.01`, ESS, means/cov within MC error), not bitwise (REGISTRY §11.6) | non-reproducible | Brief §III.A |

### 7.2 Contender-discipline gates (anti-fudge on SBT-Ξ)

| Gate | Threshold | Fail condition |
|---|---|---|
| `G-E8-RANK` | SBT-Ξ uses the **single** coherence-checked `Ξ_cosmo`, `≤ +3` (minimal) / `≤ +5–7` (full) extra params; **no per-probe free `Ξ_p`**; kernels probe-shared and linear (`<1%`) | per-probe `Ξ_p`; `> +4` params with no BIC gain; kernel non-linearity `>1%` | `plan/04` §3.1, §9.2; `plan/00` §6.2 std 2 |
| `G-E8-FROZEN` | SBT-Ξ form/kernels read from coherence ledger, **not re-tuned**; only amplitudes + cosmology/nuisances sampled | E8 introduces new `Ξ` freedom / new physics / new data | §0 hard constraint; `plan/00` §2 |
| `G-E8-STABLEREADOUT` | the SBT-Ξ phantom-crossing stability column carries E3's full stable-readout certificate (P-dens ∧ P-adeq ∧ S-stab); at E8 the **no-growing-mode (S-stab)** component `max Re λ ≤ 0` is re-verified (P-dens/P-adeq established at E3, REGISTRY §11.2) | SBT-Ξ's `w_eff` crossing requires a ghost (E3 cert absent/failed) | E3; `plan/04` §6.4 / §9.5 P4 |

### 7.3 The decisive verdict gate (std 3 — BINDING)

| Gate | PASS | FAIL |
|---|---|---|
| **`G-E8-OOS-DECISIVE`** (the program verdict) | a strict `win` (REGISTRY §8): `OOS_composite(SBT-Ξ)` better than **every** competitor **beyond the combined uncertainty band** AND **after the complexity penalty**, with **no silent loss** on any critical leg (geometry/growth/Hubble), **AND** SBT-Ξ improves the E1 ΛCDM baseline OOS by `> 3%` on `≥ 1` held-out leg | a `tie` (within the best competitor's uncertainty band — **not a pass**), OR SBT-Ξ loses overall, OR a silent loss on any critical leg, OR SBT-Ξ composite `> 1.1×` best competitor (the leg-level floor), OR no held-out leg improves the ΛCDM baseline by `> 3%`, OR SBT-Ξ wins in-sample only | `idea.md` §10 std 3; REGISTRY §8; `plan/00` §6.2 std 3 / §6.3 E8; `plan/04` §9.3 |
| `G-E8-EVID` | `ln B_{Ξ/Λ} > 1` (target `> 3`), reported with `σ_{lnB}`; SBT-Ξ evidence `≥` ΛCDM and within `2σ_{lnB}` of (or better than) the best competitor | `ln B_{Ξ/Λ} < 0` (ΛCDM decisively favored) AND SBT-Ξ also loses out-of-sample | `idea.md` §9; `plan/00` §6.3 E8 |
| `G-E8-BIC` | SBT-Ξ `ΔBIC_vs_LCDM` not worse than `+5` vs the **best** competitor; SBT-Ξ ≥ ΛCDM composite | SBT-Ξ BIC `≫ 5` worse than best with no OOS compensation | `plan/00` §6.2 std 2 / §6.3 E8 |
| `G-E8-PPC` | every contender (incl. SBT-Ξ) has all reproduced-block posterior-predictive p-values in `[0.01, 0.99]`; SBT-Ξ has no catastrophic in-sample block failure | SBT-Ξ posterior-predictive `p < 0.01` on a reproduced block (does not even reproduce in-sample) | §2.3; Brief §IV |

### 7.4 Corroboration gates (std 4 — non-binding, but required to be reported)

| Gate | Threshold |
|---|---|
| `G-E8-STAGING` | the E5 staging-fingerprint verdict column is populated; if SBT-Ξ wins, the verdict is `D_scale` (or an explicitly statused `budgeted`), not white noise (`plan/04` §9.6 / `plan/00` §6.2 std 4) |
| `G-E8-PLURALITY` | the E4 lawful-plurality / holonomy verdict column is populated and structured (LP1–LP5 reported), corroborating the Hubble-route legs (`plan/04` §9.6) |
| `G-E8-COHERENCE` | (re-assertion of §6.4) the single `Ξ_cosmo` used here is the coherence-checked one; cross-amplitudes within `10×`, consistent sign — **program-phase make-or-break** | `plan/00` §6.4; `plan/04` §9.4 |

### 7.5 Pre-registered failure modes (std 5 — honored and reported with numbers)

E8 (and thus the **program**) records a **FAIL verdict** (each a *valid, statused* scientific outcome,
`plan/00` §8) if, after honest execution, any of:

1. **Out-of-sample loss or tie (the primary failure).** `G-E8-OOS-DECISIVE` fails — SBT-Ξ is not a
   strict `win` (REGISTRY §8): it merely **ties** the best competitor (within the combined uncertainty
   band — a tie is **not** a pass), loses overall, takes a silent loss on any critical leg
   (geometry/growth/Hubble), trips the leg-level floor (composite `> 1.1×` the best competitor), or no
   held-out leg beats the ΛCDM baseline by `> 3%`. *Statused:* the predictive closure claim is
   `budgeted`/not-bridged; reported as "SBT-Ξ does not win out-of-sample (std 3 FAIL)".
2. **Fudge / over-parameterization.** SBT-Ξ uses `> +4` extra params with no BIC gain, OR requires
   distinct per-probe `Ξ_p` (`G-E8-RANK` fail) — "the residual fragmented into probe-specific
   corrections" (`idea.md` §10 std 5; `plan/00` §6.3 E8 / §8).
3. **Coherence failure.** The §6.4 coherence gate is not green (E5 `K_S` vs E1 `K_L/K_M` `> 10×` or sign
   disagreement) — the sharpest refutation of "one residual, many shadows"; E8 stops at §4 step 0.
4. **Reproduction failure.** Any contender (especially the baselines) cannot reproduce its published
   result within tolerance (`G-E8-REPRO` fail) — the competition is built on an unverified pipeline and
   is void (`plan/00` §6.1).
5. **In-sample-only win.** SBT-Ξ is best in-sample (`χ²`/`ln Z`) but loses out-of-sample — the explicit
   anti-fudge trap (§6.3); recorded as FAIL on std 3, not spun as a partial win.
6. **Evidence decisively against.** `ln B_{Ξ/Λ} < 0` beyond `2σ_{lnB}` *and* out-of-sample loss — ΛCDM
   (or a specialist) is the audited best closure; SBT-Ξ is not selected.

> **What is NOT a program failure.** (a) SBT-Ξ *tying* a specialist on that specialist's own leg while
> winning the composite is a **win** (the generalist matched the specialist and beat it overall).
> (b) A specialist (`M_w`/`M_Q`/`M_μΣ`) winning a *single* leg is expected and fine, provided SBT-Ξ wins
> the composite. (c) An honest **FAIL** that is correctly statused (e.g. "ΛCDM remains the audited best
> closure out-of-sample") is a legitimate scientific result and the cc / Λ row is then statused
> accordingly (Λ **not** ruled out — the precursor's standing non-claim). The unacceptable outcomes are
> an unreproduced baseline, an `unstatused` residual, or a gate relaxed after the fact.

---

## 8. Dependencies, blocking, and links

### 8.1 Blocked by (E8 is strictly last — `plan/00` §4 E8 row, §7 carrier order)

- **`plan/03`** data acquisition: the full joint combination (§3.1) — CMB, BAO, SN (×3), WL (×3), RSD,
  CMB-lensing, local-ladder route posteriors, inverse ladder — with loaders, fallbacks, integrity gates.
- **`plan/02`** environment: cobaya + CLASS + pyccl + **PolyChord** (the named evidence estimator) +
  getdist + arviz; the per-program single-backend rule.
- **`plan/04`** §1–§9: the carrier, the four residuals (esp. **§4.4** `PPD_{p→q}`), the `Ξ_cosmo` ansatz
  + kernels, the `Δ_SBT` `λ·complexity` anti-fudge objective, the coherence gate, the AOR carrier
  hierarchy (target **AOR**).
- **E1** — verified ΛCDM/wCDM/w₀w_a baselines, per-block `χ²`, baseline `ln Z`, inverse-ladder `H₀`,
  E1-B SBT-geometry `Ξ` seed (`a₀`, `K_L/K_M`); the reproduction credential (std 1).
- **E2** — the **CDDR-only contender** `M_η` form + fit; the gluing-chart `Ξ` amplitude (`a₂`).
- **E3** — the phantom-crossing rewrite + **stable-readout certificate** (certifies SBT-Ξ's `w_eff` column).
- **E4** — the Hubble route matrix, holonomy `𝔥_γ`, route-`H₀` posteriors (legs `L4`,`L5`), the
  lawful-plurality verdict (std-4 corroboration).
- **E5** — the growth/staging fit, `K_G/K_S` amplitudes, the staging-fingerprint verdict
  (legs `L2`,`L3`; std-4 corroboration); the make-or-break coherence anchor.
- **E6** — the fitted **IDE contender** `M_Q` + the SBT↔IDE `Q`-equivalence result.
- **E7** — the fitted **MG contender** `M_μΣ` + the MG-as-repair viability/instability flag.
- **`results/xi_cosmo_coherence.csv`** — the coherence ledger that defines the *single* SBT-Ξ residual.

### 8.2 Blocks / unblocks (E8 is the terminus)

- **Closes the phase.** E8 produces the `plan/00` §8 done-items 6 (the committed model-competition
  matrix) and 7 (the AOR status master, zero `unstatused`), and certifies the carrier to its **AOR**
  target. No experiment depends on E8; E8 *is* the program verdict.
- **Feeds the (later, out-of-scope here) manuscript.** The matrix, the OOS bar/heatmap, the shadow-map
  table, and the AOR master are the publication-grade deliverables a later writing phase consumes
  (`plan/00` §0: prose is out of scope *now*).

### 8.3 `idea.md` citations

- **§9 "Model competition"** (verbatim contenders + the three machineries — *the spec for this file*).
- **§10 "The standard of evidence to aim for"**: std 1 (reproduce first — `G-E8-REPRO`), std 2 (one
  low-rank residual — `G-E8-RANK`/`G-E8-COHERENCE`), **std 3 (win out-of-sample — `G-E8-OOS-DECISIVE`,
  the binding gate)**, std 4 (staging fingerprints — `G-E8-STAGING`/`G-E8-PLURALITY`), std 5
  (pre-register failure modes — §7.5).
- **§6 Experiment 4** (the leave-one-probe-out PPD battery `L1…L5` aggregated here).
- **§3 shadow map** (the six charts whose specialist models compete with the one residual).
- **UPDATE block** (the Hubble routes that enter via E4 legs `L4`,`L5` and the lawful-plurality column).

### 8.4 Corpus citations

- **`A_Six_Birds_Eye_View_of_Dark_Energy`** — the precursor: closure package, route mismatch, "Λ not
  ruled out" (the standing non-claim that frames an honest E8 FAIL); the model-as-package framing the
  competition formalizes.
- **`Adequacy_Residuals`** — `Ξ_C(D∣L)` as the Schur complement; the residual calculus behind the
  *single* `Ξ_cosmo` whose adequacy E8 tests against the field's specialist models; the
  optimal-residual / DPI laws underlying "least rewrite wins out-of-sample".
- **`Audited_Operational_Realisability` (AOR)** — the carrier hierarchy `PreSB → RefStableAOR →
  CascadeStableAOR → AOR`; E8 synthesis targets **AOR**; the AOR-8 statuses for the master ledger; the
  No-Unstatused-Residual discipline (`thm:F9`).
- **`Foundations_IV`** — `thm:F2` Descent-Repair (the SBT-Ξ rewrite, P1), `thm:F4` Local-Global (the
  CDDR-only contender, P3), `thm:F11` Adequacy/No-Overread (the cc-row statusing, P2), `thm:F9` No
  Unstatused Residual (the AOR-master obligation).
- **`Emergence_IS_the_Needle_Killer`** — the membrane positivity / layer-dissolving endpoint that
  underwrites the imported E3 stable-readout certificate used in the SBT-Ξ stability column.
- **`Six_Birds_for_Neutrino_Mass`** — the cross-lens held-out-mismatch + localization template the OOS
  legs (`L2`,`L3`) and the PPC discrepancy heatmap reuse; the worked audit pattern E8 generalizes to a
  full leave-one-probe-out competition.

### 8.5 arXiv anchors

DESI DR2 BAO 2503.14738; Planck 2018 1807.06209; Pantheon+ 2202.04077; Union3 2401.06956; DES-SN5YR
Zenodo:13827844; DES Y6 2601.14559; KiDS-Legacy 2503.19441; HSC Y3 2511.18134; DESI DR1 full-shape RSD/MG
2411.12026 / 2411.12022; ACT DR6 / CMB-lensing 2509.02945; SPT-3G D1 2506.20707; SH0ES 2509.01667; CCHP_TRGB_JAGB
2408.06153; TDCOSMO 2110.00517; GW170817 1709.05895; CDDR critique (Afroz–Mukherjee) 2504.16868; IDE
2503.23225.

---

## 9. Compute / runtime budget (Brief §IV)

E8 is the most expensive experiment: it runs Bayesian model comparison across **six** contenders
(PolyChord, ≥2 seeds each) plus a **five-leg leave-one-probe-out** battery per contender.

| Task | Hardware | Wall time | Memory | Notes |
|---|---|---|---|---|
| Full joint MCMC per contender (×6) | 32–64 CPU | 12–24 h each | 16–32 GB | yardstick C + PPC |
| PolyChord evidence per contender (×6, ×≥2 seeds) | 64 CPU | 24–72 h each | 32 GB | yardstick A; Brief §IV "Bayesian model comparison … 120–360 h total" |
| Leave-one-probe-out OOS (×6 contenders × 5 legs) | 32 CPU | 72–144 h total | 16 GB | yardstick B; Brief §IV "PPD leave-one-probe-out … 72–144 h" — **import** E4/E5 legs where computed |
| Matrix assembly + figures + AOR synthesis | 8 CPU | < 1 h | 4 GB | reads committed upstream artifacts |

Pragmatic order (`plan/00` §6.5 spirit): assert dependencies (Step 0, cheap) → in-sample + PPC (Step 2)
→ OOS battery (Step 4, import E4/E5 legs to avoid recompute) → PolyChord evidence (Step 3, most
expensive, last) → verdict + matrix (Steps 5–6). The decisive `G-E8-OOS-DECISIVE` can be evaluated after
Step 4, before the costly evidence runs, to fail fast if SBT-Ξ loses out-of-sample.

---

## 10. Step-by-step implementation checklist

1. Assert all `BLOCKED_BY` (§8.1) present; every upstream `summary.json.terminal_state ∈ {PASS,
   ACCEPTED_NEGATIVE}` (`terminal_accepted`, REGISTRY §2/§11.4 — never universal `PASS`); coherence
   ledger from all of E1–E7 consistent and §6.4 green (`G-E8-DEPS`). Stop on any failure.
2. Build the joint cobaya likelihood over the full §3.1 combination; instantiate the six contenders
   with **frozen** forms (§3.2); assert `G-E8-RANK`, `G-E8-FROZEN`, kernel linearity.
3. Per contender: minimize → MCMC to `R̂−1<0.01`, ESS>400; record per-block + total `χ²`, `k`, BIC/AIC/DIC.
4. Run PPC (yardstick C): posterior-predictive p-values, discrepancy heatmap; check `G-E8-REPRO`,
   `G-E8-PPC`.
5. Run the leave-one-probe-out battery `L1…L5` (yardstick B): import E4 (`L4`,`L5`) and E5 (`L2`,`L3`)
   legs, compute `L1` here; uniformly re-score `PPD`/`OOS_RMSE`/`OOS_composite` (E8.1–E8.3). Build
   `oos_battery.csv`. **Evaluate `G-E8-OOS-DECISIVE` (fail fast if SBT-Ξ loses).**
6. Run PolyChord evidence (yardstick A, ≥2 seeds/contender): `ln Z`, `ln B_{M/Λ}`, Jeffreys scale;
   check `G-E8-EVID-DET` scatter `< 0.3`, `G-E8-EVID`, `G-E8-BIC`.
7. Apply the §2.4 lexicographic verdict; compute `CompositeScore` (E8.4); populate the std-4
   corroboration columns from E4/E5 (`G-E8-STAGING`, `G-E8-PLURALITY`); re-assert `G-E8-COHERENCE`.
8. Emit `results/tables/model_competition.csv` (§5.1), `oos_battery.csv`,
   `one_residual_nine_shadows.csv`, and the §5.2 figures.
9. Synthesize the consolidated AOR status master (`results/tables/aor_status_master.csv`); status every
   residual; advance the carrier toward **AOR** (§5.3). Confirm zero `unstatused` (`thm:F9`).
10. Write `manifest.json` + `summary.json` with all `G-E8-*` gates and the single binding verdict
    (`is_winner`, `verdict_reason`, carrier status). Verify determinism (`G-E8-DET`).

---

## 11. Cross-experiment links (summary)

- **Consumes** E1 (baselines + inverse ladder + SBT-geom seed), E2 (CDDR-only contender), E3 (stable-readout
  cert), E4 (Hubble routes + holonomy + legs `L4`/`L5`), E5 (growth + staging + legs `L2`/`L3`), E6 (IDE
  contender), E7 (MG contender), and the coherence ledger.
- **Produces** the program verdict: the master model-competition matrix, the out-of-sample decisive
  figure, the shadow-map closure table, and the AOR status master — closing `plan/00` §8 done-items 6
  and 7 and certifying the carrier to its **AOR** target.
- **Decisive gate** `G-E8-OOS-DECISIVE` (std 3): SBT-Ξ must win *out-of-sample* with the single low-rank
  `Ξ_cosmo`, or the unification thesis is honestly, statusedly refuted.
