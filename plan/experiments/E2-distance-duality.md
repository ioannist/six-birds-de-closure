# E2 — Distance Duality as a Local–Global Obstruction

> **One-line charter.** Treat the cosmic distance-duality relation (CDDR) audit
> `η(z) = D_L(z) / [(1+z)² D_A(z)]` as the **local–global gluing test** between the SN
> luminosity-distance section `f_SN` and the BAO angular/radial-distance sections `f_BAO`,
> and decide — *without forcing one answer in advance* — whether the DESI-preferred apparent
> `w_a` is a **rewrite residual** (genuine `Ξ_cosmo` repair, P1/F2), a **gluing residual**
> (a CDDR/calibration obstruction, P3/F4), or a **mixture**.

> **Read-order / consistency.** This file implements *one* experiment of the program defined in
> `plan/00-overview.md` (§3 shadow map, §6 gates, §8 done) and `../GROUNDING_BRIEF.md`
> (datasets, stack, AOR vocabulary). Every formal object used here is *locked* in
> `plan/04-formal-foundations.md`: the carrier and the four residuals (§4), the low-rank ansatz +
> kernels `K_L/K_M` (§3), proposition **P3 ↔ F4** (§6.3), the metric `d` (§4.0), and the AOR
> status catalogue (§8). Data products and access are locked in `plan/03-data-acquisition.md`
> (BAO §2, SN §4). **Science source of truth:** `idea.md` §3 (shadow map row 4), §6 Experiment 2,
> §7 ("Dataset inconsistency and distance duality"), and §10 (five hard standards). This file
> does **not** re-derive those objects; it specifies the *pipeline, models `M₀/M₁/M₂`, outputs,
> and pre-registered pass/fail gates*.
>
> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean/finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a
> gate in §8 below).

---

## 1. Scientific framing and grounding

### 1.1 What this experiment is about

`idea.md` §3 (shadow map, **row 4**) and §6 **Experiment 2** state the thesis precisely:

> *"SN luminosity distances `D_L` and BAO angular/radial distances `D_M`, `D_H` may be locally
> valid probes but fail to glue into one global FLRW completion; `η(z) = D_L/[(1+z)²D_A]`
> deviation is the measured gluing defect."* — `idea.md` §3 row 4; `plan/00-overview` §3 row 4.

The **headline of the program** (`idea.md` §3; `plan/00-overview` §3 "one-line headline"):
`Λ`, `w_a`, `Q_IDE`, **`η_CDDR`**, `μ/Σ`, and `S₈` shifts are *coordinate charts on the same
closure defect* `Ξ_cosmo(z,ℓ,p)`. E2 is the experiment that isolates the **gluing chart** (`η`)
and asks how much of the **redshift chart** (`w_a`) it can absorb.

E2 is the formal centerpiece for **Proposition P3 ↔ F4** (`plan/04` §6.3): *distance duality is
the statement that the SN and BAO local sections globalize into one metric-distance object; CDDR
failure is a gluing obstruction, not automatically new dark energy.* The audit functional is the
local–global gluing defect `LG_{SN,BAO}` of `plan/04` §4.3 (eq. 13), measured with the explicit
`η(z)` overlap relation.

### 1.2 The live controversy this experiment must engage (mandatory)

`idea.md` §3 and §7 ("Your strongest claim needs nuance") frame two *opposed* published readings
that E2 must engage **explicitly and adversarially** — the experiment is designed not to
pre-decide between them:

| Source | arXiv | Claim | What it implies for `η(z)`/`w_a` |
|---|---|---|---|
| **Afroz & Mukherjee** | **2504.16868** | Pantheon+ SN and DESI DR2 BAO show a **redshift-dependent CDDR violation**; once the inconsistency is modelled, the DESI evolving-DE signal is **absent** (they report `w₀ = −0.92 ± 0.08`, `w_a ≈ −0.49` with broad uncertainty). | `η(z) ≠ 1` → **OverlapInconsistent** (F4); apparent `w_a` *collapses into the gluing residual*. |
| **Crossing-Statistics consistency** | **2604.19393** | A model-independent consistency test finds DESI DR2 BAO and Pantheon+/Union3 SN remain **mutually consistent** under flexible deformations while still permitting a low-z evolving-DE reconstruction. | `η(z) ≡ 1` (within deformation freedom) → **CompatibleNonGlobal** or **GloballyExact** (F4); apparent `w_a` is *not* a gluing artifact and must be a rewrite residual. |
| (corroborating, low weight) PAge + Gaussian-process | 2603.27616 | CDDR valid within 1σ using recent SN/BAO/chronometer/GRB incl. DESI DR2. | consistency leg; cross-check on `η≡1`. |
| (corroborating, low weight) DESI–DES SN crosscheck | 2510.04179 | `D_M/r_d` consistent with SN up to calibration; `D_H/r_d` shows only a mild trend whose significance is treatment-dependent. | calibration-degeneracy leg; informs the `M_B`–`r_d` nuisance handling (§3.4). |

> **`idea.md` §6 Exp2 pass criterion (verbatim intent):** *"Six Birds must explain whether the
> DESI signal is a genuine rewrite residual, a gluing residual, or a mixture. The paper becomes
> stronger if it does **not** force one answer in advance."* This is operationalized in §8 as a
> **decision gate with three admissible verdicts**, each with its own quantitative threshold.

### 1.3 Foundations grounding (P3 ↔ F4)

The local–global obstruction normal form (`Foundations_IV` `thm:F4`, Lean
`Transport.LocalGlobalObstruction.local_global_obstruction_normal_form`; restated in `plan/04`
§6.3) is the spine of E2. For a compatible local family, *globalization ⇔ membership in the
restriction image*, and **every compatible family carries exactly one of four statuses**:

```
ExactlyOneStatus(a) ⇔ OverlapInconsistent(a) ⊻ CompatibleNonGlobal(a)
                       ⊻ GloballyAmbiguous(a) ⊻ GloballyExact(a)
```

determined by `Comp(a)` (overlap compatibility), membership in `R(𝒢)` (image of the FLRW
restriction map), and the fiber cardinality `|R⁻¹(a)|`. The cosmological instantiation
(`plan/04` §6.3) is fixed below in §4.

Secondary anchors actively used:
- **F2 Descent–Repair Normal Form** (`thm:F2`): if FLRW descent fails, F2 supplies exactly **two** repairs:
  source refinement and minimal target coarsening. `M₂`'s `Ξ_cosmo` is the **P1 operator-rewrite chart** (the P1 extension of F2 applied to the same obstruction, NOT a third F2 repair) — the *operator
  rewrite* leg. The competition `M₁` vs `M₂` is precisely "rewrite the `w(z)` history" vs "rewrite
  via the gluing residual."
- **Adequacy Residuals** (`Ξ_C(D∣L)` Schur complement): the gluing defect is the part of the joint
  SN+BAO dissolving family the single FLRW native family cannot explain (`plan/04` §1).
- **F9 No Unstatused Residual** (`thm:F9`): whatever `η(z)` and the apparent `w_a` resolve to, the
  leftover must carry exactly one AOR status (§7).

### 1.4 The CDDR identity made concrete (LOCKED)

In a flat FLRW background the transverse comoving distance `D_M(z)` and angular-diameter distance
`D_A(z)` satisfy `D_A(z) = D_M(z)/(1+z)`, and Etherington reciprocity gives
`D_L(z) = (1+z)² D_A(z) = (1+z) D_M(z)`. Hence the CDDR audit ratio reduces to a form built
**directly from the two observed sections**:

```
η(z) = D_L(z) / [(1+z)² D_A(z)] = D_L(z) / [(1+z) D_M(z)]                                   (E2.1)
```

- `D_L(z)` is read from SN distance moduli: `μ(z) = 5 log₁₀(D_L/10 pc)`, so
  `D_L = 10^{(μ − 25)/5}` Mpc (with `μ = m_B − M_B`).
- `D_M(z)` is read from BAO: the released `D_M(z)/r_d` times the sound horizon `r_d`.

> **The unavoidable calibration degeneracy (LOCKED, this is the crux).** SN measure `D_L` only up
> to the absolute magnitude `M_B` (an additive `μ` offset); BAO measure `D_M/r_d` only up to the
> sound horizon `r_d`. Therefore the *amplitude* of `η(z)` is degenerate with the constant
> `c ≡ 10^{−M_B/5} · r_d`, and **only the redshift *shape*** of `η(z)` is calibration-independent.
> This is exactly the "up to calibration" caveat in the DESI–DES crosscheck (2510.04179) and the
> reason Afroz–Mukherjee's *evolving* `η(z)` is the load-bearing claim, not its normalization. E2
> therefore tests two things separately:
> 1. **`η₀` (amplitude):** absorbed into the `(M_B, r_d)` nuisance pair — a `selected`/`moduli`
>    residual, never itself counted as a CDDR violation.
> 2. **`η(z)/η₀` (shape):** the genuine gluing diagnostic. A non-flat shape is the F4
>    `OverlapInconsistent` signature.

---

## 2. The three models (LOCKED)

E2 fits **three nested models** to the *same* SN+BAO joint data, sharing background parameters
`θ = (Ω_m, H₀ r_d, …)` and the SN/BAO calibration nuisances `(M_B, r_d)` where applicable.
This is the `M₀/M₁/M₂` triad of `idea.md` §6 Exp2 and `plan/00-overview` §6.3 (E2 row):

| Model | `η(z)` | `w(z)` | Extra free params beyond ΛCDM | Reads as | F-law |
|---|---|---|---|---|---|
| **`M₀`** | `η(z) ≡ 1` (Etherington imposed) | `w = −1` (ΛCDM) | 0 | the null / GR + Λ | baseline |
| **`M₁`** | `η(z) ≡ 1` (Etherington imposed) | `w₀wₐ` (CPL: `w(a)=w₀+wₐ(1−a)`) | `+2` (`w₀, wₐ`) | the DESI dynamical-DE reading | P1 operator-rewrite (extension of F2) of `w(z)` |
| **`M₂`** | `η(z) ≠ 1` (free shape) **and** `Ξ_cosmo ≠ 0` | `w = −1` background; deviations carried by `Ξ` | `+1…3` (`a₀,a₂[,β]`) gluing-chart | the SBT gluing reading | P3/F4 + the `Ξ` gluing chart |

> **`M₂` construction detail (LOCKED).** `M₂` does **not** add a free `w(z)`. It keeps the
> background at `w=−1` and lets the **gluing/calibration chart** of the low-rank ansatz absorb the
> SN–BAO tension. From `plan/04` §3.1 (ansatz eq. 4) the gluing chart is the **term-2** piece
> `a₂ · φ₂(z) · c_p` with `φ₂(z)=ln(1+z)` and probe weights `c_SN=+1`, `c_BAO=−1` (`plan/04` §3.1
> table). The induced observable shifts are the *same* kernels used everywhere else:
> ```
> D_L^obs(z)       = D_L^FLRW(z;θ)       + K_L[Ξ](z)     (plan/04 eq. 6; SN, c_SN=+1)
> (D_M/r_d)^obs(z) = (D_M/r_d)^FLRW(z;θ) + K_M[Ξ](z)     (plan/04 eq. 7; BAO, c_BAO=−1)
> ```
> Because `c_SN` and `c_BAO` have **opposite sign**, a single term-2 amplitude `a₂` pushes `D_L`
> and `D_M` in opposite directions — i.e. it generates exactly a redshift-shaped `η(z)−1`. This is
> why the gluing chart is the natural carrier of a CDDR defect, and why it can *mimic* `w_a` while
> using **fewer** parameters and **shared** shapes (the anti-fudge rank constraint, `plan/04` §3.1
> "Hard rule"). The map `(a₂, φ₂) → η(z)` is the operational link from `Ξ_cosmo` to the F4 overlap
> predicate.

> **Auxiliary models for the decision gate (declared, run only for model comparison):**
> - **`M₁₊₂`** (mixture): `w₀wₐ` background **and** the gluing chart `a₂` active. Tests whether the
>   data want *both* a rewrite and a gluing residual (the "mixture" verdict).
> - **`M_AM`** (Afroz–Mukherjee replica): `w₀wₐ` plus a *parametric* `η(z)=1+ε₀ z` (or
>   `η(z)=(1+z)^ε`) CDDR-violation term, fit jointly, to reproduce 2504.16868's reported
>   `w₀≈−0.92, wₐ≈−0.49` collapse. This is the literal replication leg (§6).

---

## 3. Inputs

### 3.1 Datasets (versions and access — from `../GROUNDING_BRIEF.md` §I and `plan/03`)

| Probe | Dataset | Release | Vector | Covariance | Loader (`plan/03`) | Role | AOR status of fallback |
|---|---|---|---|---|---|---|---|
| **SN (primary)** | **Pantheon+** | arXiv:2202.04077 | `μ(z_hel, z_cmb)`, 1550 SN, z=0.01–2.26 | full stat+sys `C_μμ` (1550×1550) | `load_pantheon_plus(z_min=0.023)` | `D_L(z)` section `f_SN` | `zero` (full) / `budgeted` (binned) |
| **SN (cross-check)** | **Union3** | arXiv:2401.06956 | 1258 SN standardized dist. | systematic block cov | `load_union3()` | second SN section (consistency leg) | `budgeted` (5-bin) |
| **SN (precursor leg)** | **DES-SN5YR** | Zenodo:13827844 / arXiv:2401.02929 | 1470 SN `μ(z)` | calibration cov | `load_des_sn5yr()` | third SN section; precursor continuity | `budgeted` |
| **BAO (primary)** | **DESI DR2 BAO** | arXiv:2503.14738 | `D_M(z)/r_d`, `D_H(z)/r_d` per tracer bin (~13–15 elt) | full analytic+mock | `load_desi_dr2_bao()` | `D_M(z)` section `f_BAO` (+ `D_H` for the radial leg) | `budgeted` (compressed BAO-only) |
| **CMB anchor (prior leg)** | Planck 2018 | arXiv:1807.06209 | TT/TE/EE compressed (`Ω_m`, `θ*`, `r_d` prior) | published | `load_planck2018(compressed=True)` | anchors `r_d`, breaks `M_B–r_d` partially (§3.4) | `budgeted` (compressed) |

> **SN-dataset dependence is a signal, not noise (`idea.md` §6 Exp1; `plan/03` G-DATA-9).** Run the
> CDDR audit **separately** for Pantheon+, Union3, DES-SN5YR against the *same* DESI DR2 BAO. Any
> spread in the resulting `η(z)` shape / `M₂` verdict across SN compilations is itself a packaging
> signal (P4 staging) and must be **recorded, not averaged away**.

### 3.2 Redshift handling and section overlap (LOCKED)

- SN and BAO live at *different* effective redshifts. To form `η(z)` (eq. E2.1) one must evaluate
  `D_L^SN` and `D_M^BAO` at a **common** `z`. Use a **model-independent reconstruction** of each
  section onto a shared `z`-grid (Gaussian-process or local-polynomial smoothing of each probe's
  distance section), as in the Crossing-Statistics methodology (2604.19393) and PAge/GP (2603.27616).
  This avoids assuming the FLRW model in the overlap test itself (critical: the *gluing test must
  not pre-bake the global object*).
- Shared grid: `z ∈ {0.05, 0.10, …, 2.0}` (Δz=0.05), restricted per-probe to each section's support
  (SN: z≳0.023 after peculiar-velocity cut; DESI BAO `z_eff ∈ [0.51, 2.33]`). Overlap region for
  the **primary** CDDR test: `z ∈ [0.51, 1.5]` where both probes have data; extrapolation outside is
  flagged `D_horizon` (sampling-cutoff residual, `plan/04` §8.2) and excluded from the headline gate.

### 3.3 Parameters and priors

| Parameter | Model(s) | Prior | Notes |
|---|---|---|---|
| `Ω_m` | all | `U(0.1, 0.6)` | background |
| `H₀ r_d` (or `Ω_m`, `r_d·h`) | all | `U` broad | BAO measures this combination |
| `w₀` | `M₁`, `M₁₊₂`, `M_AM` | `U(−3, 1)` | CPL |
| `wₐ` | `M₁`, `M₁₊₂`, `M_AM` | `U(−3, 2)` | CPL |
| `M_B` (SN abs. mag) | all with SN | `U` broad, or `N` from SH0ES if a ladder prior is declared | calibration nuisance (§3.4) |
| `r_d` | all with BAO | `N(147.1, 0.3)` Mpc from Planck (when CMB prior leg on) else `U` | calibration nuisance |
| `a₀` (Λ-chart) | `M₂`, `M₁₊₂` | `U`, `complexity`-penalized | usually inactive in E2 (geometry-only); kept for coherence with E1 |
| `a₂` (gluing chart) | `M₂`, `M₁₊₂` | `U`, `complexity`-penalized | **the E2 control parameter** |
| `β` (ℓ-response) | optional | `U(0,2)` | not used in E2 (no ℓ structure in pure geometry); fixed unless logged |
| `ε₀` (AM CDDR slope) | `M_AM` only | `U(−0.5, 0.5)` | replica of 2504.16868 |

> **Ansatz rank ceiling (anti-fudge, `plan/04` §3.1 / §9.2).** `M₂` adds **≤ 3** free params beyond
> ΛCDM (`a₀, a₂[, β]`), and the shapes `φ₀, φ₂, c_p` are **fixed and probe-shared** — *no per-probe
> free `Ξ_p`*. Any extension is a logged statused deviation.

### 3.4 The `M_B`–`r_d` calibration handling (LOCKED — required for honesty)

Because `η₀` amplitude ≡ `c = 10^{−M_B/5} r_d` is degenerate (§1.4), the experiment must:
1. **Marginalize** over `(M_B, r_d)` analytically (Gaussian) or via MCMC in every model, so the
   headline CDDR test is on the **shape** `η(z)/η₀`, not the amplitude.
2. Run in **two calibration regimes** and report both:
   - **Regime A (uncalibrated):** flat `M_B`, flat `r_d` → only `η(z)` *shape* is constrained.
     This is the cleanest pure-gluing test (no external ladder/CMB injected).
   - **Regime B (anchored):** `r_d` Planck-prior `N(147.1,0.3)` Mpc + `M_B` SH0ES-style prior →
     `η₀` becomes measurable. Differences between A and B are themselves a **bridge residual**
     (P2-adjacent; status `bridged` or `budgeted`).
3. Record the `η₀` amplitude shift as a `selected`/`moduli` residual (`plan/04` §8.3), **never** as
   a CDDR violation. A nonzero *slope/curvature* of `η(z)` is the only thing that counts as a gluing
   obstruction.

---

## 4. The F4 instantiation (the decision spine) (LOCKED)

Following `plan/04` §6.3, instantiate the F4 normal form on the SN/BAO pair:

| F4 object | Cosmological instantiation |
|---|---|
| patch index `I` | `{SN, BAO}` |
| local objects `Q_i` | fitted/reconstructed distance sections: `D_L^SN(z)`, `D_M^BAO(z)` (and `D_H^BAO(z)` radial leg) |
| overlap predicate `Comp(a)` | the CDDR relation `η(z) = D_L/[(1+z)D_M] = 1` (shape-flat) within whitened tolerance |
| global object set `𝒢` | FLRW completions `U_θ` (the `M₀`/`M₁` family) |
| restriction `R: 𝒢 → 𝓕` | restriction of an FLRW state to the two distance probes |
| `Globalizes(a)` | `∃ g ∈ 𝒢, R(g)=a`: a single FLRW reproduces *both* sections |
| fiber `R⁻¹(a)` | the set of FLRW completions reproducing the glued family |

**The four-status classification of the fitted glued family `a = (D_L^SN, D_M^BAO)`** (`plan/04`
§6.3; `Foundations_IV` `thm:F4`):

| Status | Condition (operational) | Physical reading | Decision verdict | AOR status (§7) |
|---|---|---|---|---|
| **`GloballyExact`** | `Comp(a)` holds (`η`-shape flat) **and** `a ∈ R(𝒢)` with `|R⁻¹(a)|=1` (unique FLRW fits both) | no obstruction; one FLRW reproduces SN+BAO | apparent `w_a` (if any) is a **rewrite residual**, *not* gluing | `zero` (gluing) / `bridged` (if `w_a≠0` via `M₁`) |
| **`CompatibleNonGlobal`** | `Comp(a)` holds (`η`-shape flat) **but** `a ∉ R(𝒢)` (no single FLRW reproduces both) | the **subtle case** `idea.md` §6 E2 wants: overlap test passes yet no global FLRW exists | **mixture**: a real residual exists that is *not* a CDDR violation | `bridged` (by `Ξ`) |
| **`OverlapInconsistent`** | `¬Comp(a)` (`η`-shape *not* flat: slope/curvature significant) | the **Afroz–Mukherjee** reading (2504.16868): SN+BAO genuinely inconsistent | apparent `w_a` **collapses into the gluing residual** | `bridged` (CDDR-repair) / `D_local`,`D_global` typed |
| **`GloballyAmbiguous`** | `Comp(a)` holds **and** `|R⁻¹(a)|>1` (a family of FLRW fits both) | flat direction; data underdetermine the completion | a `moduli` residual; cannot decide rewrite vs gluing | `moduli` |

> **The status is the verdict.** The whole experiment funnels to assigning the fitted `η(z)` exactly
> one of these four statuses (F4 exclusive-or), with quantitative thresholds in §8. Each maps to one
> of the three admissible decisions of `idea.md` §6 Exp2 (rewrite / gluing / mixture) — see §8.4.

---

## 5. Method (pipeline)

> **Determinism/provenance (mandatory, `GROUNDING_BRIEF` §III).** Every run pins
> `numpy`/`random`/sampler seeds, writes a run-manifest JSON (`run_id`, date, seeds, datasets+versions,
> software versions, parameters, output files, `audit_status`), and emits `[chain, posterior.hdf5,
> triangle.png]`. `float64` throughout. Reproduce-before-rewrite gate G-DATA-3 (`plan/03`) must pass
> first.

### Step 0 — Reproduce baselines (gate `G-E2-REPRO`, §8.1)
- Load Pantheon+ (`C_μμ` PD, Cholesky OK) and DESI DR2 BAO (cov PD, κ<10⁸).
- Fit `M₀` (ΛCDM) and `M₁` (`w₀wₐ`) jointly to **SN + DESI BAO (+ Planck prior leg)** with the
  team stack (`cobaya ≥3.4` + `CLASS ≥3.2`/`CAMB ≥1.5.7`; `getdist`/`arviz` diagnostics).
- **Must recover** the published DESI DR2 `w₀wₐ` contour (`w₀ > −1, wₐ < 0`) and the 2.8–4.2σ
  dynamical-DE preference band **before** any `Ξ`/`η` machinery (`idea.md` §10 test 1).
- Convergence: Gelman–Rubin `R̂ < 1.01` all params; ESS > 400/chain.

### Step 1 — Model-independent section reconstruction
- Reconstruct `D_L^SN(z)` from `μ(z)` (eq. E2.1) and `D_M^BAO(z)` from `D_M/r_d · r_d`, each by
  Gaussian-process / local-polynomial smoothing onto the shared grid (§3.2), **propagating full
  covariance** to the reconstructed sections (whitened with `Σ^{-1}`, `plan/04` §4.0). Use the
  Crossing-Statistics-style deformation freedom (2604.19393) so the test is not FLRW-biased.

### Step 2 — Compute the CDDR audit and the gluing residual `LG_{SN,BAO}`
- Form `η(z)` and `η(z)/η₀` (eq. E2.1) on the overlap grid, both calibration regimes (§3.4).
- Compute the gluing defect `LG_{SN,BAO} = d(glue(f_SN, f_BAO), R(g_best))` (`plan/04` eq. 13):
  the whitened residual of the best joint FLRW globalization subject to the CDDR overlap relation.
- Compute the **shape test statistic**: fit `η(z) = η₀ · (1 + ε₀·g(z))` (with `g(z)=z` and, as a
  robustness check, `g(z)=ln(1+z)`) and test `ε₀ = 0` (flat shape).

### Step 3 — Fit the three models `M₀/M₁/M₂` (+ auxiliaries)
- Joint MCMC for `M₀, M₁, M₂` (and `M₁₊₂, M_AM`) to SN+BAO(+Planck). For `M₂`, the gluing chart
  `a₂` perturbs `D_L`/`D_M` with opposite-sign `c_p` (§2). Marginalize `(M_B, r_d)`.
- Record for each model: `χ²`, `χ²/dof`, `k` (params), `BIC = χ² + k ln N`, `AIC`, posteriors.

### Step 4 — The `w_a`-collapse test (the central question)
- Quantify how much of the `M₁` apparent `w_a` is absorbed by the gluing residual. Define the
  **collapse fraction**
  ```
  F_collapse = 1 − |w_a^{M₁₊₂}| / |w_a^{M₁}|                                                  (E2.2)
  ```
  i.e. the fractional reduction of the fitted `w_a` when the gluing chart `a₂` is *also* allowed to
  absorb the SN–BAO tension (mixture model `M₁₊₂`). `F_collapse → 1` ⇒ `w_a` is essentially a
  gluing artifact (Afroz–Mukherjee direction); `F_collapse → 0` ⇒ `w_a` survives the gluing chart
  (Crossing-Statistics direction). Report with posterior credible interval.
- Cross-check by the **replica** `M_AM`: refit with the explicit parametric `η(z)=1+ε₀z` and verify
  whether the DESI `w_a` migrates toward the reported `w₀≈−0.92, wₐ≈−0.49` of 2504.16868.

### Step 5 — Out-of-sample / cross-probe predictive audit `PPD`
- Leave-one-probe-out (`plan/04` §4.4; `idea.md` §6 E4): fit each model to **BAO(+CMB) only**,
  posterior-predict the **held-out SN** `μ(z)`; and fit to **SN only**, predict held-out BAO.
- Score `PPD_{p→q}` (whitened distance to held-out data). The genuine-`Ξ` test: does `M₂` lower
  held-out `PPD` versus `M₀`/`M₁`, or only in-sample `χ²`? (Anti-fudge, `plan/04` §1.3 pt 3.)

### Step 6 — F4 status assignment + AOR ledger
- Compute `Comp(a)` (shape flat?), image membership `a ∈ R(𝒢)` (does a single FLRW reproduce both?),
  and fiber cardinality `|R⁻¹(a)|` (is the FLRW completion unique?), and assign **exactly one** of the
  four F4 statuses (§4). Emit the AOR status for the residual (§7).

### Step 7 — Coherence handoff
- Export the fitted `Ξ_cosmo` (specifically the term-0 `a₀` and term-2 `a₂` amplitudes) and the
  implied `K_L`/`K_M` amplitudes to the **coherence ledger** so E1/E5/E4 can check the make-or-break
  cross-amplitude constraint (`plan/04` §9.4; `plan/00-overview` §6.4): the E2 `Ξ` must be within
  **10×** and consistent sign with the E1 geometry `Ξ` and the E5 growth `Ξ`.

### Software (from `GROUNDING_BRIEF` §II)
`cobaya ≥3.4` (MCMC/nested), `CLASS ≥3.2` or `CAMB ≥1.5.7` (FLRW distances; pick one, do not mix),
`getdist ≥1.5` + `arviz ≥0.15` (R̂/ESS/posteriors), `numpy/scipy` (GP reconstruction, SVD/Schur for
`LG`), `matplotlib ≥3.5`. Optional Lean 4 (≥v4.28.0) only for the P3 scaffold (§7).

---

## 6. Engaging Afroz–Mukherjee vs Crossing-Statistics explicitly (LOCKED)

This section is a mandatory deliverable, not optional discussion. The experiment must produce a
**side-by-side adjudication**:

1. **Replicate Afroz–Mukherjee (2504.16868).** Run `M_AM` (`w₀wₐ` + parametric `η(z)=1+ε₀z` or
   `(1+z)^ε`) on Pantheon+ + DESI DR2 BAO. Check whether `ε₀` is detected at >2σ and whether the
   DESI `w_a` migrates toward their reported `w₀≈−0.92, wₐ≈−0.49`. **Report the recovered `(w₀,wₐ,ε₀)`
   with credible intervals.** If reproduced, that is direct evidence for the `OverlapInconsistent`
   status / gluing-residual verdict.
2. **Replicate the Crossing-Statistics consistency test (2604.19393).** Run the model-independent
   section reconstruction (Step 1) and the deformation-freedom consistency check on DESI DR2 BAO +
   Pantheon+/Union3. Check whether `η(z)` shape is consistent with flat within the deformation
   family (i.e. `Comp(a)` holds). If consistent, that is evidence for `CompatibleNonGlobal` /
   `GloballyExact` and a *surviving* rewrite residual.
3. **Adjudicate via the SBT carrier.** The two literature results disagree *because they make
   different completion/calibration assumptions*. SBT's contribution is to show this is a
   `(M_B, r_d)`-calibration + reconstruction-method dependence (a packaging signal), and to
   **type the disagreement** with the F4 status + the `F_collapse` number — *without* declaring one
   paper right a priori. The honest output is: "under regime/SN-compilation/reconstruction choice
   X, the family is status S with collapse fraction F." The spread across choices *is* the result
   (P4 staging fingerprint; `idea.md` §10 standard 4).

---

## 7. Outputs and AOR statusing

### 7.1 Artifacts (committed)

| Artifact | Path (suggested) | Contents |
|---|---|---|
| Run manifests | `results/E2/manifests/*.json` | per-run seeds, datasets+versions, software, params, audit_status (`GROUNDING_BRIEF` §III.B) |
| `η(z)` audit ledger | `results/E2/eta_audit.hdf5` | `η(z)`, `η(z)/η₀`, full cov, both calibration regimes, per SN compilation |
| `LG_{SN,BAO}` ledger | `results/E2/lg_gluing.npy` + json | the gluing-defect value, whitened, with the F4 status |
| Model-comparison table | `results/E2/model_comparison.csv` | rows `{M₀,M₁,M₂,M₁₊₂,M_AM}` × cols `{χ², χ²/dof, k, BIC, AIC, ΔBIC vs M₁, w₀, wₐ, ε₀, a₂, OOS PPD}` |
| Collapse-fraction record | `results/E2/w_a_collapse.json` | `F_collapse` (E2.2) with credible interval, per SN compilation/regime |
| F4 status verdict | `results/E2/f4_status.json` | the four-status assignment + the `(Comp, image, fiber)` evidence + the decision verdict |
| Posterior triangles | `results/E2/triangle_*.png` | per model (`getdist`) |
| AOR status entry | appended to `results/aor_status_table.csv` | the typed residual (§7.2) |
| Coherence handoff | `results/coherence_ledger/E2.json` | `a₀, a₂`, implied `K_L/K_M` amplitudes + sign, for §9.4 cross-check |

### 7.2 AOR statusing of the E2 residual (`plan/04` §8; `idea.md` §6 Exp2)

The leftover after E2 must carry **exactly one** AOR base status (F9 No Unstatused Residual). The
status is determined by the F4 verdict (§4):

| F4 verdict | AOR status | Residual type (`plan/04` §8.2) | Payload `π` |
|---|---|---|---|
| `OverlapInconsistent` (gluing wins) | `bridged` | `D_local`, `D_global` | the `Ξ` gluing chart `a₂` that repairs CDDR + the explicit `η(z)` deviation |
| `CompatibleNonGlobal` (mixture) | `bridged` | `D_global` | the `Ξ` repair of the no-global-FLRW residual |
| `GloballyExact` (rewrite survives) | `zero` (gluing) + `bridged` (`w_a` rewrite) | `D_descent` | gluing residual = 0; `w_a` is a genuine `M₁` rewrite |
| `GloballyAmbiguous` | `moduli` | `D_global` | the flat-direction pin (data cannot fix the completion) |

Plus standing statuses always recorded:
- `η₀` amplitude → `selected`/`moduli` (calibration, never a CDDR violation; §3.4).
- Out-of-overlap extrapolation → `D_horizon` (sampling cutoff), `budgeted`.
- "A fundamental Λ is not ruled out" → `nonclaim` (`Dark Energy` precursor; `plan/04` §1.2(2)).
- Any compressed-likelihood fallback (DESI BAO-only, Union3 5-bin) → `budgeted`.

This run advances the carrier toward **RefStableAOR** (E1–E3 leg, `plan/00-overview` §7).

### 7.3 Lean anchor (optional this experiment, target for P3 closure)

`SBTCosmo.LocalGlobal` (`plan/04` §6.3, §10 Lean map): a scaffold importing
`Transport.LocalGlobalObstruction.local_global_obstruction_normal_form` instantiated with
`(𝒢, 𝓕, Comp, R)` of §4, plus a **numerical witness** that the fitted `η(z)`/distance data carries
exactly one of the four statuses. Normal form is `[T]` (reused directly); the data status is
`[C]/[E]`. The numerical witness should compile/verify under `lean --check` for the final P3 claim
(`plan/00-overview` §8 item 5: P3 = scaffold + verified-computation witness).

---

## 8. Pass / fail gates (quantitative, pre-registered)

> **Pre-registration discipline (`plan/00-overview` §6, `plan/04` §9).** These thresholds are fixed
> **before** seeing results and may not be relaxed afterward; any relaxation is a logged statused
> deviation (`budgeted`). Units are χ²/dof, ΔBIC, whitened distances, and credible-interval bounds.

### 8.1 Reproduction gate (must pass first — else cannot proceed)

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E2-REPRO` | `M₀`/`M₁` joint fit recovers published DESI DR2 `w₀wₐ` contour (`w₀>−1, wₐ<0`) and the 2.8–4.2σ DE-preference band; `χ²_SN` and `χ²_BAO` within **5%** of published; `R̂<1.01`, ESS>400 | `idea.md` §10.1; `plan/03` G-DATA-3 |

### 8.2 Data / metric gates

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E2-COV` | Pantheon+ `C_μμ` and DESI BAO cov PD, condition number `<10⁸`, all entries finite (else `Σ^†` on legal quotient) | `plan/04` §4.0; `GROUNDING_BRIEF` §VI |
| `G-E2-RECON` | section reconstruction (Step 1) reproduces each probe's own distances within its 1σ on the native grid before mapping to the shared grid | §3.2 |
| `G-E2-CALIB` | the headline CDDR test is on `η(z)` **shape** with `(M_B, r_d)` marginalized; `η₀` amplitude reported separately as `selected`/`moduli`, never counted as violation | §1.4, §3.4 |

### 8.3 The four-status / decision gates (the heart of E2)

These operationalize the F4 status (§4) and the three-verdict decision (`idea.md` §6 Exp2). The
**`η(z)` shape test** (`ε₀` slope of `η=η₀(1+ε₀ g(z))`) drives `Comp(a)`:

| F4 status assigned iff | Quantitative condition |
|---|---|
| **`OverlapInconsistent`** | `ε₀ ≠ 0` at **> 2σ** (CDDR-shape violation detected), robust across `g(z)∈{z, ln(1+z)}` |
| **`Comp(a)` holds** (`η` flat) | `\|ε₀\|/σ(ε₀) < 2` for both `g(z)` forms |
| within `Comp(a)`: **`GloballyExact`** | a single FLRW (`M₀` or `M₁`) reproduces both sections with joint `χ²/dof ≤ 1.05` **and** the FLRW completion is unique (no degenerate-`χ²` plateau, i.e. `|R⁻¹|=1`) |
| within `Comp(a)`: **`CompatibleNonGlobal`** | no single FLRW gives joint `χ²/dof ≤ 1.05` (`a ∉ R(𝒢)`) despite flat `η` |
| within `Comp(a)`: **`GloballyAmbiguous`** | multiple FLRW completions give `Δχ² < 1` over a continuous direction (`|R⁻¹|>1`) |

> The status assignment must be **exclusive** (F4 exclusive-or). Report the `(Comp, image-membership,
> fiber)` evidence triple. *Exactly one* status; an ambiguous assignment is itself a defect requiring
> a logged `moduli`/`D_global` statusing.

### 8.4 The decision (three admissible verdicts — no answer forced in advance)

| Verdict | Condition (LOCKED) | Maps to |
|---|---|---|
| **Gluing residual** (Afroz–Mukherjee direction) | `F_collapse > 0.5` (eq. E2.2: gluing chart absorbs **>50%** of `M₁`'s `w_a`) **and** F4 = `OverlapInconsistent` (or `CompatibleNonGlobal`) | `idea.md` §6 Exp2 "gluing residual"; `plan/00-overview` §6.3 E2 pass |
| **Rewrite residual** (Crossing-Statistics direction) | `F_collapse < 0.2` (gluing chart absorbs **<20%**, per REGISTRY §11.9) **and** F4 = `GloballyExact`/`CompatibleNonGlobal`; `M₁`'s `w_a` survives the gluing chart | `idea.md` §6 Exp2 "genuine rewrite residual"; `plan/00-overview` §6.3 E2 fail-leg-for-gluing-but-not-for-program |
| **Mixture** | `0.2 ≤ F_collapse ≤ 0.5` (per REGISTRY §11.9), or `M₁₊₂` beats both `M₁` and `M₂` by `ΔBIC > 5`, indicating both a rewrite and a gluing residual are needed | `idea.md` §6 Exp2 "or a mixture" |

> **Both extremes are scientifically valid E2 outcomes.** The experiment is **not** designed to make
> the gluing verdict win. A clean `Rewrite residual` verdict (Crossing-Statistics direction) is a
> legitimate, publishable E2 result that *strengthens* the program by showing SBT does not force the
> CDDR explanation (`idea.md` §6 Exp2: "the paper becomes stronger if it does not force one answer").

### 8.5 SBT-claim gates (the `M₂`/`Ξ` value test)

| Gate | PASS | FAIL |
|---|---|---|
| `G-E2-OOS` (out-of-sample, `plan/04` §4.4) | `M₂` (or `M₁₊₂`) lowers held-out `PPD_{BAO→SN}` and/or `PPD_{SN→BAO}` by **> 3%** vs ΛCDM, and beats every alternative beyond the combined uncertainty band (a `≤`-best / within-3% margin is a floor/tie, not a pass) | `M₂` improves only in-sample `χ²`, not held-out `PPD` (= fudge) |
| `G-E2-BIC` (model competition, `plan/00-overview` §6.3 E2) | the winning gluing/mixture model has **OOS ΔBIC > 5** vs `{M₀, M₁}` *when the gluing verdict holds* | `M₂`/`M₁₊₂` never beats `M₁` by ΔBIC, in any regime/SN compilation |
| `G-E2-SHAPE` (correlation, `plan/00-overview` §6.3 E2 failure) | the fitted `η(z)` shape is **correlated** with the SN–BAO joint residual (the gluing defect *explains* the residual; Spearman p<0.05) | `η`-shape is **uncorrelated** with the residuals (p>0.05): the CDDR term is not actually doing the explaining → reject the gluing reading |
| `G-E2-RANK` (anti-fudge, `plan/04` §9.2) | `M₂` uses `≤ 3` extra params, shapes probe-shared, no per-probe free `Ξ_p` | rank ceiling exceeded without logged justification |
| `G-E2-COHERE` (coherence handoff, `plan/04` §9.4 / `plan/00-overview` §6.4) | E2's term-2 `a₂` (and `K_L/K_M` amplitudes) within **10×** and consistent sign with the E1 geometry `Ξ` | E2 `Ξ` amplitude differs from E1 by `>10×` or sign disagrees → **program-phase coherence failure** |

### 8.6 Pre-registered failure modes (honored and reported with numbers; `plan/00-overview` §6.3 E2, §6.2 std 5)

E2 (as a gluing claim) **fails** if any of:
1. `M₂` never beats `M₁` by ΔBIC in any regime/SN compilation (`G-E2-BIC` fail), **and**
2. the gluing chart explains `< 20%` of the apparent `w_a` (`F_collapse < 0.2`, per REGISTRY §11.9), **and**
3. the `η(z)` shape is uncorrelated with the SN–BAO residuals (`G-E2-SHAPE` fail, p>0.05).

> **Crucial distinction.** Failure of the *gluing* reading is **not** failure of the *program*: it
> instead delivers the `Rewrite residual` verdict (§8.4), which is a valid E2 outcome. The program
> fails at E2 only if (a) `G-E2-REPRO` fails (cannot even reproduce DESI), (b) `G-E2-COHERE` fails
> (E2 `Ξ` is mutually inconsistent with E1 — the make-or-break coherence gate), or (c) `G-E2-RANK`
> is violated (the CDDR term is a per-probe fudge, not a shared low-rank chart).

---

## 9. Dependencies, blocking, and links

- **Blocked by:** `plan/03` data acquisition (Pantheon+ §4, Union3, DES-SN5YR, DESI DR2 BAO §2,
  Planck compressed prior); `plan/02` environment (cobaya/CLASS/CAMB/getdist/arviz stack);
  `plan/04` §1–§9 (carrier, residuals, ansatz, kernels `K_L/K_M`, P3↔F4, metric `d`, AOR statuses);
  **E1** (DESI DR2 reproduction + the fitted geometry `Ξ`, needed for the `G-E2-COHERE` cross-check
  and to define the `M₁` `w_a` baseline that E2 tries to collapse).
- **Blocks / unblocks:** **E3** (phantom-crossing — uses whether the `w(z)`/`Ξ` survives the gluing
  collapse); **E8** (model-competition synthesis — the `{M₀,M₁,M₂,M₁₊₂}` row + the F4 verdict feed
  the final matrix); **the P3 Lean closure** (`SBTCosmo.LocalGlobal`); the **coherence ledger**
  consumed by E4/E5.
- **`idea.md` citations:** §3 (shadow map row 4), §6 Experiment 2 (the `M₀/M₁/M₂` triad, the
  "rewrite vs gluing vs mixture, don't force one answer" criterion), §7 ("Dataset inconsistency and
  distance duality" — the Afroz–Mukherjee/Crossing-Statistics tension), §10 (standards 1, 3, 4, 5).
- **Corpus citations:** `Foundations_IV` `thm:F4` (Local–Global Obstruction Normal Form, four
  statuses) + `thm:F2` (Descent–Repair) + `thm:F9` (No Unstatused Residual); `Adequacy_Residuals`
  (`Ξ_C(D∣L)` Schur complement = the SN+BAO content one FLRW cannot explain);
  `A_Six_Birds_Eye_View_of_Dark_Energy` (route mismatch, "Λ not ruled out" nonclaim, SN/BAO
  packaging on DES); `Audited_Operational_Realisability` (the status catalogue and carrier
  hierarchy); `Six_Birds_for_Neutrino_Mass` (the cross-lens audit template this experiment mirrors
  for SN-compilation swapping as a packaging signal).
- **arXiv anchors:** DESI DR2 BAO 2503.14738; Pantheon+ 2202.04077; Union3 2401.06956; DES-SN5YR
  Zenodo:13827844 / 2401.02929; Planck 2018 1807.06209; **Afroz–Mukherjee 2504.16868**;
  **Crossing-Statistics consistency 2604.19393**; PAge+GP CDDR 2603.27616; DESI–DES SN crosscheck
  2510.04179.
