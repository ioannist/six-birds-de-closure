# E7 — Modified Gravity as Another Descent-Repair Chart (the "the anomaly is not in local gravity" experiment)

> **One-line charter.** Use the **DESI full-shape modified-gravity results** (DESI 2024 VII /
> DESI MG paper, arXiv:2411.12022 / **2411.12026**: phenomenological `(μ₀, Σ₀)` and Hu–Sawicki
> `f(R)` constraints all **consistent with GR** while the *background* `w₀w_a` preference persists)
> to demonstrate the central E7 thesis: **the DESI dynamical-dark-energy anomaly lives in the
> closure / completion layer, not in local gravitational law.** SBT explains the `w(z)`-like signal
> as the operator-rewrite chart `R[Ξ_cosmo]` (P1/F2) **without requiring nonlocal modified gravity**,
> while still admitting modified gravity (`(μ,Σ)`, `f(R)`, scalar-tensor) as a **legitimate
> alternative repair chart** of the *same* failed FLRW descent — accepted only when *its own* audits
> (growth out-of-sample, no instability, coherence with the same `Ξ`) pass. The make-or-break logic:
> SBT does **not** need to defeat MG; it must show MG and `Ξ` are **alternative repairs of one
> obstruction** (Descent-Repair Normal Form, F2), and that the data's GR-consistency of `(μ₀,Σ₀)`
> *supports* the SBT reading that the residual is a completion-layer rewrite, not a local-gravity
> modification.

> **Read-order / consistency.** This file implements *one* experiment of the program defined in
> `plan/00-overview.md` (§3 shadow map **row 9** — the MG / descent-repair-choice chart; §4 E7 row;
> §6.3 E7 headline gate; §6.4 coherence gate; §7 AOR) and `../GROUNDING_BRIEF.md` (datasets §I.D/§I.E
> — DESI DR2 full-shape RSD/MG; growth stack §II.A — CCL/`pyccl`; determinism §III; AOR §VI). Every
> formal object used here is *locked* in `plan/04-formal-foundations.md`: the carrier and four residuals
> (§4), **P1 ↔ F2 Descent-Repair Normal Form** — F2's **two** canonical repairs (source refinement,
> minimal target coarsening) **plus** the cosmology-specific **operator-rewrite** chart that is P1's
> extension of F2 — and the explicit statement that "DESI's `w₀w_a`, IDE `Q`, and `(μ,Σ)` are
> *alternative* repair charts of the same nonempty obstruction" (§6.1, eq. F2 instantiation), the
> low-rank ansatz and the kernels `K_M`/`K_G`/`K_S`
> (§3.1, §3.3 eqs. 6–9), the **stable-readout / spectral-stability certificate** (§7, reused from E3 for the
> MG-instability audit), the AOR statuses incl. `approved_other` / `blocked` (§8.3), and the metric `d`
> (§4.0). Data products / loaders / fallbacks for `DESI_RSD_FS` are locked in `plan/03-data-acquisition.md`
> §2 (`load_desi_rsd_fs`, compressed `(fσ₈, D_M/r_d, D_H/r_d)` + `(μ₀,Σ₀)` MG inputs). The CCL/`pyccl`
> `(μ,Σ)`-growth backend and the **G-ENV-4 pyccl↔CLASS agreement gate** are locked in `plan/02-environment-and-deps.md`
> §1.4 / §6.G-ENV-4 (E7 is **blocked** if G-ENV-4 fails, exactly as E5). **Science source of truth:** `idea.md`
> §8 ("modified gravity vs dark energy"), §6 **Experiment 7** (verbatim pass criterion: *"show that
> Six Birds explains the DESI `w(z)`-like signal without requiring nonlocal modified gravity, while
> still allowing MG as an alternative repair when its audits pass"*), §7 (the **Modified gravity**
> resolution: *"Modified gravity, evolving `w`, IDE, and backreaction are all repair options under
> Descent–Repair Normal Form; Six Birds gives the unifying classification"*), §3 shadow map **row 9**
> (MG = the **operator-rewrite chart**), §9 (MG is the "operator-rewrite chart" of the residual), §10
> (five hard standards). **Precursor grounding:** `A_Six_Birds_Eye_View_of_Dark_Energy` §framework
> (route mismatch forces an operator rewrite; ΛCDM is *one* successful rewrite family; the explicit
> three-way repair choice "refine the completion / change the lens / rewrite the macro operator").
>
> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean / finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a gate
> in §7 below).

---

## 1. Scientific framing and grounding

### 1.1 What this experiment is about

`idea.md` §3 (shadow map, **row 9**) and §6 **Experiment 7** state the thesis precisely:

> *"DESI full-shape modified-gravity analyses find `(μ, Σ)` parameters consistent with GR while still
> allowing a preference for dynamical dark energy in `w₀w_a` backgrounds. That is very favorable to Six
> Birds: it supports the claim that the anomaly may live in the **closure/completion layer**, not in
> local gravitational law.*
> *Pass criterion: show that Six Birds explains the DESI `w(z)`-like signal without requiring nonlocal
> modified gravity, while still allowing MG as an alternative repair when its audits pass."* —
> `idea.md` §6 Exp7.

And the **unifying classification** (`idea.md` §7 "Modified gravity", §9):

> *"Modified gravity, evolving `w`, IDE, and backreaction are all repair options under Descent–Repair
> Normal Form. Six Birds gives the unifying classification."* — `idea.md` §7.
> *"modified gravity is the operator-rewrite chart"* of the residual. — `idea.md` §9.

The **headline of the program** (`idea.md` §3; `plan/00-overview` §3 row 9): `Λ`, `w_a`, `Q_IDE`,
`η_CDDR`, **`μ/Σ`**, and `S₈` shifts are *coordinate charts on the same closure defect* `Ξ_cosmo(z,ℓ,p)`.
E7 isolates the **modified-gravity chart** (`μ₀, Σ₀`, `f_R0`, scalar-tensor) and answers three questions:

1. **Does the data put the anomaly in the completion layer, not local gravity?** Reproduce the DESI
   result that the *growth-sector* MG parameters `(μ₀, Σ₀)` are **GR-consistent** *while* the
   *background* `w₀w_a` preference persists. If the modification needed to fit DESI lives in the
   *background expansion* (a completion/operator rewrite) and **not** in the linear growth/lensing
   gravity functions `(μ,Σ)`, that is direct empirical support for the SBT reading: the residual is a
   completion-layer rewrite `R[Ξ]`, not a change to local gravitational law.
2. **Does SBT explain the `w(z)`-like signal *without* requiring nonlocal MG?** Show that the same
   low-rank `R[Ξ_cosmo]` rewrite (E1's operator-rewrite chart, `K_M`) reproduces the DESI background
   `w(z)`-like signal **with `(μ,Σ)` held at GR** — i.e. SBT needs *no* modification of the growth
   gravity functions to match the geometry the MG analysis attributes (in the background) to dynamical
   dark energy.
3. **Is MG a *legitimate alternative repair* of the same obstruction (F2)?** Demonstrate, via the
   Descent-Repair Normal Form (P1/F2, `plan/04` §6.1), that an explicit MG model (`(μ₀,Σ₀)`-EFT;
   Hu–Sawicki `f(R)`; reconstructed scalar-tensor) and the SBT `Ξ`-rewrite are **two charts of the
   *same* nonempty descent obstruction** `RM_p > 0`. MG is *accepted as an alternative repair* iff its
   own audits pass: GR-consistency / data preference, **no instability** (the stable-readout / spectral-
   stability certificate of `plan/04` §7), growth out-of-sample within budget, and **coherence** with
   the same `Ξ` amplitude (the make-or-break §6.4 gate). MG simply being *not preferred* is **not** a
   failure — it is a *logged alternative repair* (`plan/00-overview` §6.3 E7 note).

### 1.2 The decisive conceptual move (LOCKED): MG and `Ξ` are two repair charts of one obstruction

The formal spine is **P1 ↔ F2, Descent-Repair Normal Form** (`plan/04` §6.1; `Foundations_IV`
`thm:F2`). The instantiation (`plan/04` §6.1):

```
q := U_θ        (the FLRW completion as the quotient map onto homogeneous descriptors)
F := f_p ∘ T    (lensed evolution)
r := observable readout (distances, fσ₈, C_ℓ)
```

Then `splitObs(q, F, r) ≠ ∅ ⇔ RM_p > 0` (the route-mismatch positivity that E0/E1 establish). **F2's
normal form names exactly two canonical repairs**: (i) **source refinement** and (ii) the **minimal
target coarsening** `c_F: R → R_F`. The **operator rewrite** `R[Ξ_cosmo]` is **not** part of F2's
statement — it is the **cosmology-specific extension of F2** that P1 adds (the "operator-rewrite repair
chart"), so P1 = F2's two repairs **plus** the operator-rewrite chart (`plan/04` §6.1). The cosmology
mapping of the repair branches — F2's two plus P1's operator-rewrite extension (`plan/04` §6.1;
`idea.md` §7 §9; `Dark Energy` precursor §framework):

| Repair branch | Origin | Cosmology chart | Where the modification lives | This program's experiment |
|---|---|---|---|---|
| **operator rewrite** | P1 cosmology extension of F2 | the SBT `Ξ`-rewrite `R[Ξ_cosmo]`; ΛCDM/`w₀w_a` as a successful rewrite *family* | the **background completion / macro operator** | E1 (geometry), E3 (phantom), **this is the SBT default** |
| **operator rewrite (alt)** | P1 cosmology extension of F2 | **modified gravity** `(μ,Σ)`, `f(R)`, scalar-tensor | the **growth/lensing gravity functions** *and/or* the background | **E7 (this file)** |
| accounting chart | P1 cosmology extension (P6 ledger) | IDE `Q(z)` continuity-equation transfer | the dark-sector energy ledger (P6) | E6 (IDE) |
| target coarsening | **F2 canonical repair** | dropping/binning a probe so the obstruction descends | the lens/observable resolution | E2/E5 staging |
| source refinement | **F2 canonical repair** | adding a heterogeneity proxy / hidden variable | the micro source description | E0/E1 LP5 |

> **The unifying claim E7 makes (LOCKED).** MG, evolving `w`, IDE, and backreaction are **not rival
> ontologies**; they are **alternative charts on the same `Ξ_cosmo` repair** of the *same nonempty*
> F2 obstruction. E7's job is to *prove the classification empirically*: (a) the obstruction is the
> same one (the MG fit and the `Ξ` fit are explaining the *same* DESI residual, verified by a shared
> `RM_p` / shared geometry), (b) the data's **GR-consistency of `(μ,Σ)`** localizes the modification to
> the *background completion* (favoring the operator-rewrite-on-the-completion reading over a local-
> gravity reading), and (c) when MG's own audits pass, MG is a *legitimate* alternative repair — logged,
> not refuted. This is `idea.md` §9's "modified gravity is the operator-rewrite chart" made operational.

> **What E7 explicitly does NOT claim (nonclaim register, F9 `nonclaim`).** E7 does **not** claim GR is
> wrong, does **not** claim MG is ruled out, and does **not** claim SBT is "better than" MG. It claims
> the weaker, defensible thing (`idea.md` §7 rhetorical discipline): the DESI anomaly is *equally well*
> read as a completion-layer operator rewrite that needs **no** modification of local gravity, and the
> data's GR-consistency of `(μ,Σ)` is *consistent with and favorable to* that reading. "A fundamental
> modification of gravity is not ruled out here" is a standing `nonclaim` (mirroring the precursor's
> "a cosmological constant is not ruled out").

### 1.3 Foundations grounding (the operator-rewrite chart and the repair classification)

- **F2 / P1 Descent-Repair Normal Form (`plan/04` §6.1; `Foundations_IV` `thm:F2`,
  `Transport.DescentRepair.descent_repair_normal_form`).** F2 itself names exactly **two** canonical
  repairs (source refinement, minimal target coarsening); the **operator-rewrite** chart is the
  **cosmology-specific extension of F2** that P1 adds (`plan/04` §6.1). Both the `Ξ`-rewrite and MG sit
  in that P1 operator-rewrite extension (one on the background completion, one on the growth gravity
  functions) — they are not F2's own two repairs. The *gauge-invariant-observables* layer instantiation
  of F2 (`Foundations_IV`
  layer-inst:F2, "physics; source refinement") is the closest analogue: a candidate observable descends
  through the orbit quotient iff it is gauge-invariant — here, a candidate macro law descends through
  the FLRW completion iff `RM_p = 0`; when it does not, MG and `Ξ` are two ways to repair descent. E7's
  Lean target reuses `SBTCosmo.DescentRepair` (`plan/04` §6.1) and adds an **MG-as-repair witness**:
  the MG model and the `Ξ`-model both make `r∘F` descend through `q`, i.e. both lie in the admissible-
  repair set of the *same* `splitObs ≠ ∅`.
- **The stable-readout / spectral-stability certificate (`plan/04` §7, reused from E3).** MG models can carry
  instabilities (ghosts, gradient/tachyonic instabilities). The **same** certificate used for the SBT
  rewrite in E3 is applied to the MG repair: all eigenvalues of the linearized macro Jacobian satisfy
  `Re λ ≤ 0` (no growing mode) and the rewrite is positive on the audit-energy inner product. A MG model
  that *fails* this certificate is an **inadmissible repair** → AOR `blocked` (the rewrite is provably
  inadmissible, `plan/04` §8.3 `blocked`). This is the precise operationalization of "MG as an
  alternative repair *when its audits pass*."
- **The four residuals (`plan/04` §4).** `RM_p` (the shared obstruction MG and `Ξ` both repair),
  `PPD_{p→q}` (the growth out-of-sample test that decides whether MG is *needed* beyond `Ξ`), and the
  metric `d` (Mahalanobis whitened, eq. 10).
- **Kernels `K_M`, `K_G`, `K_S` (`plan/04` §3.3 eqs. 7–9).** `K_M` maps `Ξ` to the BAO/background
  geometry (the `w(z)`-like signal SBT must reproduce *with* `(μ,Σ)=`GR); `K_G`/`K_S` map `Ξ` to growth
  `fσ₈` / `S₈` (the growth sector the MG `(μ,Σ)` modification touches). The coherence test asks whether
  the *same* `Ξ` amplitude that reproduces the background also leaves growth GR-consistent — i.e.
  whether SBT predicts `(μ,Σ)≈`GR, which is exactly what DESI measures.
- **Coherence gate (`plan/04` §9.4 / §3.3; `plan/00-overview` §6.4).** The MG repair's effective `Ξ`
  amplitude (read through `K_M`/`K_G`) must lie within **10×** and consistent sign of E1's geometry-`Ξ`
  amplitude — i.e. MG and `Ξ` must be the *same* low-rank residual, not unrelated fudges. This is the
  make-or-break "one residual, many charts" constraint applied to the MG chart.
- **F9 No Unstatused Residual / AOR (`plan/04` §8).** Every surviving MG tension (residual growth
  offset, an instability, a flat `f_R0` direction, MG-vs-`Ξ` preference) carries **exactly one** AOR
  base status; the MG model itself, when run as a comparator owned by E7 but informing E5/E8, is logged
  `approved_other` where another experiment hosts it.

### 1.4 The live MG picture this experiment must engage (mandatory, adversarial)

`idea.md` §8 frames the current MG-vs-DE situation. E7 must engage **all** of it — the GR-consistency
that favors SBT *and* the scalar-tensor reconstructions that keep MG alive:

| Result | Release | What it found | What it implies for E7 |
|---|---|---|---|
| **DESI 2024 VII full-shape** | arXiv:2411.12022 | full-shape clustering tests deviations from GR via growth | the growth-sector MG test; `(μ₀,Σ₀)` inputs |
| **DESI MG (full-shape)** | arXiv:**2411.12026** | DESI DR1 FS + BAO + CMB + DESY3 gives **`μ₀ = 0.04 ± 0.22`, `Σ₀ = 0.044 ± 0.047`** — **GR-consistent** — *while still recovering a preference for dynamical DE in `w₀w_a` backgrounds* | **the central E7 datum**: growth gravity ≈ GR *but* background `w(z)` evolves → the anomaly is in the **completion/background**, not local growth gravity (the SBT reading) |
| **Scale-dependent MG, DESI DR1** | arXiv:2604.26915 | no evidence for deviations from GR; constrains Hu–Sawicki `f(R)` to **`log₁₀\|f_R0\| < −4.59`** (95%), fifth-force range `< 17.8 Mpc` | the `f(R)` leg: a tight upper bound on a *specific* MG model → MG repair, if invoked, is strongly constrained; SBT needs no fifth force |
| **Reconstructed scalar-tensor** | arXiv:2511.04610 | scalar-tensor reconstructions allow *effective phantom crossing* and can raise `H₀`; one DESI DR2 + Pantheon+ + CMB + RSD fit gives **`H₀ = 70.6 ± 1.7`** | the "MG is alive" leg: a *viable* alternative repair that touches the Hubble (E4) and phantom (E3) charts — E7 must admit it as a legitimate alternative repair when its audits pass |

> **The packaging reading (`idea.md` §8, §9).** The data's **GR-consistency of `(μ₀,Σ₀)`** is not a
> nuisance; it is the *positive signal* for SBT. If the DESI anomaly required a *local-gravity*
> modification, `(μ₀,Σ₀)` would deviate from `(0,0)`. They do not (within `~0.2 / 0.05`). Yet the
> *background* `w₀w_a` preference persists. SBT's reading: the modification needed to fit DESI lives in
> the **background completion** (an operator rewrite `R[Ξ]`), and SBT *predicts* `(μ,Σ)≈`GR because its
> rewrite acts on the completion, not on the linear growth gravity functions. E7 turns this into a
> falsifiable prediction (§4.2, gate `G-E7-MUSIGMA`): **the SBT `Ξ` that reproduces the DESI background
> `w(z)` must leave `(μ₀,Σ₀)` GR-consistent.** If fitting the DESI background with `Ξ` *forced* a
> non-GR `(μ,Σ)`, the SBT reading would fail.

---

## 2. The models (LOCKED)

E7 fits a model ladder to the **same** DESI full-shape (geometry + growth) data with a physical CCL
forward model, sharing background + growth parameters with E1's verified geometry fit and E5's verified
growth baseline:

| Model | Background | Growth gravity | Closure / MG term | Extra free params beyond ΛCDM | Reads as | F-law |
|---|---|---|---|---|---|---|
| **`M₀`** (null) | ΛCDM (`w=−1`) | GR (`μ=Σ=1`) | none | 0 | a fundamental Λ + GR | baseline |
| **`M_w`** (DESI background) | `w₀w_a` (CPL) | GR (`μ=Σ=1`) | none | `+2` (`w₀,w_a`) | the DESI dynamical-DE background preference, GR growth | the signal to be explained |
| **`M_Ξ`** (SBT operator-rewrite chart) | ΛCDM + `R[Ξ]` (background rewrite via `K_M`) | GR (`μ=Σ=1`), growth via `K_G`/`K_S` from the **same** `Ξ` | term-0/term-2 `Ξ` from E1 (**`a₀` pinned**, `a₂` allowed) | `+1…2` (inherited `a₀`; `a₂`) | SBT: anomaly is a completion rewrite; growth stays GR | operator rewrite (P1/F2) |
| **`M_μΣ`** (MG repair, EFT) | ΛCDM (or `w₀w_a`) | `(μ₀,Σ₀)` phenomenological MG (CCL `μΣ` parameterization) | none (MG *is* the repair) | `+2` (`μ₀,Σ₀`) [+2 if `w₀w_a` background] | the MG operator-rewrite-on-growth chart | operator rewrite (alt; P1 ext. of F2) |
| **`M_fR`** (MG repair, `f(R)`) | ΛCDM | Hu–Sawicki `f(R)` scale-dependent `(μ(k,z),Σ(k,z))` | the `f_R0` rewrite | `+1` (`log₁₀\|f_R0\|`) | a specific MG model; strongly bounded by DESI | operator rewrite (alt; P1 ext. of F2) |
| **`M_ST`** (MG repair, scalar-tensor) | reconstructed `w_eff(z)` | reconstructed `(μ,Σ)(z)` | scalar-tensor reconstruction | `+k` (reconstruction basis) | the "MG is alive" comparator (raises `H₀`, allows phantom crossing) | operator rewrite (alt; P1 ext. of F2) |

> **`M_Ξ` construction detail (LOCKED — the SBT default).** `M_Ξ` does **not** modify the growth
> gravity functions: it keeps `(μ,Σ) = (1,1)` (GR) and repairs the descent by the **background**
> operator rewrite `R[Ξ_cosmo]` through `K_M` (and the induced growth/WL response `K_G`/`K_S` of the
> *same* `Ξ`). The background `Ξ` term-0 amplitude `a₀` is **pinned to E1's fitted value** (coherence
> ledger `results/xi_cosmo_coherence.csv`, `plan/04` §9.4); the calibration/gluing term `a₂` (the
> `c_p` chart, `plan/04` §3.1) may be fit. The induced observable shifts use the *same* probe-shared
> kernels:
> ```
> (D_M/r_d)^obs(z) = (D_M/r_d)^FLRW(z; θ) + K_M[Ξ](z)        (plan/04 eq. 7; background geometry)
> (fσ₈)^obs(z)     = (fσ₈)^GR(z; θ)       + K_G[Ξ](z)        (plan/04 eq. 8; RSD growth)
> S₈^obs           = S₈^GR(θ)             + K_S[Ξ]           (plan/04 eq. 9; WL amplitude)
> ```
> The SBT prediction E7 tests: this `M_Ξ` reproduces the DESI `M_w` background `w(z)`-like signal
> **while leaving the *inferred* `(μ₀,Σ₀)` GR-consistent** — i.e. SBT *predicts* the DESI MG result.
> There is **no** per-probe free `Ξ_p` and **no** free `(μ,Σ)` in `M_Ξ` (G-E7-RANK).

> **`M_μΣ` / `M_fR` / `M_ST` construction (LOCKED — the alternative-repair comparators).** These are
> the MG repair charts. Each is a genuine MG model fit (CCL `μΣ` / `f(R)` / reconstructed scalar-tensor),
> **not** the SBT rewrite. They are run to: (a) reproduce the DESI GR-consistency (`G-E7-REPRO`),
> (b) be classified as F2 alternative repairs of the *same* obstruction (§4.1), (c) pass or fail their
> **own** stability / OOS / coherence audits (§4.2–4.4), and (d) feed E8's model competition. Whether
> any of them is *preferred* over `M_Ξ` is decided by E8; here E7 only certifies they are *admissible*
> (or `blocked`) and *coherent* (or not) with the same `Ξ`.

---

## 3. Inputs

### 3.1 Datasets (versions, access, real-vs-fallback — from `GROUNDING_BRIEF` §I.D/§I.E, `plan/03` §2/§5)

| Probe | Dataset | Release | Vector | Physical CCL `(μ,Σ)`-growth backend? | Loader (`plan/03`) | Role | Fallback (statused) |
|---|---|---|---|---|---|---|---|
| **Full-shape RSD + MG (PRIME)** | **DESI DR2 full-shape** | arXiv:**2411.12026** (DR1 FS methodology) + DR2 FS tables | `fσ₈(z)` 6–8 bins z∈[0.1,1.5] + `(D_M/r_d, D_H/r_d)` per bin; mock cov; **published `(μ₀,Σ₀)` MG constraints** (`μ₀=0.04±0.22, Σ₀=0.044±0.047`) | **YES** — `desilike` full-shape + CCL `μΣ` forward model | `load_desi_rsd_fs(compressed=…)` | **the central E7 probe**: growth gravity `(μ,Σ)` *and* the background `w(z)` signal | compressed `(fσ₈, D_M/r_d, D_H/r_d)` Gaussian (loses full-shape `P(k)`) → **`budgeted`** |
| **BAO geometry (background)** | DESI DR2 BAO | arXiv:2503.14738 | `D_M/r_d`, `D_H/r_d` 7 tracer bins | YES (background; CCL/CLASS) | `load_desi_dr2_bao()` | the background `w(z)`-like signal `M_Ξ` must reproduce via `K_M` | compressed BAO-only Gaussian → `budgeted` |
| **CMB anchor** | Planck 2018 | arXiv:1807.06209 | TT/TE/EE + lensing native | YES (`clik`) | `load_planck_2018(...)` | the early-universe anchor; `(μ,Σ)` lensing-amplitude cross-check | compressed distance priors → `budgeted` |
| **WL/3×2pt (growth, from E5)** | DES Y6 (+ DESY3 in DESI MG combo) | arXiv:2601.14559 (DES Y3 2212.00091) | shear+clustering+GGL, n_z=4 | YES — CCL `(μ,Σ)` 3×2pt forward model | `load_des_y6(...)` (E5 loader) | the lensing leg `Σ₀` modifies; supplies `K_S` cross-check | Gaussian on published vector+cov → `budgeted`; DES Y3 → `approved_other` |
| **Scalar-tensor reconstruction inputs** | DESI DR2 + Pantheon+ + CMB + RSD | arXiv:2511.04610 (comparator config) | combined geometry+growth | YES (reconstruction over CCL) | reuse E1/E5 loaders | the `M_ST` "MG-alive" comparator (raises `H₀`, phantom crossing) → ties to E3/E4 | published reconstruction posterior → `approved_other` |

> **The real-vs-fallback decision (LOCKED, mirrors E5 §3.1).** Backend selection per leg follows strict
> precedence, recorded per-run in the manifest: **(T1)** official survey/`desilike` likelihood + CCL —
> headline physics; **(T2)** CCL physical `(μ,Σ)`-forward model + Gaussian likelihood on the published
> vector/cov with official cuts — acceptable headline (`budgeted` on the likelihood-approximation axis
> only); **(T3)** reduced-systematics CCL — cross-check; **(T4)** DES Y3 substituting for DES Y6 →
> `approved_other`; **(T5)** compressed `(μ₀,Σ₀)` published-contour reuse only (no forward model) →
> `out_of_scope` for the headline, `approved_other` for the GR-consistency reproduction. Decision rule
> per leg: *use the highest-precedence backend that builds and passes the pyccl↔CLASS agreement gate G-ENV-4*
> (`plan/02` §6.G-ENV-4: `P(k)` <1%, `σ8` <0.5%). The headline E7 result is computed only from T1/T2 legs.

### 3.2 Parameters and priors

| Parameter | Model(s) | Prior | Notes |
|---|---|---|---|
| `Ω_m, Ω_b, H₀, n_s, ln(10¹⁰A_s)` (→ `σ8`) | all | standard broad priors (match E1/E5) | background+primordial; shared with geometry+growth fits |
| `w₀, w_a` (CPL) | `M_w` (and `M_μΣ` w₀w_a variant) | `w₀∈U(−3,1)`, `w_a∈U(−3,2)` | the DESI background preference to be explained |
| `a₀` (Λ-chart) | `M_Ξ` | **fixed to E1's fitted value** (coherence ledger) | NOT re-fit (the coherence anchor) |
| `a₂` (gluing/calibration chart) | `M_Ξ` | `U`, `complexity`-penalized | the calibration/gluing amplitude (`c_p` chart, `plan/04` §3.1) |
| **`μ₀, Σ₀`** | `M_μΣ` (MG repair) | `U(−3,3)` each (DESI-style broad) | **the MG growth-gravity parameters**; the central reproduction target `(0.04±0.22, 0.044±0.047)` |
| **`log₁₀\|f_R0\|`** | `M_fR` (MG repair) | `U(−8,−2)` | Hu–Sawicki `f(R)`; reproduce the `< −4.59` (95%) bound |
| scalar-tensor reconstruction basis coeffs | `M_ST` (MG repair) | survey/comparator-default | the "MG-alive" comparator (arXiv:2511.04610-class) |
| galaxy bias `b_i`, RSD nuisances, IA `A_IA`, baryon feedback, photo-z `Δz_i`, shear cal `m_i` | all growth legs | survey-default priors | **known systematics** — marginalized in *every* model incl. `M₀`; not charged to `Ξ` or `(μ,Σ)` |

> **Ansatz / MG rank ceiling (anti-fudge, `plan/04` §3.1 / §9.2).** `M_Ξ` adds **≤ 2** *closure* free
> params beyond ΛCDM (`a₂`[, optional], with `a₀` **inherited, not free**); shapes `φ₀,φ₂,c_p` are
> **fixed and probe-shared** — *no per-probe free `Ξ_p`* and **`(μ,Σ)=(1,1)` held at GR in `M_Ξ`**. The
> MG comparators add their model's native params (`μ₀,Σ₀`; `f_R0`; reconstruction basis) — these are
> *MG model parameters*, the whole point of the alternative-repair comparison, and are *not* part of the
> SBT residual budget. Systematics nuisances are survey-standard and marginalized in *every* model.

---

## 4. The repair-classification object (the decision spine) (LOCKED)

The central object is the **Descent-Repair classification** (F2): are `M_Ξ` and the MG models repairs
of the *same* obstruction, and where does the required modification live? Following `plan/04` §6.1 and
`idea.md` §6 Exp7.

### 4.1 The shared-obstruction test (F2 instantiation — the unifying classification)

The obstruction is the route mismatch `RM_p > 0` (`plan/04` §4.2 eq. 12) established by E0/E1 — a
**single** nonempty `splitObs(q, F, r)`. E7 verifies that the MG repair and the `Ξ` repair both
discharge *this* obstruction:

```
For the SAME fitted geometry/growth residual r_obs − r_FLRW(θ̂_ΛCDM):
  Repair_Ξ  : r_obs ≈ r_FLRW + K_M[Ξ]            (background rewrite, μ=Σ=1)        (E7.1a)
  Repair_MG : r_obs ≈ r_FLRW^{(μ,Σ)} (or w₀w_a)  (growth-gravity / background rewrite)(E7.1b)
Shared-obstruction certificate: both fits target the SAME RM_p>0 obstruction, i.e.
  |splitObs(M_Ξ) △ splitObs(M_MG)| / |splitObs| < ε_share   (the obstruction sets coincide)   (E7.2)
```

`E7.2` is the operational form of F2's claim that the two are alternative repairs of *one* obstruction:
the set of split pairs each model resolves must (largely) coincide. If MG repairs a *different*
obstruction than `Ξ` (e.g. an isotropy violation no `Ξ`-rewrite touches), they are not the same chart
and E7 logs that distinction (`D_sym`/`out_of_scope`).

### 4.2 The where-does-the-modification-live test (the central E7 prediction)

The DESI datum: `(μ₀,Σ₀)` GR-consistent *while* background `w(z)` evolves. E7's falsifiable SBT
prediction:

```
Fit M_Ξ (background rewrite, μ=Σ=1) to reproduce the DESI w(z)-like background signal (K_M).        (E7.3)
THEN infer (μ₀,Σ₀) from the SAME M_Ξ posterior (the growth sector via K_G/K_S).
SBT prediction:  the inferred (μ₀,Σ₀) is GR-consistent:  |μ₀^{SBT}| < 2σ_μ,  |Σ₀^{SBT}| < 2σ_Σ        (E7.4)
                 i.e. SBT reproduces DESI's μ₀=0.04±0.22, Σ₀=0.044±0.047 WITHOUT a local-gravity mod.
```

`E7.4` is the make-or-break SBT prediction (gate `G-E7-MUSIGMA`): a completion-layer operator rewrite
**predicts** GR-consistent growth gravity. If reproducing the DESI background with `Ξ` *forced* a
non-GR `(μ,Σ)`, SBT's "the anomaly is in the completion, not local gravity" reading would be falsified.

### 4.3 The MG-admissibility (no-instability) audit (`plan/04` §7, reused from E3)

Each MG repair model must pass the **same** stable-readout / spectral-stability certificate the SBT rewrite
passes in E3 (`plan/04` §7):

```
No-instability certificate for an MG repair R_MG:
  (1) Spectral stability: max_λ Re λ(J_MG) ≤ 0  (no growing mode), to numerical tolerance.            (E7.5)
  (2) Energy positivity:  R_MG positive on ⟨·, C·⟩  (C=Σ^{-1}); min symmetrized eigenvalue ≥ 0.        (E7.6)
A MG model that FAILS (E7.5)/(E7.6) is an INADMISSIBLE repair → AOR `blocked` (plan/04 §8.3).
```

This operationalizes "MG as an alternative repair *when its audits pass*" (`idea.md` §6 Exp7). An MG
model with a ghost/gradient instability is a *blocked* rewrite, exactly as a ghost-inducing `Ξ` rewrite
would be (`plan/00-overview` §6.3 E7 failure: "MG eigenvalue instability (AOR fail)").

### 4.4 The MG-vs-`Ξ` necessity test (growth out-of-sample)

The anti-fudge test (`plan/04` §4.4, `PPD_{p→q}`): is the MG growth-gravity modification *needed* beyond
the SBT background rewrite?

```
Train on geometry (E1 BAO+SN+CMB) → predict growth fσ₈/S₈ (held-out).                                 (E7.7)
  PPD_{geom→growth}(M_Ξ)   : the SBT background rewrite's held-out growth prediction
  PPD_{geom→growth}(M_μΣ)  : the MG repair's held-out growth prediction
Necessity verdict: MG is NEEDED beyond Ξ iff M_μΣ lowers PPD_{geom→growth} by > 15% vs M_Ξ.            (E7.8)
                   Otherwise the MG (μ,Σ) modification is NOT required (the SBT/GR-growth reading holds).
```

`E7.8` decides whether the data *demand* a local-gravity modification once the completion rewrite is in
place. `idea.md` §8's "large-scale data do not demand modified gravity" is the expected verdict; E7
makes it quantitative.

### 4.5 The repair-classification verdict (the output)

| Verdict | Operational condition | AOR status (`plan/04` §8.2–8.3) | Reads as |
|---|---|---|---|
| **`Ξ`-repair sufficient; MG not required** | `G-E7-MUSIGMA` passes (E7.4) **and** MG does not lower `PPD_{geom→growth}` by >15% (E7.8 negative) | SBT residual `bridged` (operator-rewrite chart); MG `nonclaim`/`approved_other` | the SBT reading: anomaly in the completion; GR growth predicted; MG not demanded |
| **MG admissible alternative repair (audits pass)** | MG reproduces DESI GR-consistency (`G-E7-REPRO`), passes the no-instability certificate (E7.5–E7.6), **and** is coherent with the same `Ξ` (G-E7-COHERE) | MG repair `approved_other`; classified F2 alternative-repair chart | MG is a *legitimate* alternative chart of the *same* `Ξ`-repair — logged, not refuted |
| **MG inadmissible (instability)** | an MG model fails the no-instability certificate (E7.5/E7.6) | `blocked` (provably inadmissible rewrite) | that specific MG model is a blocked repair (a ghost/instability) |
| **MG required beyond `Ξ`** | MG lowers `PPD_{geom→growth}` by >15% (E7.8 positive) **and** passes stability | MG `bridged` (a needed growth-gravity repair) | the data *demand* a growth-gravity modification — a genuine, honest, falsifying-for-SBT outcome (logged) |

---

## 5. Method (pipeline)

> **Determinism / provenance (mandatory, `GROUNDING_BRIEF` §III; `plan/02` §determinism).** Every run
> pins `numpy`/`random`/sampler seeds and `OMP_NUM_THREADS=1` for the determinism gate, writes a
> run-manifest JSON (`run_id`, date, seeds, datasets+versions, software versions incl. **pyccl-internal
> vs standalone CLASS version**, backend tier per leg, parameters, output files, `audit_status`), and
> emits `[chain, posterior.hdf5, triangle.png]`. `float64` throughout.

### Step 0 — Environment + backend gate (must pass first)
- Confirm `plan/02` T0/T1 build gates: `import pyccl` succeeds; **G-ENV-4 pyccl↔CLASS agreement** passes
  (`P(k)` <1%, `σ8` <0.5%); CCL computes one `(μ,Σ)`-modified `fσ₈(z)`, one `f(R)` `μ(k,z)`, one shear
  `C_ℓ` vs stored references <0.5%. *Fail → E7 is blocked* (`plan/02` §6.G-ENV-4: "fail → block growth
  experiments E5/E7"). This is the precondition the precursor never met (surrogate-only LSS).

### Step 1 — Reproduce the DESI MG result (gate `G-E7-REPRO`, §7.1) — the central reproduction
- Fit `M_μΣ` (phenomenological MG, GR background or `w₀w_a`) with the physical CCL `(μ,Σ)` forward
  model to DESI DR2 full-shape + BAO + CMB (+ DESY3/DES Y6), and **recover the published GR-consistent
  `(μ₀,Σ₀)`**: `μ₀ = 0.04 ± 0.22`, `Σ₀ = 0.044 ± 0.047` within the quoted uncertainty (arXiv:2411.12026).
- Fit `M_fR` and recover the Hu–Sawicki bound `log₁₀|f_R0| < −4.59` (95%) (arXiv:2604.26915).
- Fit `M_w` and recover the DESI **background** `w₀w_a` preference (the same contours E1 reproduces).
- **No SBT object is introduced until these pass** (`idea.md` §10 standard 1). Convergence: `R̂ < 1.01`
  all params; ESS > 400/chain.

### Step 2 — The where-does-the-modification-live test (the central E7 prediction)
- Fit `M_Ξ` (background rewrite via `K_M`, `μ=Σ=1`, `a₀` pinned from E1) to reproduce the DESI
  background `w(z)`-like signal (E7.3); verify it matches the `M_w` background to within the E1 gate.
- From the **same** `M_Ξ` posterior, infer the *would-be* `(μ₀,Σ₀)` (the growth sector via `K_G`/`K_S`)
  and test the SBT prediction `|μ₀^{SBT}| < 2σ_μ`, `|Σ₀^{SBT}| < 2σ_Σ` (E7.4, gate `G-E7-MUSIGMA`).
- Record whether SBT *reproduces* DESI's GR-consistency without a local-gravity modification.

### Step 3 — The shared-obstruction (F2) classification
- Compute the route-mismatch obstruction `RM_p` and the split-pair set `splitObs` (`plan/04` §4.2, §6.1)
  on the fitted geometry/growth residual. Verify (E7.2) that `M_Ξ` and each MG model repair (largely)
  the **same** `splitObs` set (`|△|/|splitObs| < ε_share`, default `ε_share = 0.15`). Classify each MG
  model as an F2 **operator-rewrite (alt) chart of the same obstruction**, or flag a distinct
  obstruction (`D_sym`/`out_of_scope`).

### Step 4 — The MG no-instability (admissibility) audit
- For each MG repair model (`M_μΣ`, `M_fR`, `M_ST`), apply the `plan/04` §7 stable-readout / spectral-
  stability certificate (E7.5–E7.6): linearize the macro evolution including the MG modification,
  compute `max_λ Re λ` (require `≤ 0`) and the min symmetrized eigenvalue in `C`-coordinates (require
  `≥ 0`). Any model failing → AOR `blocked`. Verify kernel/operator linearity of `K_M,K_G,K_S` to <1%
  (finite-difference, `plan/04` §9.2), shared with E3/E5.

### Step 5 — The MG-vs-`Ξ` necessity test (growth out-of-sample)
- Leave-one-probe-out PPD (`plan/04` §4.4): fit each model to **geometry (E1 BAO+SN+CMB) → predict
  growth `fσ₈`/`S₈`** (E7.7); score whitened `PPD_{geom→growth}`. The necessity verdict (E7.8): does
  `M_μΣ` lower held-out `PPD_{geom→growth}` by **>15%** vs `M_Ξ`? Also the reverse growth→geometry.
- This is the "is MG *demanded*?" decision (`idea.md` §8 "data do not demand modified gravity").

### Step 6 — Coherence handoff (the make-or-break)
- Read E1's `a₀` and `K_M` amplitude and E5's `K_G`/`K_S` from `results/xi_cosmo_coherence.csv`. Compute
  the **effective `Ξ` amplitude implied by each MG model** (the `(μ,Σ)`/`f_R0`-induced growth shift,
  mapped back through `K_G`/`K_S` to an effective `Ξ` amplitude). **Check the coherence gate
  `G-E7-COHERE`**: the MG-implied `Ξ` amplitude within **10×** and consistent sign with E1/E5's
  amplitude (`plan/04` §9.4; `plan/00-overview` §6.4). Append E7's `(a₂, μ₀, Σ₀, f_R0, effective-Ξ)`
  amplitudes + the repair-classification verdict to the coherence ledger for E8.

### Step 7 — Repair-classification verdict + AOR ledger
- Assign the §4.5 verdict; emit the AOR status for the MG residual, the SBT residual, every blocked MG
  model, every systematic / backend-tier descent, and every standing nonclaim (F9, no `unstatused`).

### Step 8 — Model-comparison record (handoff to E8)
- Record per model `{M₀, M_w, M_Ξ, M_μΣ, M_fR, M_ST}`: `χ²`, `χ²/dof`, `k`, `BIC = χ²+k ln N`, `AIC`,
  posteriors, fitted `(w₀,w_a)`/`(μ₀,Σ₀)`/`f_R0`, derived `w_eff(z)`, `fσ₈(z)`, `S₈`, OOS
  `PPD_{geom→growth}`, the stability certificate result, the F2-classification, the coherence amplitude.

### Software (from `GROUNDING_BRIEF` §II.A; `plan/02` §1.4)
`pyccl ≥3.0,<3.2` (CCL — the physical `(μ,Σ)`/`f(R)`/3×2pt/RSD forward model, the core of E7),
`cobaya ≥3.5,<3.6` (MCMC/likelihood interface), `desilike` (DESI full-shape RSD + MG),
`CLASS ≥3.2`/`CAMB ≥1.5.7` (transfer/background; reconcile with pyccl-internal CLASS via G-ENV-4; MGCAMB /
hi_class for `(μ,Σ)`/`f(R)`/scalar-tensor where CCL's native parameterization is insufficient),
`getdist ≥1.5` + `arviz ≥0.15` (`R̂`/ESS/posteriors), `numpy<2.0`/`scipy` (eigenvalue/stability,
whitened distances), `matplotlib ≥3.5`. Optional Lean 4 (`v4.28.0`) for the F2 MG-as-repair witness (§6).

---

## 6. Outputs and AOR statusing

### 6.1 Artifacts (committed)

| Artifact | Path (suggested) | Contents |
|---|---|---|
| Run manifests | `results/E7/manifests/*.json` | per-run seeds, datasets+versions, **backend tier per leg**, pyccl/CLASS/MGCAMB versions, params, audit_status (`GROUNDING_BRIEF` §III.B) |
| MG reproduction record | `results/E7/repro_mg.csv` | published-vs-recovered `(μ₀,Σ₀)`, `log₁₀\|f_R0\|` bound, `(w₀,w_a)` per model (G-E7-REPRO) |
| Where-modification-lives record | `results/E7/musigma_prediction.json` | `M_Ξ`-inferred `(μ₀^{SBT}, Σ₀^{SBT})` + credible intervals; the GR-consistency test (E7.4); the `M_Ξ`-vs-`M_w` background match |
| Shared-obstruction (F2) record | `results/E7/f2_repair_classification.json` | `RM_p`, `splitObs` overlap `|△|/|splitObs|` per MG model (E7.2); the F2 alternative-repair classification |
| MG stability certificates | `results/E7/mg_stability.json` | per-MG-model `max_λ Re λ`, min symmetrized eigenvalue (E7.5–E7.6); admissible / `blocked` verdict |
| MG-vs-`Ξ` necessity (OOS) | `results/E7/ppd_geom_growth.json` | held-out `PPD_{geom→growth}` per model; the >15% necessity verdict (E7.8) |
| Model-comparison table | `results/E7/model_comparison.csv` | rows `{M₀,M_w,M_Ξ,M_μΣ,M_fR,M_ST}` × cols `{χ²,χ²/dof,k,BIC,ΔBIC vs M₀,AIC, w₀,w_a, μ₀,Σ₀, f_R0, S₈, OOS PPD_{geom→growth}, stable?}` |
| Repair-classification verdict | `results/E7/repair_verdict.json` | the §4.5 verdict + evidence (E7.4, E7.8, stability, coherence) + AOR statuses |
| Posterior triangles | `results/E7/triangle_*.png` | per model (`getdist`); the `(μ₀,Σ₀)` contour with GR `(0,0)` marked |
| AOR status entry | appended to `results/aor_status_table.csv` | the typed MG/SBT residuals + every blocked model / systematic / backend descent (§6.2) |
| Coherence handoff | `results/coherence_ledger/E7.json` (+ append `results/xi_cosmo_coherence.csv`) | `a₂`, MG `(μ₀,Σ₀,f_R0)` → effective-`Ξ` amplitude + sign, the F2 verdict, for §6.4 cross-check + E8 |

### 6.2 AOR statusing of the E7 residuals (`plan/04` §8; `idea.md` §6 Exp7)

Every surviving MG/SBT tension carries **exactly one** AOR base status (F9). Determined by §4.5:

| E7 residual | AOR status | Residual type (`plan/04` §8.2) | Payload `π` |
|---|---|---|---|
| SBT background residual repaired by `Ξ` (the `w(z)` signal) | `bridged` | `D_descent` | the `Ξ` operator-rewrite `R[Ξ]` (term-0 `a₀` inherited + `a₂`) that repairs FLRW descent |
| MG `(μ,Σ)` model as admissible alternative repair (audits pass) | `approved_other` | `D_descent` | the cited DESI MG result + this run's GR-consistent reproduction (F2 alt chart) |
| an MG model failing the no-instability certificate | `blocked` | `D_descent` | the block reason (`max_λ Re λ > 0` or negative-norm direction) — a provably inadmissible repair |
| residual growth offset not explained by `Ξ` or `(μ,Σ)` | `budgeted` | `D_target` | the finite bound on the unexplained `fσ₈`/`S₈` offset |
| flat `f_R0` direction (data cannot pin it below the bound) | `moduli` | `D_scale` | the moduli pin: `log₁₀\|f_R0\| < −4.59` upper bound is a one-sided flat direction |
| scalar-tensor reconstruction comparator (`M_ST`, raises `H₀`) | `approved_other` | `D_transport` | the cited arXiv:2511.04610-class result; ties to E3 (phantom) / E4 (Hubble) |
| galaxy-bias / IA / baryon / photo-z / shear-cal nuisances | `budgeted` | `D_source` | survey-standard systematic priors (known-systematics), marginalized in every model |
| any Gaussian-likelihood approximation (tier-2) | `budgeted` | `D_presentation` | the likelihood-approximation budget |
| DES-Y6 official likelihood unavailable (tier-4, DES Y3 used) | `approved_other` | `D_interface` | the external-substitute citation |
| a leg only runnable as compressed-contour reuse (tier-5) | `out_of_scope` | `D_horizon` | the physics-grade-decision deferral |

Plus standing statuses always recorded:
- "a fundamental modification of gravity is **not ruled out** here; MG is a legitimate alternative
  repair, not refuted" → `nonclaim` (`idea.md` §7 §8; mirrors precursor "Λ not ruled out").
- "we do not claim GR is wrong, nor that SBT is superior to MG; we claim they are alternative repairs
  of the *same* obstruction (F2)" → `nonclaim` (`idea.md` §1.2, §7 rhetorical discipline).
- the QFT→cosmology bridge (P2) is **not** attempted here → `out_of_scope` (cross-reference `plan/04` §6.2).

This run advances the carrier; combined with E4–E6 it targets **CascadeStableAOR** (`plan/00-overview`
§7; E1–E3 → RefStableAOR, E4–E7 → CascadeStableAOR).

### 6.3 Lean anchor (optional this experiment, target for the F2 MG-as-repair witness)

`SBTCosmo.DescentRepair` (`plan/04` §6.1; `Foundations_IV` `thm:F2`,
`Transport.DescentRepair.descent_repair_normal_form`): reuse the E1 descent-repair anchor and add an
**MG-as-alternative-repair witness** — a finite statement that the MG model (`(μ,Σ)`-modified `r∘F`)
and the `Ξ`-model both make `r∘F` descend through `q = U_θ`, i.e. both lie in the admissible-repair set
of the *same* `splitObs(q,F,r) ≠ ∅`. The F2 normal form and the membership are `[T]`; the data
classification (E7.2 overlap, E7.4 GR-consistency, E7.8 necessity) is `[E]`. The MG no-instability
certificate (E7.5–E7.6) reuses the E3 `SBTCosmo.PhantomStableReadout` spectral-stability scaffold (`[T]` for
the constructed map; the data verdict `[E]`).

---

## 7. Pass / fail gates (quantitative, pre-registered)

> **Pre-registration discipline (`plan/00-overview` §6, `plan/04` §9).** Thresholds are fixed
> **before** seeing results and may not be relaxed afterward; any relaxation is a logged statused
> deviation (`budgeted`). Units: `(μ₀,Σ₀)` in σ of the DESI quote, `χ²/dof`, `ΔBIC`, eigenvalue real
> part, whitened distances, fractional `PPD` improvement, coherence-amplitude ratio.

### 7.1 Backend + reproduction gates (must pass first — else blocked)

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E7-BACKEND` | `pyccl` imports; **G-ENV-4 pyccl↔CLASS agreement** passes (`P(k)`<1%, `σ8`<0.5%); CCL `(μ,Σ)`/`f(R)`/shear reference checks <0.5% | `plan/02` §6.G-ENV-4, T1 |
| `G-E7-REPRO` | physical-CCL `M_μΣ` recovers DESI **`μ₀=0.04±0.22, Σ₀=0.044±0.047`** within the quoted 1σ; `M_fR` recovers `log₁₀\|f_R0\| < −4.59` (95%); `M_w` recovers the DESI background `w₀w_a` contours within ±5% (matching E1); `R̂<1.01`, ESS>400 | `idea.md` §8, §10.1; arXiv:2411.12026, 2604.26915 |
| `G-E7-COV` | each probe `Σ` PD, cond `<10⁸`, finite (else `Σ^†` on legal quotient) | `plan/04` §4.0; `GROUNDING_BRIEF` §VI |

### 7.2 Ansatz / kernel / admissibility gates

| Gate | Threshold | Tie to |
|---|---|---|
| `G-E7-RANK` | `M_Ξ` adds `≤2` closure params (`a₂`[, optional]); `a₀` **inherited from E1, not re-fit**; **`(μ,Σ)=(1,1)` held at GR in `M_Ξ`**; `φ₀,φ₂,c_p` probe-shared; **no per-probe free `Ξ_p`** | `plan/04` §3.1, §9.2 |
| `G-E7-KERNEL` | `K_M,K_G,K_S` linear in `(a₀,a₂)` to `<1%` (finite-difference); `R[Ξ]` positive+stable (stable-readout, `plan/04` §7) | `plan/04` §3.2–3.3, §9.2 |
| `G-E7-STABILITY` | **every MG repair model that is admitted** passes the no-instability certificate (E7.5–E7.6): `max_λ Re λ ≤ 0` (tol `10⁻⁶`) **and** min symmetrized eigenvalue `≥ −10⁻⁸`; any MG model failing is logged `blocked` (not silently dropped) | `plan/04` §7; `plan/00-overview` §6.3 E7 |
| `G-E7-SYS` | bias/IA/baryon/photo-z/shear-cal nuisances marginalized in **every** model incl. `M₀`; not charged to `Ξ` or `(μ,Σ)` | §3.2 anti-fudge |

### 7.3 The repair-classification gates (the heart of E7)

These operationalize `idea.md` §6 Exp7 and the §4.5 verdict:

| Gate | PASS condition | Reads as |
|---|---|---|
| **`G-E7-MUSIGMA`** (the central SBT prediction; **where-modification-lives**) | the `M_Ξ` background rewrite (μ=Σ=1) reproduces the DESI `w(z)`-like background signal (matches `M_w` background within the E1 gate) **and** the `(μ₀,Σ₀)` inferred from the *same* `M_Ξ` posterior is **GR-consistent** (`\|μ₀^{SBT}\| < 2σ_μ`, `\|Σ₀^{SBT}\| < 2σ_Σ`) (E7.4) | SBT explains the DESI signal **without** a local-gravity modification, and **predicts** DESI's GR-consistent `(μ,Σ)` (the central thesis) |
| **`G-E7-F2`** (shared obstruction) | `M_Ξ` and each admitted MG model repair the **same** obstruction: split-pair overlap `\|△\|/\|splitObs\| < 0.15` (E7.2); each MG model classified as an F2 alternative-repair chart (or distinct obstruction flagged) | MG and `Ξ` are alternative charts of one obstruction (the unifying F2 classification, `idea.md` §9) |
| **`G-E7-NECESSITY`** (is MG demanded?) | report `PPD_{geom→growth}(M_μΣ)` vs `PPD_{geom→growth}(M_Ξ)`: MG is *required beyond `Ξ`* iff it lowers OOS `PPD` by **>15%** (E7.8); otherwise MG is **not demanded** (the expected `idea.md` §8 verdict) | quantifies "data do not demand modified gravity" — a *verdict*, either direction is a valid logged outcome |

### 7.4 SBT-claim gates (the coherence / value test)

| Gate | PASS | FAIL |
|---|---|---|
| `G-E7-COHERE` (coherence, the make-or-break, `plan/04` §9.4; `plan/00-overview` §6.4) | the MG-implied effective `Ξ` amplitude (and `M_Ξ`'s `a₂`) within **10×** and **consistent sign** with E1's `K_M`/E5's `K_G,K_S` amplitude (coherence ledger) — MG and `Ξ` are the *same* low-rank residual | MG/`Ξ` amplitude differs by `>10×` or sign disagrees → **program-phase coherence failure** (`plan/00-overview` §6.4) |
| `G-E7-OOS` (out-of-sample, `plan/04` §4.4) | `M_Ξ`'s held-out `PPD_{geom→growth}` is within **15%** of the best MG model (`M_μΣ`/`M_ST`) — i.e. the SBT background rewrite predicts growth essentially as well as the local-gravity modification | `M_Ξ` growth OOS is **>20% worse** than the best MG model (the SBT/GR-growth reading is insufficient) |
| `G-E7-BIC` (model competition, handoff to E8) | record `ΔBIC` of every model vs `M₀`; no headline pass/fail here (E8 owns the competition) — but flag if any MG model beats `M_Ξ` by `ΔBIC > 5` for the E8 synthesis | (informational; the competition verdict is E8's) |

### 7.5 Pre-registered failure modes (honored and reported with numbers; `plan/00-overview` §6.3 E7, §6.2 std 5; `idea.md` §10 std 5)

E7 (as an SBT claim about the MG chart) **fails** if **any** of:
1. **`G-E7-MUSIGMA` fails**: reproducing the DESI background `w(z)` with the `Ξ` rewrite *forces* a
   **non-GR** `(μ₀,Σ₀)` (`|μ₀^{SBT}| > 2σ_μ` or `|Σ₀^{SBT}| > 2σ_Σ`) — i.e. the SBT reading that the
   anomaly lives in the completion (not local gravity) is **falsified by the data**; **or**
2. **`G-E7-COHERE` fails**: the MG chart's effective `Ξ` is mutually inconsistent with E1/E5's `Ξ`
   (`>10×` amplitude or sign disagreement) — the sharpest refutation of "one residual, many charts" for
   the MG chart (a **program-phase** coherence failure, `plan/00-overview` §6.4); **or**
3. **`G-E7-OOS` fails**: `M_Ξ`'s growth OOS is **>20% worse** than the best MG model — the SBT/GR-growth
   reading cannot predict growth and a local-gravity modification is genuinely required; **or**
4. **`G-E7-STABILITY` is mishandled**: an admitted MG model carries an instability that is **not** logged
   `blocked` (an unstatused inadmissible repair, violating F9).

> **Crucial distinctions (LOCKED — the E7-specific honesty discipline).**
> - **MG simply being *not preferred* is NOT a failure.** `plan/00-overview` §6.3 E7 states it verbatim:
>   *"MG simply not preferred is not a failure — it is a logged alternative repair."* If MG passes its
>   audits but does not beat `M_Ξ`, the correct outcome is a **logged F2 alternative-repair chart**
>   (`approved_other`), exactly `idea.md` §6 Exp7's *"still allowing MG as an alternative repair when its
>   audits pass."* E7's purpose is the **classification**, not a contest SBT must win against MG.
> - **MG being *required beyond `Ξ`* (E7.8 positive) is a valid, honest outcome** — it would mean the
>   data demand a growth-gravity modification, which is a genuine finding and a real falsifier for the
>   "anomaly is in the completion only" reading; it is logged (`bridged` MG residual), not hidden.
> - The **program** fails at E7 only if (a) `G-E7-BACKEND`/`G-E7-REPRO` fails (cannot reproduce the real
>   DESI MG constraints with a physical backend), (b) **`G-E7-MUSIGMA` fails** (the `Ξ` rewrite forces a
>   non-GR `(μ,Σ)` — the SBT completion-layer reading is data-falsified), or (c) **`G-E7-COHERE` fails**
>   (the MG chart is mutually inconsistent with the same `Ξ`). These are the only conditions under which
>   E7 refutes the SBT program; everything else is a logged, statused outcome.

---

## 8. Dependencies, blocking, and links

- **Blocked by:**
  - `plan/03` data acquisition: **DESI DR2 full-shape RSD/MG** (`DESI_RSD_FS`, arXiv:2411.12026 — the
    prime probe, with `(μ₀,Σ₀)` MG inputs and `fσ₈(z)`) + DESI DR2 BAO + Planck 2018 anchor + DES Y6 /
    DES Y3 (WL leg, shared with E5) + the scalar-tensor reconstruction comparator inputs (arXiv:2511.04610).
  - `plan/02` environment: the **CCL/`pyccl` `(μ,Σ)`/`f(R)` growth backend** (+ MGCAMB/hi_class where
    needed) + `desilike` + the **G-ENV-4 pyccl↔CLASS agreement gate** (E7 is explicitly blocked if G-ENV-4 fails,
    exactly as E5).
  - `plan/04` §1–§9: carrier + four residuals; **P1 ↔ F2 Descent-Repair Normal Form** (§6.1 — the
    formal spine: F2's two canonical repairs plus P1's cosmology-specific operator-rewrite extension, the
    "`(μ,Σ)` is an alternative operator-rewrite chart" statement); kernels
    `K_M`/`K_G`/`K_S`; the **stable-readout / spectral-stability certificate** (§7); AOR statuses
    (`approved_other`, `blocked`, `nonclaim`, `moduli`); coherence gate; metric `d`.
  - **E1** (DESI DR2 reproduction): provides the **fitted geometry `Ξ` (`a₀`, `K_M` amplitude)** and the
    reproduced DESI background `w₀w_a` contours via `results/xi_cosmo_coherence.csv` — *required* to pin
    `a₀` in `M_Ξ`, to define the background signal `M_Ξ` must reproduce, and to run the coherence gate.
  - **E5** (growth/staging): provides the **GR-growth baseline and the `(μ,Σ)` comparator `G_MG`**, plus
    the `K_G`/`K_S` growth kernels and the verified CCL growth backend (E5 §2, §6.2 "the `G_MG` `(μ₀,Σ₀)`
    comparator is owned by E7"). E7 cannot run its growth-sector tests until E5's growth backend +
    coherence ledger entries exist.
  - **E3** (phantom crossing): provides the **stable-readout / spectral-stability certificate** machinery
    (`plan/04` §7; `SBTCosmo.PhantomStableReadout`) reused for the MG no-instability audit; and the
    scalar-tensor comparator's phantom-crossing behavior cross-references E3.
- **Blocks / unblocks:**
  - **E4** (Hubble route matrix): the scalar-tensor MG comparator (`M_ST`, arXiv:2511.04610) raises `H₀`
    to `70.6±1.7` — an input to E4's lawful-plurality / Hubble-readout analysis (MG is one route's
    completion choice); E7's F2 classification feeds E4's "alternative repairs of the same `Ξ`" reading.
  - **E8** (model-competition synthesis): the `{M₀,M_w,M_Ξ,M_μΣ,M_fR,M_ST}` model-comparison row + the
    repair-classification verdict + the stability certificates + the coherence amplitudes feed the final
    model-competition matrix and the residual-reuse matrix. E7 certifies which models are *admissible*
    (or `blocked`) and *coherent*; E8 decides which is *preferred*.
  - the **coherence ledger** consumed by E8; the **AOR status table** advancing toward CascadeStableAOR.
- **`idea.md` citations:** §3 shadow map **row 9** ("MG = the operator-rewrite chart; `(μ,Σ)`, evolving
  `w`, IDE `Q`, backreaction are alternative repair charts of the same failed FLRW descent; DESI's
  `(μ,Σ)≈`GR supports the anomaly living in the completion layer, not local gravity"); §6 **Experiment
  7** (verbatim pass criterion: *"show that Six Birds explains the DESI `w(z)`-like signal without
  requiring nonlocal modified gravity, while still allowing MG as an alternative repair when its audits
  pass"*; the GR-consistency datum as "very favorable to Six Birds"); §7 **Modified gravity**
  (*"Modified gravity, evolving `w`, IDE, and backreaction are all repair options under Descent–Repair
  Normal Form; Six Birds gives the unifying classification"*); §8 (the full live MG-vs-DE picture —
  `μ₀=0.04±0.22, Σ₀=0.044±0.047`; `f_R0 < −4.59`; scalar-tensor `H₀=70.6±1.7`); §9 ("modified gravity is
  the operator-rewrite chart"); §10 (standard 1 reproduce-first, std 2 one low-rank residual, std 3 win
  out-of-sample, std 5 pre-register failure modes).
- **Corpus citations:** `Foundations_IV` **`thm:F2`** *Descent-Repair Normal Form* (the formal spine —
  F2's two canonical repairs, source refinement and minimal target coarsening, with the operator-rewrite
  chart added as P1's cosmology-specific extension; the gauge-invariant-observables physics
  instantiation; Lean `Transport.DescentRepair.descent_repair_normal_form`) + **`thm:F9`** No Unstatused
  Residual;
  `A_Six_Birds_Eye_View_of_Dark_Energy` (the three-way repair choice "refine the completion / change the
  lens / rewrite the macro operator"; "ΛCDM is one successful rewrite *family*"; route mismatch forces
  an operator rewrite); `Emergence IS the Needle Killer` (the membrane/spectral-positivity discipline
  underlying the stable-readout / MG-instability certificate); `Six_Birds_for_Neutrino_Mass` (the cross-lens
  audit + directional held-out mismatch template, reused for the growth-sector OOS); `Audited_Operational_Realisability`
  (the `approved_other` / `blocked` / `moduli` statuses, the `D_descent` residual type, the carrier
  hierarchy); `Adequacy_Residuals` (the Schur-complement `Ξ_C(D|L)` = the joint geometry+growth content
  one GR/Λ family cannot explain, which both MG and `Ξ` repair).
- **arXiv anchors:** DESI MG full-shape **2411.12026** (`μ₀=0.04±0.22, Σ₀=0.044±0.047`, GR-consistent
  while `w₀w_a` preferred — the central E7 datum); DESI 2024 VII full-shape 2411.12022; scale-dependent
  MG / `f(R)` DESI DR1 2604.26915 (`log₁₀\|f_R0\| < −4.59`, range `<17.8 Mpc`); reconstructed
  scalar-tensor 2511.04610 (`H₀=70.6±1.7`, effective phantom crossing); DESI DR2 BAO 2503.14738;
  Planck 2018 1807.06209; DES Y6 3×2pt 2601.14559 / DES Y3 fallback 2212.00091.
