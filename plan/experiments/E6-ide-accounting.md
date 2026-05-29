# E6 — Interacting Dark Sector as an Accounting Shadow (the P6 ledger experiment)

> **One-line charter.** Show that the fitted interacting-dark-energy transfer term `Q_IDE(z)` is a
> **continuity-equation (P6 accounting) chart of the single closure residual `Ξ_cosmo`**, not
> necessarily a new dark-sector force: first **reproduce the IDE background expansion history with the
> closure rewrite `R[Ξ_cosmo]`** (same `H(z)`, same distances, same effective `Q(z)`), then use
> **growth-sector and probe-split (PPD) audits** to decide whether a *real* energy exchange between
> dark matter and dark energy is required by the data, or whether the IDE coupling `ξ` is a
> bookkeeping representation that a background-equivalent `Ξ` already discharges.
>
> **The decisive logic (LOCKED, `idea.md` §6 Exp 6).** Background equivalence is *cheap* — many
> rewrites reproduce one `H(z)`. The reality of `Q` is decided **off the background**: in the growth
> sector (`fσ₈(z)`, `S₈`) and in cross-probe posterior prediction. A genuine dark-sector coupling
> imprints a *specific* growth/clustering signature (modified `δ_m` source, modified `(μ, Σ)`); a pure
> accounting chart of `Ξ` does **not** unless `Ξ`'s own staging term `a₁` happens to carry it. E6's
> verdict is therefore one of: **(a)** `Q` is reducible to `Ξ` (accounting shadow; status `bridged`),
> **(b)** `Q` carries growth content `Ξ` cannot reach with the *same* amplitude (real interaction
> indicated; status `out_of_scope` / `approved_other` — MG/IDE is the better repair here), or
> **(c)** undecidable at current precision (status `moduli` / `budgeted`).

> **Read-order / consistency.** This file implements **one** experiment of the program defined in
> `plan/00-overview.md` (§3 shadow map **row 8** — the IDE/accounting chart; §4 experiment table row
> **E6**; §6.3 headline gate E6; §6.4 coherence gate) and `../GROUNDING_BRIEF.md` (datasets
> §I.A/§I.B/§I.E/§I.F, stack §II.A/§II.B, determinism §III, AOR §VI). Every formal object used here is
> *locked* in `plan/04-formal-foundations.md`: the carrier and four residuals (§4), the low-rank ansatz
> `Ξ_cosmo = a₀φ₀ + a₁φ₁ψ₁s_p + a₂φ₂c_p` (§3.1), the rewrite operator `R[Δ]` and `ρ_eff = ρ_FLRW +
> R[Ξ]` (§3.2 eq. 5), the observable kernels `K_L/K_M/K_G/K_S` (§3.3 eqs. 6–9), and the metric `d`
> (§4.0 eq. 10). Datasets / loaders / fallbacks are locked in `plan/03-data-acquisition.md`. The
> cobaya/CLASS/`pyccl` stack and version pins are locked in `plan/02-environment-and-deps.md`. Repo
> layout, run-manifest schema, and the gate verifier are locked in `plan/01-repo-structure.md`.
> **Science source of truth:** `idea.md` §6 **Experiment 6** (*"Q_IDE is a continuity-equation chart of
> Ξ_cosmo … show that the same background behavior attributed to Q is reproduced by the closure
> residual, then use growth/probe-split audits to decide whether a real interaction is needed"*); §3
> **shadow map row 8** (*"Interacting dark sector → P6 accounting shadow → a fitted energy-transfer
> term Q is a bookkeeping representation of the residual, not necessarily a new dark force"*); §7 (*"the
> interaction term Q becomes a P6 accounting variable … not automatically evidence of a new dark
> force"*); §9 (*"IDE is the continuity-equation chart"*). Live-literature framing: `idea.md` §7
> (Pan et al. 2504.00994; Silva et al. **2503.23225**; aggressive IDE 2510.12627; late-time S-IDE
> 2601.02789).
>
> **Corpus grounding.** `A_Six_Birds_Eye_View_of_Dark_Energy` (P6 accounting/audit role of cosmology;
> the `Q(t)` closure-term proxy of Toy 2, eq. `toy2_Q_def` — the *original* "Q is a closure diagnostic,
> not the GR backreaction term" disclaimer this experiment generalizes); `To_Spend_a_Stone`
> (currency–constraint duality: a lower-layer currency `Q` becomes a higher-layer constraint; the IDE
> coupling is a **shadow price**, not a substance — the formal backbone of "accounting chart");
> `Foundations_IV` F11 *Adequacy / No-Overread* (do not overread the fitted `Q` as a dark force without
> a declared bridge), F9 *No Unstatused Residual* (every leftover `Q`–`Ξ` discrepancy is statused), F2
> *Descent-Repair Normal Form* (`Ξ`-rewrite and IDE-`Q` are two admissible repairs of the same failed
> descent — the basis of the E6/E7 comparison); `Six_Birds_for_Neutrino_Mass` (the cross-lens
> held-out `δχ` audit template, here applied to IDE-vs-`Ξ` probe splits); `Audited_Operational_Realisability`
> (the status vocabulary and the carrier-record reading); `Adequacy_Residuals` (the block-currency /
> Schur-complement reading of "what `Q` measures beyond `Ξ`").

> **Grade convention** (from `plan/04` §0): `[T]` theorem-grade (Lean / finite verified computation);
> `[C]` conditional/recognition-grade (under a named hypothesis); `[E]` empirical (decided by a gate
> in §9 below).

---

## 0. Charter (one sentence)

Demonstrate, on `Planck 2018 + DESI DR2 BAO + cosmic chronometers + SN`, that the IDE background
expansion attributed to a dark-matter↔dark-energy energy transfer `Q_IDE(z)` is reproduced to data
precision by the closure rewrite `R[Ξ_cosmo]` (background-equivalence leg), and then use growth
(`fσ₈`, `S₈`) and leave-one-probe-out PPD audits to **decide** whether a *real* interaction is needed
— recording the verdict as exactly one AOR status with the `Q`↔`Ξ` discrepancy budgeted.

### 0.1 Why E6 exists (the gate logic and the ontological move)

- **The headline claim of the program** (`idea.md` §3, §9; `plan/00-overview` §3 row 8 + §4 E6):
  `Λ`, `w_a`, `Q_IDE`, `η_CDDR`, `μ/Σ`, and `S₈` shifts are **coordinate charts on one closure
  defect** `Ξ_cosmo(z, ℓ, p)`. E6 isolates the **IDE / continuity-equation chart**: the fitted
  energy-transfer `Q`. The move is *not* "Six Birds is a better IDE model." The move is:

  > A continuity-equation transfer `Q` is a way of *writing down* the closure residual in the
  > dark-sector energy ledger. It re-balances the books between `ρ_dm` and `ρ_de`; it does not, by
  > itself, certify a new force. The reality of the force is an *additional, growth-sector* claim that
  > must pass its own audit.

- **E6 is an `Adequacy / No-Overread` (F11) instance.** A fit prefers nonzero coupling `ξ` ⇒ one
  reports a "hint of interacting dark energy." Six Birds says: nonzero `ξ` is an **overread** of the
  background ledger unless a bridge descends through the cosmological access quotient — i.e. unless the
  *growth* sector (which `Q` and `Ξ` can differ on) demands it. E6 builds and tests exactly that
  bridge.
- **E6 is a `To_Spend_a_Stone` currency-constraint instance.** The IDE coupling is a **shadow price**:
  the dual variable of the dark-sector energy-conservation constraint under the FLRW closure. A shadow
  price is real *as bookkeeping* and informative *as a diagnostic*, but it is not a new substance. E6
  makes this precise by exhibiting the explicit `Q ↦ Ξ` chart map and measuring its defect.
- **E6 feeds E8.** The IDE model is a **row** in the E8 model-competition matrix (`plan/00-overview`
  §4 E8; §6.3 E8). E6 produces: (i) the verified IDE baseline fit (`ξ`, its evidence, its `H(z)`,
  its `fσ₈`), (ii) the `Ξ`-reproduction of that background, (iii) the growth-split decision, and (iv)
  the `Q`↔`Ξ` chart-defect ledger. E7 (MG-as-repair) and E6 are the two "alternative repair chart"
  experiments (`idea.md` §7; F2); E8 ranks all repairs.

### 0.2 Two stages — hard ordering

| Stage | Name | Contents | Gate |
|-------|------|----------|------|
| **E6-A** | **IDE reproduction (the baseline gate)** | Fit the standard IDE / sign-switching-IDE (S-IDE) models on `Planck 2018 + DESI DR2 BAO + CC + SN`; recover the published coupling/`H₀`/`S₈` constraints of the 2503.23225-class analyses (mild `ξ`, `H₀`-tension → ≈2.7σ) | **Must pass G-E6-REPRO-* before E6-B/E6-C** |
| **E6-B** | **Background equivalence (the chart map)** | Construct the `Q ↦ Ξ` map; fit `R[Ξ_cosmo]` to reproduce the *same* IDE background (`H(z)`, distances, effective `Q(z)`); measure the background chart defect | Runs only after E6-A; gated by G-E6-BG-* |
| **E6-C** | **Growth-split decision (the centerpiece)** | Off-background audits: growth `fσ₈`/`S₈` comparison + leave-one-probe-out PPD; decide reality of `Q`; status the verdict | Runs only after E6-B; gated by G-E6-GROWTH-*, G-E6-PPD-* |

> **HARD CONSTRAINT (locked).** No E6-B/E6-C file, run, or table may be produced until `summary.json`
> for the E6-A run records all `G-E6-REPRO-*` gates as `PASS`. As in every experiment, **the standard
> result is reproduced before any Six Birds object is added** (`idea.md` §10 standard 1;
> `plan/00-overview` §6.1). The gate verifier (`tests/test_gates.py`, `plan/01` §6) refuses to score
> E6-B/E6-C if the E6-A manifest is absent or its reproduction gates are not green.

---

## 1. Scientific framing and grounding

### 1.1 The IDE continuity equations and the chart map (LOCKED)

In an interacting dark sector the dark-matter and dark-energy continuity equations exchange energy
through a phenomenological transfer term `Q`:

```
ρ̇_dm + 3 H ρ_dm =  + Q(z)                                                                       (E6-1a)
ρ̇_de + 3 H (1 + w_de) ρ_de =  − Q(z)                                                            (E6-1b)
```

with the **total** dark-sector continuity conserved by construction (`Q` only *re-partitions*):

```
d/dt (ρ_dm + ρ_de) + 3 H [ρ_dm + (1 + w_de) ρ_de] = 0.                                            (E6-2)
```

The canonical phenomenological forms (the ones E6-A fits; cf. Silva et al. 2503.23225, Pan et al.
2504.00994):

| Model key | `Q(z)` form | Free param(s) | Notes |
|---|---|---|---|
| `IDE_xiDE`  | `Q = ξ H ρ_de`             | `ξ` (+ `w_de`) | coupling proportional to DE density; standard "Q ∝ ρ_de" |
| `IDE_xiDM`  | `Q = ξ H ρ_dm`             | `ξ` (+ `w_de`) | coupling proportional to DM density |
| `SIDE`      | `Q = ξ(z) H ρ_de`, sign-switching `ξ(z)` | `ξ`, `z_switch` | sign-switching IDE (2503.23225); lowers `S₈` |
| `IDE_w0wa`  | `Q = ξ H ρ_de`, `w_de = w₀ + w_a z/(1+z)` | `ξ, w₀, w_a` | IDE on a CPL background — the direct E1/E3 cross-link |

**The chart map (the formal heart of E6, LOCKED).** Integrating (E6-1a)–(E6-1b) yields an *effective*
dark-energy density `ρ_de^eff(z)` whose departure from `ρ_Λ` encodes the entire interaction at the
background level:

```
ρ_de^eff(z) := ρ_de(z) + ∫ [partition of Q into the DE ledger]  ≡  ρ_FLRW(z; θ) + ΔρQ(z).         (E6-3)
```

Six Birds *identifies* this background departure with the closure rewrite (`plan/04` §3.2 eq. 5):

```
ρ_eff(z) = ρ_FLRW(z; θ) + R[Ξ_cosmo](z)        and the chart map is        R[Ξ_cosmo](z) ↦ ΔρQ(z).  (E6-4)
```

Equivalently, **the IDE transfer is the time-derivative (continuity-equation) reading of the rewrite**:

```
Q_Ξ(z) := + (1+z) H(z) · d/dz [ R[Ξ_cosmo](z) ]  −  3 H(z) (1 + w_eff) R[Ξ_cosmo](z),              (E6-5)
```

i.e. `Q_Ξ` is the source term that, inserted in (E6-1a)–(E6-1b), reproduces the same `ρ_de^eff(z)`.
**Derivation (sign LOCKED, ADDENDUM §6).** From `ρ̇ + 3H(1+w)ρ = −Q` with `ρ ≡ R` and `ρ̇ = dR/dt =
−(1+z)H·R′(z)` (since `ż = −(1+z)H`): `Q = −ρ̇ − 3H(1+w)R = +(1+z)H·R′(z) − 3H(1+w)R`. **Sign sanity:**
`R(z)=R₀(1+z)`, `w=−1` ⇒ `Q = (1+z)H R₀ > 0` (DE *losing* energy as `ρ_de` decreases toward the future) —
the leading **+** is mandatory; a `−` inverts the inferred energy-transfer direction.
This is exactly the sense in which **`Q` is the continuity-equation chart of `Ξ`** (`idea.md` §9). The
inverse map `Q ↦ Ξ` exists whenever `ΔρQ(z)` lies in the span of the low-rank ansatz shapes
`{φ₀, φ₁ψ₁s_p, φ₂c_p}` (`plan/04` §3.1) — and its **defect** (the part of `ΔρQ` *outside* that span)
is the background chart residual measured by G-E6-BG.

> **Anti-fudge note (LOCKED).** `Ξ` is **not** allowed to absorb `Q` by adding free shapes. `Q_Ξ`
> must be produced by the *same* rank-≤3 ansatz `(a₀, a₁, a₂)` (`plan/04` §3.1) already constrained by
> E1/E2/E3/E5. If reproducing the IDE background requires `Ξ` shapes outside `𝒜`, that is itself the
> finding (it means `Q` carries content `Ξ` cannot reach — a point in favor of a real interaction) and
> is reported, not patched.

### 1.2 Why background equivalence is necessary but not sufficient (the decisive logic, LOCKED)

`idea.md` §6 Exp 6 pass criterion, verbatim intent:

> *"show that the same background behavior attributed to `Q` is reproduced by the closure residual,
> **then use growth/probe-split audits to decide whether a real interaction is needed**."* — `idea.md`
> §6 Exp 6.

The two halves are not symmetric:

- **Background `H(z)` / distances are highly degenerate.** Any of: a constant `Λ`, a CPL `w₀w_a`, an
  IDE `Q`, or a closure rewrite `R[Ξ]` can be tuned to a *single* `H(z)`. So background equivalence is
  **cheap** and proves only that `Q` and `Ξ` are *not distinguishable by geometry alone* over the
  sampled `z` range. (The precursor already saw this: SN+BAO geometry could not separate a fundamental
  `Λ` from a constant closure correction — `A_Six_Birds_Eye_View_of_Dark_Energy` §discussion, "power-law
  shape parameter saturates at `m ≈ 0`".)
- **The growth sector breaks the degeneracy.** A genuine dark-matter↔dark-energy coupling modifies the
  matter density source: the linear growth equation acquires an extra friction/source from `Q`,
  shifting `fσ₈(z)` and `S₈` in a way *predicted by `ξ`*. A pure background chart of `Ξ` shifts growth
  only through its *own* staging term `a₁` (`K_G`, `K_S`; `plan/04` §3.3) — a **different, already
  constrained** amount. So:

  > **Reality test (LOCKED).** A *real* interaction is indicated **iff** the growth-sector data
  > demand the IDE growth signature at an amplitude the background-equivalent `Ξ` (with its E1/E5-fixed
  > `a₁`) **cannot** match. If the growth data are equally well described by `Ξ`'s own `K_G`/`K_S` at
  > the coherent amplitude (within the program's 10× coherence band, `plan/04` §3.3/§9.4), then `Q` is
  > **reducible** to the accounting chart and no new force is needed.

This is the cosmological instance of `Adequacy / No-Overread` (F11): the coupling `ξ` is accepted as a
*physical force* only at the access quotient that *includes growth*, never at the background-only
quotient.

### 1.3 Foundations grounding (P6 accounting; F11; F2; To Spend)

- **P6 accounting / audit (`plan/04` §2; `A_Six_Birds_Eye_View_of_Dark_Energy` §framework table, P6
  row).** `Q` is a **ledger entry**: it balances the dark-sector energy books. The continuity equation
  (E6-2) is the *conservation constraint*; `Q` is the *transfer* that keeps it satisfied given a chosen
  partition between `ρ_dm` and `ρ_de`. P6 says a ledger entry is a bookkeeping device whose
  *directionality and budget* are auditable, not automatically an ontological commitment.
- **To_Spend_a_Stone (currency–constraint duality, shadow prices).** Formally: under the FLRW closure,
  dark-sector energy conservation is a constraint; the IDE coupling `ξ` is the **dual variable
  (shadow price)** of that constraint in the constrained-max-entropy closure. Shadow prices are the
  *same mathematical object* across layers (temperatures, regularizers, attention weights — and here,
  the IDE coupling). E6's claim "`Q` is an accounting chart" is precisely "`ξ` is a shadow price of
  `Ξ`'s closure constraint, not a coupling constant of a new Lagrangian term."
- **F2 Descent-Repair Normal Form (`plan/00-overview` §5 P1; `plan/04` §6).** When the FLRW descent
  fails, the F2 normal form supplies the **two** canonical repairs — source refinement and minimal target coarsening; operator rewrite is the **P1** cosmology extension (not part of F2 itself). The
  IDE-`Q` repair and the `Ξ`-rewrite repair are **two charts of the same repair class**; E6 establishes
  the chart map (E6-4) and E8 ranks them. F2 is what makes "`Q` and `Ξ` describe the same thing" a
  *theorem-shaped* statement rather than an analogy.
- **F11 Adequacy / No-Overread (`plan/04` §1; `Foundations_IV` thm:F11, def:access-quotient).** The
  identification "nonzero `ξ` ⇒ a real dark force" is an **overread** unless a bridge descends through
  the access quotient that distinguishes them (growth). E6 builds the bridge test; if it fails to
  demand a force, the overread is rejected and `Q` is statused `bridged` (reducible to `Ξ`).
- **F9 No Unstatused Residual (`plan/04` §8.3).** The `Q`↔`Ξ` chart defect, any residual growth offset,
  and the verdict itself each carry **exactly one** AOR base status (§6, §8).
- **Adequacy_Residuals (Schur complement).** "What does `Q` measure beyond `Ξ`?" is the adequacy
  residual `Ξ_C(Q | Ξ) = K_{QQ} − K_{QΞ} K_{ΞΞ}^† K_{ΞQ}` evaluated on the *growth-augmented* currency
  block. A vanishing residual ⇒ `Q` adds nothing to `Ξ` (accounting shadow). A nonzero residual with a
  blind-spot witness ⇒ `Q` carries a growth direction `Ξ` cannot reach (interaction indicated). This
  is the §7 decision functional.

### 1.4 The live IDE picture this experiment must engage (mandatory, adversarial)

`idea.md` §7 frames the IDE situation as **mixed**: the model is flexible enough to address several
tensions at once, but the evidence for a nonzero coupling is mild and criterion-dependent. E6 must
**not** claim IDE is wrong; it must claim IDE's *background* success is chart-equivalent to `Ξ` and let
the growth audit decide the force question. The references E6 reproduces / engages:

| Reference | arXiv | What it reports | What E6 must do |
|---|---|---|---|
| Silva et al. (DESI DR2 IDE) | **2503.23225** | IDE/S-IDE on DESI DR2 BAO: `H₀` tension → ≈2.7σ; standard IDE compatible with `S₈`; S-IDE lowers `S₈`; **only mild evidence** for nonzero coupling | **Reproduce** the coupling/`H₀`/`S₈` constraints (E6-A baseline); use S-IDE as the lower-`S₈` growth-stress case |
| Pan et al. (IDE after DESI DR2) | 2504.00994 | IDE vs Planck18 + DESI DR2 BAO + cosmic chronometers + SN: mild interaction preference (>1σ, within 2σ); model comparison mixed (some criteria prefer IDE, Bayesian/AIC can favor ΛCDM) | **Anchor the dataset combination** (CC included); reproduce the mixed-evidence picture as the E6-A reference |
| Aggressive IDE + dynamical `Λ`-scale | 2510.12627 | `H₀ = 71.90 ± 1.00`, tension → 0.8σ with SH0ES — but via an *extra* dynamical-Λ parameter (model-dependent) | Treated as a **counterfactual**: extra parameters ⇒ extra ledger freedom; E6 tests whether `Ξ` reaches the same `H(z)` *without* the extra parameter, and statuses the difference |
| Late-time strongly-interacting (threshold) | 2601.02789 | dark-sector interaction *turns on* below a transition redshift; fits comparable to CPL without phantom crossing | The **late-activation** structure is the `φ₁(z)=z/(1+z)` staging shape of `Ξ` (`plan/04` §3.1) — a direct chart-map prediction; E6 tests the `z_switch` ↔ staging-shape correspondence |

> **Honesty rule (LOCKED).** E6's verdict is **not** "IDE is unnecessary." If the growth audit
> *demands* the interaction (G-E6-GROWTH fails the reducibility direction), the verdict is "a real
> interaction is indicated here" (status `out_of_scope` / `approved_other` — IDE is the better repair
> chart for this dataset), and that is reported with numbers. E6 is adversarial in both directions.

---

## 2. Inputs

### 2.1 Datasets (exact releases; from `plan/03` and Brief §I)

All dataset keys, loaders, fetch URLs, formats, licenses, and fallbacks are fixed in
`plan/03-data-acquisition.md`. E6 consumes the following and **only** the following:

| Role | Dataset key | Release (arXiv/DOI) | Product used in E6 | Loader (`io/datasets.py`) | Fallback (AOR status) |
|------|-------------|---------------------|--------------------|---------------------------|-----------------------|
| **CMB (ANCHOR)** | `PLANCK_2018` | arXiv:1807.06209 | Native `clik`: TT(ℓ2–2500), TE/EE(ℓ2–2300), low-ℓ, lensing | `load_planck_2018(...)` | compressed CMB distance priors `(R, ℓ_A, ω_b, n_s)` + cov (`budgeted`) |
| **BAO (PRIMARY)** | `DESI_DR2_BAO` | arXiv:2503.14738 | Joint `D_M(z)/r_d`, `D_H(z)/r_d` (+ `D_V/r_d`) + full covariance | `load_desi_dr2_bao()` | compressed BAO-only Gaussian likelihood (`budgeted`) |
| **Cosmic chronometers (CC)** | `CC_HZ` | compiled `H(z)` (Moresco-class differential-age `H(z)` set; per `plan/03`) | direct `H(z_i) ± σ_i` (model-independent expansion-rate anchor) | `load_cc_hz()` | drop CC leg → status `out_of_scope` for the CC-anchored sub-claim |
| **SN (PRIMARY)** | `PANTHEON_PLUS` | arXiv:2202.04077 | `μ(z_hel, z_cmb)` for 1550 SN + full `C_μμ` | `load_pantheon_plus(z_min=0.01)` | binned `μ(z̄)` 10–20 bins + cov (`budgeted`; full = `zero`) |
| **SN (variant)** | `UNION3` | arXiv:2401.06956 | Standardized `μ` for 1258 SN + systematic block cov | `load_union3()` | compressed 5-bin distance–redshift (`budgeted`) |
| **RSD / growth (DECISION leg)** | `DESI_RSD_FS` | **DR2 compressed `fσ₈` primary** (DR1 FS *method* arXiv:2411.12026) | compressed `(fσ₈, D_M/r_d, D_H/r_d)` (6–8 bins) + `(μ₀, Σ₀)` MG inputs | `load_desi_rsd_fs(compressed=True)` | DR1 FS retained only as a method control (`budgeted`); see `plan/03` §2 |
| **WL / `S₈` (DECISION leg)** | `DES_Y6` / `KIDS_LEGACY` | arXiv:2601.14559 / 2503.19441 | published `S₈` + (where available) 3×2pt likelihood via `pyccl` (reuses E5 backend) | `load_des_y6()` / `load_kids_legacy()` | published Gaussian `S₈` summary (`budgeted`) |

> **Why cosmic chronometers are mandatory here (LOCKED).** CC give a **model-independent `H(z)`**
> anchor that does not pass through the BAO `r_d` calibration or the SN distance-duality bridge. This
> is what makes the background-equivalence leg (E6-B) honest: if `Ξ` and `Q` reproduce the *same*
> `H(z)` including the CC points, the background equivalence is not an artifact of a shared calibration
> degeneracy. CC is the dataset that the 2504.00994 IDE analysis used and the one `idea.md` §7 names
> explicitly for IDE constraints. The CC leg is also the cleanest place to expose the 2510.12627
> "extra dynamical-Λ parameter buys `H₀`" counterfactual.

### 2.2 Baseline chains consumed from E1 (fixed inputs)

E6 does **not** re-derive the standard baselines. It reads from E1 (`results/E1/`):

| Input | From | Use in E6 |
|---|---|---|
| Verified `ΛCDM` chain + `χ²` per probe block | E1-A | null reference for ΔBIC/evidence and the OOS baseline |
| Verified `w₀w_aCDM` chain + contours | E1-A | the dynamical-DE competitor; the `IDE_w0wa` cross-link background |
| Fitted `Ξ_cosmo` amplitudes `(a₀, a₁, a₂)` + posterior | E1-B | the **coherence-locked** `Ξ` whose `a₁` sets the *allowed* growth amplitude for the reducibility test |
| `fσ₈`/`S₈` SBT predictions via `K_G`/`K_S` | E5 | the `Ξ`-implied growth signature E6 compares against the IDE growth signature |

> **Coherence lock (LOCKED, `plan/04` §3.3/§9.4; `plan/00-overview` §6.4).** The `a₁` (staging
> amplitude) used in E6's reducibility test is **not refit freely**; it is inherited (within the
> joint-fit posterior) from E1/E5 so that the same `Ξ` is being tested across charts. E6 is allowed to
> refit `(a₀, a₂)` for the background-equivalence leg (those are the geometry charts), but `a₁` carries
> the growth content and must stay coherence-consistent or the program fails the phase (§6.4 fail rule).

### 2.3 Models fitted (the competition set for E6)

| Model key | Description | Free params beyond ΛCDM | Stage |
|---|---|---|---|
| `LCDM` | flat ΛCDM (null) | 0 | reference (from E1) |
| `w0wa` | CPL dynamical DE | 2 (`w₀, w_a`) | competitor (from E1) |
| `IDE_xiDE` | standard IDE, `Q = ξ H ρ_de` | 1–2 (`ξ`, `w_de`) | **E6-A** |
| `SIDE` | sign-switching IDE | 2 (`ξ`, `z_switch`) | **E6-A** |
| `SBT_Xi` | ΛCDM + `R[Ξ_cosmo]`, rank ≤ 3 (`a₀, a₁, a₂`), `a₁` coherence-locked | ≤ 3 | **E6-B/E6-C** |

---

## 3. Method (pipeline)

The pipeline is `cobaya + CLASS` for background/CMB/BAO/SN/CC and `pyccl` for the growth/3×2pt
predictions (reusing the E5 CCL backend), with all runs producing a run-manifest JSON
(`GROUNDING_BRIEF` §III.B) and seeds fixed (`GROUNDING_BRIEF` §III.A: numpy/random/sampler seeds
recorded; float64 throughout, §III.D).

### 3.1 E6-A — IDE reproduction (the baseline gate) `[E]`

**A1.** Implement the IDE background in CLASS via a custom dark-sector module (or the published IDE
patch per `plan/02`): solve (E6-1a)–(E6-1b) for `IDE_xiDE`, `IDE_xiDM`, `SIDE` with the chosen `Q`
form; verify total conservation (E6-2) to machine precision as a sanity audit.

**A2.** Fit each IDE model on `Planck 2018 + DESI DR2 BAO + CC + SN` (the 2504.00994 / 2503.23225
combination) with cobaya MCMC. Record: posterior on `ξ` (and `z_switch` for S-IDE), `H₀`, `S₈`,
`σ₈`, `Ωm`, the `H(z)` posterior band, the full `Q(z)` posterior, and per-probe `χ²`.

**A3.** Reproduce the published numbers within tolerance (G-E6-REPRO, §9.2): mild coupling preference
(`ξ` consistent with the 2503.23225/2504.00994 posteriors), `H₀`-tension reduced toward ≈2.7σ, S-IDE
`S₈` lowered. Convergence `R̂ < 1.01`, ESS > 400/chain.

**A4.** Compute the **fitted effective `Q(z)`** along the chain: `Q_IDE(z) = ξ H(z) ρ_de(z)` (or the
model's form), with its posterior band. This is the *target* the `Ξ`-chart must reproduce.

### 3.2 E6-B — Background equivalence via the chart map `[E]`/`[T]`

**B1.** Construct the chart map (E6-4)/(E6-5): from the E6-A posterior-mean IDE background, compute
`ΔρQ(z) = ρ_de^eff(z) − ρ_Λ` and the implied `Q_IDE(z)`.

**B2.** Fit `R[Ξ_cosmo]` (rank ≤ 3, `a₁` coherence-locked per §2.2) to reproduce the IDE background
on the *same* probes (Planck + DESI BAO + CC + SN), targeting equality of `H(z)`, `D_M/r_d`,
`D_H/r_d`, `μ(z)`, and the effective `Q(z)` (via E6-5). The fit minimizes the route-mismatch /
adequacy functional of `plan/04` §4 in the audit metric `d` (eq. 10).

**B3.** Compute the **background chart defect** (G-E6-BG, §9.3):

```
Δ_bg(Q, Ξ) := RMS_z  d( {H, D_M/r_d, D_H/r_d, μ, Q}^{IDE}(z) ,  {…}^{SBT_Xi}(z) )                  (E6-6)
```

normalized by the data error in each channel (whitened by the published covariance). Background
equivalence passes iff `Δ_bg` is within the **background-degeneracy band** (the spread already present
between `LCDM`, `w0wa`, and `IDE` at fixed `χ²`), quantitatively `Q`-vs-`Q_Ξ` RMS ≤ **20%** of the `Q`
posterior amplitude (the §6.3 E6 headline number) and `H(z)` agreement within the CC error bars.

**B4.** Record the **span defect** explicitly: the fraction of `ΔρQ(z)` *outside* the ansatz span
`𝒜` (the residual after projecting onto `{φ₀, φ₁ψ₁s_p, φ₂c_p}`). If this is small, `Q` is a clean
chart of `Ξ`; if large, `Q` carries background structure `Ξ` cannot reach (a finding, §1.1 anti-fudge
note) — statused, not patched.

**B5.** Lean witness target (T-E6, `[T]`, §7): the finite statement that `Q_Ξ` defined by (E6-5)
inserted into (E6-1a)–(E6-1b) reproduces the *same* `ρ_de^eff(z)` on the sampled grid (chart-map
soundness / exactness on the finite grid).

### 3.3 E6-C — Growth-split decision (the centerpiece) `[E]`

This is where the reality of `Q` is decided (`idea.md` §6 Exp 6). Three sub-audits.

**C1 — Growth-signature comparison.** With the *background-matched* IDE and `Ξ` from E6-B (so they
agree on geometry by construction), compute and compare the **growth** observables:

- IDE growth: solve the IDE-modified linear growth equation (the `Q`-modified `δ_m` source) for
  `fσ₈^IDE(z)` and `S₈^IDE`; for S-IDE include the `S₈`-lowering effect (2503.23225).
- `Ξ` growth: `fσ₈^Ξ(z) = (fσ₈)^GR + K_G[Ξ]` (eq. 8) and `S₈^Ξ = S₈^GR + K_S[Ξ]` (eq. 9), with the
  **coherence-locked `a₁`** (§2.2) — `Ξ` is *not* allowed to refit `a₁` to chase the IDE growth.
- Compare both against the DESI DR2 (compressed) `fσ₈(z)` and the DES Y6 / KiDS-Legacy `S₈`.

**The reducibility test (LOCKED, §1.2):**

```
reducible  ⟺  d( fσ₈^data , fσ₈^Ξ )  ≈  d( fσ₈^data , fσ₈^IDE )   AND   |S₈^Ξ − S₈^data| ≈ |S₈^IDE − S₈^data|
              at the coherence-locked a₁ (within the program 10× coherence band, plan/04 §9.4)         (E6-7)

interaction indicated  ⟺  fσ₈^IDE fits the growth data significantly better than fσ₈^Ξ can at the
                          coherence-locked a₁, i.e. Δχ²_growth(Ξ→IDE) exceeds the §9 threshold        (E6-8)
```

**C2 — Modified-gravity cross-check `(μ₀, Σ₀)`.** A *real* dark-sector interaction generically
imprints a nonzero effective `(μ₀, Σ₀)` deviation in the DESI (DR1) full-shape MG analysis (the same
phenomenological window E7 uses). Compute `(μ₀, Σ₀)^IDE` and `(μ₀, Σ₀)^Ξ`. The E6 headline
sub-gate (§6.3, `plan/00-overview` E6): `|μ_SBT − μ_GR| < |μ_IDE − μ_GR|` — i.e. the closure chart
should *not* require a larger gravity-sector deviation than IDE does. (If both require the *same*
`(μ, Σ)` deviation, that is the E6 failure direction in §6.3: `Q` and `Ξ` are not distinguishable and
neither resolves the growth chart — statused `moduli`.)

**C3 — Leave-one-probe-out PPD (the `PPD_{p→q}` residual; `plan/04` §4).** The cross-probe audit, in
the `Six_Birds_for_Neutrino_Mass` directional held-out-`δχ` style:

| Split | Train on | Predict | Decision content |
|---|---|---|---|
| S1 | BAO + CMB + CC (geometry) | `fσ₈` (growth) | does background-fixed `Ξ`/IDE predict growth? |
| S2 | SN + BAO (geometry) | `S₈` (WL) | geometry→amplitude transfer |
| S3 | growth (`fσ₈`, `S₈`) | geometry (`D_M/r_d`) | reverse direction (the IDE growth content should *help* here iff real) |

For each split compute the held-out whitened `δχ²` (eq. 10) for `SBT_Xi` vs `IDE` vs `LCDM`/`w0wa`.
The E6 headline reducibility/comparability gate (§6.3): **SBT RSD reducible to IDE within 10%** (comparability — NOT a std-3 OOS win; the program OOS win is decided only at E8). If `Ξ` predicts the held-out
growth as well as IDE *with fewer/equal effective parameters and the coherence-locked `a₁`*, the IDE
coupling adds no out-of-sample predictive content ⇒ accounting shadow.

**C4 — Adequacy residual (the decision functional, `Adequacy_Residuals`).** Compute
`Ξ_C(Q | Ξ)` (the Schur complement, §1.3) on the **growth-augmented** currency block. Report its
value and, if nonzero, the blind-spot recombination witness (the growth direction `Q` reaches that
`Ξ` does not). This is the single scalar that summarizes "what `Q` measures beyond `Ξ`."

### 3.4 Determinism, provenance, audit gates (mandatory)

- Seeds: numpy/random/sampler seeds fixed and recorded (`GROUNDING_BRIEF` §III.A). float64 throughout
  (§III.D). Re-run identical seed ⇒ likelihood/forward-model bitwise + committed summaries to tolerance; chains validated by statistical equivalence (`R̂<1.01`, ESS), not bitwise.
- Run manifest JSON per run (`GROUNDING_BRIEF` §III.B; `plan/01` schema): `run_id`, datasets +
  versions (incl. `2503.23225`, `2504.00994` reference numbers used for the reproduction gate), software
  versions, model key, seeds, `audit_status`.
- Pre-inference: dump `H(z)`, `Q(z)`, distances, `fσ₈(z)` predictions to FITS/HDF5 for inspection
  (`GROUNDING_BRIEF` §III.C).
- Post-MCMC: `R̂`, ESS/N_eff, KL to the literature posteriors (2503.23225/2504.00994), per-block `χ²`
  summary table (`GROUNDING_BRIEF` §VI(2)–(4)). Covariance sanity: PD, condition number `< 10⁸`,
  finite (§VI(1)).

---

## 4. Outputs (artifacts the implementation must produce)

All under `results/E6/` with a committed `summary.json` recording every gate verdict.

| Artifact | Path | Content |
|---|---|---|
| IDE baseline chains + contours | `results/E6/E6A_ide_chains.hdf5`, `E6A_contours.png` | `IDE_xiDE`, `SIDE` posteriors: `ξ`, `H₀`, `S₈`, `Q(z)` band |
| Reproduction table | `results/E6/E6A_repro_table.csv` | recovered vs published (2503.23225 / 2504.00994) `ξ`, `H₀`-tension σ, `S₈`; pass flags |
| Chart map + background-equivalence | `results/E6/E6B_chartmap.hdf5`, `E6B_bg_overlay.png` | `Q_IDE(z)` vs `Q_Ξ(z)`; `H(z)`, distances overlay incl. CC points; `Δ_bg` (eq. E6-6); span defect (B4) |
| Growth-split decision | `results/E6/E6C_growth.csv`, `E6C_fsigma8.png`, `E6C_S8.png` | `fσ₈^IDE`/`fσ₈^Ξ`/data; `S₈` comparison; reducibility verdict (E6-7/E6-8); `(μ₀,Σ₀)` (C2) |
| PPD held-out ledger | `results/E6/E6C_ppd.csv` | per-split held-out `δχ²` for `SBT_Xi`/`IDE`/`LCDM`/`w0wa` (S1–S3) |
| Adequacy residual | `results/E6/E6C_adequacy.json` | `Ξ_C(Q | Ξ)` value + blind-spot witness (C4) |
| AOR status table entry | appended to `results/aor_status_table.csv` | the typed E6 verdict + residuals (§6) |
| Run manifests | `results/E6/manifests/*.json` | one per run (§3.4) |
| Lean witness | `lean/SbtCosmo/IdeChartMap.lean` (target T-E6) | chart-map soundness on the finite grid (§7) |

---

## 5. The decision tree (what each outcome means)

```
E6-A passes (IDE reproduced)?  ──no──►  G-E6-REPRO FAIL: cannot proceed; pipeline/likelihood bug; status blocked
        │ yes
        ▼
E6-B: Δ_bg within degeneracy band AND span defect small?
        │ no (Ξ cannot reach the IDE background within 𝒜)
        ▼  ──►  FINDING: Q carries background structure outside the rank-3 ansatz.
        │        Status: out_of_scope for the pure-chart claim; the background chart is incomplete.
        │        (This is an honest negative for the "one residual" thesis at the background level.)
        │ yes (background equivalence holds — Q is a background chart of Ξ)
        ▼
E6-C: growth/PPD reducibility (E6-7) vs interaction-indicated (E6-8)?
        ├─ reducible (E6-7), |μ_SBT−μ_GR| < |μ_IDE−μ_GR|, OOS within 10%, Ξ_C(Q|Ξ)≈0
        │     ──►  VERDICT A: Q is an accounting shadow of Ξ. Status: bridged.
        │           The IDE "hint of coupling" is an overread of the background ledger (F11).
        ├─ interaction indicated (E6-8): IDE fits growth significantly better than coherence-locked Ξ,
        │  or Ξ_C(Q|Ξ) ≠ 0 with a growth blind-spot witness
        │     ──►  VERDICT B: a real interaction is indicated here. Status: out_of_scope / approved_other.
        │           IDE is the better repair chart for this dataset (F2 alternative repair). Reported with numbers.
        └─ undecidable at current precision (overlapping growth predictions within errors)
              ──►  VERDICT C: chart-equivalent at current data. Status: moduli / budgeted.
                    The flat direction (ξ ↔ a₁) is the residual; precision/forecast budgeted.
```

> **Note (LOCKED).** Verdict A is the program's preferred-but-not-assumed outcome; B and C are equally
> publishable and are *not* failures of E6 (they are findings). E6 **fails** only on the discipline
> gates (§6, §9.5): if `Ξ` is allowed to refit `a₁` to chase IDE growth (coherence violation), if the
> reproduction gate is skipped, or if any residual is left unstatused (F9).

---

## 6. AOR statusing of the E6 residual (`plan/04` §8; `idea.md` §6 Exp6; §10)

Every E6 leftover carries **exactly one** AOR base status (F9 No Unstatused Residual). The LOCKED
mapping:

| E6 outcome / residual | AOR status | Residual type (`plan/04` §8.2) | Payload `π` |
|---|---|---|---|
| Verdict A: `Q` reducible to `Ξ` (growth + PPD + adequacy agree) | `bridged` | `D_descent` (accounting chart bridged to the rewrite) | the explicit chart map (E6-4/E6-5) + `Δ_bg` + `Ξ_C(Q|Ξ)≈0` |
| Verdict B: real interaction indicated (growth demands it) | `out_of_scope` (for the pure-chart claim) / `approved_other` (IDE is the better repair) | `D_descent` (descent demands the dark-sector source) | the growth `Δχ²` + blind-spot witness + the `(μ,Σ)` evidence |
| Verdict C: undecidable at current precision | `moduli` (the `ξ ↔ a₁` flat direction) / `budgeted` (precision) | `D_limit` / `D_horizon` | the flat-direction record + the forecast precision needed to decide |
| Background span defect (B4) nonzero | `out_of_scope` (background chart incomplete) | `D_descent` | the out-of-span fraction of `ΔρQ(z)` |
| CC leg dropped (fallback) | `out_of_scope` | (logged) | the CC-anchored sub-claim withheld |
| Any compressed-likelihood fallback used | `budgeted` | (logged) | the compression budget |
| 2510.12627 extra-parameter counterfactual | `budgeted` (extra ledger freedom) | `D_descent` | the `H₀` bought by the extra dynamical-Λ parameter, separately accounted |

> **The "no new force claimed by default" disclaimer (LOCKED, mirrors `A_Six_Birds_Eye_View_of_Dark_Energy`
> and E3 §1.4).** E6 does **not** claim "there is no interacting dark sector." It claims the *background*
> evidence for `Q` is chart-equivalent to `Ξ`, and reports whether the *growth* sector demands a real
> coupling. A fundamental dark-sector interaction is **not ruled out**; if the growth audit demands it
> (Verdict B), E6 says so. This is the F11 No-Overread discipline, not a negative ontological claim.

---

## 7. Lean anchor — `SbtCosmo.IdeChartMap` (TARGET T-E6, `[T]`)

> **Statement (finite, theorem-grade).** Let `R[Ξ]` be the rank-≤3 rewrite (eq. 5) on the sampled
> redshift grid `{z_k}`, and let `Q_Ξ` be defined by the discretized continuity-equation chart (E6-5).
> Then inserting `Q_Ξ` into the discretized IDE continuity equations (E6-1a)–(E6-1b) reproduces the
> **same** effective dark-energy density `ρ_de^eff(z_k)` (within the finite-difference tolerance) that
> `R[Ξ]` defines via (E6-4). I.e. *the continuity-equation chart of the rewrite is exact on the finite
> grid* — `Q` and `Ξ` are two presentations of one background object.

- **Feasibility:** **Full finite proof feasible** (verified computation on the sampled grid; matches
  the `plan/05-lean-mechanization.md` verified-computation convention). The map (E6-5) is linear in
  `(a₀, a₁, a₂)` (kernel linearity, `plan/04` §3.2), so the chart is an exact algebraic identity at
  the discretization order; the Lean target certifies the identity + the linearity (finite-difference
  consistency to `< 1%`, the kernel-linearity gate of `plan/04` §"Kernel linearity").
- **Anchors reused:** F2 *Descent-Repair Normal Form* (the two repairs are charts of one repair class);
  `To_Spend_a_Stone` (currency–constraint duality — `ξ` as shadow price). The residual obligation (the
  *growth* distinguishability) is **not** a theorem; it is the empirical E6-C decision and is explicitly
  statused (F9), never proved.

> **Scope discipline (LOCKED).** The Lean theorem certifies only the **background** chart-map
> soundness. It does **not** prove `Q` is unnecessary; the reality of the interaction is the empirical
> growth-split decision (§3.3) and carries an AOR status (§6), per the corpus pattern that conditional
> claims are recognition-grade `[C]`/empirical `[E]`, not `[T]`.

---

## 8. Pass / fail gates (quantitative, pre-registered)

> **All thresholds are pre-registered** (`plan/00-overview` §6): they may not be relaxed after seeing
> results; a relaxation must be logged as a statused deviation (`budgeted`). Units are χ²/dof, ΔBIC,
> whitened distances `d` (eq. 10), percentage RMS, and nats. `[E]` = decided by data; `[T]` = decided
> by verified computation.

### 8.1 Data / metric gates (must hold for all legs)

| Gate | Threshold | Source |
|---|---|---|
| `G-E6-COV` | every probe covariance PD; condition number `< 10⁸`; all entries finite | `GROUNDING_BRIEF` §VI(1) |
| `G-E6-CONV` | Gelman–Rubin `R̂ < 1.01` on all sampled params; ESS > 400/chain | `GROUNDING_BRIEF` §III.C, §VI(2) |
| `G-E6-DET` | identical seed ⇒ likelihood/forward-model bitwise + committed summaries to tolerance; chains by statistical equivalence (`R̂<1.01`, ESS, means/cov within MC error), not bitwise; manifest recorded | `GROUNDING_BRIEF` §III.A/B |
| `G-E6-CONS` | IDE total-continuity (E6-2) conserved to machine precision in the CLASS module | §3.1 A1 |

### 8.2 Reproduction gate (`G-E6-REPRO-*`, must pass before E6-B/E6-C) `[E]`

| Gate | Pass condition | Fail condition |
|---|---|---|
| `G-E6-REPRO-XI` | recovered IDE coupling posterior on `ξ` agrees with 2503.23225 / 2504.00994 within **1σ** (mild preference: `ξ` consistent with the published >1σ, within-2σ hint) | recovered `ξ` posterior inconsistent with published at **>2σ** |
| `G-E6-REPRO-H0` | reproduced `H₀`-tension reduction toward **≈2.7σ** (standard IDE) within ±0.3σ; S-IDE lowers `S₈` in the published direction | tension reduction not reproduced (off by >0.5σ) or S-IDE `S₈` moves the wrong way |
| `G-E6-REPRO-CHI2` | per-block `χ²` within **5%** of the published reference; ΛCDM/`w0wa` baselines match E1 | `χ²` off by >5%; baselines disagree with E1 |

### 8.3 Background-equivalence gate (`G-E6-BG-*`, the chart map) `[E]`/`[T]`

| Gate | Pass condition | Fail condition |
|---|---|---|
| `G-E6-BG-Q` (headline) | `Q_Ξ(z)` matches the fitted `Q_IDE(z)` to RMS **≤ 20%** of the `Q` posterior amplitude over the sampled `z` range | `Q` discrepancy **> 30%** (background not reproduced by `Ξ` within `𝒜`) |
| `G-E6-BG-HZ` | `H(z)` agreement within the CC error bars at every CC point; distances (`D_M/r_d`, `D_H/r_d`, `μ`) within DESI/SN whitened `d ≤ 1`/dof | `H(z)` outside CC errors or distances `d > 1`/dof |
| `G-E6-BG-SPAN` | out-of-span fraction of `ΔρQ(z)` (B4) **< 20%** (clean chart) | out-of-span fraction **> 50%** ⇒ `Q` carries background structure outside `𝒜` (FINDING, status `out_of_scope`) |
| `G-E6-BG-LEAN` `[T]` | T-E6 verified: continuity-chart (E6-5) reproduces `ρ_de^eff` on the grid; kernel linearity `< 1%` | chart-map identity fails the finite-difference tolerance |

### 8.4 Growth-split decision gates (`G-E6-GROWTH-*`, `G-E6-PPD-*`, the centerpiece) `[E]`

| Gate | Pass condition (one of the three verdicts) | Notes |
|---|---|---|
| `G-E6-GROWTH-RED` (Verdict A) | at the **coherence-locked `a₁`**: `Δχ²_growth(Ξ→IDE) ≤ 4` (i.e. `Ξ` fits `fσ₈`/`S₈` *as well as* IDE within ~2σ) **and** `|μ_SBT−μ_GR| < |μ_IDE−μ_GR|` **and** `Ξ_C(Q|Ξ)` consistent with 0 | ⇒ `Q` is an accounting shadow; status `bridged` |
| `G-E6-GROWTH-INT` (Verdict B) | IDE fits growth significantly better than the coherence-locked `Ξ`: `Δχ²_growth(Ξ→IDE) ≥ 9` (≈3σ) **or** `Ξ_C(Q|Ξ)` nonzero with a growth blind-spot witness above its noise floor | ⇒ real interaction indicated; status `out_of_scope`/`approved_other` |
| `G-E6-PPD` (headline reducibility / comparability — NOT a std-3 OOS win) | **SBT RSD held-out `δχ²` within 10% of IDE** on split S1 (geometry→growth); and within 15% on S2/S3 | OOS **> 15% worse** ⇒ headline fail (E6 §6.3) |
| `G-E6-MUSIGMA` (headline) | `|μ_SBT − μ_GR| < |μ_IDE − μ_GR|` (closure chart needs no larger gravity-sector deviation than IDE) | **same** `(μ,Σ)` deviation in both ⇒ headline fail / Verdict C undecidable |
| `G-E6-COH` (program coherence) | the `a₁` used here is within the **10× cross-amplitude band** and consistent sign with E1/E5 (`plan/04` §9.4) | violation ⇒ **whole program fails the phase** (`plan/00-overview` §6.4 fail rule) |

### 8.5 SBT-claim / discipline gates (the five hard standards, `plan/00-overview` §6.2)

| Gate | Pass condition | Maps to standard |
|---|---|---|
| `G-E6-RANK` | the `Ξ` used in E6 has **≤ 3** free params; **no** IDE-specific free `Ξ_p`; `a₁` not refit to chase growth | std 2 (one low-rank residual) |
| `G-E6-OOS` | `G-E6-PPD` met (reducibility: SBT RSD within 10%/15% of IDE) and improves the ΛCDM OOS baseline on ≥1 split | reducibility / comparability — NOT std-3 (the strict program-level OOS win is decided only at E8 `G-E8-OOS-DECISIVE`) |
| `G-E6-NOFUDGE` | reproducing the IDE background did **not** require shapes outside `𝒜`; any extension logged (B4/G-E6-BG-SPAN) | std 2 / anti-fudge (§1.1) |
| `G-E6-STATUS` | every residual + the verdict carries exactly one AOR base status (§6); none `unstatused` | std 5 / F9 |
| `G-E6-FAILREPORT` | the §8.6 pre-registered failure modes are all checked and reported with numbers | std 5 |

### 8.6 Pre-registered failure modes (honored and reported with numbers)

E6 (the **chart-equivalence thesis**) is rejected, or the verdict is forced, if:

1. **Background not reproducible by `Ξ` within `𝒜`** (`G-E6-BG-Q` > 30%, or `G-E6-BG-SPAN` > 50%):
   the IDE background carries structure the rank-3 closure residual cannot reach ⇒ the "one residual,
   IDE chart" thesis fails *at the background level*. Status `out_of_scope`; reported, not patched.
2. **Coherence violation** (`G-E6-COH` fails): the only way `Ξ` matched IDE growth was by refitting
   `a₁` outside the 10× band ⇒ this is **not** the same residual as E1/E5 ⇒ the whole program fails the
   phase (`plan/00-overview` §6.4). This is the cleanest E6 self-falsification.
3. **Reproduction gate skipped or failed** (`G-E6-REPRO-*`): no `Ξ` result may be reported (the
   IDE baseline is not established). Status `blocked`.
4. **Interaction genuinely demanded** (`G-E6-GROWTH-INT` triggers): this is **not** a failure of the
   *program* (it is a finding), but it **is** a falsification of the "accounting shadow" reading *for
   this dataset* — Verdict B, status `out_of_scope`/`approved_other`, reported with the growth `Δχ²`.
5. **Undecidable** (`G-E6-MUSIGMA` shows the same `(μ,Σ)` deviation in both; growth predictions overlap
   within errors): Verdict C, status `moduli`/`budgeted`; the `ξ ↔ a₁` flat direction is the residual,
   and the forecast precision needed to break it is reported.

> **Symmetry of evidence (LOCKED, mirrors E3 §9.6).** A `G-E6-GROWTH-INT` trigger (real interaction
> indicated) must be reported with the growth `Δχ²` and the blind-spot witness numbers, **not hidden**.
> E6 is adversarial in both directions: it can confirm `Q` is a shadow (Verdict A) *or* find that the
> data demand a real coupling (Verdict B). Suppressing either outcome violates `G-E6-FAILREPORT`.

---

## 9. Dependencies, blocking, and links

### 9.1 Blocked by (prerequisites)

- **E1** (`plan/experiments/E1-desi-dr2-reproduction.md`): the verified `ΛCDM`/`w₀w_a` baselines and
  the coherence-locked fitted `Ξ` `(a₀, a₁, a₂)` — E6 consumes these as fixed inputs (§2.2). E6-A
  cannot be scored until E1-A reproduction gates are green.
- **E5** (`plan/experiments/E5-growth-staging-S8.md`): the physical CCL growth backend (`pyccl`) and
  the `K_G`/`K_S` growth predictions of the coherence-locked `Ξ` — E6-C reuses both for the growth
  comparison and the coherence band.
- **`plan/04-formal-foundations.md`**: the carrier + four residuals (§4), the ansatz (§3.1), the
  rewrite + kernels (§3.2–3.3), the metric `d` (§4.0), the AOR status atlas (§8).
- **`plan/03-data-acquisition.md`**: `PLANCK_2018`, `DESI_DR2_BAO`, `CC_HZ`, `PANTHEON_PLUS`/`UNION3`,
  `DESI_RSD_FS`, `DES_Y6`/`KIDS_LEGACY` loaders + fallbacks.
- **`plan/02-environment-and-deps.md`**: cobaya/CLASS (+ IDE dark-sector module) and `pyccl` install
  + version pins; the pyccl↔CLASS agreement gate.
- **`plan/01-repo-structure.md`** + **`plan/05-lean-mechanization.md`**: run layout, manifest schema,
  gate verifier (`tests/test_gates.py`), and the `SbtCosmo.IdeChartMap` Lean target conventions.

### 9.2 Blocks (what E6 unblocks)

- **E8** (model-competition synthesis, `plan/00-overview` §4 E8 / §6.3 E8): E6 produces the **IDE row**
  of the competition matrix (verified `ξ`/evidence/`H(z)`/`fσ₈`), the `Q↔Ξ` chart map, the growth-split
  verdict, and the chart-defect ledger that E8 ranks alongside ΛCDM/`w₀w_a`/CDDR/MG/SBT.
- **E7** (MG-as-repair, `plan/experiments/E7-*.md`): E6 and E7 are the paired "alternative repair chart"
  experiments (`idea.md` §7; F2). E6's `(μ₀, Σ₀)` cross-check (C2) feeds the E7 MG comparison, and the
  two together populate the F2 descent-repair classification (IDE-`Q` vs MG-`(μ,Σ)` vs SBT-`Ξ`).

### 9.3 Science / corpus source map (for the executor)

- **`idea.md` §6 Experiment 6** — the charter, the chart-map claim, and the exact pass criterion
  (background reproduced by `Ξ`; growth/probe-split decides the reality of `Q`).
- **`idea.md` §3 shadow map row 8 / §7 / §9** — "IDE → P6 accounting shadow"; "`Q` is the
  continuity-equation chart"; the mixed live-evidence picture (2503.23225 / 2504.00994 / 2510.12627 /
  2601.02789).
- **`A_Six_Birds_Eye_View_of_Dark_Energy`** §framework (P6 accounting role) + the Toy-2 `Q(t)`
  closure-term proxy and its "this is a closure diagnostic, not the GR backreaction term" disclaimer —
  the seed E6 generalizes from a toy proxy to the fitted IDE `Q`.
- **`To_Spend_a_Stone`** — currency–constraint duality / shadow prices: the formal backbone for "`ξ`
  is a shadow price of `Ξ`'s closure constraint, not a coupling of a new dark force."
- **`Foundations_IV`** — F11 *Adequacy / No-Overread* (the no-overread of `Q` as a force), F9 *No
  Unstatused Residual*, F2 *Descent-Repair Normal Form* (IDE-`Q` and `Ξ` as alternative repairs).
- **`Adequacy_Residuals`** — the Schur-complement `Ξ_C(Q | Ξ)` decision functional (C4) and the
  blind-spot witness.
- **`Six_Birds_for_Neutrino_Mass`** — the directional held-out `δχ` cross-lens audit template reused
  in the E6-C PPD splits.
- **`Audited_Operational_Realisability`** — the AOR status vocabulary and the carrier-record reading
  of the E6 verdict.
