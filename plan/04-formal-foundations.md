# 04 — Formal Foundations: The Complete Mathematical Specification

> **Read order.** This file is the mathematical contract the whole implementation builds on.
> Read `plan/00-overview.md` first (thesis, scope, gates, definition of done) and
> `GROUNDING_BRIEF.md` (datasets, stack, AOR vocabulary). This file *locks* every formal
> object those files reference: the `Ξ_cosmo` reconciliation, the carrier, the four residuals and
> their metric `d`, the low-rank ansatz and observable kernels `K_L/K_M/K_G/K_S`, the four
> propositions P1–P4 with proof strategies and Foundations-IV grounding, and the Hubble readout
> field `H_{r,ℓ}` / Hubble holonomy `𝔥_γ` / lawful-plurality test set.
>
> **Scope of THIS file:** *the math only.* It defines symbols, equations, finite operational
> recipes, and the proof skeletons. It does **not** specify repository layout (that is
> `plan/01-repo-structure.md`), environment/versions (`plan/02-environment-and-deps.md`), nor the
> per-experiment pipelines (`plan/experiments/E#.md`). Where an object maps to a code module or a
> Lean file, the mapping is named so the executor can wire it, but the implementation is elsewhere.
>
> **Source of truth for the science:** `idea.md`, especially §1 (closure package), §3 (shadow map),
> §4 (carrier + four residuals + `Δ_SBT`), §5 (minimal ansatz + kernels), §6 (experiments), §10
> (five hard standards), and the post-§10 **UPDATE** block (Hubble readout field, holonomy, route
> matrix, lawful plurality). Corpus anchors are cited inline by short name and label.
>
> **Grade convention.** Every named result below is tagged with a *grade*:
> - **`[T]` theorem-grade** — provable now in Lean 4 (≥ v4.28.0) or by a finite verified computation,
>   reusing a corpus anchor. These are obligations, not aspirations.
> - **`[C]` conditional / recognition-grade** — holds *under a named structural hypothesis* (e.g.
>   the SB closure assumption, a declared bridge, a fitted-ansatz adequacy claim). The hypothesis is
>   stated explicitly and the result is recorded at recognition grade per the corpus discipline
>   (INDEX "Notes": `accepted` vs `recognition`/`model_realization`).
> - **`[E]` empirical / data-conditional** — a claim whose truth value is decided by an experiment's
>   pass/fail gate (§9), not by proof.

---

## 0. Notation and standing conventions

| Symbol | Meaning | Fixed in |
|---|---|---|
| `X` | underlying cosmological world-state space (micro/inhomogeneous) | §1 |
| `T : X → X` | one-step deterministic evolution (micro dynamics) | §1 |
| `P` | probe set `{CMB, BAO, SN, WL, RSD, ladder}` | §1 |
| `f_p : X → O_p` | probe lens for `p ∈ P` (information-losing coarse-graining) | §1 |
| `U_θ : O_p → X̂` | homogeneous FLRW completion with parameters `θ` | §1 |
| `E_{θ,p} := U_θ ∘ f_p` | packaging operator (per-probe) | §1 |
| `T_θ : X̂ → X̂` | FLRW macro evolution induced by `θ` | §1 |
| `Ξ_cosmo(z,ℓ,p)` | cosmological closure residual (the named object) | §2, §3 |
| `R[Ξ]` | the operator *rewrite* induced by `Ξ` (the repair) | §3, P1 |
| `Δ_SBT` | least audit-closed rewrite (the variational definition of `Ξ_cosmo`) | §2 |
| `δ_p, RM_p, LG_{p,q}, PPD_{p→q}` | the four residuals | §4 |
| `d` | response-space (pseudo)metric used by all four residuals | §4.0 |
| `K_L, K_M, K_G, K_S` | observable-correction kernels (SN, BAO, growth, WL) | §3.3 |
| `K_{r,ℓ}` | Hubble-route observable kernel | §5 |
| `H_{r,ℓ}(z)`, `H₀^{(r,ℓ)}` | Hubble readout field and its `z=0` value | §5 |
| `𝔥_γ` | Hubble holonomy around route loop `γ` | §5 |
| `Ξ_C(D∣L)` | adequacy residual (Schur complement) — *the reconciliation target* | §1, `Adequacy_Residuals` |
| `Ξ_SB` | AOR eight-stratum structural defect — **distinct object, same Greek letter** | §8, `AOR` |

> **Naming caution (mandatory, from `AOR` def:aor:xi-sb).** Three different objects wear "Ξ":
> (i) `Ξ_cosmo` = the *physical* closure residual / rewrite this program fits;
> (ii) `Ξ_C(D∣L)` = the *Schur-complement adequacy residual* of `Adequacy_Residuals`;
> (iii) `Ξ_SB` = the *AOR eight-stratum structural defect* of `AOR`.
> They are formally disjoint. §1 states the precise relation between (i) and (ii); §8 keeps (iii)
> in its own meta-theoretic lane. Code and Lean must keep these namespaced (`xi.residual` vs the
> adequacy Schur module vs `aor.status`).

All carriers are **finite-dimensional / finite-state** wherever a `[T]` grade is claimed; the
continuum FLRW objects are sampled on finite `z`/`ℓ` grids before any audit metric is computed
(this is what makes the four residuals *finite operational* quantities — §4).

---

## 1. The `Ξ_cosmo` reconciliation (LOCKED)

This is the load-bearing identification of the whole program. It connects three things that
`idea.md` §3–§5 left as separate notations: the **least-rewrite** definition `Δ_SBT` (`idea.md` §4),
the **Schur-complement adequacy residual** `Ξ_C(D∣L)` (`Adequacy_Residuals`, eq. `Ξ_C(D∣L)=K_DD −
K_DL K_LL^† K_LD`), and the **fudge-function critique** ("Six Birds is just adding a flexible
function", `idea.md` §4 final paragraph).

### 1.1 The two definitions of the residual

**Definition (variational / least-rewrite, `idea.md` §4).** `Ξ_cosmo` is realized by the rewrite

```
Δ_SBT = argmin_Δ [ Σ_p RM_p(Δ) + Σ_{p,q} LG_{p,q}(Δ) + Σ_{p,q} PPD_{p→q}(Δ) + λ · complexity(Δ) ]   (1)
```

over the *low-rank ansatz class* `𝒜` of §3.1 (NOT over arbitrary functions). `complexity(Δ)` is the
ℓ₀/ℓ₁ surrogate on the ansatz coefficients (§3.1), and `λ > 0` is the audit-complexity price.

**Definition (algebraic / Schur, `Adequacy_Residuals`).** Fix the cosmological carrier `E` priced by
an audit energy `C = C^* ⪰ 0`. Let

- `L : E → Y_native` = the **native probe family** = the FLRW-completion readouts the standard
  pipeline already has (the `θ`-parameterized FLRW distances/`C_ℓ`/`fσ₈`);
- `D : E → Z_dissolving` = the **dissolving probe family** = the *enriched* readouts available after
  admitting the heterogeneity/staging structure the FLRW lens discards (the joint multi-probe,
  multi-staging vector).

Form the block currencies `K_LL, K_DD, K_DL, K_LD` from `(C, C^†, L, D)` exactly as in
`Adequacy_Residuals` §sec:adequacy-residual. The **cosmological adequacy residual** is the Schur
complement

```
Ξ_C(D ∣ L) = K_DD − K_DL · K_LL^† · K_LD                                                          (2)
```

with the projection identity `Ξ_C(D∣L) = T_D (I − P_L) T_D^*` in energy-scaled coordinates
(`Adequacy_Residuals` §sec:projection), where `P_L` projects onto the energy-scaled native range.
`Ξ_C(D∣L) ⪰ 0` (Loewner) always.

### 1.2 The precise relation (CONDITIONAL, grade `[C]` — per-sector, numerical)

> **`[C]` Reconciliation (Schur ⇒ least-rewrite content) — CONDITIONAL, established per probe sector
> and numerically (REGISTRY §5).** This identification is **not** asserted as an unconditionally proved
> theorem. The identity "audit cost = Schur energy after whitening" is established **per probe sector
> `p`** and verified **numerically** (residual `‖Ξ_C − audit_cost‖` reported, §1.2′ and gate §9.1),
> except where an exact per-sector proof is supplied. `Ξ_C(D∣L)` is the **content** that `Δ_SBT` must
> repair, and `Δ_SBT` is the **minimal-norm rewrite that drives `Ξ_C(D∣L)` to within the declared
> budget**. The three component claims:
>
> 1. **Audit cost = adequacy energy (per-sector, numerical `[C]`).** The combined audit cost
>    `J(Δ) := Σ_p RM_p + Σ LG + Σ PPD` in (1), evaluated on the *residual* observable vector (data minus
>    FLRW(θ) minus `R[Δ]`), is claimed to equal the energy-`C` quadratic form of the residual dissolving
>    readout `(I − P_L) T_D^* v` summed over the audit directions `v`. This equality is **verified
>    sector-by-sector against the explicit `(L_p, D_p, C_p, …)` of §1.2′** and reported as the residual
>    `‖Ξ_C − audit_cost‖` (gate §9.1); it is NOT taken as proved a priori.
> 2. **Zero residual ⇔ exact adequacy.** `Ξ_C(D∣L) = 0` iff the native FLRW family already explains
>    the dissolving family (`Adequacy_Residuals` optimal-residual / exact-adequacy theorem:
>    `∃ A, D₀ = A L₀` on the legal quotient). In that regime `Δ_SBT = 0`: **no dark-energy rewrite is
>    needed** — equivalently, a fundamental Λ (or nothing) suffices. *This is the formal statement of
>    "a cosmological constant is not ruled out"* (`Dark Energy` precursor non-claim). This direction is
>    a restatement of the corpus exact-adequacy equivalence.
> 3. **Minimal rewrite = Loewner-minimal residual carrier.** Among rewrites `Δ ∈ 𝒜` that close the
>    audits to budget, `Δ_SBT` selects the one whose post-rewrite adequacy residual is Loewner-minimal
>    *and* whose complexity is minimal — the two-stage optimum of the adequacy *optimal-residual
>    theorem* composed with the `λ·complexity` tie-break.
>
> **Status discipline (LOCKED).** No file may state this reconciliation as unconditionally proved. The
> claim is recorded at recognition grade `[C]` (numerical/per-sector witness); part (1) carries a
> reported residual `‖Ξ_C − audit_cost‖`. Part (2) is `[T]`-restated from the corpus exact-adequacy
> equivalence; the **composite "audit cost = Schur energy after whitening" identity remains `[C]`.**
> **Lean target:** `SBTCosmo.Adequacy.reconciliation` reuses the adequacy Schur lemmas as opacity-
> guarded anchors (mirrors `Foundations_IV`/`Needle Killer` reuse of `Ξ_C`) for the parts that ARE
> proved (exact-adequacy equivalence, Loewner monotonicity); the per-sector energy identity is carried
> as a **numerical witness**, not a closed proof. Grade `[C]` (per-sector, numerical).

### 1.2′ Per-sector reconciliation data (LOCKED, REGISTRY §5)

For **each** probe sector `p ∈ P = {CMB, BAO, SN, WL, RSD, ladder}` the reconciliation is instantiated
on the concrete tuple below. Each row gives the **native readout `L_p`**, the **dissolving readout
`D_p`**, the **audit energy `C_p`**, the **transport** carrying `D_p` into the energy-scaled coordinates,
the **projection `P_{L_p}`** onto the native range, the **covariance blocks** forming `K_LL/K_DD/K_DL/K_LD`,
and the **residual readout** whose `C_p`-energy is compared to the per-sector audit cost. The per-sector
identity is either proved for that sector or marked `[C]` with the reported residual `‖Ξ_C^{(p)} −
audit_cost_p‖` (gate §9.1).

| Sector `p` | Native `L_p` | Dissolving `D_p` | Audit energy `C_p` | Transport `T_{D_p}` | Projection `P_{L_p}` | Covariance blocks | Residual readout | Per-sector grade |
|---|---|---|---|---|---|---|---|---|
| **SN** | FLRW `D_L^FLRW(z;θ)` on the SN `z`-grid | SN distances enriched by host/staging proxies (LP5) | `Σ_SN^{-1}` (Pantheon+ block, §4.0) | whiten by `C_SN^{1/2}` on the SN `z`-grid | onto range of whitened `D_L^FLRW(·;θ)` columns | `K_LL=L_SN^*C_SN L_SN`, `K_DD=D_SN^*C_SN D_SN`, `K_DL=D_SN^*C_SN L_SN` | `(I−P_{L_SN})T_{D_SN}^* v` = SN distance residual after FLRW + `R[Δ]` | `[C]` numerical |
| **BAO** | FLRW `(D_M/r_d, D_H/r_d)(z;θ)` | BAO geometry enriched by staging/compression variants | `Σ_BAO^{-1}` (DESI block) | whiten by `C_BAO^{1/2}` on the BAO `z`-nodes | onto range of whitened FLRW BAO columns | `K_·` from `(C_BAO, L_BAO, D_BAO)` | BAO `D_M/r_d`, `D_H/r_d` residual readout | `[C]` numerical |
| **CMB** | compressed FLRW `(ℓ_A, R, ω_b)` / `C_ℓ` predictors | enriched early-universe staging readout | `Σ_CMB^{-1}` (compressed-likelihood block) | whiten by `C_CMB^{1/2}` | onto range of whitened compressed FLRW predictors | `K_·` from `(C_CMB, L_CMB, D_CMB)` | compressed-CMB residual readout (`c_CMB=0` for the gluing term) | `[C]` numerical |
| **WL** | GR `S₈^GR(θ)` / shear `C_ℓ^{κκ}` predictors | scale-resolved (`ψ₁(ℓ)`-weighted) staging readout | `Σ_WL^{-1}` (shear block) | whiten by `C_WL^{1/2}`; ℓ-weight by `ψ₁(ℓ)` | onto range of whitened GR WL predictors | `K_·` from `(C_WL, L_WL, D_WL)` | WL amplitude residual readout (term-1/staging dominated) | `[C]` numerical |
| **RSD** | GR `fσ₈^GR(z;θ)` | growth readout enriched by Meszaros-source staging | `Σ_RSD^{-1}` (growth block) | whiten by `C_RSD^{1/2}` on the RSD `z`-nodes | onto range of whitened GR `fσ₈` columns | `K_·` from `(C_RSD, L_RSD, D_RSD)` | `fσ₈` growth residual readout | `[C]` numerical |
| **ladder** | distance-ladder `H₀` predictor (anchor→SN) | route/staging-resolved `H₀^{(r,ℓ)}` readout (§5) | `Σ_ladder^{-1}` (route-posterior covariance) | bridge transport `B_γ` (§5.2) into the ladder frame | onto range of whitened single-`H₀` predictor | `K_·` from `(C_ladder, L_ladder, D_ladder)` | route-matrix residual `(I−P_{L})𝓗_{r,ℓ}` | `[C]` numerical |

> **Reconciliation discipline (per-sector).** For each sector the executor (i) forms `C_p`-whitened
> `L_p, D_p`; (ii) builds the four covariance blocks and the Schur complement `Ξ_C^{(p)}(D_p∣L_p)`
> (eq. 2); (iii) computes the per-sector audit cost from `RM_p`/`LG`/`PPD` on the residual readout;
> (iv) reports `‖Ξ_C^{(p)} − audit_cost_p‖` and tags the sector `[C]` (numerical) unless an exact
> per-sector proof is supplied. The whole-program identity is the per-sector aggregate, recorded at
> grade `[C]`.

### 1.3 Why this defuses the "flexible fudge function" critique (LOCKED)

The critique (`idea.md` §4): *"Six Birds is merely adding a flexible fudge function `Ξ(z,ℓ,p)`."*
The reconciliation answers it with **three independent disciplines**, each a concrete gate (§9):

1. **It is not "any function" — it is a Schur leftover.** `Ξ_C(D∣L)` is *uniquely determined* by the
   native family `L`, the dissolving family `D`, and the audit energy `C` (eq. 2). There is no freedom
   to choose it: it is what the native FLRW family *cannot* explain, computed by a pseudo-inverse, not
   posited. The *only* modeling freedom is the rank-≤(5–7) ansatz `𝒜` for the *repair* `R[Δ]` (§3.1).
2. **It is the least rewrite, not a free one (`λ·complexity`).** Equation (1) penalizes complexity;
   a fudge function that overfits one probe pays `λ·complexity` and loses to `Δ_SBT = 0` unless it
   *simultaneously* lowers `RM`, `LG`, and `PPD`. This is enforced by the **coherence gate** (§9,
   `idea.md` §5 key rule): *the same `Ξ` must improve geometry, growth, AND calibration*.
3. **It must win out-of-sample (`PPD`).** A fudge function can always lower in-sample residuals; the
   `PPD_{p→q}` term (§4.4) measures *held-out* cross-probe prediction. A genuine closure residual
   improves held-out prediction; a fudge does not. This is `idea.md` §10 standard 3.

> **The headline (LOCKED).** `Λ`, `w_a`, `Q_IDE`, `η_CDDR`, `μ/Σ`, and `S₈` shifts are *coordinate
> charts* on the single Schur leftover `Ξ_C(D∣L)`, repaired by the single rank-low rewrite `R[Δ_SBT]`
> (`idea.md` §3 closing line). The reconciliation turns "one residual, many shadows" into a *recognition-
> grade `[C]` statement about a Schur complement*, established per probe sector and numerically (§1.2,
> §1.2′; REGISTRY §5) rather than a slogan. It is **not** asserted as an unconditionally proved theorem.

---

## 2. The Cosmological Closure Carrier `𝔉_cosmo` (LOCKED)

Reconstructed and de-garbled from `idea.md` §4 (the source has mangled `========` separators).

> **Definition (Cosmological Closure Carrier).**
> ```
> 𝔉_cosmo = ( X, T, {f_p}_{p∈P}, U_θ, E_{θ,p} = U_θ∘f_p, ℛ, 𝒜 )                                  (3)
> ```
> where
> - `X` — finite-state world-state space (micro substrate, possibly heterogeneous patches);
> - `T : X → X` — deterministic micro evolution;
> - `P = {CMB, BAO, SN, WL, RSD, ladder}` — the six probe lenses;
> - `f_p : X → O_p` — probe lens (coarse-graining onto observable space `O_p`);
> - `U_θ : O_p → X̂` — homogeneous FLRW completion (parameters `θ`); `T_θ : X̂ → X̂` its macro evolution;
> - `E_{θ,p} := U_θ ∘ f_p : X → X̂` — packaging operator (the "fit an FLRW model" map, `Dark Energy`
>   precursor §framework: `Ê = U∘f`, intended idempotent, defines macro objects as fixed points);
> - `ℛ` — the **rewrite registry**: the ansatz class `𝒜` of admissible repairs `R[Δ]` plus the
>   Descent–Repair options — F2's **two** canonical repairs (source refinement / minimal target
>   coarsening) **plus** the cosmology-specific **operator-rewrite** chart that is P1's extension of F2
>   (§6.1);
> - `𝒜` — the **audit system**: the four residual functionals `(δ_p, RM_p, LG_{p,q}, PPD_{p→q})` plus
>   the AOR status ledger (§8).
>
> Code map: `X,T` → `sbt_cosmo.background`/synthetic generators; `f_p` → `sbt_cosmo.probes`;
> `U_θ, T_θ` → `sbt_cosmo.background`; `R[Δ]` → `sbt_cosmo.xi.residual` + `xi.kernels`;
> `(δ,RM,LG,PPD)` → `sbt_cosmo.audits`; status ledger → `sbt_cosmo.aor`.

This carrier is the PreSB carrier of the AOR meta-theory (§8): its records are the observations
(probe vectors), stages (scale cuts / z-bins), constraints (priors / positivity), rewrites (`R[Δ]`),
holonomies (route loops), residuals (the four), nonclaims (e.g. "Λ not ruled out"), and meta-audit
(manifests / seeds / version pins).

---

## 3. The closure residual: ansatz, rewrite, and observable kernels (LOCKED)

### 3.1 The low-rank `Ξ_cosmo` ansatz (`idea.md` §5)

> **Definition (minimal ansatz class `𝒜`).** De-garbled from `idea.md` §5:
> ```
> Ξ_cosmo(z, ℓ, p) = a₀ · φ₀(z)                ← constant-like repair        (Λ-shadow)            (4)
>                  + a₁ · φ₁(z) · ψ₁(ℓ) · s_p   ← staging/scale-dependent     (growth / WL shadow)
>                  + a₂ · φ₂(z) · c_p           ← calibration/gluing residual (SN–BAO / H₀ / CDDR)
> ```
> with **at most 5–7 free parameters total** (`plan/00-overview` §1; ≤ 3 *beyond* ΛCDM in the
> minimal run). The fixed (non-free) ingredients:
>
> | Symbol | Role | Fixed form (default) | Free? |
> |---|---|---|---|
> | `a₀, a₁, a₂` | amplitudes (the 3 core params) | — | **yes** (3) |
> | `φ₀(z)` | constant-like z-shape | `φ₀ ≡ 1` | no |
> | `φ₁(z)` | staging z-shape | `φ₁(z) = z/(1+z)` (CPL-like, activates late) | no |
> | `φ₂(z)` | gluing z-shape | `φ₂(z) = ln(1+z)` (path-length-like) | no |
> | `ψ₁(ℓ)` | scale/staging response | `ψ₁(ℓ) = (ℓ/ℓ₀)^{-β}` smoothing kernel | `β` optional free (4th) |
> | `s_p` | probe staging weight | fixed per-probe constant from `f_p`'s ℓ-support | no |
> | `c_p` | probe calibration weight | `+1` for SN, `−1` for BAO radial, `0` for CMB | no |
>
> **Hard rule (anti-fudge):** `s_p, c_p, φ_i, ψ₁` are **shared across all probes** — they are *not*
> per-probe free functions. Only `(a₀, a₁, a₂[, β])` (and at most 2–3 more if the ansatz is extended
> with a logged justification) are fitted. Any extension of `𝒜` requires a logged deviation
> (`plan/00-overview` §2). This is exactly the rank constraint that the reconciliation (§1.3) needs.

The three terms are read off the shadow map (`plan/00-overview` §3): term 0 is the **constant chart**
(Λ, cc-problem row 1), term 1 is the **staging chart** (S₈/growth row 6, coincidence row 7), term 2
is the **gluing/calibration chart** (CDDR row 4, H₀ row 2).

### 3.2 The rewrite operator `R[Δ]` (LOCKED)

> **Definition.** The rewrite is the additive macro-operator correction
> ```
> ρ_eff(z) = ρ_FLRW(z; θ) + R[Ξ_cosmo](z)                                                          (5)
> ```
> realized as a positive, stable update on the macro state (P4/§7 requires positivity + stability).
> `R[·]` is *linear in the ansatz coefficients* `(a₀,a₁,a₂)` for fixed shapes, which is what makes
> the adequacy reconciliation (§1.2) a rank-extension of the native family.

### 3.3 The four observable-correction kernels (`idea.md` §5) (LOCKED)

De-garbled from `idea.md` §5. Each kernel maps the residual `Ξ` to an additive shift of one
observable; **the same `Ξ` feeds all four** (this is the coherence constraint, enforced as a gate).

> **Definitions (observable kernels).**
> ```
> D_L^obs(z)        = D_L^FLRW(z; θ)        + K_L[Ξ](z)        SN luminosity distance               (6)
> (D_M/r_d)^obs(z)  = (D_M/r_d)^FLRW(z; θ)  + K_M[Ξ](z)        BAO transverse geometry              (7)
> (fσ₈)^obs(z)      = (fσ₈)^GR(z; θ)        + K_G[Ξ](z)        growth (RSD)                          (8)
> S₈^obs            = S₈^GR(θ)              + K_S[Ξ]           weak-lensing amplitude                (9)
> ```
> Explicit (default) forms — each is a **linear functional of `Ξ`** with fixed, probe-shared shapes:
>
> | Kernel | Maps to | Default form | Dominant `Ξ` term |
> |---|---|---|---|
> | `K_L` | SN `D_L(z)` | `∫₀^z Ξ_cosmo(z',·,SN)/H̃(z') dz'` (comoving-distance perturbation) | term 0 + term 2 (`c_SN=+1`) |
> | `K_M` | BAO `D_M/r_d` | same comoving integral, BAO lens/ stage, `c_BAO` weight | term 0 + term 2 (`c_BAO=−1`) |
> | `K_G` | RSD `fσ₈(z)` | `∂_z`-linearized growth response to `R[Ξ]` (Meszaros-source shift) | term 1 (staging) |
> | `K_S` | WL `S₈` | scale-integrated `K_G` over the WL kernel with `ψ₁(ℓ)` weighting | term 1 (staging) |
>
> Hubble kernel `K_{r,ℓ}` (§5) is the **fifth** kernel and reuses the same `Ξ`.
>
> **Key rule (LOCKED, `idea.md` §5):** *the same `Ξ` must improve geometry (`K_L,K_M`), growth
> (`K_G`), and calibration (`K_S`, `K_{r,ℓ}`) predictions.* If each probe needs an unrelated `Ξ_p`,
> Six Birds fails (coherence gate, §9.4). The cross-amplitude tolerance is the make-or-break number:
> the `Ξ` amplitude implied by `K_S` must lie within **10×** of the amplitude implied by `K_L/K_M`,
> with consistent sign (`plan/00-overview` §6.4).

---

## 4. The four residuals: finite operational definitions (LOCKED)

These are the audit functionals `𝒜` of the carrier. All four are **finite, computable from data**,
and share one metric `d`. They are the quantities `Δ_SBT` minimizes (eq. 1) and, via §1, the energy
form of the adequacy residual.

### 4.0 The metric `d` (LOCKED)

> **Definition (audit metric).** On any response/observable space the audit metric is the
> **covariance-whitened (Mahalanobis) pseudometric**
> ```
> d(u, v)² := (u − v)^T · Σ^{-1} · (u − v)                                                         (10)
> ```
> where `Σ` is the published data covariance for that probe block (positive-definite; condition
> number `< 10⁸`, all entries finite — `GROUNDING_BRIEF` §VI(1)). When `Σ` is singular on a legal
> null space, use the Moore–Penrose pseudoinverse `Σ^†` on the legal quotient (matches
> `Adequacy_Residuals` legal-energy quotient `E_C` and the null-mode legality hypothesis; the audit
> energy is `C = Σ^{-1}`). On state space `X` (toy/synthetic, E0) use the same form with a declared
> norm (`Dark Energy` precursor: pseudometrics `d_X, d_O` implemented as residual norms on vectors).
>
> This choice makes every residual a **χ²-type quantity**, so the four-residual sum in (1) is a
> **sector-by-sector numerical comparison target** against the audit energy of §1.2 part (1) — checked
> per probe sector under `G-FORMAL-3` (grade `[C]`, not an exact identity) — and the gates in §9 are
> stated in χ²/dof, ΔBIC, RMSE units.

### 4.1 Idempotence defect `δ_p` (does the closure stabilize?)

> **Definition.** `δ_p := d( E²_{θ,p}, E_{θ,p} )`, i.e. for the sampled state(s) `x`,
> ```
> δ_p(x) = d( E_{θ,p}(E_{θ,p}(x)),  E_{θ,p}(x) )                                                    (11)
> ```
> (`idea.md` §4; `Dark Energy` precursor eq:idempotence_defect: `iddef(x)=d(Ê(Ê x), Ê x)`).
> **Computed from data:** apply the FLRW packaging twice (fit FLRW to the data, then re-package the
> FLRW prediction through the same lens) and measure the whitened distance. **Interpretation:** the
> macro "object" is a fixed point of packaging; `δ_p ≈ 0` means packaging is a genuine projection.
> A nonzero, ℓ-structured `δ_p(ℓ)` is a *staging fingerprint* (E5).
> **Grade:** exact idempotence ⇒ `δ_p = 0` is `[T]` (Lean: `SBTCosmo.Idempotence`, reusing
> `Dark Energy` `idempotenceDefectAt_of_idempotent`). Numerical `δ_p` on real data is `[E]`.

### 4.2 Route mismatch `RM_p` (does coarse-graining commute with dynamics?)

> **Definition.** `RM_p := d( E_{θ,p}∘T,  T_θ∘E_{θ,p} )`, i.e.
> ```
> RM_p(x) = d( E_{θ,p}(T(x)),  T_θ(E_{θ,p}(x)) )                                                    (12)
> ```
> (`idea.md` §4; `Dark Energy` precursor eq:route_mismatch_def, eq. `RM(x)=d_X(Ê(Tx),T(Êx))`).
> **Computed from data:** evolve the micro/heterogeneous state one step then package, versus package
> then evolve the FLRW macro state; whitened distance of the two readouts. **Interpretation:** the
> central diagnostic. `RM_p > 0` ⇔ a closed homogeneous macro theory does **not** descend ⇔ a rewrite
> `R[Δ]` is forced (P1/F2). Precursor result to reproduce in E0: `RM ≈ 0` in the linear control regime,
> `RM > 0` once nonlinearity is on (`heterogeneous patches ⇒ Q_peak ≈ 1.74`, `Ω_Λ ≈ 0.60` mis-fit).
> **Grade:** commutation ⇒ `RM_p = 0` is `[T]` (Lean: `SBTCosmo.RouteMismatch`, reusing the precursor
> exact-commutation lemma). Numerical `RM_p` is `[E]`.

### 4.3 Local–global gluing defect `LG_{p,q}` (do local probes glue to one metric object?)

> **Definition.** `LG_{p,q} := d( glue(f_p, f_q),  global FLRW )`, the failure of two local probe
> sections to globalize into one FLRW completion:
> ```
> LG_{p,q} = d( glue(f_p(x), f_q(x)),  R(g) for the best global g )                                 (13)
> ```
> where `glue(·,·)` enforces the declared overlap comparison (e.g. CDDR `η(z)=D_L/[(1+z)²D_A]=1`) and
> `R` is the restriction of a global FLRW state to the patch system (F4 `def:local-global-compat`).
> **Computed from data:** for the SN/BAO pair, fit each probe's distance section, impose the overlap
> relation, and measure the whitened residual of the best joint FLRW globalization. The CDDR audit
> functional is `LG_{SN,BAO}` with the explicit `η(z)` test (E2). **Interpretation:** `LG > 0` is a
> *gluing obstruction*, not automatically new dark energy — this is P3/F4. The F4 status of the glued
> family (§6.3, four route statuses) types the defect.
> **Grade:** the local-global *normal form* (F4) is `[T]`; the *value* of `LG_{p,q}` on data is `[E]`.

### 4.4 Cross-probe predictive defect `PPD_{p→q}` (out-of-sample closure)

> **Definition.** `PPD_{p→q} := d( q_obs,  q_pred-from-p )`, the held-out predictive failure:
> ```
> PPD_{p→q} = d( observed probe-q vector,  posterior-predictive of q from a fit to probe-p only )   (14)
> ```
> (`idea.md` §4, §6 Experiment 4.) **Computed from data:** fit the model (ΛCDM, or ΛCDM+`Ξ`) to probe
> block `p` only, draw the posterior-predictive distribution of probe `q`, and measure the whitened
> distance to the *held-out* `q` data. The leave-one-probe-out battery (`idea.md` §6 E4): BAO+CMB→SN;
> SN+BAO→growth; WL+RSD→geometry; ladder→inverse-ladder; CMB+BAO→local `H₀`. **Interpretation:** the
> anti-fudge test. A genuine `Ξ_cosmo` lowers `PPD`; a per-probe fudge does not (§1.3 point 3).
> **Grade:** `[E]` (this is the central empirical claim — `idea.md` §10 standard 3).

> **Summary table (LOCKED).**
>
> | Residual | Symbol | Eq. | Tests | Metric `d` | Grade of "=0" |
> |---|---|---|---|---|---|
> | idempotence defect | `δ_p` | (11) | packaging is a projection | (10) | `[T]` |
> | route mismatch | `RM_p` | (12) | coarse-graining commutes with `T` | (10) | `[T]` |
> | local–global gluing | `LG_{p,q}` | (13) | local sections globalize (CDDR) | (10) | `[T]` (normal form) |
> | cross-probe predictive | `PPD_{p→q}` | (14) | out-of-sample closure | (10) | `[E]` |

---

## 5. The Hubble readout field, holonomy, and lawful plurality (LOCKED)

This section reconstructs the garbled `idea.md` UPDATE-block formulas and locks the central diagnostic
of E4 (`plan/00-overview` §3 row 2). The corpus anchors are `Holonomy_with_Memory` (route transport,
loop action on a predictive quotient), `Protocol_Trap` (holonomy ≠ arrow-of-time, do not over-read
scatter), and `To_Plot` (curvature = loop holonomy).

### 5.1 The Hubble readout field (`idea.md` UPDATE)

> **Definition (route).** A *route* is the tuple
> ```
> r = (probe, anchor, z-depth, lens scale, completion, calibration bridge)                          (15)
> ```
> Canonical rows (`idea.md` UPDATE): `r₁ = CMB→BAO`, `r₂ = BAO→SN`, `r₃ = Cepheid→SN`,
> `r₄ = TRGB→SN`, `r₅ = JAGB→SN`, `r₆ = time-delay`, `r₇ = standard-siren`. A *staging* `ℓ` is the
> bridge/cut choice: redshift cut, host cut, SN sample, anchor choice, BAO compression, calibration
> bridge.
>
> **Definition (Hubble readout field).** `H₀` is **not** a closure-independent scalar; it is a
> route- and staging-indexed readout:
> ```
> H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo]                                                       (16)
> ```
> where `H_closed(0)` is the (single) Hubble value that would obtain if cosmological closure succeeded,
> and `K_{r,ℓ}` is the **fifth observable kernel** (§3.3), the route-and-staging projection of the
> *same* `Ξ_cosmo`. The field is `𝓗_{r,ℓ}(z)`; its `z=0` slice is `H₀^{(r,ℓ)}`.

> **Three competing models for the route matrix `{H₀^{(r,ℓ)}}` (LOCKED, `idea.md` UPDATE):**
> ```
> Null      (closed):     K_{r,ℓ}[Ξ] = 0                         (one scalar, no fragmentation)     (17a)
> Nuisance:               H₀^{(r,ℓ)} = H₀ + ε_{r,ℓ}              (unrelated per-route noise)        (17b)
> Six Birds:              H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ_cosmo]   (one low-rank Ξ, shared)   (17c)
> ```
> The Six Birds claim is decided **against both** (17a) and (17b): the disagreement must be *lawful
> plurality* — structured by route and staging via a low-rank `Ξ`, not white noise (17b) and not zero
> (17a).

### 5.2 Hubble holonomy `𝔥_γ` (reconstructed formula)

The `idea.md` UPDATE formula is garbled (`## B_{γ#}P(H_0^{r_1}) / P(H_0^{r_1})`). It is the posterior
transported around a loop of routes, compared to the starting posterior — a holonomy in the sense of
`Holonomy_with_Memory` (loop action `T_γ` on a quotient) and `To_Plot` (curvature = loop holonomy).

> **Definition (route bridge transport).** For a directed route step `γ: r → r'`, let `B_γ` be the
> declared **bridge transport** that carries a Hubble posterior measured on route `r` to the route-`r'`
> frame (the calibration map identifying the two currencies; `Holonomy_with_Memory` `T_γ` on the
> predictive quotient). `B_{γ#}` is the pushforward of distributions along `B_γ`.
>
> **Definition (Hubble holonomy).** For a *loop* of routes `γ = (r₁ → r₂ → … → r_k → r₁)`, the
> **Hubble holonomy** is the discrepancy between the posterior transported around the loop and the
> original posterior:
> ```
> 𝔥_γ := 𝒟( B_{γ#} P(H₀^{r₁}),  P(H₀^{r₁}) )                                                       (18)
> ```
> where `B_{γ#} = B_{(r_k→r₁)#} ∘ … ∘ B_{(r₁→r₂)#}` is the composed loop transport and `𝒟` is a
> distribution divergence (**KL** in nats, with **Wasserstein-2** as a robust alternative; report
> both). `P(H₀^{r})` is the route-`r` Hubble posterior (`getdist`/importance-reweighted, E4).
>
> **Reading (`idea.md` UPDATE, four steps):** (1) start with a Hubble posterior from one route;
> (2) transport it through another route via the declared bridge; (3) transport it back; (4) ask
> whether it returns unchanged. `𝔥_γ = 0` ⇒ the Hubble currency is globally consistent (closure
> succeeded). `𝔥_γ ≠ 0` ⇒ a **route holonomy** has been found: *the Hubble tension is the scalar
> shadow of Hubble holonomy* (`idea.md` UPDATE headline).

> **`[T]` Holonomy non-triviality (loop action can be nonzero with trivial scalar).** On a finite
> route-transport carrier, the loop transport `B_{γ#}` can act **trivially on the current (scalar `H₀`)
> quotient while acting nontrivially on the predictive (full-posterior) quotient** — exactly the
> `Holonomy_with_Memory` loop-asymmetry theorem (`thm:predictive-transport` + the coherent-memory
> benchmark: current loop trivial, predictive loop nontrivial). **Proof strategy:** instantiate the
> route-transport package with interfaces = routes, continuations = bridges `B_γ`, current quotient =
> scalar `H₀` readout, predictive quotient = full posterior; reuse the loop-asymmetry theorem.
> **Lean target:** `SBTCosmo.Holonomy` reusing `Holonomy_with_Memory` `predictiveToCurrent_commutes_
> with_transport` and the loop-asymmetry witness. Grade `[T]` for the finite carrier; the *value* of
> `𝔥_γ` on real posteriors is `[E]`.
>
> **Discipline (do not over-read — `Protocol_Trap`).** A nonzero `𝔥_γ` is *not* automatically
> meaningful: a protocol-trap / flattenable holonomy can be removed by honest internalization of the
> bridge. E4 must therefore separate **structured route holonomy** (survives bridge internalization,
> reuses the same `Ξ`) from **removable scheduling artifact** (vanishes under internalization). This is
> the "careful" clause of `idea.md` UPDATE: turn disagreement into a disciplined diagnostic, not
> automatic confirmation.

### 5.3 The lawful-plurality test set (LOCKED, `idea.md` UPDATE five tests)

Six Birds wins the Hubble sector only if disagreements are **lawful** (structured), not arbitrary.
The five pre-registered tests (`idea.md` UPDATE "Why 'careful' still matters"):

| # | Test | Operationalization | Pass condition (gate, §9) |
|---|---|---|---|
| **LP1** | **Route structure** | offsets `H₀^{(r,ℓ)} − H_closed` cluster by route, not random | within-route variance `<` between-route variance; Spearman `ρ(r=r′) > ρ(r≠r′)`, p `< 0.05` |
| **LP2** | **Staging structure** | varying `ℓ` (z-cut, host cut, anchor, compression) moves `H₀^{(r)}` predictably | staging regression OOS `R² > 0.7` |
| **LP3** | **Closure transport** | transporting a posterior around a route loop exposes nonzero holonomy | `𝔥_γ > 0.1` nats on at least one loop, `≫` measurement error |
| **LP4** | **Residual reuse** | the *same* `Ξ_cosmo` that organizes `{H₀^{(r,ℓ)}}` also repairs CDDR (E2), DESI `w(z)` (E1), growth/staging (E5) | shared-`Ξ` cross-amplitudes within 10×, consistent sign (coherence gate §9.4) |
| **LP5** | **Source refinement** | adding *genuine* hidden-variable / heterogeneity proxies reduces the residual; adding *unrelated* per-route nuisance does **not** count as success | `Ξ`-corrected `std[H₀^{(r,ℓ)}]` shrinks vs nuisance model (17b); ΔBIC favors (17c) over (17b) by `> 5` |

> **The Hubble route matrix.** Rows = routes `r₁…r₇` (eq. 15); columns = stagings `ℓ`. Each cell holds
> `H₀^{(r,ℓ)}` with its posterior. The Six Birds question: *is there a low-rank `Ξ_cosmo(z,ℓ,r)`
> explaining the whole matrix via (16)?* The decisive comparison is (17c) vs (17a) **and** (17b).

---

## 6. The four propositions (LOCKED): statements, proof strategies, Foundations-IV grounding

The formal backbone (`idea.md` §4, §8 Section 4). Each maps a paradox to a named Foundations-IV law
and gets a Lean target. **"Proved" here = a Lean 4 theorem with either (a) a complete proof reusing
the corpus anchor, or (b) a verified-computation witness for the finite/numerical instance, with the
residual obligation explicitly statused.** (`plan/00-overview` §5.)

### 6.1 P1 ↔ F2 — Descent–Repair Normal Form (`[T]`)

> **Statement (F2 + cosmology extension).** When the FLRW descent of a macro law fails
> (`E_{θ,p}∘T ≠ T_θ∘E_{θ,p}`, i.e. `RM_p > 0`), **F2's normal form supplies exactly two canonical
> repairs:** (i) **source refinement** and (ii) the **minimal target coarsening** `c_F: R → R_F`. The
> `Ξ_cosmo` **operator rewrite** `R[Δ_SBT]` is **not** part of F2's statement — it is the
> **cosmology-specific extension** of F2 used by this program (the "operator-rewrite repair chart" for
> P1), an addition to F2's two repairs, not a restatement of them. So P1 is a cosmology-specific
> *extension* of F2 (F2's two repairs + the operator-rewrite chart), not a verbatim restatement.
>
> **Foundations-IV grounding.** `thm:F2` *Descent-Repair Normal Form* (`Foundations_IV`
> `sec:transport:descent-repair`; Lean `Transport.DescentRepair.descent_repair_normal_form`):
> `r∘F` descends through `q` iff `splitObs(q,F,r) = ∅`; if nonempty, the **two** canonical repairs are
> **source refinement** and the **minimal target coarsening** `c_F: R → R_F`. (F2 itself names exactly
> these two; the operator rewrite is the cosmology extension below.)
>
> **Instantiation.** Set `q := U_θ` (FLRW completion as the quotient map onto homogeneous descriptors),
> `F := f_p ∘ T` (lensed evolution), `r :=` the observable readout. Then `splitObs(q,F,r) ≠ ∅ ⇔
> RM_p > 0`, and F2's two repairs are precisely {source refinement, minimal target coarsening `c_F`}.
> The cosmology extension adds the **operator-rewrite chart** `R[Ξ]`: the `Ξ` rewrite is that branch,
> and DESI's `w₀w_a`, IDE `Q`, and `(μ,Σ)` are *alternative* operator-rewrite charts of the same
> nonempty obstruction (shadow rows 3, 8, 9).
>
> **Proof strategy.** The F2 part (two-repair normal form + minimality of the target repair) is direct
> reuse of `thm:F2`: instantiate `(q,F,r)` as above; the split-pair obstruction nonemptiness ⇔
> route-mismatch positivity is a definitional unfolding (eq. 12); the minimality clause is F2's
> verbatim. The operator-rewrite chart is the cosmology extension layered on top of F2.
> **Lean target:** `SBTCosmo.DescentRepair` importing `Transport.DescentRepair` as an opacity-guarded
> anchor. **Grade `[T]` — full proof feasible.**

### 6.2 P2 ↔ F11 — No-Overread / Access Quotient (`[C]`, scaffold + witness)

> **Statement.** QFT vacuum energy does **not** descend automatically to cosmological dark energy:
> the identification `ρ_vac^QFT ≡ ρ_Λ^cosmo` is **rejected** unless a declared bridge descends through
> the *cosmological access quotient*. The 10¹²⁰ cosmological-constant mismatch is therefore *dissolved*
> as an **unbridged cross-layer identification** (an overread defect), not solved by numerology
> (`idea.md` §7 cc-problem).
>
> **Foundations-IV grounding.** `thm:F11` *Adequacy / No-Overread* (`Foundations_IV`
> `sec:access:adequacy`; Lean `Access.Adequacy.adequacy_no_overread`): an accepted current-layer claim
> `F: H → W` must be constant on the fibers of the access quotient `accessQ: H → Q_I`
> (`def:access-quotient`), i.e. `F = F̄ ∘ accessQ`. A claim depending on instrument-suppressed content
> with no explicit bridge is an *overread defect*.
>
> **Instantiation.** Let `H` = the joint micro carrier; `accessQ` = the **cosmological observation
> signature** (what the late-time expansion-history probes can actually distinguish — distances,
> growth, `C_ℓ`). The map "read off `ρ_Λ^cosmo`" factors through `accessQ`. The QFT vacuum-energy
> functional does **not** factor through `accessQ` (it lives on a different access package). Hence
> `ρ_vac^QFT ≡ ρ_Λ^cosmo` violates F11 *unless* a declared bridge `Q_I^{QFT} → Q_I^{cosmo}` is
> exhibited. Absent the bridge, the identification is an overread defect; with a *declared but
> unverified* bridge, the residual is statused `out_of_scope` or `budgeted` (§8).
>
> **Proof strategy.** State the cosmological access quotient explicitly (finite observation signature
> over the sampled probe vectors); show the QFT-vacuum functional is non-constant on its fibers
> (verified-computation witness on the sampled signature) ⇒ no factorization ⇒ overread defect by
> F11. Full no-factorization theorem reuses `thm:F11`.
> **Lean target:** `SBTCosmo.NoOverread` (scaffold importing `Access.Adequacy`) + a numerical witness
> that the two functionals separate a fiber of `accessQ`. **Grade `[C]` — recognition-grade under the
> declared cosmological access signature; scaffold + witness feasible, full proof reuses F11.**

### 6.3 P3 ↔ F4 — Local–Global / Distance Duality (`[C]`/`[T]`, scaffold + numerical witness)

> **Statement.** Distance duality is the statement that the SN luminosity-distance section and the
> BAO angular/radial-distance sections **globalize into one metric-distance object**. CDDR failure
> (`η(z) = D_L/[(1+z)²D_A] ≠ 1`) is a **gluing obstruction** (`LG_{SN,BAO} > 0`), **not** automatically
> new dark energy. The glued family carries exactly one of four route statuses.
>
> **Foundations-IV grounding.** `thm:F4` *Local-Global Obstruction Normal Form* (`Foundations_IV`
> `sec:transport:local-global`; Lean `Transport.LocalGlobalObstruction.local_global_obstruction_
> normal_form`). For compatible local data, globalization ⇔ membership in the restriction image, and
> every compatible family carries **exactly one** of four statuses:
> `OverlapInconsistent ⊻ CompatibleNonGlobal ⊻ GloballyAmbiguous ⊻ GloballyExact`
> (determined by `Comp(a)`, membership in `R(𝒢)`, and the fiber cardinality `|R^{-1}(a)|`).
>
> **Instantiation.** Patch system `I = {SN, BAO}`; local objects = the fitted distance sections;
> overlap-compatibility `Comp` = the CDDR relation `η(z)=1`; global object = one FLRW completion;
> `R` = restriction of an FLRW state to the two distance probes. Then:
> - `η(z) ≡ 1` and a global FLRW exists with unique fit ⇒ **GloballyExact** (no obstruction);
> - `η(z) ≡ 1` but no global FLRW reproduces both ⇒ **CompatibleNonGlobal** (gluing obstruction
>   *even though* the overlap test passes — the subtle case `idea.md` §6 E2 wants);
> - `η(z) ≠ 1` ⇒ **OverlapInconsistent** (the Afroz–Mukherjee SN+BAO inconsistency reading);
> - multiple FLRW completions fit ⇒ **GloballyAmbiguous** (a `moduli` residual, §8).
> The apparent `w_a` may collapse into the gluing residual (E2 question; `idea.md` §6 E2 deliberately
> does **not** force one answer).
>
> **Proof strategy.** The F4 normal form is `[T]` and reused directly (instantiate `(𝒢, 𝓕, Comp, R)`).
> The *status assignment* on the fitted `η(z)`/distance data is a numerical witness (`[C]`/`[E]`):
> compute `Comp`, test image membership, count the fiber.
> **Lean target:** `SBTCosmo.LocalGlobal` (scaffold importing `Transport.LocalGlobalObstruction`) +
> a numerical witness on the fitted `η(z)`. **Grade: normal form `[T]`; the data status is `[C]/[E]`.**

### 6.4 P4 — Phantom Crossing With a Stable Finite Effective Readout (`[T]`, finite verified-computation witness)

> **Statement (downgraded per REGISTRY §5).** A finite, **positive, stable** rewrite operator `R[Ξ]`
> can induce an effective equation of state `w_eff(z)` that **crosses −1** (the phantom divide) with
> **no growing mode** — a *stable finite effective readout*. The deliverable is exactly this finite-witness
> stability property: phantom crossing is a property of the *effective readout*, realized by an operator
> that is positive and spectrally stable on the audit-energy inner product (`idea.md` §4 P4, §6 E3,
> §7 phantom-crossing).
>
> **Scope boundary (LOCKED, REGISTRY §5).** The stronger claim — that there is **no negative-kinetic
> (ghost) fundamental degree of freedom** — is **`out_of_scope`** (statused, §8) here: it requires a
> Lagrangian / Hamiltonian / kinetic-metric framework that this program does **not** build. This file
> therefore claims "no growing mode / stable effective readout", **not** "no ghost", wherever a
> Lagrangian is not exhibited. The full ghost-absence statement is registered as a scope exclusion until such
> a framework is added.
>
> **The effective equation of state (de-garbled, `idea.md` §6 E3):**
> ```
> w_eff(z) = −1 + ( (1+z)/3 ) · d/dz [ ln ρ_eff(z) ]                                                (19)
> ```
> with `ρ_eff(z) = ρ_FLRW(z;θ) + R[Ξ_cosmo](z)` (eq. 5). `w_eff` crosses −1 exactly where
> `d/dz ln ρ_eff` changes sign.
>
> **Foundations-IV grounding.** No single named F-law; uses the **operator-rewrite repair** (the
> cosmology/P1 extension of F2, §6.1) plus an **eigenvalue/stability audit** in the membrane discipline
> of `Emergence IS the Needle Killer` (positive native currency, layer-dissolving endpoint). The
> stability criterion is operationalized as spectral positivity (no growing mode), **not** a Lagrangian
> kinetic-sign analysis (which is out of scope, REGISTRY §5).
>
> **Proof strategy (finite, theorem-grade).**
> 1. Construct the finite macro-evolution map `M_Ξ` on the sampled macro state including `R[Ξ]`.
> 2. **Stable-readout criterion:** all eigenvalues of the linearized Jacobian `J = ∂M_Ξ/∂(state)` have
>    `Re λ ≤ 0` (stable, **no growing mode**). Equivalently the rewrite is a *positive* operator on the
>    audit-energy inner product (`Adequacy_Residuals` positivity; the membrane positivity of
>    `Needle Killer`). This is a finite spectral fact, **not** a claim about kinetic-metric signs.
> 3. **Crossing:** show `w_eff(z)` from (19) crosses −1 at the DESI-preferred `z_c` for the fitted `Ξ`.
> 4. Conclude: a positive/stable operator yields `w_eff < −1` over an interval with no growing mode —
>    *finite witness* of a stable effective readout, hence theorem-grade for the constructed instance.
> **Lean target:** `SBTCosmo.PhantomStableReadout` — prove `(∀ λ ∈ spec(J), Re λ ≤ 0) ∧ (∃ z, w_eff(z) <
> −1)` for the constructed finite map (verified computation over a rational/interval-arithmetic grid);
> states the **finite stability property only** (stable effective readout, no growing mode), not a
> ghost-absence / negative-kinetic-DOF claim. **Grade `[T]` — full finite proof feasible.** (The *physical* claim that the data
> prefer a crossing realized by a positive/stable `R` is `[E]`, decided by the E3 stability gate; the
> full no-negative-kinetic-DOF / ghost-absence claim is `out_of_scope`, REGISTRY §5.)

> **Meta-obligation across P1–P4: `thm:F9` No Unstatused Residual.** Every leftover tension after
> P1–P4 must carry exactly one AOR status (§8). F9 (`Foundations_IV` `sec:stability:no-unstatused-
> residual`; Lean `Stability.NoUnstatusedResidual.no_unstatused_residual`): a formed stability package
> with a single-valued typed-status classifier `st_𝒫` has `∀ r, ¬ UnstatusedResidual(r)`. This is the
> phase-end gate: zero `unstatused` entries (§9.5). **Grade `[T]`** (reused directly).

> **Proposition summary (LOCKED).**
>
> | Prop | Paradox / shadow row | F-IV anchor | Lean module | Grade |
> |---|---|---|---|---|
> | **P1** Descent–Repair | DESI `w(z)` (3), MG (9), IDE (8) | `thm:F2` | `SBTCosmo.DescentRepair` | `[T]` |
> | **P2** No-Overread | cc-problem (1), anthropic (10) | `thm:F11` | `SBTCosmo.NoOverread` | `[C]` |
> | **P3** Local–Global / CDDR | distance-duality (4) | `thm:F4` | `SBTCosmo.LocalGlobal` | `[T]` norm / `[C]` data |
> | **P4** Phantom stable readout | phantom crossing (5) | (operator-rewrite + spectral, `Needle Killer`) | `SBTCosmo.PhantomStableReadout` | `[T]` |
> | (meta) No Unstatused Residual | all | `thm:F9` | `SBTCosmo.AORStatus` | `[T]` |

---

## 7. The stable-effective-readout stability audit (LOCKED detail for P4 / E3)

Because P4 is the formal centerpiece showing that phantom crossing can be realized by a stable finite
effective readout, the stability audit is specified here (the E3 pipeline implements it). It certifies
**no growing mode**, not the absence of a negative-kinetic fundamental degree of freedom (that ghost-absence
claim is `out_of_scope`, REGISTRY §5).

> **Stable-readout certificate.** The rewrite `R[Ξ]` passes the stable-effective-readout audit iff
> **both**:
> 1. **Spectral stability.** All eigenvalues of the linearized macro Jacobian satisfy `Re λ ≤ 0`
>    (no growing mode); report `max_λ Re λ` and require `≤ 0` to numerical tolerance.
> 2. **Energy positivity.** `R[Ξ]` is a positive operator on the audit-energy inner product `⟨·,C·⟩`
>    (`C = Σ^{-1}`), i.e. the rewrite adds no negative-norm direction. Report the minimal eigenvalue of
>    the symmetrized `R` in `C`-coordinates; require `≥ 0`.
> The certificate shows the *macro readout* `w_eff(z)` (eq. 19) crosses −1 while the *operator* is
> positive/stable with no growing mode. It deliberately does **not** adjudicate the presence or absence
> of a fundamental ghost: that would require a Lagrangian / Hamiltonian / kinetic-metric framework not
> built here, and the no-negative-kinetic-DOF claim is statused `out_of_scope` (§8, REGISTRY §5).
> **Crossing stability:** the crossing redshift `z_c` must be stable to `< 0.1` under 1σ parameter
> jitter (E3 gate, §9). **Grade:** the certificate is `[T]` for the constructed map (finite stability
> property); "the data prefer a crossing realized by a positive/stable `R`" is `[E]`.

---

## 8. AOR status usage (LOCKED): how every residual is typed

All results are recorded in an **Audited Operational Realisability** carrier (`AOR`). The carrier of
this program is `𝔉_cosmo` (§2) viewed as a PreSB carrier; closing it to AOR means every stratum is
empty (`AOR` def:aor:xi-sb, `thm:aor:eight-stratum-decomposition`).

### 8.1 The eight structural-defect strata (`Ξ_SB`, `AOR`)

`Ξ_SB(𝔉_cosmo)` is the disjoint sum of eight strata; the carrier is AOR iff each is independently
empty (`AOR` def:aor:xi-sb). Mapping to this program:

| Stratum | `AOR` meaning | Cosmology instance (what must be declared) |
|---|---|---|
| `Σ_obs` | observation records fully typed | each probe vector typed: codomain, role, provenance (arXiv/DOI), eval context |
| `Σ_stage` | stage/refinement declared | each scale-cut / z-bin / staging `ℓ` has a declared refinement axis (E5) |
| `Σ_constraint` | constraints positive + paired with a witness | priors, positivity of `Σ`, stable-readout spectral positivity (§7) each have a typed witness |
| `Σ_rewrite` | rewrites have source/target + admissibility | `R[Ξ]` declared (allowed) or a blocked rewrite explicitly tagged |
| `Σ_holonomy` | route memory has typed carrier-route | each Hubble route loop `γ` and bridge `B_γ` (§5) declared with attribution |
| `Σ_residual` | every residual carries a discharge status | the four residuals + every surviving tension typed (§8.2–8.3) |
| `Σ_nonclaim` | scope exclusions registered | "Λ not ruled out", "no microphysical alternative", "LSS surrogate where used", "no-negative-kinetic-DOF / ghost-absence claim not made (no Lagrangian framework, REGISTRY §5)" registered |
| `Σ_meta` | meta-audit discharged | run manifests, seeds, version pins, audit pass logs (`GROUNDING_BRIEF` §III) |

### 8.2 The twelve-type residual atlas (`Σ_residual`, `AOR`)

Every `Σ_residual` entry has a unique primary type from the twelve-type atlas (`AOR`
`def:aor:residual-types-twelve`). Cosmology mapping (the executor assigns each surviving tension a
primary type):

| Residual type | `AOR` meaning | Cosmology example |
|---|---|---|
| `D_descent` | legal-quotient descent failure | `RM_p > 0`: FLRW does not descend (P1) |
| `D_transport` | route-map failure | nonzero Hubble holonomy `𝔥_γ` (P3/§5) |
| `D_interface` | bounded-interface failure | probe ℓ-support cutoff effects |
| `D_local`, `D_global` | local/global mismatch | CDDR gluing obstruction `LG_{SN,BAO}` (P3/F4) |
| `D_presentation` | normalization mismatch | `r_d` / `A_s` vs `ln(10^10 A_s)` convention skew |
| `D_source` | source-admission failure | unmodeled heterogeneity proxy (LP5) |
| `D_horizon` | carrier-class horizon failure | sampling cutoff in z/ℓ grid |
| `D_scale` | stage-law failure | staging fingerprint `∂Ξ/∂ℓ ≠ 0` (E5) |
| `D_limit` | asymptotic failure | continuum-limit residual (needs asymptotic status, §8.4) |
| `D_sym` | symmetry/equivariance failure | isotropy-violation residual (out of scope here) |
| `D_role` | role-typing failure | a probe vector with undeclared role |
| `D_target` | response-target failure | observable kernel target mismatch |

### 8.3 The AOR-8 status catalogue (eleven base statuses, `AOR` def:aor:aor-8-statuses)

Each residual atom is discharged by a triple `(a, s, π)`: atom `a`, status `s`, typed witness payload
`π` (`AOR` def:aor:discharge-record). The eleven base statuses and their cosmology usage:

| Status | Payload `π` (AOR) | Cosmology usage example |
|---|---|---|
| `zero` | positivity proof | `RM_p = 0` in the linear control regime (E0); exact-adequacy `Ξ_C = 0` |
| `budgeted` | finite budget bound | an irreducible systematic bounded by a declared budget; cc-problem bridge bound |
| `bridged` | bridging-carrier id | CDDR gluing defect repaired by `Ξ` via a declared bridge (P3) |
| `hidden` | (latent) | a determining variable exposed only after refinement (LP5 source refinement) |
| `moduli` | moduli-space pin | a parameter the data cannot fix (`GloballyAmbiguous` F4 case); a flat direction |
| `selected` | selection rule | an anchor/sample choice fixed by a declared selection rule |
| `probabilistic` | measure record | a residual paid in a posterior-measure sense |
| `out_of_scope` | scope reference | QFT-vacuum→cosmology bridge (P2) when not attempted; isotropy violations; the no-negative-kinetic-DOF / ghost-absence claim for P4 (no Lagrangian/kinetic-metric framework built, REGISTRY §5) |
| `nonclaim` | scope reference | "Λ not ruled out"; "no new microphysics claimed" |
| `blocked` | block reason | a rewrite that is provably inadmissible (e.g. one with a growing/unstable mode) |
| `approved_other` | external-record citation | a residual discharged by a cited external result |

> **The cc-problem (P2) statusing (LOCKED example).** The cross-layer identification
> `ρ_vac^QFT ≡ ρ_Λ^cosmo` is *not* `zero`; absent a verified bridge it is `out_of_scope` (we do not
> attempt the QFT→cosmology descent) and the *observed acceleration residual* is `bridged` (repaired by
> `Ξ`) — so the 10¹²⁰ mismatch is dissolved as an unbridged identification, exactly P2 (`idea.md` §7).

### 8.4 Asymptotic statuses and the carrier hierarchy (`AOR`)

Limit-stage residuals (e.g. continuum-limit `D_limit`) require one of four **asymptotic statuses**
(`AOR` def:aor:asymptotic-statuses): `asymptotic_budgeted` (uniform finite tail budget),
`summable` (per-stage costs summable), `contractive` (cost ratios → constant `< 1`), `eventual_zero`
(cost zero past a tail index). The carrier-status hierarchy (`AOR`, matched in `plan/00-overview` §7):

```
PreSB  ⊆  RefStableAOR  ⊆  CascadeStableAOR  ⊆  AOR
(raw fit)  (asymptotic-stable)  (finite cascade discharge)  (Ξ_SB = 0, all strata empty)
```

> **Phase-end AOR requirement (LOCKED).** At phase end the carrier must reach **CascadeStableAOR**
> (every residual discharged in finitely many steps using only base AOR-8 statuses) with the **AOR
> Status Table** committed and **zero `unstatused` entries** (F9, §6.4). Progression mirrors
> `plan/00-overview` §7: E1–E3 pass → RefStableAOR; E4–E7 pass → CascadeStableAOR; E8 synthesis → AOR
> target. Code map: `sbt_cosmo.aor` (status ledger) + Lean `SBTCosmo.AORStatus` (well-formedness:
> single-valued classifier, no unstatused residual).

---

## 9. Pass / fail gates (quantitative, pre-registered)

These are the **formal-foundations-level** gates. They refine `plan/00-overview` §6 and the
GROUNDING_BRIEF Part 2 to the specific math objects of this file. All thresholds are **pre-registered**
and may not be relaxed after seeing results; a relaxation is a logged statused deviation (`budgeted`).

### 9.1 Reconciliation gates (§1)

| Gate ID | Gate | Threshold | Tie to |
|---|---|---|---|
| `G-FORMAL-1` | Schur identity sanity | `Ξ_C(D∣L) ⪰ 0` (Loewner): min eigenvalue `≥ −10⁻⁸` | §1.1 |
| `G-FORMAL-2` | Exact-adequacy ⇒ no rewrite | when synthetic data is FLRW-exact, `Ξ_C ≈ 0` (Frobenius `< 10⁻⁶`) and the fit selects `Δ_SBT = 0` (all `|a_i| < 10⁻³`) | §1.2(2) |
| `G-FORMAL-3` | Per-sector reconciliation (`[C]`, numerical) | for each sector `p` (§1.2′), audit cost `J_p(Δ)` equals the Schur energy of the residual readout to `< 1%`; report `‖Ξ_C^{(p)} − audit_cost_p‖` | §1.2(1), §1.2′ |

### 9.2 Ansatz / kernel gates (§3)

| Gate ID | Gate | Threshold | Tie to |
|---|---|---|---|
| `G-FORMAL-4` | Rank ceiling | total free `Ξ` params `≤ ΛCDM + 3` (minimal) / `≤ 5–7` (full); **no per-probe free `Ξ_p`** | §3.1 |
| `G-FORMAL-5` | Kernel linearity | `K_L,K_M,K_G,K_S,K_{r,ℓ}` linear in `(a₀,a₁,a₂)` to `< 1%` (finite-difference check) | §3.2–3.3 |
| `G-FORMAL-6` | Coherence (cross-amplitude) | `Ξ`-amplitude from `K_S` within **10×** of `K_L/K_M`-implied amplitude, consistent sign | §3.3, §9.4 |

### 9.3 Four-residual gates (§4)

| Gate ID | Gate | Threshold | Tie to |
|---|---|---|---|
| `G-FORMAL-7` | Metric well-posedness | every probe `Σ` PD, cond `< 10⁸`, finite (else use `Σ^†` on legal quotient) | §4.0 |
| `G-FORMAL-8` | Linear-control nulls | `RM_p ≈ 0` and `δ_p ≈ 0` in the E0 linear control (`< 10⁻⁶` of data variance) | §4.1–4.2 |
| `G-FORMAL-9` | Nonlinear positivity | `RM_p > 0` when nonlinearity/heterogeneity on (reproduce precursor `Ω_Λ ≈ 0.60`, `Q_peak ≈ 1.74`) | §4.2 |
| `G-FORMAL-10` | Out-of-sample win | `Ξ` lowers `PPD_{p→q}` and beats **every** alternative on the primary OOS metric by **more than the combined uncertainty band** after the complexity penalty, with **no silent loss** on any critical leg — a `tie` (within the band) is **not** a pass (REGISTRY §8; cf. `G-E8-OOS`) | §4.4 |

### 9.4 Coherence gate (the make-or-break, §3.3 / §5 LP4) — `G-PHASE-COHERENCE`

> **One `Ξ_cosmo` everywhere (gate `G-PHASE-COHERENCE`, REGISTRY §3).** The *same* fitted `Ξ_cosmo`
> must reduce geometry (E1, E2), growth (E5),
> Hubble (E4), phantom (E3), and accounting (E6) residuals, and be compatible with MG (E7).
> **Fail rule (LOCKED, `plan/00-overview` §6.4):** if any experiment's fitted `Ξ_cosmo` is mutually
> inconsistent with another (e.g. E5 `K_S` amplitude differs from E1 `K_L/K_M`-implied amplitude by
> `> 10×`, or signs disagree), **the entire program fails the phase.** The residual-reuse matrix is a
> committed artifact.

### 9.5 Proposition / AOR gates (§6, §8)

| Gate ID | Gate | Threshold | Tie to |
|---|---|---|---|
| `G-FORMAL-11` | P1 (`[T]`) | `SBTCosmo.DescentRepair` compiles under `lean --check`; `splitObs ≠ ∅ ⇔ RM_p > 0` verified | §6.1 |
| `G-FORMAL-12` | P2 (`[C]`) | `SBTCosmo.NoOverread` scaffold compiles; numerical witness separates an `accessQ` fiber | §6.2 |
| `G-FORMAL-13` | P3 (`[T]`/`[C]`) | `SBTCosmo.LocalGlobal` compiles; the fitted `η(z)` carries exactly one of the four F4 statuses | §6.3 |
| `G-FORMAL-14` | P4 (`[T]`, stable readout) | `SBTCosmo.PhantomStableReadout` compiles; `max_λ Re λ ≤ 0` (no growing mode) AND `∃ z, w_eff(z) < −1`; `z_c` stable `< 0.1` under 1σ. (No-negative-kinetic-DOF / ghost-absence claim is `out_of_scope`, REGISTRY §5.) | §6.4, §7 |
| `G-FORMAL-15` | F9 / No-Unstatused | `SBTCosmo.AORStatus` compiles; **zero `unstatused` entries** in the committed AOR Status Table | §6.4, §8 |
| `G-FORMAL-16` | Carrier status | reach **CascadeStableAOR** (finite cascade discharge, base statuses only) at phase end | §8.4 |

### 9.6 Hubble / lawful-plurality gates (§5)

| Gate ID | Gate | Threshold | Tie to |
|---|---|---|---|
| `G-FORMAL-17` | LP1 route structure | within-route var `<` between-route var; Spearman `ρ(r=r′) > ρ(r≠r′)`, p `< 0.05` | §5.3 |
| `G-FORMAL-18` | LP2 staging structure | staging regression OOS `R² > 0.7` | §5.3 |
| `G-FORMAL-19` | LP3 closure transport | `𝔥_γ > 0.1` nats on ≥ 1 loop, `≫` measurement error; report KL and W₂ | §5.2–5.3 |
| `G-FORMAL-20` | LP4 residual reuse | shared-`Ξ` cross-amplitudes within 10×, consistent sign (= §9.4) | §5.3 |
| `G-FORMAL-21` | LP5 source refinement | `Ξ`-corrected `std[H₀^{(r,ℓ)}]` shrinks vs nuisance (17b); ΔBIC favors (17c) over (17b) by `> 5` | §5.3 |
| `G-FORMAL-22` | Holonomy not artifact | structured holonomy survives bridge internalization (does not flatten away) — `Protocol_Trap` discipline | §5.2 |

> **Failure is acceptable iff statused.** A `FAIL` (e.g. "phantom crossing required a growing mode /
> unstable readout — P4 fail", "`Ξ` fragmented into per-probe corrections — coherence fail", "`𝔥_γ` flattened away under
> internalization — Hubble holonomy is artifact") is a legitimate scientific result **only if** it is
> typed in the AOR ledger (§8) with a base status and reported with numbers. Unacceptable outcomes:
> an unreproduced baseline, an `unstatused` residual at phase end, or a gate relaxed after the fact.

---

## 10. Corpus grounding (for the executor who wants the proofs)

| Object in this file | Corpus anchor | Where |
|---|---|---|
| `Ξ_C(D∣L) = K_DD − K_DL K_LL^† K_LD`; projection identity; exact-adequacy; Loewner-min | **Adequacy Residuals and Blind-Spot Currency** | §1 |
| `Ê = U∘f`, `RM(x)=d_X(Ê(Tx),T(Êx))`, `iddef`, null-Λ toy → `Ω_Λ≈0.60`, "Λ not ruled out" | **A Six Birds' Eye View of Dark Energy** | §1.2(2), §2, §4.1–4.2 |
| `thm:F2` Descent–Repair Normal Form (`Transport.DescentRepair`) | **Foundations IV** | P1, §6.1 |
| `thm:F11` Adequacy / No-Overread + `def:access-quotient` (`Access.Adequacy`) | **Foundations IV** | P2, §6.2 |
| `thm:F4` Local-Global Obstruction Normal Form + four route statuses (`Transport.LocalGlobalObstruction`) | **Foundations IV** | P3, §6.3 |
| `thm:F9` No Unstatused Residual (`Stability.NoUnstatusedResidual`) | **Foundations IV** | §6.4, §8 |
| eight strata `Ξ_SB`, twelve-type residual atlas, AOR-8 + asymptotic statuses, `PreSB⊆…⊆AOR` | **Audited Operational Realisability (AOR)** | §8 |
| route transport, loop action, current vs predictive quotient, loop-asymmetry (current trivial / predictive nontrivial) | **Holonomy with Memory** | §5.2 |
| holonomy ≠ arrow; removable protocol-trap holonomy ⇒ "do not over-read scatter" | **Protocol Trap** | §5.2, §9.6 |
| curvature = loop holonomy; distance = optimized protocol cost | **To Plot a Stone** | §5 |
| membrane positivity / layer-dissolving endpoint ⇒ stable-readout (no-growing-mode) spectral discipline | **Emergence IS the Needle Killer** | P4, §6.4, §7 |
| worked cross-lens audit template (SPT-3G 2018→D1 lens swap; held-out `δχ`, localization, common-staging control) | **Six Birds for Neutrino Mass** | §4.4 method, §5 |

**Lean module map (per `plan/01-repo-structure.md` §5, Lean v4.28.0, mathlib selectively):**
`SBTCosmo.Idempotence` (δ), `SBTCosmo.RouteMismatch` (RM), `SBTCosmo.Adequacy` (§1 reconciliation),
`SBTCosmo.DescentRepair` (P1), `SBTCosmo.NoOverread` (P2), `SBTCosmo.LocalGlobal` (P3),
`SBTCosmo.PhantomStableReadout` (P4), `SBTCosmo.Holonomy` (§5), `SBTCosmo.AORStatus` (F9 / no-unstatused).

**Python module map (per `plan/01-repo-structure.md` §4):** `sbt_cosmo.xi.residual` (eq. 4),
`sbt_cosmo.xi.kernels` (eqs. 6–9, `K_{r,ℓ}`), `sbt_cosmo.audits` (eqs. 11–14, metric eq. 10),
`sbt_cosmo.hubble.holonomy` (eqs. 16, 18; LP1–LP5), `sbt_cosmo.aor` (§8 status ledger).
