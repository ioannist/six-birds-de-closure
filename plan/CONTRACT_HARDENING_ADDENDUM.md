# CONTRACT HARDENING ADDENDUM (LOCKED)

**Status:** LOCKED contract, peer to `REGISTRY.md`. Where any file disagrees with this addendum on the
items below, **this addendum wins** (and `REGISTRY.md` wins over both on items it covers). Created to
close the final pre-implementation review's under-specification findings (1, 2, 4, 6, 17) and to give
executors one place for the load-bearing definitions. Nothing here is prose/manuscript; it is an
execution contract.

This addendum does **not** re-derive the program — it pins the objects that were named but not made
numeric, and records the formula/threshold corrections applied in the same review pass. Read it
alongside `04-formal-foundations.md` (§1, §3, §4, §6), `03-data-acquisition.md`, and `05-lean-mechanization.md`.

---

## §1 — Observable dictionary (closes finding 2, part A)

For each probe sector `p`, the executor instantiates the §1.2′ reconciliation and the §4 residuals on the
**concrete tuple** below. Dimensions are the *target* shapes; the loader (`03`) fixes the exact bins.

| Sector `p` | Data vector `y_p` (dim) | Covariance `Σ_p` | Nuisance vector `ν_p` | Shared-nuisance couplings | Whitening |
|---|---|---|---|---|---|
| **SN** | distance moduli `μ(z_i)` or `D_L(z_i)` (~1500–1700, Pantheon+/Union3/DES-SN5YR) | published stat+sys covariance | `M_B` (abs. mag), light-curve `(α,β)`, host-mass step, per-survey offsets | `M_B` shared with **ladder** (anchor) | `C_SN = Σ_SN⁻¹`; whitening by `C_SN^{1/2} = Σ_SN^{−1/2}` |
| **BAO** | `(D_M/r_d, D_H/r_d)` per tracer bin (~13–15, DESI DR2) | analytic+mock covariance | `r_d` (sound horizon) | `r_d` shared with **CMB**, **ladder** | `C_BAO = Σ_BAO⁻¹` |
| **CMB** | compressed `(R, ℓ_A, ω_b, n_s)` (4) OR native `C_ℓ` TT/TE/EE | compressed covariance / `clik` | foreground/calibration nuisances (native only) | `ω_b, r_d` shared (early-universe) | `C_CMB = Σ_CMB⁻¹` |
| **WL** | `S₈` and/or shear `C_ℓ^{κκ}` band-powers per ℓ-bin (DES Y6 / KiDS / HSC) | shear covariance | `(A_IA, η_IA)` intrinsic alignment, photo-z `Δz_i`, baryon `b` | photo-z partially shared with **RSD** | `C_WL = Σ_WL⁻¹`, `ψ₁(ℓ)`-weighted |
| **RSD** | `f σ_8(z_j)` per z-bin (~6–8, DESI DR2 FS compressed) | mock covariance | growth bias `b_j`, FoG `σ_v` | `(Ω_m)` shared with geometry | `C_RSD = Σ_RSD⁻¹` |
| **ladder** | route posteriors `H₀^{(r,ℓ)}` (§5 / E4) | route-posterior covariance | `M_B`, `r_d`, anchor (Cepheid/TRGB/JAGB), lens-profile (TDCOSMO), siren-cal | `M_B`↔SN, `r_d`↔BAO/CMB | `C_ladder = Σ_ladder⁻¹` |

**Rule.** The *residual* `d`-metric is evaluated in whitened coordinates `C_p^{1/2}(u−v)`; the *Schur blocks*
(§2) use the **un-whitened** `(L_p, D_p)` with `C_p` inside (`K = L_p^* C_p L_p`) — **one** convention,
applied **once**, never doubled. Nuisance parameters are **marginalized** (not fixed) before the per-sector
audit cost is read. Shared
nuisances (`M_B`, `r_d`, `ω_b`, photo-z) are carried in a **joint** vector when two sectors are reconciled
together (this is what makes "one `Ξ`" testable rather than per-probe).

---

## §2 — Schur realization, per sector (closes finding 2, part B)

For each sector `p`, with native readout matrix `L_p` (columns = the **un-whitened** FLRW/GR predictors,
`n_p` of them) and dissolving readout matrix `D_p` (columns = the **un-whitened** enriched/staging-resolved
predictors, `m_p` of them), the audit energy `C_p = Σ_p⁻¹` enters the blocks (the `04` §1.2′ convention —
**do NOT pre-whiten `L_p, D_p` and *also* multiply by `C_p`; that double-counts**):

```
K_LL = L_pᴴ C_p L_p     (n_p × n_p)
K_DD = D_pᴴ C_p D_p     (m_p × m_p)
K_DL = D_pᴴ C_p L_p     (m_p × n_p)   ,   K_LD = K_DLᴴ
Ξ_C^{(p)} = K_DD − K_DL (K_LL)† K_LD = T_{D_p}(I − P_{L_p}) T_{D_p}ᴴ ⪰ 0        (eq. 2, per sector)
```

- `(K_LL)†` is the Moore–Penrose pseudoinverse on the legal quotient (§4.0); when `K_LL` is **positive-
  definite** it is the ordinary inverse (this is the case the **Lean** receipt T3 mechanizes — `05`/finding 16).
- `P_{L_p} = L_p (K_LL)† L_pᴴ C_p` is the `C_p`-orthogonal projector onto the native range; `T_{D_p}` is the
  `C_p^{1/2}`-whitening transport of `D_p`.
- **Typical dimensions (target):** SN `n_p≈2` (FLRW `D_L` shape + amplitude), `m_p≈3` (Ξ terms 0,2 + staging);
  BAO `n_p≈2`, `m_p≈3`; CMB `n_p≈4`, `m_p≈2`; WL `n_p≈1`, `m_p≈2`; RSD `n_p≈2`, `m_p≈2`; ladder `n_p≈1`,
  `m_p = #routes`. These are *pre-registered* shapes; the rank ceiling `G-FORMAL-4` (`≤ ΛCDM+3`, no per-probe
  free `Ξ_p`) still binds the **total** free `Ξ` parameters across all sectors.

**`G-FORMAL-3` tolerance (LOCKED).** The per-sector identity "audit cost `J_p(Δ)` = Schur energy of the
residual readout" is `[C]` numerical with **target `< 1%`** relative. A sector that cannot reach the target
is **not** a program fail: record `‖Ξ_C^{(p)} − audit_cost_p‖` and the **achieved** tolerance, status the
sector `budgeted` (§8). Only `G-FORMAL-1` (Loewner `⪰ 0`) and `G-FORMAL-2` (exact-adequacy ⇒ no rewrite) are
hard.

---

## §3 — Theoretical residuals vs empirical estimators (closes finding 1)

The §4 residuals have a **theoretical** form (used in E0 where the microstate is known) and an **empirical
estimator** (used on real data, where there is no observed microstate). They are kept typographically distinct.

| Residual | Theoretical (E0, `[T]`) | Empirical estimator on real data (`[E]`) |
|---|---|---|
| `δ_p` (macro) | `d(E²x, Ex)` on the toy state | `\widehat{δ}_p` = re-package the FLRW fit through the lens twice — **directly computable from data** (no microstate) |
| `RM_p` | `d(E∘T x, T∘E x)` on the heterogeneous generator | `\widehat{RM}_p` — requires a **declared forward model / microstate proxy**; computed as the whitened gap between (evolve-then-package) and (package-then-evolve) under that model. **NOT read off observations.** |
| `LG_{p,q}` | `d(glue(f_p,f_q), global FLRW)` | `\widehat{LG}_{p,q}` = best-global-FLRW gluing residual on the fitted distance sections — computable from data |
| `PPD_{p→q}` | held-out predictive discrepancy | `\widehat{PPD}_{p→q}` = train on `p`, score held-out `q` posterior-predictive — computable from data |

**Rule.** Wherever a real-data experiment "computes `RM_p`", it computes `\widehat{RM}_p` under a forward
model that **must be declared in the run manifest** (which microstate model, which `T`). The theoretical
identities (`RM_p=0 ⇔ commutation`, `δ_p=0 ⇔ idempotent`) are `[T]`; the numbers on real data are `[E]`.
"Computable from data" = *estimable via the declared model*, never *directly observed*.

---

## §4 — P4: three distinct certificates — two positivity, one stability (closes finding 4)

P4's witness is a **conjunction of three certificates** (two *positivity*, one *stability*), never an
equivalence among them. Throughout, `J^*` is the conjugate-transpose (adjoint; `Jᵀ` in the real case).

1. **P-dens — native-currency density positivity** — `ρ_eff(z) > 0` on the grid, and the audit energy
   `C = Σ⁻¹ ≻ 0`. (`Adequacy_Residuals` / `Needle Killer` membrane positivity.)
2. **P-adeq — rewrite-operator / adequacy positivity** — the symmetrized rewrite `sym_C(R[Ξ]) = ½(R + R^†)`
   in `C`-coordinates is PSD (↔ the Schur adequacy residual `Ξ_C ⪰ 0`, `G-FORMAL-1`): the rewrite adds no
   negative audit-energy direction. **This is a positivity, NOT a stability, certificate.**
3. **S-stab — dynamical stability / no growing mode** — for the **continuous-generator** Jacobian
   `J = ∂f/∂(state)` of the macro-evolution `dstate/d(ln a) = f`, `Re λ ≤ 0` for all `λ ∈ spec(J)`. (For the
   discretized one-step integrator the equivalent criterion is spectral radius `ρ ≤ 1`; the plan uses the
   continuous-generator reading and the run manifest states which.)

**Why positivity (P-dens/P-adeq) ≠ stability (S-stab) — the corrected claim.** "`J` is a *positive* (PSD)
operator on `⟨·,·⟩_C`" means `J^*C + CJ ⪰ 0`, which makes the `C`-energy `x^*Cx` **grow** along trajectories
— i.e. **instability**. Stability is the opposite: `C`-**dissipativity** `J^*C + CJ ⪯ 0`. So a PSD operator
is not a stable one; the old "`Re λ ≤ 0` ⇔ positive operator on the audit-energy inner product" (removed from
`04`) was wrong.

**Certifying S-stab.** Directly (`Re λ(J) ≤ 0`), or via a **Lyapunov** certificate: a positive-definite `C`
with `J^*C + CJ ⪯ 0` ⇒ `Re λ ≤ 0` (audit energy non-increasing). The **Lean** witness (T5) uses a *decidable,
mathlib-free* sufficient condition — **strict Gershgorin diagonal dominance with non-positive real diagonal**
(every disc in the closed left half-plane) — `faithful`; the Lyapunov-PSD route is `narrowed_surrogate`.
`G-FORMAL-14`, `REGISTRY` §11.2, E3 §4.1–§4.2 / `G-E3-CONSTRUCT`, and `06` (`stable_readout`) carry **all
three** certificates. E0's synthetic toy-3 witness carries **P-dens + S-stab** (crossing + density + no
growing mode); **P-adeq** (the Schur-adequacy positivity `sym_C(R)⪰0 ↔ Ξ_C⪰0`) is exercised where the
operator/Schur structure is explicit — **E1/E3** — not in the single-sector toy. The no-negative-kinetic-DOF
/ **ghost-absence** claim remains `out_of_scope` (REGISTRY §5).

---

## §5 — Hubble bridge maps and holonomy eligibility (closes finding 6)

The E4 holonomy `𝔥_γ` is well-defined only once the transported object and bridges are pinned:

- **Transport state vector** (the fiber): `s = (H₀, ν_route)` where `ν_route` carries the route's nuisances —
  `M_B` (Cepheid/SN routes), `r_d` (BAO/CMB routes), anchor zero-point (TRGB/JAGB), lens-profile/time-delay
  parameters (TDCOSMO), siren-calibration (sirens). All routes are lifted to a **common** state space
  `Z = (H₀, M_B, r_d, anchor, lens, siren, Ω_m)` with missing coordinates marginalized — this is the
  `Protocol_Trap` honest internalization `Z = X × Φ` (E4 §4.5), made explicit here.
- **Bridge map** `B_{r→r'}: P(s | r) ↦ P(s | r')` is a **declared, deterministic** push-forward of the
  posterior (carry the shared calibration coordinate forward; re-anchor), **not** a refit. For a (locally)
  affine bridge `s' = A s + b`, the covariance push-forward is `Σ' = A Σ Aᵀ` (general case: `Σ' = J_B Σ J_Bᵀ`
  with `J_B` the bridge Jacobian). The manifest records `A/J_B` and `b` per bridge.
- **Loop holonomy** `𝔥_γ = d( B_{γ#} P(H₀|r₁), P(H₀|r₁) )`, `B_{γ#}` the composed bridges around the loop,
  `d = W₂` (primary) / `D_sym` (secondary), read on the marginal `H₀`.
- **Eligibility (LOCKED).** Only routes that publish (or permit reconstruction of) the **full transport state**
  needed by a loop's bridges are eligible for `𝔥_γ` gates (`G-FORMAL-19`/LP3). A **summary-only** route
  (posterior on `H₀` alone, no transportable nuisances) is statused `budgeted` and **excluded** from holonomy
  loops that require its nuisances; it may still enter the route-structure (LP1) and staging (LP2) tests. A
  loop with `< 3` independent recomputable cells is reported but **not** used as a decisive holonomy gate.

---

## §6 — Canonical formulas & thresholds index (closes findings 3, 9, 10; cross-refs 4, 5)

The single source of truth for the formulas/thresholds that drifted across files. **These values win.**

- **Effective equation of state (P4 / E3 / brief):**
  `w_eff(z) = −1 + ((1+z)/3) · d/dz[ ln ρ_eff(z) ]`  (≡ `−1 − (1/3) · d ln ρ_eff / d ln a`).
  Sanity: `ρ_eff` const ⇒ `w=−1`; `ρ_eff ∝ (1+z)³` ⇒ `w=0`. (Canonical = `04` eq. 19, `E3` eq. E3.1. The
  earlier brief form `(1/3)[−(1+z)/ρ · dρ/dz] − 1` had the derivative-term sign **flipped** — corrected.)
- **IDE continuity (E6 / brief):** `ρ̇_DE + 3H(1+w_DE)ρ_DE = −Q` and `ρ̇_dm + 3H ρ_dm = +Q` (overdot = `d/dt`;
  `w_dm = 0`). The **`(1+w_DE)` factor is mandatory** — dropping it makes DE evolve like dust. In `d/a` form,
  divide the transport by `aH` and keep `(1+w_DE)`.
- **E2 gluing/rewrite/mixture classification (REGISTRY §11.9 — the locked split):** gluing reading
  `F_collapse > 0.5` (>50%); rewrite reading `F_collapse < 0.2` (<20%); mixture `0.2 ≤ F_collapse ≤ 0.5`.
  (The `< 0.3`/`< 30%` numbers previously in E2/07/00/brief were drift — corrected to 0.2/20%.) A clean
  low-gluing result is the valid **rewrite** verdict, **not** a program fail (E2 §8.4/§8.6).
- **OOS pass semantics (REGISTRY §8):** a `win` = strictly beat every alternative **beyond the combined
  uncertainty band** after the complexity penalty. "Within 3%"/"within 10%"/"win or tie"/"≤ best" is a
  **floor = tie = NOT a pass**, anywhere (incl. E1-B's `G-E1-SBT-OOS`). The decisive program-level OOS win is
  `G-E8-OOS-DECISIVE`.
- **P1 biconditional (`04` §6.1):** unconditionally `RM_p > 0 ⇒ splitObs ≠ ∅`; the converse (hence the
  biconditional `splitObs ≠ ∅ ⇔ RM_p > 0`) holds **only under (H-faithful)**: faithful readout + nondegenerate
  audit metric on the legal quotient.
- **Determinism tolerances (REGISTRY §2.1):** deterministic forward-likelihood evals reproduce to `< 1e-12`
  rel (bitwise-class); MAP/`χ²_min` reproduce within optimizer/sampler tolerance (**not** `1e-10`); chains by
  statistical equivalence (R̂, ESS), not bitwise.

---

## §7 — Coherence-amplitude normalization (closes finding 17)

The make-or-break "within **10×**, consistent sign" coherence gate (`G-FORMAL-6`/`-20`, §9.4) compares
amplitudes in a **single shared, dimensionless basis** — it is *not* a comparison of raw kernel outputs
(which carry different units: distances, `fσ_8`, `S₈`).

- **Definition.** Let `a_p` be the coefficient of the **shared rank-`k` `Ξ` mode** obtained by projecting
  sector `p`'s `C_p`-whitened residual onto the (fixed-shape) kernel `K_p`:
  `a_p := argmin_a ‖ C_p^{1/2}(y_p − FLRW_p) − a · C_p^{1/2} K_p[φ] ‖²`, i.e. the least-squares `Ξ`-amplitude
  the data of sector `p` imply through `K_p`. Because all kernels share the **same** basis functions `φ` with
  basis functions `φ` (`04` §3.2–3.3, `G-FORMAL-5` linearity), `a_p` is a **dimensionless** number in common
  `Ξ`-coefficient units across sectors. It is invariant under **probe-unit changes once the shared basis `φ`
  and the whitening convention are fixed** — it is *not* automatically invariant to arbitrary per-kernel
  rescaling, so the basis normalization is **frozen once** (`04` §3.2) and **recorded in the run manifest**;
  a rescaling of `φ` with a compensating rescaling of `a_p` is forbidden by that frozen normalization.
- **Gate (LOCKED).** `1/10 ≤ |a_S / a_{L,M}| ≤ 10` **and** `sign(a_S) = sign(a_{L,M})` (and likewise for the
  growth/Hubble kernels). Equivalently, report each as **whitened predictive displacement per posterior σ**;
  the 10× band must hold in that normalized unit.
- **Sensitivity (mandatory, pre-registered).** Report the coherence verdict at bands **3× / 10× / 30×** and at
  rank `k ∈ {1,2}`; the headline uses **10×**. A verdict that flips between 3× and 30× is flagged
  `moduli`/non-robust, not silently passed.

---

## §8 — Execution-contract patch ledger (this review pass)

Applied across the tree in the same pass that created this addendum. `file → finding`:

| # | File(s) edited | Finding | Change |
|---|---|---|---|
| 3 | `GROUNDING_BRIEF.md` | 3 | `w_eff` sign corrected to the canonical §6 form |
| 7 | `GROUNDING_BRIEF.md` | 7 | E4 pass: reduce std + holonomy, **no Planck-collapse** (lawful plurality) |
| 8 | `E1` §4.2/item-3 | 8 | `G-E1-SBT-OOS`: "within 3%" = tie, **not** a pass (the lone within-3%-pass straggler) |
| 9 | `E2` §8.4/§8.6, `07` rows, `00` E2 row, `GROUNDING_BRIEF` §·| 9 | gluing/rewrite/mixture boundary `30% → 20%` (REGISTRY §11.9) |
| 10 | `GROUNDING_BRIEF.md` | 10 | IDE continuity: restored `(1+w_DE)` + correct conversion |
| 11 | `03` SPT_3G row | 11 | primary data product → **arXiv:2506.20707** (D1) + 2212.05642 (2018); 2601.16277 = framing only |
| 12 | `03` DESI_RSD_FS row | 12 | compressed `fσ_8`+geometry is the **default/primary**; DR1 paper = method control |
| 18 | `E1` `G-E1-REPRO-DET` | 18 | forward-eval `<1e-12`; MAP within optimizer tol; chains statistical (REGISTRY §2.1) |
| 4 | `04` §6.4 + `G-FORMAL-14` | 4 | positivity ≠ stability; Lyapunov framing; **three** certificates required (P-dens ∧ P-adeq ∧ S-stab — see Round 2) |
| 5 | `04` §6.1 + `G-FORMAL-11` | 5 | P1 biconditional conditioned on (H-faithful) |
| 2 | `04` `G-FORMAL-3` + §1 | 2 | per-sector Schur bases frozen here (§1–§2); `<1%` = target w/ `budgeted` fallback |
| 16 | `05` T3 | 16 | `K_LL` PosDef (genuine inverse); singular/pseudoinverse deferred to paper |
| 15 | `05` + `lean-trust-scan.sh` | 15 | prefer `decide`; `native_decide` tracked-and-justified (scanner ≠ prohibition) |
| 14 | `ops/bootstrap/ralph.md` | 14 | P1 = F2's two repairs + operator-rewrite *extension*; P4 stable-readout, ghost out_of_scope |
| 13 | `01-repo-structure.md` | 13 | clarified: experiments don't invoke `ops/` at runtime; `ops/` **is** the mgmt harness above the plan |

### Round 2 — second-review remediation (propagation gaps + two new bugs)

| Area | Files | Change |
|---|---|---|
| **P4 three-certificate propagation** | `REGISTRY` §11.2, `E0` §6(ii), `E3` §4.1/§4.2/`G-E3-CONSTRUCT`, `04` §6.4, this §4 | Named **P-dens ∧ P-adeq ∧ S-stab** (two positivity + one stability); **"no-growing-mode"** denotes the **S-stab** component, while **"stable-readout certificate"** (boolean `stable_readout`) denotes the **full conjunction P-dens ∧ P-adeq ∧ S-stab** (REGISTRY §11.2 v5 — the locked `G-E8-STABLEREADOUT` gate and Lean `PhantomStableReadout` target bind "stable-readout" to the P4 deliverable, so the bundle keeps that name and S-stab is the "no-growing-mode" component); removed the "operator PSD = stability" bundling; declared `J` the **continuous generator** (`Re λ≤0`; discrete one-step map ⇒ spectral radius `≤1`); dropped the "wrong-sign kinetic term" overreach |
| **Schur double-whitening** | this §1 Rule, §2 | `(L_p,D_p)` are **un-whitened**; `C_p=Σ_p⁻¹` enters once via `K=L^*CL` (matches `04` §1.2′) — never pre-whiten *and* multiply |
| **E6 `Q_Ξ` sign** | `E6` (E6-5) | leading term `−(1+z)H·R′ → +(1+z)H·R′`; added the locked derivation + sign-sanity test |
| **DESI_RSD_FS propagation** | `E6`, `E7`, `E8` | compressed DR2 `fσ₈` is the **primary** RSD/MG leg everywhere; DR1 FS `2411.12026` demoted to method control (matches `03` §2) |
| **P1 biconditional propagation** | `E7`, `06` F-5 | unconditional `RM_p>0 ⇒ splitObs≠∅`; biconditional only under **(H-faithful)** (matches `04` §6.1) |
| **Coherence-amplitude invariance** | this §7 | reworded — invariant under probe-unit changes *once basis/whitening are frozen*, not "manifestly invariant to per-kernel rescaling" |
| **Lyapunov adjoint notation** | this §4, `04` §6.4 | `J*C+CJ → J^*C+CJ` (`J^*` = conjugate-transpose) |
| **E2 p-value typo** | `00` E2 row, `GROUNDING_BRIEF` E2 failure modes | the "η-shape uncorrelated" *failure* is `p>0.05` (was `p<0.05`), matching `E2` `G-E2-SHAPE` |
| **RM_p wording** | `04` §4.2 | "computed from data" → via the declared forward/microstate model (estimator `\widehat{RM}_p` on real data) |

> **Reviewer point assessed as a non-defect:** `06-results-manifest.md:147` retains `lambda_min_sym` —
> this is the **legitimate P-adeq field** (rewrite-operator/adequacy positivity, ↔ `Ξ_C⪰0`), not a stale
> stability criterion. Its `G-E3-CONSTRUCT` acceptance check is now relabeled (P-dens/P-adeq/S-stab), so
> the field is correct and kept.

**Deliberately NOT changed (flagged, not edited):**
- **Finding 19** — `idea.md:417` "phantom crossing without ghosts": `idea.md` is the **user's source program**,
  not a plan deliverable. The plan/ops forbidden-token sweep is **clean** (all plan/ops files use the canonical
  "stable-readout / no-growing-mode" terminology; `04` even de-garbles `idea.md`'s original). Editing the
  user's source is out of bounds without the user's say-so.
- **Finding 20** — no Lean project yet: **expected**. `ops/bootstrap/ralph.md` makes Lean scaffold + green
  `lake build` the mandatory **packet-0** before any T1–T7 is accepted. No action.
