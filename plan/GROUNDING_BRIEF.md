# Dense Grounding Brief for Six Birds Cosmology Experiment Architecture

**Date:** 29 May 2026  
**Program:** Resolving the dark-energy paradoxes through six-birds closure audit  
**Status:** Planning checkpoint for experiment operationalization

---

## Part 1: The One-Residual-Nine-Shadows Organizing Logic

The core claim of Six Birds Theory (SBT) applied to cosmology is that a **single cosmological closure residual** appears in nine different observable guises depending on which observational lens and completion choice is used.

### Section 3 Table — Corrected Six Birds Diagnosis Map

| Problem | Six Birds Diagnosis | How the Same Residual Appears | Organizing Principle |
|---------|-------------------|------------------------------|----------------------|
| **Cosmological constant problem** | No-overread / cross-layer descent failure | The observed acceleration term is a cosmological closure residual, not automatically the QFT vacuum-energy scalar. The 10^120 problem dissolves as an unbridged cross-layer identification. | **P1 operator rewrite:** closure correction, not primitive constant |
| **Hubble tension** | Instrument-relative bridge residual; route-mismatch holonomy | CMB-inferred H₀, Cepheid H₀, TRGB/JAGB H₀, inverse-ladder H₀, and standard-siren H₀ are not the same accepted scalar until the cosmological package closure succeeds. Local-local disagreement is **lawful plurality**: structured by route, staging, bridge, and lens-choice. | **P3 route holonomy:** H₀ becomes a field H₀^(r,ℓ) rather than a scalar |
| **DESI evolving dark energy (w(z))** | P1 rewrite term; redshift-dependent closure correction | A homogeneous FLRW completion needs a redshift-dependent operator repair to recover coherence when route mismatch is present. w₀w_a preference is a readout of macro closure failure. | **P1/P4:** redshift-staged rewrite |
| **Distance-duality violation (CDDR)** | Local-global obstruction; gluing residual | SN luminosity distances D_L and BAO angular/radial distances D_M/r_d, D_H/r_d may be locally valid probes but fail to glue into one global FLRW completion. η(z)=D_L/(1+z)²D_A deviation is a measured projection of this gluing failure. | **P5 packaging failure:** metrics don't close globally |
| **Phantom crossing (w_eff < -1)** | Effective-coordinate artifact; readout of closure rewrite, not fundamental | w_eff(z) crossing w=-1 occurs because it is a macro readout of the closure rewrite operator (a stable effective readout / no growing mode), not a fundamental equation-of-state field. The crossing is a coordinate chart of non-closure. This does NOT by itself establish absence of a negative-kinetic (ghost) degree of freedom — that requires a Lagrangian/kinetic-metric framework and is out_of_scope (REGISTRY §5). | **P1:** dark-energy "equation of state" is fiction |
| **S₈ tension (growth/weak-lensing staging)** | Growth-lens staging residual; scale-cut and probe-dependent | Growth (f σ₈ from RSD/BAO) and geometry (Ω_m from BAO distance) are different closure lenses. Weak-lensing scale cuts, redshift calibration, baryonic physics, intrinsic-alignment modeling, and probe-staging all change the effective Ξ_cosmo manifested. The residual is not universal but **staging-dependent**. | **P4/P6:** staging fingerprint; growth ≠ geometry |
| **Coincidence problem** | Late-stage activation threshold; nonlinear structure triggers residual | The closure residual turns on when nonlinear structure formation and coarse-graining failure become cosmologically important (z≲1). The "why now?" is answered: the residual is late because closure failure is late. | **P4/P3:** staging and routing of coarse-graining |
| **Interacting dark sector (IDE/Q term)** | P6 accounting shadow; continuity-equation bookkeeping representation | The fitted energy-transfer term Q_IDE in continuity equations is a **P6 accounting variable**, a ledger representation of the closure residual, not necessarily evidence of a new dark-sector force. When the residual is rewritten as a rewrite operator, energy bookkeeping induces apparent "interaction." | **P6:** energy accounting, not new physics |
| **Modified gravity vs. dark energy** | Descent–Repair Normal Form choice; alternative repairs of failed descent | Modified-gravity parameters (μ, Σ), evolving w(z), IDE interaction, and backreaction terms are **alternative repair charts** under Descent–Repair Normal Form. All repair the same failed FLRW descent; they differ in which layer absorbs the cost. DESI's MG parameter consistency with GR supports the diagnosis that the anomaly is in the **completion layer**, not in local gravitational law. | **P1:** repair choice, not ontology choice |
| **Anthropic retreat; multiverse** | Closure–reality boundary; if measured term is not fundamental, anthropic explanation is unnecessary | If Λ_obs is a closure residual rather than a primitive constant, anthropic selection of the observed acceleration becomes less default. Remains relevant only if true layer-descended cosmological constant survives all audits. The boundary between closure artifacts and reality-level physics must be earned. | **Boundary principle:** closure ≠ ontology |

**Key insight:** Ξ_cosmo(z, ℓ, p) is indexed by redshift z, staging ℓ (scale cuts, smoothing, lens), and probe p (geometry, growth, calibration). The same low-rank residual must repair all nine shadows or Six Birds fails.

---

## Part 2: Nine Experiments — Charters and Operationalized Pass Criteria

Each experiment has:
1. A **charter** (what it tests)
2. An **idea.md pass criterion** (qualitative)
3. **Quantitative gates** (operationalized failure modes)
4. **Cross-experiment constraint** (coherence with other tests)

### E0: Synthetic Demos — Proof of Concept

**Charter:** Six Birds can construct a null-Λ heterogeneous generator (synthetic universe without fundamental dark energy), fit it with homogeneous ΛCDM, recover spurious Ω_Λ > 0, and then reproduce ΛCDM fit quality using only closure-residual rewrite terms. No new degrees of freedom; same parameter count.

**Idea.md reference:** Section 2 (precursor toy result); Section 5 (synthetic experiments).

**Pass criteria (quantitative):**
- Generate toy heterogeneous patch universe with Λ=0 and heterogeneous {ρ_i0, κ_i}
- Fit homogeneous ΛCDM to synthetic distance–redshift data: recover |Ω_Λ| > 0.5
- Construct rewrite term Ξ_cosmo using mismatch diagnostics: route-mismatch RM(x) becomes non-zero when nonlinearity is enabled, zero when linear
- Refit using Ξ_cosmo instead of Ω_Λ: achieve RMSE match to ΛCDM fit (within 5%) using ≤2 free parameters in Ξ
- Demonstrate idempotence defect δ ≈ 0 in rewrite model (closure stabilizes)
- **Failure modes:** Ξ_cosmo requires >2 free parameters per redshift bin → E0 fails; RMSE gap >10% → E0 fails; δ remains >10% of data variance → E0 fails

**Cross-experiment use:** Establishes that the mechanism (coarse-graining → route mismatch → closure residual) is real in a controlled setting. Proves that Ξ_cosmo can be a low-rank object.

---

### E1: DESI DR2 Reproduction (Before and After)

**Charter:** Reproduce DESI DR2's reported (w₀w_a)CDM preference and 3.1–4.2σ dynamical dark-energy signal using standard pipeline (DESI BAO + CMB + SN). Then add Six Birds Ξ_cosmo and test whether it better explains the signal's structure (residuals, posterior-predictive checks, staging dependence).

**Idea.md reference:** Section 1 (DESI reports w₀>-1, w_a<0 at 3.1σ; DESI DR2 is the anchor battleground); Section 6, Experiment 1.

**Pass criteria (quantitative):**
- **Baseline (no SBT):** Reproduce published DESI DR2+CMB contours: (w₀ = -0.92±0.08, w_a = -0.49±0.23) or equivalent per DESI's report arXiv:2503.14738
- **Fit quality metric:** χ² per dof ≤ 1.05 for baseline (w₀w_a)CDM; χ² for (ΛCDMμ=0.67 cm) must be >5% worse
- **Six Birds rewrite:** Fit (\Lambda)CDM + Ξ_cosmo(z) with ≤3 free coefficients (e.g., a₀, a₁, a₂ as in idea.md Section 5); achieve χ² ≤ 0.99 on same data
- **Out-of-sample prediction:** Split DESI+CMB training from SN test; baseline (w₀w_a)CDM prediction error on SN Pantheon+/Union3 distance residuals vs. Six Birds—Six Birds must reduce RMSE by >10% (a within-band tie is not a pass)
- **Phantom-crossing readout:** If DESI data prefer w_eff < -1, show that Ξ_cosmo induces effective crossing with a stable effective readout (no growing mode) (operationalized in E3)
- **Failure modes:** Ξ_cosmo cannot match ΛCDM χ² (>5% worse) → E1 fails; Six Birds parameter count exceeds 4 free params total → E1 fails; out-of-sample SN prediction worse by >15% → E1 fails

**Cross-experiment use:** Establishes that Six Birds can handle the central DESI puzzle and that the residual is not arbitrary but constrained by data.

---

### E2: Distance-Duality as Local-Global Obstruction

**Charter:** Operationalize cosmic distance-duality relation (CDDR) as a local-global obstruction. Fit Ξ_cosmo-augmented models allowing η(z)=D_L/(1+z)²D_A ≠ 1 and test whether: (a) apparent (w_a) signal is a gluing residual, not true evolution; (b) the same Ξ_cosmo from E1 predicts the CDDR structure; (c) model-independent consistency tests (Crossing Statistics et al.) are satisfied.

**Idea.md reference:** Section 3 (distance-duality row); Section 6, Experiment 2; UPDATE section (Hubble as route mismatch).

**Pass criteria (quantitative):**
- **Three models:**
  - M₀: η(z)=1, w=-1 (flat ΛCDM null)
  - M₁: η(z)=1, w₀w_a (standard DESI choice)
  - M₂: η(z)≠1, Ξ_cosmo≠0 (Six Birds gluing)
- **Fit comparison:** Compute Δ(AIC/BIC) for M₂ vs. {M₀, M₁} using DESI BAO + Pantheon+/Union3 SN
- **Six Birds prediction:** Use Ξ_cosmo(z) from E1 (trained on geometry) to predict η(z) shape without refitting amplitude; out-of-sample BIC improvement >5 → pass
- **Gluing residual amplitude (CDDR/local-global verdict, per REGISTRY §11.9):** Measure the share of the apparent w_a signal absorbed by the η≠1 (LG) chart (M2-vs-M1 amplitude share / Δχ²). The **gluing-residual** reading is supported when the η≠1 (LG) chart absorbs the **majority (>50%)** of the apparent w_a signal; the **rewrite** reading when it absorbs a small fraction (<~20%); **mixture** otherwise.
- **Reconcile literature:** Model-independent Crossing Statistics tests (arXiv:2604.19393) vs. Afroz–Mukherjee distance-duality-violation claim (arXiv:2504.16868)—Six Birds must be compatible with whichever is correct, or explicitly diagnose the difference
- **Failure modes:** M₂ is always worse than M₁ (Ξ_cosmo provides no advantage) → E2 fails; gluing residual explains <30% of w_a signal → E2 fails; Six Birds prediction of η(z) structure uncorrelated with observed DESI BAO/SN residuals (p-value <0.05) → E2 fails

**Cross-experiment use:** Tests whether the same Ξ_cosmo from E1 can explain calibration and distance-gluing issues, not just geometry. Operationalizes "local-global obstruction" as a quantifiable phenomenon.

---

### E3: Phantom Crossing with Stable Readout

**Charter:** Demonstrate that Ξ_cosmo (a rewrite operator on the macro closure) can induce an effective w_eff(z) that crosses w=-1 with a stable effective readout (no growing mode). Prove stability of the closed system; show that the crossing is a coordinate artifact, not an instability. (The stronger Lagrangian-level negative-kinetic-DOF exclusion is out_of_scope — see the stability criterion below.)

**Idea.md reference:** Section 4 (phantom crossing); Section 6, Experiment 3; Section 7 (phantom-crossing resolution).

**Pass criteria (quantitative):**
- **Construct effective equation of state:** Using Ξ_cosmo from E1, compute induced w_eff(z) via the macro Friedmann law:
  - Fit homogeneous completion parameters (Ω_m, H₀) from DESI+CMB
  - Add Ξ_cosmo rewrite term to background density ρ_eff(z)
  - Calculate w_eff = (1/3)×[−(1+z)/ρ_eff × d(ρ_eff)/dz] − 1
- **Phantom crossing test:** Show w_eff(z) crosses w=-1 at some z_c (if DESI data prefer crossing); measure crossing redshift z_c and crossing width Δz_c
- **Stability (no-growing-mode) criterion** — per REGISTRY §5, the deliverable is that the rewrite operator Ξ_cosmo is a **positive, stable** endomap on macro state space (a *stable effective readout*, NOT a Lagrangian-level proof of ghost-absence). Operationally:
  - Compute eigenvalues of the Jacobian of the macro evolution with Ξ_cosmo included
  - All eigenvalues must have Re λ ≤ 0 in cosmological forward-time (no growing mode)
  - Native-currency positivity (ρ_eff > 0) on the grid
  - The full **no-negative-kinetic-DOF (ghost-absence)** claim requires a Lagrangian/kinetic-metric framework that this program does not build; it is therefore statused **`out_of_scope`**. "Stable-readout certificate" elsewhere names *this* spectral-stability + positivity check, not a kinetic-sign proof.
- **Stability under perturbation:** Perturb DESI data within 1σ; recompute Ξ_cosmo and w_eff; show that z_c and Δz_c vary by <0.1 in redshift (robust crossing)
- **Alternative: effective scalar-field rewrite** If desired, show that an explicit scalar field with w < −1 is **not** necessary; the macro rewrite Ξ_cosmo achieves the same fit quality with a stable effective readout (no growing mode)
- **Failure modes:** w_eff does not cross w=-1 when E1's Ξ_cosmo is applied (only ΛCDM behavior) → E3 fails if DESI prefers crossing; eigenvalue with positive real part → E3 fails (instability); crossing redshift z_c shifts by >0.5 under 1σ data perturbation → E3 fails (not robust)

**Cross-experiment use:** Tests the claim that the "phantom crisis" is dissolved by treating w_eff as a coordinate artifact, not a fundamental field property.

---

### E4: Hubble Route Matrix and Holonomy (UPDATE: Central Diagnostic)

**Charter:** Build a Hubble route matrix organized by observational routes r and staging/bridge choices ℓ. Test whether disagreement among CMB/BAO, inverse-ladder, Cepheid, TRGB, JAGB, time-delay, and standard-siren (H₀)^(r,ℓ) follows the **lawful plurality** predicted by Six Birds (structured by route and staging, not random noise). Operationalize Hubble holonomy: transport a Hubble posterior around a closed loop of routes and measure non-trivial return (holonomy).

**Idea.md reference:** UPDATE section (Hubble as route-mismatch signature; lawful plurality; Hubble route matrix; holonomy H_γ); Section 10 (hard evidence standard #4: show staging fingerprints).

**Pass criteria (quantitative):**

**4a. Route matrix structure:**
- Assemble posterior on H₀ from: (r₁) CMB→BAO, (r₂) BAO→SN, (r₃) Cepheid→SN, (r₄) TRGB→SN, (r₅) JAGB→SN, (r₆) time-delay lensing, (r₇) standard-siren
- Staging choices ℓ: redshift cuts, host-galaxy cuts, SN sample variant, BAO compression method, CMB dataset (Planck vs. ACT vs. SPT), calibration anchor
- Build matrix entry H₀^(r,ℓ) for each combination
- **Measure route structure:** H₀^(r,ℓ) differences must not scatter randomly. Operationally, run a clustering analysis on {H₀^(r,ℓ)} and test whether routes cluster (same r but varied ℓ should be correlated; different r with same ℓ should separate)
- Classification metric: compute Pearson ρ(H₀^(r,ℓ), H₀^(r',ℓ')) for all pairs; if route-structure is real, then ρ(r=r') > ρ(r≠r') on average (Spearman rank p-value < 0.05 for this separation)

**4b. Staging fingerprints:**
- For fixed r (e.g., Cepheid→SN), vary ℓ (redshift cut z_cut, host cut, SN sample)
- Plot H₀^(r,ℓ) as a function of ℓ parameters; expect structured trajectories (smooth dependence on z_cut, for example), not wild scatter
- Operationalize: fit a low-dimensional model to {H₀^(r,ℓ) | varying ℓ} (e.g., linear model with ℓ as features); out-of-sample R² > 0.7 on held-out routes r indicates **staging fingerprint**
- Compare: null model (H₀^(r,ℓ) = H₀ + ε_random) vs. Six Birds model (H₀^(r,ℓ) = H_closed(0) + K_{r,ℓ}[Ξ_cosmo])
- Six Birds model must have BIC improvement >10 (strong evidence) or >5 (moderate) vs. null

**4c. Hubble holonomy:**
- Define a closed loop of observational routes, e.g., γ = [CMB→BAO] → [BAO→SN] → [SN→Cepheid] → [Cepheid→CMB]
- Each leg transports a Hubble posterior through a declared bridge (e.g., DESI H₀ BAO calibration to SN calibration)
- Measure holonomy H_γ as the KL divergence of the transported-back posterior to the starting posterior: H_γ = KL(P_final || P_start)
- **Null expectation:** H_γ ≈ 0 if routes are globally consistent (all (H₀)^(r) measure the same object)
- **Six Birds prediction:** H_γ > 0 when closure fails; H_γ structure should correlate with Ξ_cosmo and route-mismatch signatures
- Operationally: compute H_γ for multiple route loops and compare to cosmic variance + measurement error; if H_γ >> measurement error, report holonomy

**4d. Closure-transport test:**
- Use the same Ξ_cosmo(z) from E1
- Recompute {H₀^(r,ℓ)} using a corrected FLRW completion that includes Ξ_cosmo
- Test: does the corrected completion reduce route mismatch? Operationally, measure std[H₀^(r,ℓ) | corrected] vs. std[H₀^(r,ℓ) | uncorrected]
- Pass: std[corrected] < std[uncorrected] AND corrected H₀ values cluster with CMB value (Planck H₀ = 67.4±0.5)

**Failure modes:**
- Route structure is absent: ρ(r=r') ≈ ρ(r≠r') (no clustering by route) → E4 fails (supports null model)
- Staging fingerprints fail: out-of-sample R² < 0.5 for ℓ prediction → E4 fails
- Holonomy H_γ is negligible (< 0.1 nats) across all loops → E4 fails (routes already globally consistent)
- Ξ_cosmo does not reduce route mismatch → E4 fails

**Cross-experiment use:** E4 is a **primary diagnostic**. It directly tests the lawful-plurality prediction and operationalizes Hubble holonomy. It serves as the gold-standard test that separates random noise from structured route-dependent closure failure. **All other experiments must be compatible with E4's Ξ_cosmo(z, r, ℓ) structure.**

---

### E5: Growth and Staging Sweep for S₈ (Calibration)

**Charter:** Run weak-lensing (DES Y6, KiDS-Legacy, HSC Y3) and RSD growth measurements under systematic **scale-cut sweeps** and **redshift-binning variations**. Test whether the same Ξ_cosmo from E1 (trained on geometry) predicts growth-sector residuals and whether (S₈) variations are staging-dependent (a growth-closure signature) rather than universal (fundamental constant signature).

**Idea.md reference:** Section 5 (S₈ problem); Section 6, Experiment 5 (growth/staging sweep).

**Pass criteria (quantitative):**
- **Three-way split:** Train Ξ_cosmo(z) on DESI BAO+CMB (geometry only), predict weak-lensing (S₈) and RSD growth without refitting
- **Scale-cut sweep:** For each survey (DES Y6, KiDS, HSC), vary scale cuts ℓ_cut (e.g., k_max from 0.1 to 1.0 h Mpc⁻¹) and measure inferred (S₈)^(ℓ_cut)
- **Null model:** (S₈) is universal; (S₈)^(ℓ_cut) should vary only due to statistical noise (∝ 1/√(information retained))
- **Six Birds model:** (S₈)^(ℓ_cut) = S₈_CMB(θ) + K_S[Ξ_cosmo(z, ℓ_cut)]
  - Compute K_S[Ξ] using the rewrite operator on growth predictions
  - Fit K_S as a low-dimensional function of ℓ_cut and redshift
- **Staging fingerprint:** Plot (S₈)^(ℓ_cut) vs. ℓ_cut for each survey; expect a smooth trajectory if Six Birds is correct (K_S[Ξ] is structured), not white noise
- **Cross-probe comparison:** KiDS-Legacy reports (S₈ = 0.815^{+0.016}_{-0.021}), only 0.73σ from Planck; HSC Y3 with DESI redshift calibration reports (S₈ = 0.805±0.018); DES Y6 is ~1.8σ lower. Test whether the Six Birds Ξ_cosmo explains this spread as staging + survey-specific lens choices
- **Quantitative gate:** Fit a linear model (S₈)^(ℓ_cut) = α + β·ℓ_cut + γ·K_S[Ξ] to combined survey data; compare BIC(Six Birds) to BIC(null). Six Birds must show BIC improvement >10 vs. null, or explain >40% of the variance in {(S₈)^(ℓ_cut)} across {survey, ℓ_cut}
- **Residual reuse:** The amplitude of K_S[Ξ] should be comparable in magnitude to K_L[Ξ] and K_M[Ξ] from geometry experiments (consistency check across observables)
- **Failure modes:**
  - (S₈)^(ℓ_cut) shows white-noise scatter → E5 fails (no staging structure)
  - Six Birds model BIC < null model BIC by <5 → E5 fails
  - K_S[Ξ] amplitude is >10× larger or smaller than K_L, K_M → E5 fails (inconsistent rewrite)

**Cross-experiment use:** Tests whether the residual is truly one (Ξ_cosmo) or whether it fragments into probe-specific corrections. Operationalizes P4 (staging) and shows that growth and geometry close differently.

---

### E6: Interacting Dark Sector (Q) as Accounting Shadow

**Charter:** Fit DESI+CMB data to IDE/S-IDE models (Q ≠ 0) and demonstrate that: (a) the fitted Q term is a ledger representation of Ξ_cosmo, not evidence of a new dark force; (b) growth/probe-split audits show that the same {Ω_m, H₀, σ₈} parameters explain both w(z) and Q when Ξ_cosmo is used; (c) direct measurement of dark-sector coupling via growth-data cross-checks is null (P6 audit fails to find new force).

**Idea.md reference:** Section 7 (interacting dark sector); Section 6, Experiment 6; Section 7 (IDE resolution: Q is a P6 accounting variable).

**Pass criteria (quantitative):**
- **Fit IDE model:** Use DESI DR2 + CMB + Pantheon+ with interacting dark energy; fit w₀, w_a, Q (energy transfer rate)
- **DESI report:** Pan et al. and Silva et al. find mild IDE preference (~1–1.5σ), reducing (H₀) tension to ~2.7σ
- **Six Birds comparison:** Fit Ξ_cosmo (low-rank rewrite) to same data; compare χ² and parameter counts
- **Continuity-equation ledger:** If ρ_DE and ρ_m evolve with interaction:
  - dρ_DE/da + 3ρ_DE = −Q  (energy flows out)
  - dρ_m/da + 3ρ_m = +Q   (energy flows in)
- **Show equivalence:** Construct Ξ_cosmo such that its macro-level rewrite operator induces the same energy-balance equations as the IDE model with Q
- **Operationally:** Solve Friedmann laws with Ξ_cosmo, extract implied dρ_DE/da and dρ_m/da, compute effective Q from balance equations
- **Pass criterion:** Effective Q(z) from Ξ_cosmo must match fitted IDE Q to within 20% RMS error (over z ∈ [0, 2])
- **Growth audit:** Fit RSD growth f σ₈ using both IDE and Six Birds models
  - Train on BAO geometry, predict RSD
  - Out-of-sample prediction error for IDE vs. Six Birds: should be comparable (within 10%) — a **reducibility/comparability** check (Q is a chart of Ξ), NOT a std-3 OOS win; the strict program-level OOS win is decided only at E8 (`G-E8-OOS-DECISIVE`)
  - If Six Birds is better by >15%, IDE model is not needed
- **Direct force test:** If Q represents a real dark-sector interaction, there should be a corresponding modification to lensing and clustering beyond what ΛCDM+rewrite predicts
  - Fit modified-gravity parameters (μ, Σ) in both IDE and Six Birds contexts
  - Constraint (μ, Σ from DESI full-shape + lensing should show: IDE model → (μ, Σ) slightly off GR; Six Birds → (μ, Σ) consistent with GR (since rewrite is in the completion, not in the operator)
  - Measure difference: |μ_IDE − μ_GR| vs. |μ_SBT − μ_GR|; pass if |μ_SBT − μ_GR| < |μ_IDE − μ_GR|
- **Failure modes:**
  - Effective Q from Ξ_cosmo differs from fitted Q by >30% → E6 fails
  - Six Birds prediction of RSD growth is >15% worse than IDE → E6 fails
  - Modified-gravity parameters show same deviation from GR in IDE and Six Birds → E6 fails (no distinction)

**Cross-experiment use:** Demonstrates that the IDE accounting is a **shadow** of closure failure, operationalizing the P6 (accounting) primitive.

---

### E7: Modified Gravity as an Alternative Repair Chart

**Charter:** Fit DESI+CMB+LSS data to modified-gravity theories (f(R), scalar-tensor) and show that: (a) standard tests (μ, Σ parameters) constrain MG to near-GR values; (b) the effective w(z) signal DESI prefers is compatible with MG phenomenology when the metric completion is modified instead of adding dark energy; (c) Six Birds predicts that MG is a **valid alternative repair** if its audits pass.

**Idea.md reference:** Section 8 (modified gravity vs. dark energy); Section 6, Experiment 7; Section 9 (modified gravity as descent–repair choice).

**Pass criteria (quantitative):**
- **DESI MG constraints:** Reproduce published DESI modified-gravity results (arXiv:2411.12026): μ₀ = 0.04±0.22, Σ₀ = 0.044±0.047 (consistent with GR to ~1σ)
- **Scalar-tensor reconstruction:** Fit Brans-Dicke-like ω_BD or other scalar-tensor models to DESI+CMB
- **Effective w(z) under MG:** Compute the effective dark-energy equation of state induced by MG metric modifications (without adding a separate dark fluid)
  - For f(R): effective w(z) arises from the f(R) enhancement to Hubble friction
  - For scalar-tensor: effective w(z) arises from Brans-Dicke coupling
- **Pass criterion:** MG-induced effective w(z) must match DESI-preferred (w₀w_a) contours within the 2σ confidence region (or show that MG can accommodate the signal with reasonable parameters)
- **Cross-predict growth:** Train MG model on CMB+BAO (geometry), predict RSD/weak-lensing growth
  - Out-of-sample RMSE on growth predictions
  - Compare to Six Birds and IDE models from E1, E6
  - Pass: MG prediction within 15% of data constraints
- **AOR audit:** Use the Audited Operational Realisability framework to check whether the MG completion is self-consistent
  - Does metric-modification repair scale to all redshifts without pathology (gradient instabilities, ghost modes)?
  - Operationally: check that the scalar field or f(R) perturbation eigenvalues have no positive-real part up to late times
- **Descent-repair choice:** Show that if Six Birds Ξ_cosmo is successful, MG is **not required**; conversely, if MG is required, it should activate at the same scales and redshifts as Ξ_cosmo
- **Failure modes:**
  - MG-induced w(z) does not match DESI preference (outside 2σ) → E7 still passes (MG is a valid alternative, just not preferred by current data)
  - MG growth prediction >20% worse than Six Birds → E7 fails (repair is not viable)
  - MG shows instabilities (positive eigenvalues) → E7 fails (AOR audit fails)

**Cross-experiment use:** Tests the logical structure that Six Birds claims: the closure failure can be repaired in multiple ways (dark-energy rewrite, IDE interaction, MG modification). The empirical victory condition is that one repair should be **simpler** (fewer free params, lower BIC) and **more auditable** than others.

---

### E8: Model Competition and Meta-Comparison

**Charter:** Synthesize E1–E7 into a **model-comparison matrix**. Rank ΛCDM, w₀w_a CDM, CDDR-only, IDE, MG, and Six Birds (SBT) by multiple criteria: χ² fit, BIC, out-of-sample prediction on held-out probes, staging fingerprints, and audit closure.

**Idea.md reference:** Section 6 (model competition); Section 8, Experiment 8 of original outline; Section 10 (standard of evidence: hard tests).

**Pass criteria (quantitative):**
- **Fit metrics (in-sample):**
  - χ²/dof on DESI+CMB+SN training data
  - BIC = χ² + k log(N) where k = free parameters, N = data points
  - AIC = χ² + 2k
- **Comparison table:** Rows = models {ΛCDM, w₀w_a, CDDR, IDE, MG, SBT}; columns = {χ²/dof, ΔBIC (relative to best), ΔAIC, k (param count), Red. χ² at scale cut}
- **Out-of-sample prediction (cross-probe):**
  - Train on BAO+CMB (geometry only)
  - Predict SN Pantheon+ distances: measure RMSE_SN(model)
  - Train on SN+CMB
  - Predict BAO D_M/r_d, D_H/r_d, and f σ₈: measure RMSE_BAO(model), RMSE_growth(model)
  - **Scorer:** Sum of RMSE_SN + RMSE_BAO + RMSE_growth; normalize by datum count and std of raw data
  - Pass for SBT (std-3, decisive only at `G-E8-OOS-DECISIVE`): a strict OOS **win** — strictly below every alternative beyond the combined uncertainty band AND after the complexity penalty, with no silent loss on a critical leg. `≤1.1× best` (or merely best overall) is a **tie/floor, NOT a pass**
- **Staging fingerprints (P4 test):**
  - For each model, compute coefficient of variation (std/mean) of inferred parameters across scale-cut sweeps (E5)
  - Null expectation (random noise): CV ∝ 1/√(data retained)
  - Six Birds prediction: CV shows structured variation (CV decreases smoothly with ℓ_cut, not white noise)
  - **Metric:** Compute spectral power at low frequencies of parameter-trajectory; SBT should show >2× more low-frequency power than ΛCDM (structured, not noise)
- **Route-mismatch closure (E4/E2 integration):**
  - For each model, compute residual standard deviation of {H₀^(r,ℓ)} across routes and staging
  - ΛCDM/w₀w_a: no explicit route structure; expect std ∼ √(systematic uncertainties)
  - Six Birds: predict std should reduce when Ξ_cosmo is included → measure ratio std[uncorrected]/std[corrected]
  - Pass for SBT: ratio > 1.2
- **Combined ranking:** Assign scores: fit quality (40%), out-of-sample prediction (30%), staging fingerprints (15%), route closure (15%)
  - Normalize each score to [0, 10] (10 = best model)
  - Rank models by final score
  - **Pass for SBT:** Final score ≥ ΛCDM (lower is better in some metrics; reframe as percentile)
- **Bayesian model comparison:** Compute Bayes factor B_{SBT/ΛCDM} = P(D|SBT)/P(D|ΛCDM) using marginal likelihood
  - Pass: log B > 1 (mild evidence for SBT)
  - Strong result: log B > 3 (strong evidence)
- **Failure modes:**
  - SBT BIC >>5 worse than best model → E8 fails
  - Out-of-sample RMSE for SBT >20% worse than best model → E8 fails
  - SBT has >4 more free parameters than ΛCDM with no BIC gain → E8 fails
  - Staging fingerprint absent (low-freq power similar to ΛCDM) → E8 fails

**Cross-experiment use:** E8 is the **final synthesis**. It tests the entire program's claim: that one low-rank residual Ξ_cosmo can explain the major anomalies better (or at comparable quality with fewer parameters) than nine separate phenomenological fixes.

---

## Part 3: The 5 Hard Evidence Standards (Section 10 of idea.md)

All experiments must satisfy these gates. Pre-registered failure modes for rejection:

1. **Reproduce standard results first.**
   - DESI DR2 contours (w₀w_a) must match published ±5% in both axes before Six Birds is added
   - CMB, SN, weak-lensing baselines must agree with SDSS, DES, Planck public values
   - **Operationalization:** χ² per dof < 1.05 on baseline ΛCDM

2. **Use one low-rank residual.**
   - Ξ_cosmo must have ≤3 free parameters in its simplest form (constant, redshift gradient, staging dependence)
   - No probe-specific fudge factors (e.g., different Ξ for weak lensing vs. RSD)
   - **Operationalization:** Total free parameters in SBT model ≤ ΛCDM + 3; if more needed, SBT fails

3. **Win out-of-sample.**
   - Train on geometry (BAO+CMB), predict growth (RSD, weak lensing)
   - Train on growth, predict geometry
   - Train on BAO+CMB, predict SN; train on SN, predict BAO
   - Out-of-sample SBT must be a strict **win** (per REGISTRY §8/§11.4): better than **every** competing model (IDE, MG) by **more than the combined uncertainty band** AND after the complexity penalty, with **no silent loss** on any critical leg (geometry, growth, Hubble). A **tie** (within the uncertainty band of the best alternative) is **NOT a pass**.
   - **Operationalization:** BIC-corrected (complexity-penalized) OOS score must strictly beat every alternative beyond the combined uncertainty band; no "within 3%/10%" pass.

4. **Show staging fingerprints.**
   - A closure residual must vary systematically with scale cuts, smoothing, redshift binning, lens choice
   - A fundamental Λ should not (except through known systematics)
   - **Operationalization:** Spectral analysis of parameter variation across staging sweeps must show >2σ structure (not white noise)

5. **Pre-register failure modes.**
   - E0: Ξ_cosmo parameter count >2, or RMSE gap >10%
   - E1: χ² worse by >5%, or out-of-sample SN worse by >15%
   - E2: gluing residual explains <30% of w_a, or model-independent consistency violated
   - E3: w_eff does not cross (if DESI prefers crossing), or unstable eigenvalue
   - E4: route structure absent, or holonomy <0.1 nats
   - E5: staging fingerprint absent, or BIC worse by >5
   - E6: Q discrepancy >30%, or modified-gravity signature spurious
   - E7: MG instability, or prediction >20% worse
   - E8: final SBT score < baseline ΛCDM, or Bayes factor log B < 0

---

## Part 4: Cross-Experiment Coherence — The Key Constraint

**Central rule:** The one low-rank Ξ_cosmo must explain geometry (E1, E2), growth (E5), Hubble (E4), phantom crossing (E3), accounting (E6), and be compatible with MG repair (E7).

### The Residual-Reuse Matrix

| Experiment | Observable | Rewrite Component | Consistency Test |
|------------|-----------|-------------------|------------------|
| E1 (DESI) | D_L, D_M, r_s | Ξ_cosmo(z) with a₀, a₁, a₂ | χ², BIC, w₀w_a match |
| E2 (CDDR) | η(z) gluing | Ξ_cosmo(z) predicts D_L−D_A mismatch | LG chart absorbs >50% of w_a ⇒ gluing reading (per §11.9) |
| E3 (phantom) | w_eff(z) | Ξ_cosmo induces crossing; eigenvalues stable | w_eff(<−1) at DESI-preferred z_c; stable effective readout (no growing mode) |
| E4 (Hubble) | H₀^(r,ℓ) | Ξ_cosmo(z,r,ℓ) routes and stages | Holonomy H_γ >0; route clustering ρ>0.7 |
| E5 (S₈) | f σ₈, S₈^(ℓ) | K_S[Ξ_cosmo] scales with ℓ_cut | Staging trajectory smooth; amplitude consistent with K_L, K_M |
| E6 (IDE) | Q(z) energy transfer | Ξ_cosmo continuity-eqn ledger | Effective Q matches fitted IDE to ±20% |
| E7 (MG) | μ, Σ modified-gravity | Ξ_cosmo in completion, not metric | MG eigenvalues OK; w(z) matches; RMSE <15% worse |
| E8 (synthesis) | all | Ξ_cosmo overall | BIC, out-of-sample, staging all support SBT >baseline |

**Failure rule:** If any experiment's Ξ_cosmo is inconsistent with another (e.g., E5 K_S amplitude is 100× E1 a₁), **entire program fails**. The tests are not independent; they must form a coherent **audit closure**.

---

## Part 5: The Closure Audit Carrier (AOR)

All results must be recorded in an **Audited Operational Realisability (AOR)** carrier, as defined in Audited_Operational_Realisability.tex.

Structure per experiment:

- **Carrier status:** PreSB (raw fit) → RefStableAOR (E1–E3 pass) → CascadeStableAOR (E4–E7 pass) → AOR (E8 synthesis passes)
- **Residual atlas:** For each fit, record Ξ_SB stratum (adequacy, completion, bridge, operator-rewrite, staging, route-mismatch, local-global, exchange-rate, boundary-layer)
- **Obligation discharge:** Every unresolved tension (e.g., "CDDR inconsistency" from E2) becomes a **statused residual** carrying **exactly one** status from the closed AOR enum of **15 valid statuses** (per REGISTRY §1):
  - **Base (11):** `zero` (no cost), `budgeted` (finite known cost), `bridged` (resolved by Ξ_cosmo), `hidden` (unobserved), `moduli`, `selected`, `probabilistic`, `out_of_scope` (declared irrelevant), `nonclaim` (deliberately not claiming the result), `blocked` (impossible / no recomputable likelihood), `approved_other`
  - **Asymptotic (4):** `asymptotic_budgeted`, `summable`, `contractive`, `eventual_zero`
  - **`unstatused` is NOT a status.** It is a **validator-error sentinel**: any residual that ends a phase tagged `unstatused` is a gate failure (F9, No-Unstatused-Residual). It must never appear inside an accepted-status list. The Lean enum `SBTCosmo.AORStatus` contains the 15 valid statuses only; `unstatused` is modeled as the *absence* of a status, not a constructor. Not-claiming something is represented by the valid status `nonclaim`.
- **Lean mechanization:** For each experiment's pass/fail gate, formalize the condition in Lean 4 and provide a witness term (proof or verified computation)

---

## Part 6: Corpus Papers Used

Grounding references (all Tsiokos 2026):

1. **Foundations IV** (layer-agnostic laws; F2 = source refinement + minimal target coarsening (NOT an operator rewrite); F4 = Local–Global; F9 = No-Unstatused-Residual; F11 = No-Overread / access-quotient)
2. **Adequacy Residuals** (Schur-complement leftover; blind-spot currency; how dissolving probes reveal new physics)
3. **Audited Operational Realisability** (AOR carrier; audit closure; stratum defect; how to record a theory result honestly)
4. **Holonomy with Memory** (route dependence; predictive quotient; fixed-support route transport; how H₀ can vary by route)
5. **Protocol Trap** (separation of holonomy from arrow; why route mismatch ≠ time asymmetry)
6. **To Plot a Stone** (emergent geometry from distance as protocol cost; curvature as loop holonomy)
7. **Dark Energy (Six Birds Eye View)** (precursor: toy generators, synthetic inference, DES pipeline; foundation for E0–E1)
8. **Six Birds for Neutrino Mass** (cross-lens audit template; how to apply audits to cosmological systematics)
9. **Emergence IS the Needle Killer** (layer-dissolving endpoint; how new probes dissolve old obstructions; framework-bound limits)

---

## Final Checklist: What Each Plan File Must Include

Every experiment plan (E0.md through E8.md, and synthesis.md) must contain:

- **Charter:** one-sentence statement of what is tested
- **Idea.md reference:** section/subsection number(s)
- **Corpus grounding:** which papers provide the theoretical foundation
- **Quantitative gates:** at least 3 concrete failure modes (operationalized as χ², BIC, RMSE, or dimensionless metric)
- **Cross-experiment links:** which other experiments must succeed for this one to count as a "pass"
- **AOR status:** what stratum of the residual atlas is tested (adequacy, completion, bridge, operator, staging, route, local-global, exchange, boundary)
- **Null and alternative models:** explicit competing hypotheses and how to distinguish them
- **Data source:** DESI DR2, DES Y6, KiDS-Legacy, HSC Y3, Pantheon+, etc., with version/release date
- **Lean anchor:** reference to a Lean 4 formalization or sketch of how the pass/fail condition would be mechanized
- **Expected failure pattern:** if the test fails, what does that tell us? (e.g., "E3 failure = ghost instability not avoided")

---

## Summary

This brief provides a **dense, operationalized plan** for six-birds cosmology experiments. The eight experiments (E0–E8) are organized around a single closure residual Ξ_cosmo indexed by (z, ℓ, p) and must satisfy cross-experiment coherence constraints. All results are recorded in an AOR carrier, failures are pre-registered, and the final synthesis (E8) ranks six birds against competing models on fit quality, out-of-sample prediction, staging fingerprints, and route closure. The standard of evidence is high: six birds must be simple (≤3 free parameters beyond ΛCDM), auditable (pass all five hard tests), and competitive (a strict out-of-sample **win** in model comparison — a tie is not a pass, per REGISTRY §8/§11.4). This is not a manifesto; it is an **experiment blueprint**.

