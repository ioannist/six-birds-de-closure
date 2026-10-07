# Lean Coverage Table

Packet R2 established the T3 faithful positive-definite Schur core. Packet R3
added the T1 idempotence and T2 route-mismatch faithful mathlib-free receipts.
Packet R4 adds T5 finite P-dens + S-stab and T7 no-unstatused receipts.
Packet R5 adds T4 finite local-global four-status and T6 finite Hubble
holonomy receipts.
Packet R6 strengthens T3 with the P-adeq positivity link under an explicit
Schur-realization congruence and the packaged projection identity.
Packet WP-DERIV-LT2 adds the LT1 structural closure-price capstone witnesses
and Schur-energy Lagrangian pairing.
Review update 2026-10-01: duplicate-free gluing, metric-correct P-adeq, Gram-derived joint PSD, closed route loops, analytic T5 consistency, and scoped background demarcation are now included. Unrestricted general KKT remains outside local mechanization; the original log/quadratic allocation family is now constructed below. The 2026-10-02 support extension below now covers singular native blocks and the full finite real exact-adequacy cycle.

Convention: the numerical data-design block convention is
`K_LL = L^* C L`, `K_DD = D^* C D`, `K_DL = D^* C L`, `K_LD = K_DL^*`,
while the Lean projection realization uses the equivalent operator convention `K_LL=T_L T_L^*` and `K_LD=T_L T_D^*`. The mechanized native block is positive
definite, so `K_LL⁻¹` is the genuine inverse. The singular Moore-Penrose support case is now constructed in `SbtCosmo.Adequacy.Support`. The older `Reconciliation` definitions retain their positive-definite convention.

Kernel axiom closures for delivered theorem declarations are recorded in
`lean/manifests/trust_base.txt`.

| decl | paper_claim | kind | tier | narrowing | experiment | scope_disclaimer |
|---|---|---|---|---|---|---|
| `SbtCosmo.Common.FiniteCarrier` | Shared finite explicit carrier record for mathlib-free receipts | structure | faithful | Finite by explicit exhaustive list, not by mathlib `Fintype`. | E0 toy receipts | Shared vocabulary only; no cosmological claim. |
| `SbtCosmo.Common.Defect` | Shared exact rational nonnegative/separating defect record | structure | faithful | Uses `Rat` rather than mathlib `ℚ` notation to stay mathlib-free. | E0 toy receipts | Abstract defect; empirical metrics remain numerical. |
| `SbtCosmo.Idempotence.Packaging` | T1 idempotent packaging operator `E ∘ E = E` | structure | faithful | Finite carrier supplied by `FiniteCarrier`; no empirical lens asserted. | E0 / Toy-1 | Records hypotheses only. |
| `SbtCosmo.Idempotence.image_eq_fixedSet` | T1 image of an idempotent package equals its fixed-point set | theorem | faithful | Elementary finite-carrier statement; no mathlib dependency. | E0 / Toy-1 | Does not assert any survey packaging map is idempotent. |
| `SbtCosmo.Idempotence.delta_zero_iff_fixed` | T1 idempotence defect vanishes and equivalently the packaged state is fixed | theorem | faithful | Uses an abstract exact rational `Defect`. | E0 / Toy-1 | Certifies structural zero defect only, not numerical tolerance. |
| `SbtCosmo.Idempotence.bool_lumping_delta_zero` | T1 explicit two-state lumping package has zero idempotence defect | theorem/example | faithful | Boolean toy carrier; exact `0/1` defect. | E0 / Toy-1 | Non-vacuity toy only. |
| `SbtCosmo.RouteMismatch.Package` | T2 finite closure package with micro dynamics, packaging, macro dynamics | structure | faithful | Same carrier for micro/macro toy receipt. | E0 / Toy-1 | Records hypotheses only. |
| `SbtCosmo.RouteMismatch.RM` | T2 route mismatch definition `d(E(Tx), Tθ(E x))` | def | faithful | Exact rational defect value. | E0 / Toy-1 | Does not estimate cosmological RM magnitude. |
| `SbtCosmo.RouteMismatch.route_mismatch_nonneg` | T2 route mismatch is nonnegative | theorem | faithful | Immediate from `Defect.nonneg`; no mathlib dependency. | E0 / Toy-1 | Structural positivity only. |
| `SbtCosmo.RouteMismatch.route_mismatch_zero_iff_commutes` | T2 route mismatch vanishes everywhere iff `E∘T = Tθ∘E` pointwise | theorem | faithful | Uses `Defect.zero_iff`; pointwise equality only. | E0 / Toy-1 / P1 | Does not certify a real pipeline commutes. |
| `SbtCosmo.RouteMismatch.route_mismatch_pos_witness` | T2 explicit heterogeneous toy has `RM > 0` | theorem/example | faithful | Two-patch carrier with exact `0/1` defect; proved by `decide`, not `native_decide`. | E0 / Toy-1 / P1 | Non-vacuity toy only; empirical RM shape is numerical. |
| `SbtCosmo.LocalGlobal.GluingRecord` | T4 finite gluing record: global states, local families, compatibility, restriction map | structure | faithful | Uses explicit exhaustive global-state list rather than mathlib `Fintype`. | E2 / P3 / F4 | Structural gluing record only; no real SN/BAO data classification. |
| `SbtCosmo.LocalGlobal.globalizes` | T4 local family globalizes iff it is a restriction of some global state | def | faithful | Existential over the finite global carrier. | E2 / P3 / F4 | Structural predicate only. |
| `SbtCosmo.LocalGlobal.fiberCard` | T4 explicit-list fiber cardinality for a local family | def | faithful | Counts distinct global-list preimages; completeness and `Nodup` are required by `GluingRecord`. | E2 / P3 / F4 | Fiber count for finite Lean records only. |
| `SbtCosmo.LocalGlobal.classify` | T4 classifier by compatibility, image membership, and fiber cardinality | def | faithful | Case split: incompatible / zero fiber / singleton fiber / larger fiber. | E2 / P3 / F4 | Classifier does not run the E2 estimator. |
| `SbtCosmo.LocalGlobal.globalizes_iff_in_image` | T4 local-to-global image criterion | theorem | faithful | `globalizes` and `inImage` are the same restriction-map image predicate; compatibility is the F4 side condition. | E2 / P3 / F4 | Does not assert empirical compatibility. |
| `SbtCosmo.LocalGlobal.fiberCard_ne_zero_iff_globalizes` | T4 nonzero fiber count iff local family globalizes | theorem | faithful | Induction over explicit global-state list plus completeness. | E2 / P3 / F4 | Finite-record image criterion only. |
| `SbtCosmo.LocalGlobal.fiberCard_eq_zero_iff_not_globalizes` | T4 zero fiber count iff local family does not globalize | theorem | faithful | Derived from the nonzero-fiber iff. | E2 / P3 / F4 | Finite-record image criterion only. |
| `SbtCosmo.LocalGlobal.four_status_classification` | T4/F4 four mutually exclusive status normal form | theorem | faithful | Self-derived finite case split on compatibility and fiber count. | E2 / P3 / F4 | Certifies the structural F4 statuses; real `eta(z)` status is numerical. |
| `SbtCosmo.LocalGlobal.cddr_eta_ne_one_compatibleNonGlobal` | T4 SN/BAO CDDR toy: `eta != 1` classifies as compatible-non-global | theorem/example | faithful | One closed FLRW object restricts to `eta=1`; `eta!=1` remains compatible but off image. | E2 / P3 / F4 | Toy CDDR chart only; not a survey result. |
| `SbtCosmo.LocalGlobal.cddr_eta_ne_one_semantics` | T4 semantic predicates for the same CDDR toy | theorem/example | faithful | Direct proof of compatibility and non-globalization. | E2 / P3 / F4 | Interprets `eta!=1` as gluing obstruction, not new dark energy. |
| `SbtCosmo.PhantomStableReadout.Grid3` | T5 finite three-node redshift grid for the Toy-3 witness | inductive | faithful | Exact small grid mirroring Toy-3 structure; not the full 161-node numeric array. | E0 / Toy-3 / P4 | Finite existence witness only. |
| `SbtCosmo.PhantomStableReadout.NoGrowingMode` | T5 rational Gershgorin row-disc no-growing-mode certificate | def | faithful | Sufficient finite algebraic certificate: row center plus radius is `≤ 0`; no abstract spectral theorem. | E0 / Toy-3 / P4 | Certifies S-stab/no-growing-mode only, not P-adeq or ghost absence. |
| `SbtCosmo.PhantomStableReadout.Witness` | T5 finite witness package with `rhoEff`, `wShift = w_eff+1`, and generator | structure | faithful | Uses explicit normalized rationals; analytic consistency of this witness is separately proved in `Derivation.AnalyticReadout`. | E0 / Toy-3 / P4 | Does not certify an analytic log-derivative identity or empirical cosmology. |
| `SbtCosmo.PhantomStableReadout.toy3_crossing_count_one` | T5 finite sampled `w_eff+1` has exactly one adjacent sign change | theorem | faithful | Three-node exact sign-change count; closed by reduction. | E0 / Toy-3 / P4 | Existence/sample crossing only. |
| `SbtCosmo.PhantomStableReadout.toy3_p_dens` | T5 P-dens: all `rhoEff` samples are positive | theorem | faithful | Finite min-positivity encoded as positivity at every grid node. | E0 / Toy-3 / P4 | P-dens only; not P-adeq. |
| `SbtCosmo.PhantomStableReadout.toy3_no_growing_mode` | T5 S-stab: diagonal generator satisfies the rational Gershgorin no-growing-mode certificate | theorem | faithful | Diagonal negative generator; row radii zero. | E0 / Toy-3 / P4 | No-growing-mode only; no ghost-absence claim. |
| `SbtCosmo.PhantomStableReadout.toy3_has_phantom_sample` | T5 witness has a sampled node with `w_eff < -1` | theorem | faithful | Explicit low-grid sample has `w_eff = -10/9`. | E0 / Toy-3 / P4 | Existence/sample result only. |
| `SbtCosmo.PhantomStableReadout.phantom_stable_readout_witness` | T5 finite P4 witness: one crossing, P-dens, S-stab, and phantom sample | theorem | faithful | Conjunction of finite exact receipts; T5 intentionally omits P-adeq. | E0 / Toy-3 / P4 | Not a full `stable_readout` gate, not empirical E3, not ghost absence. |
| `SbtCosmo.Holonomy.RouteGraph` | T6 finite route graph with bridge transports on readout states | structure | faithful | Explicit route/state lists; no mathlib graph library. | E4 / Hubble holonomy | Abstract finite transport graph only. |
| `SbtCosmo.Holonomy.loopTransport` | T6 composed bridge transport along a route loop list | def | faithful | Recursion over a finite route list. | E4 / Hubble holonomy | Does not transport real posteriors. |
| `SbtCosmo.Holonomy.hubbleHolonomyResidue` | T6 exact finite loop residue from a discrete readout defect | def | faithful | Exact `0/1` rational defect on the two-state witness. | E4 / Hubble holonomy | Not a KL/Wasserstein empirical value. |
| `SbtCosmo.Holonomy.injectedRouteDisagreement` | T6 exact injected route disagreement diagnostic | def | faithful | Two cases: zero or nonzero disagreement. | E4 / Hubble holonomy | Toy diagnostic only. |
| `SbtCosmo.Holonomy.hubble_holonomy_nonzero_iff_injected_disagreement_nonzero` | T6 nonzero holonomy residue iff injected route disagreement is nonzero | theorem | faithful | Case split on the injected disagreement parameter. | E4 / Hubble holonomy | Structural iff only; systematics-vs-holonomy is empirical E4. |
| `SbtCosmo.Holonomy.zero_disagreement_zero_holonomy` | T6 zero-disagreement control gives zero holonomy | theorem/example | faithful | Exact finite reduction of the zero case. | E4 / Hubble holonomy | Control witness only. |
| `SbtCosmo.Holonomy.e4_nonzero_holonomy_residue` | T6 nonzero route disagreement gives nonzero residue | theorem/example | faithful | Exact finite reduction of the nonzero case. | E4 / Hubble holonomy | Non-vacuity witness only. |
| `SbtCosmo.Holonomy.route_holonomy_nonzero` | T6 explicit route graph and loop with non-identity composite transport | theorem | faithful | Witness loop `CMB->BAO`, `BAO->SN`, `Cepheid->SN`, back to `CMB->BAO`. | E4 / Hubble holonomy | Certifies nonzero finite holonomy, not real Hubble tension. |
| `SbtCosmo.Holonomy.holonomy_current_trivial_predictive_nontrivial` | T6 current-trivial / predictive-nontrivial loop asymmetry | theorem | faithful | Current quotient forgets the two-state split; predictive quotient retains it. | E4 / Hubble holonomy | Structural lawful-plurality pattern only. |
| `SbtCosmo.Adequacy.Reconciliation.adequacyResidual` | T3 Schur residual definition, positive-definite native block case | def | faithful | Uses total ordinary matrix-inverse notation; the Schur interpretation requires `K_LL ≻ 0`; Singular case is separately covered in `Adequacy.Support`. | all / E1-E3 | Does not compute empirical `Xi_cosmo`; it defines the algebraic finite block residual. |
| `SbtCosmo.Adequacy.Reconciliation.BlockCurrency` | T3 finite block-currency data package | def | faithful | Real finite matrices; positive-definite native block; joint PSD supplied as data. | all / E1-E3 | Does not assert real survey matrices satisfy the hypotheses. |
| `SbtCosmo.Adequacy.Reconciliation.cInner` | T3/P-adeq `C`-inner-product convention | def | faithful | Finite real-vector convention `x^T C y`; no positivity of `C` asserted by the definition. | E1/E3 | Convention only; no P-adeq claim by itself. |
| `SbtCosmo.Adequacy.Reconciliation.cAdjoint` | T3/P-adeq `C`-adjoint convention | def | faithful | Positive-definite inverse convention `C^{-1} R^* C`; Legal audit quotient must be supplied; native-rank singularity is separately covered in `Adequacy.Support`. | E1/E3 | Convention only; no P-adeq claim by itself. |
| `SbtCosmo.Adequacy.Reconciliation.symC` | T3/P-adeq `C`-symmetric readout part | def | faithful | Defines `(R + R^{†_C})/2` in finite real matrices. | E1/E3 | Positivity is certified only by `p_adeq_iff_xi_psd` under realization. |
| `SbtCosmo.Adequacy.Reconciliation.PAdeqRealization` | T3/P-adeq explicit Schur-realization congruence package | structure | faithful | Carries positive-definite `C`, invertible `U`, and `C * symC C R = U^* Xi U`. | E1/E3 | Hypothesis package only; not a theorem for arbitrary rewrite operators. |
| `SbtCosmo.Adequacy.Reconciliation.nativeProjector` | Projection package `P_L = T_L^* (T_L T_L^*)^{-1} T_L` | def | faithful | Genuine-inverse finite package; Singular projector is separately constructed in `Adequacy.Support`. | all / E1-E3 | Convention only; not an empirical projector. |
| `SbtCosmo.Adequacy.Reconciliation.schur_complement_psd_of_joint_psd` | P2/T3: Schur residual is PSD when the joint currency is PSD and `K_LL ≻ 0` | theorem | faithful | Positive-definite native block; singular `K_LL` deferred. | all / E1-E3 | Certifies positivity of the algebraic Schur residual, not empirical adequacy. |
| `SbtCosmo.Adequacy.Reconciliation.adequacy_residual_psd` | P2/T3 packaged PSD receipt for `BlockCurrency` | theorem | faithful | Wrapper around the faithful positive-definite Schur theorem. | all / E1-E3 | Certifies the packaged finite algebraic receipt only. |
| `SbtCosmo.Adequacy.Reconciliation.p_adeq_iff_xi_psd` | P-adeq link `C sym_C(R) ⪰ 0 ↔ Xi_C ⪰ 0` under Schur realization | theorem | faithful-under-hypothesis | Requires explicit `PAdeqRealization`: invertible congruence `C * symC C R = U^* Xi U`, with `C` positive definite; no arbitrary-rewrite claim. | E1/E3 | Positivity certificate only; distinct from S-stab/no-growing-mode and from ghost absence. |
| `SbtCosmo.Adequacy.Reconciliation.projection_identity_packaged` | Projection identity `Xi = T_D(I-P_L)T_D^*` | theorem | faithful | Algebraic finite identity for `K_LL=T_L T_L^*`, `K_LD=T_L T_D^*`, `K_DD=T_D T_D^*` with total inverse notation; intended as the positive-definite inverse package. | all / E1-E3 | Does not cover singular Moore-Penrose support calculus. |
| `SbtCosmo.Adequacy.Reconciliation.projection_identity_packaged_psd` | PSD of the packaged projection side under Schur-core hypotheses | theorem | faithful-under-hypothesis | Assumes `(T_L T_L^*)` PosDef; derives joint Gram PSD and then residual PSD by the Schur core. | all / E1-E3 | Derives joint PSD from the finite Gram construction; does not certify empirical design matrices. |
| `SbtCosmo.Adequacy.Reconciliation.exact_adequacy_easy_chain` | T3 exact-adequacy easy chain: `D0=A*L0` implies factorization and `Ker L0 ⊆ Ker D0` | theorem | faithful | Only the easy direction chain; full DFW cycle deferred. | all / E1-E3 | Does not claim the full exact-adequacy equivalence. |
| `SbtCosmo.Adequacy.Reconciliation.oneByOne` | 1+1 worked block helper | def | faithful | Helper for explicit finite example. | E1 toy split | Helper only; no empirical claim. |
| `SbtCosmo.Adequacy.Reconciliation.worked_example_residual_eq_one` | 1+1 worked Schur residual computes to `1` | theorem/example | faithful | Explicit 1+1 block with native currency `1`, cross `1`, dissolving currency `2`. | E1 toy split | Demonstrates non-vacuity of the algebraic residual only. |
| `SbtCosmo.Adequacy.Reconciliation.worked_example_residual_nonzero` | 1+1 worked Schur residual is nonzero | theorem/example | faithful | Immediate from the computed residual `1`. | E1 toy split | Demonstrates non-vacuity of the algebraic residual only. |
| `SbtCosmo.Adequacy.Support.exact_adequacy_full` | Full four-way exact-adequacy equivalence including singular native rank | theorem | faithful finite real | Actual whitened probe matrices; inverse and projection constructed from spectral theorem. | all / E1-E3 | Legal quotient/empirical whitening and physical probe realization remain external. |
| `SbtCosmo.Adequacy.Reconciliation.minimal_rewrite_selection` | Minimal rewrite selection over the low-rank ansatz | theorem | DEFERRED-R3 | Still not mechanized after R6; no `sorry` stub. Requires finite/compact ansatz selection record. | all / E1-E8 | Empirical scalar objective equivalence remains `[C]`. |
| `SbtCosmo.Derivation.ClosurePrice.KKT1D` | LT1 one-dimensional structural KKT witness record | structure | faithful | Single scalar inequality; records only gradients, feasibility, dual nonnegativity, stationarity, and complementarity. | derivation / Claim S | Structural optimization vocabulary only; no physics bridge. |
| `SbtCosmo.Derivation.ClosurePrice.ActiveConstraint` | LT1 active scalar constraint predicate | def | faithful | Active means scalar constraint value is zero. | derivation / Claim S | Does not imply positive multiplier. |
| `SbtCosmo.Derivation.ClosurePrice.active_zero_multiplier_counterexample_optimizer` | LT1 counterexample optimizer: `x=0` minimizes `x^2` over `x≤0` | theorem | faithful | One-dimensional exact real witness. | derivation / Claim S | Shows the optimization example is real; no cosmological claim. |
| `SbtCosmo.Derivation.ClosurePrice.active_not_implies_positive_multiplier` | LT1 refutes active-implies-nonzero multiplier | theorem | faithful | Active constraint and KKT with multiplier zero. | derivation / Claim S | Blocks overclaiming; no dark-energy claim. |
| `SbtCosmo.Derivation.ClosurePrice.strict_sensitivity_positive_optimizer` | LT1 strict-sensitivity optimizer for `(x-a)^2`, `x≤Omega`, `Omega<a` | theorem | faithful | One-dimensional exact real witness. | derivation / Claim S | Structural nondegenerate case only. |
| `SbtCosmo.Derivation.ClosurePrice.strict_sensitivity_positive_kkt` | LT1 strict-sensitivity positive multiplier witness | theorem | faithful | Multiplier `2*(a-Omega)>0` under `Omega<a`. | derivation / Claim S | Certifies positive structural multiplier only. |
| `SbtCosmo.Derivation.ClosurePrice.schurEnergy` | LT1 scalar Schur energy `tr(W Xi_C)` | def | faithful | Imports validated positive-definite `adequacyResidual`; no physical units assigned. | derivation / Claim S | Audit energy only; not `rho_eff`. |
| `SbtCosmo.Derivation.ClosurePrice.closureLagrangian` | LT1 scalar Lagrangian pairing `J + lambda*(tr(W Xi_C)-Omega)` | def | faithful | Structural scalar budget pairing. | derivation / Claim S | Does not define a Friedmann source. |
| `SbtCosmo.Derivation.ClosurePrice.closure_lagrangian_pairing` | LT1 capstone Lagrangian pairing receipt | theorem | faithful | Definitional equality exposing the `lambda * tr(W Xi_C)` pairing. | derivation / Claim S | Structural dual-certificate statement only; no dark-energy bridge. |
| `SbtCosmo.AORStatus.Status` | T7 canonical 15 valid AOR statuses | inductive | faithful | Contains only valid statuses; `unstatused` is represented by `none`, not a constructor. | all ledgers / F9 | Vocabulary well-formedness only. |
| `SbtCosmo.AORStatus.StatusPackage` | T7 partial classifier plus discipline excluding `none` | structure | faithful | Generic residual type; no finiteness assumption needed for the theorem. | all ledgers / F9 | Does not validate external JSON by itself. |
| `SbtCosmo.AORStatus.no_unstatused_residual` | T7/F9 no unstatused residual and unique valid status per residual | theorem | faithful | Case split on `Option Status`; uniqueness follows from `some` injectivity. | all ledgers / F9 | Structural receipt only; pipeline must still emit the ledger. |
| `SbtCosmo.AORStatus.e0_no_unstatused` | T7 worked E0 synthetic ledger has no `none` statuses | theorem/example | faithful | Four-row E0-style ledger: `zero`, `nonclaim`, `nonclaim`, `approved_other`. | E0 / F9 | Toy ledger only. |
| `per_sector_reconciliation_witness` | Audit cost equals Schur energy per sector | numerical witness | [C] numerical | Not a Lean theorem. Report sector residual and tolerance; target `<1%`, `budgeted` fallback. | all sectors | Depends on empirical `L_p,D_p,C_p`, nuisance marginalization, and residual estimators. |
| `SbtCosmo.LocalGlobal.fiberCard_eq_one_iff_unique_global` | Singleton fiber iff unique global lift | theorem/definition | faithful-under-explicit-hypotheses | Duplicate-free exhaustive global list; semantic uniqueness. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Holonomy.IsClosedLoop` | Matching endpoints on a nonempty route path | theorem/definition | faithful-under-explicit-hypotheses | Both existential holonomy witnesses now carry this condition. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Adequacy.Reconciliation.joint_gram_psd` | Joint Gram PSD from a stacked matrix | theorem/definition | faithful-under-explicit-hypotheses | No joint-PSD hypothesis supplied. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Adequacy.Reconciliation.cInner_symC_eq_energy` | Metric quadratic form equals weighted matrix energy | theorem/definition | faithful-under-explicit-hypotheses | Exact finite matrix algebra. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Adequacy.Reconciliation.p_adeq_quadratic_nonneg` | P-adeq gives nonnegative C-inner-product energy | theorem/definition | faithful-under-explicit-hypotheses | Requires the corrected realization and Xi PSD. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.ClosurePrice.active_kkt_linear_offset` | Active KKT certificate rebases under a linear offset | theorem/definition | faithful-under-explicit-hypotheses | Requires activity and nonnegative rebased price; no physical vacuum theorem. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.ClosurePrice.equality_budget_offset_order_iff` | Equality-budget utility order is offset-invariant | theorem/definition | faithful-under-explicit-hypotheses | Elementary order identity on one fixed budget face. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.BackgroundSelection.two_admitted_values_not_forced` | Two admitted values refute a value forced by that predicate | theorem/definition | faithful-under-explicit-hypotheses | Explicit witnesses supplied; does not forbid an additional selector. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.BackgroundSelection.same_record_different_value_no_factor` | Equal records with unequal values refute record factorization | theorem/definition | faithful-under-explicit-hypotheses | Equal full declared records required; equal audit verdicts alone are weaker. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.BackgroundSelection.background_shift_identity` | Exact sitewise Step26 offset dependence | theorem/definition | faithful-under-explicit-hypotheses | Algebraic potential model; no convergence theorem. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.BackgroundSelection.background_shift_not_scalar` | Nonuniform density makes the offset non-scalar | theorem/definition | faithful-under-explicit-hypotheses | Nonzero coupling/shift and distinct densities supplied. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.AnalyticReadout.rho_positive` | Analytic quadratic density positive | theorem/definition | faithful-under-explicit-hypotheses | Positive density floor and nonnegative curvature. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.AnalyticReadout.rho_hasDerivAt` | Exact derivative of the quadratic density | theorem/definition | faithful-under-explicit-hypotheses | Analytic real theorem, not finite differencing. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.AnalyticReadout.wEff_crossing` | w equals -1 at the density extremum | theorem/definition | faithful-under-explicit-hypotheses | Readout identity; physical conservation/realization not proved. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.AnalyticReadout.wEff_phantom_iff` | Phantom iff below the unique crossing for z>-1 | theorem/definition | faithful-under-explicit-hypotheses | Positive density floor/curvature; analytic sign proof. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.AnalyticReadout.toy3_density_samples_consistent` | T5 samples belong to a single analytic density | theorem/definition | faithful-under-explicit-hypotheses | rho=287/4+16(z-7/8)^2. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
| `SbtCosmo.Derivation.AnalyticReadout.toy3_w_samples_consistent` | T5 w samples are the derivative readout of that density | theorem/definition | faithful-under-explicit-hypotheses | w+1 samples -1/9, 1/27, 9/23; no ghost claim. | review 2026-10-01 | Finite algebra or declared analytic toy only; no physical dark-energy bridge. |
## Additional construction coverage, 2026-10-01

These declarations concern the explicitly added equality-ledger/gauge carriers.
The original Step26 update and physical gravitational bridge are not certified.

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GaugeClosure.ledgerTerm_hasDerivAt`, `quadratic_ledger_unique` | Derive the unique quadratic ledger with the actual background-shift coefficient | Fixing that ledger is added content. |
| `GaugeClosure.objective_shift`, `objective_order_on_ledger`, `optimizer_shift_iff` | Whole optimizer set unchanged on a fixed equality-ledger surface | Existence/strict concavity of the concrete simplex problem are proved in the math note. |
| `GaugeClosure.feedbackForce_shift`, `projected_feedback_blind` | Original feedback force shift lies in an annihilated ledger-normal direction | Pointwise real-coordinate theorem; smooth complex constrained-flow/global existence argument is not locally mechanized. |
| `GaugeClosure.screenedPotential_eq_relative`, `screenedPotential_shift` | Exact compensated potential depends on relative background | Signed equality price; inequality screening still needs active/nonnegative rebasing. |
| `GaugeClosure.simplex_projection_unique`, `projected_gradient_state_shift`, `full_projected_histories` | Actual lawful finite projected-gradient histories agree under any common background shift | Projection records are hypotheses; numerical implementation and analytical convergence are checked separately. |
| `GaugeClosure.record_eq_iff_shift`, `absolute_price_not_descend`, `no_equivariant_absolute_selector` | Maximal gauge quotient, explicit split pair, and no equivariant absolute selector | Does not exclude chosen gauge conventions or unrestricted selectors. |
| `GaugeClosure.allocationKKT_shift`, `realized_pair`, `realized_admitted_prices_not_descend` | Explicit heterogeneous, nonlinear, positive-price KKT-admitted split pair and domain-level non-descent | Concrete strict-concavity/global optimizer sufficiency argument is mathematical, not locally mechanized. |
| `GaugeClosure.history_shift` | Every finite history of any deterministic update on the declared quotient is invariant | Quotient-update scope; actual projected-gradient coverage is proved separately. |
| `PriorObstruction.weighted_ratio_bound` | Finite mixture probability bounded by all group conditional probabilities | Nonnegative weights and positive total mass. |
| `PriorObstruction.base_counts_bound`, `base_prior_cannot_collapse` | Frozen equal-seed base top-decade probability <=8/11<4/5 | Reified rational count premise checked against CSV; fixed full-support band; no upstream ODE interval certificate. |

## Original-carrier coverage, 2026-10-02

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `CPLReadout.density_eq_cpl_product`, `exponent_hasDerivAt`, `density_hasDerivAt`, `fluid_is_log_derivative` | Actual CPL power/product density and exact fluid readout | Fit parameters are supplied empirical inputs; z>-1. |
| `CPLReadout.density_positive`, `density_continuousAt`, `same_history_additive`, `expansion_positive` | Positive regular additive density encodes the same declared history | No physical stability, ghost-absence, or P-adeq bridge. |
| `CPLReadout.crossing_iff`, `exact_crossing`, `phantom_iff` | Exact affine crossing and phantom sign, including degeneracy guard for division | Frozen fit/grid correspondence is separately checked numerically. |
| `WindowRecords.both_tags_iff`, `constant_tags_fail`, `tag_relevance_witness`, `complement_tags_iff`, `collapse_monotone` | Exact Boolean RS predicate, distribution relevance, label complement and collapse inclusion | No assertion that changing tag probability is irrelevant or separately reseeded N populations are nested. |
| `WindowRecords.tag_collapse_iff_max`, `record_iff_threshold` | Actual finite-patch record gate reduces to attained tag maxima and one growth threshold | Attained maxima are supplied by the finite population; growth monotonicity in time is proved in the math note. |
| `WindowRecords.expanding_horizon_iff`, `negative_horizon_tightens`, `base_negative_cutoff`, `base_threshold_growth_bounds` | Horizon sign/scaling and exact reified threshold bounds | Turnaround-erasure toy; actual ODE interval/sensitivity theorem is not locally mechanized. |
| `WindowRecords.population_increment`, `population_monotone_step`, `population_monotone`, `two_patch_probability`, `population_constant_tags`, `population_tag_dependence` | Nondecreasing IID probability expression and tag-dependence witnesses | Probability-law inclusion-exclusion proof is mathematical, not a formal probability-space construction. Fixed-seed sweeps are not population distributions. |

## Singular-native support coverage, 2026-10-02

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `Support.spectralInverse_inner`, `spectralInverse_outer`, `spectralInverse_hermitian`, `spectralInverse_commutes`, `spectralInverse_penrose`, `spectralInverse_unique` | Construct and uniquely identify the real Hermitian Moore-Penrose inverse, including zero eigenvalues | Kernel-checked mathlib spectral theorem import; finite real matrices. |
| `Support.gramInverse_range`, `native_projected`, `projector_hermitian`, `projector_idempotent`, `projector_kernel`, `projector_range` | Actual orthogonal projection onto native row range, kernel equals native kernel | Derived from Gram structure; no supplied projection identity or native positive definiteness. |
| `Support.residual_projection`, `residual_gram`, `residual_error_gram`, `residual_psd`, `exact_adequacy_full` | Singular-support residual positivity and all four exact-adequacy statements | Whitened finite real probes; not an empirical ansatz-to-matrix bridge. |
| `Support.error_native_orthogonal`, `optimal_residual_identity`, `optimal_residual_loewner` | Canonical factor attains the least linear-prediction residual currency | Does not construct arbitrary nonlinear low-rank rewrite selection. |
| `Support.whitened_exact_adequacy`, `weighted_residual_formula`, `weighted_optimal_residual` | Exact return to original probes and weighted block convention | For exact-adequacy return B is invertible; identifying B B* with legal inverse audit energy is separate. |
| `Support.spectralInverse_eq_inverse`, `residual_eq_positiveDefinite` | Exact compatibility with the older genuine-inverse implementation | Compatibility hypothesis is native positive definiteness. |
| `Support.residual_nonzero_iff_blind_witness`, `residual_trace_zero_iff_factor`, `weighted_gram_trace_zero_iff`, `weighted_residual_nonnegative`, `weighted_residual_zero_iff_factor` | Blind native direction iff nonzero residual; faithful scalar audit detects exact adequacy | General nonnegative weights prove nonnegative energy only; zero detects exact adequacy with a positive-definite weight. |
| `Support.nonfaithful_weight_counterexample`, `residual_zero_native`, `rankOne_native_singular`, `rankOne_gramInverse`, `rankOne_adequate_zero`, `rankOne_blind_residual` | Exact extreme-rank and genuinely deficient-rank controls | Kernel arithmetic, no floating approximation or physical interpretation. |

## Original allocation-price coverage, 2026-10-02

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `AllocationPrice.localUtility_hasDerivAt`, `log_tangent`, `local_strong_tangent` | Actual objective derivative and quantitative concave tangent bound | Nonnegative allocations and weights; no supplied optimality. |
| `AllocationPrice.demand_zero`, `demand_positive`, `demand_eq_root`, `demand_rationalized`, `demand_stationary`, `demand_certificate`, `demand_continuous`, `kkt_exists`, `selected_kkt` | Construct a KKT solution for every original finite-family input by clipped root and checked IVT | Positive weights/curvatures, nonnegative budgets; exact real arithmetic rather than a floating error certificate. |
| `AllocationPrice.kkt_strong_support`, `kkt_global_optimal`, `penalty_zero_iff`, `kkt_unique_optimizer`, `price_unique_at_positive_budget`, `kkt_unique` | Global optimality, unique allocation, unique positive-budget price | Zero-budget price uniqueness is false; no Schur-budget or physical bridge. |
| `AllocationPrice.cost_value_support`, `cost_value_derivative`, `strictly_sensitive_price_positive`, `price_antitone` | Actual optimal cost support, derivative-price equality, positive price under negative derivative, budget antitonicity | Derivative theorem explicitly assumes differentiability at B>0; unrestricted convex duality is a separate theorem. |
| `AllocationPrice.below_unconstrained_price_positive`, `below_unconstrained_budget_active`, `above_unconstrained_price_zero`, `slack_price_zero`, `active_offset_kkt`, `positive_patch_prices_equal` | Original active/slack and price/offset signatures | Offset return requires active budget and admissible rebased price; gradient equality requires a positive patch allocation. |
| `AllocationPrice.demo_kkt`, `changed_weights_kkt`, `demo_unique_optimizer`, `price_depends_on_weights`, `negative_offset_slack`, `zero_budget_price_nonunique` | Genuine heterogeneous optimization and exact failure controls | Price value can depend on local objective parameters at the same budget; spatial uniformity does not imply value blindness. |

All 37 new theorem declarations are included in the current 192-theorem raw
axiom audit `axiom_audit_allocation_2026-10-02.txt`.

## Staging-rank coverage, 2026-10-02

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `StagingAudit.component_translation`, `component_denominator_positive`, `common_shift_can_still_fire` | Common estimate shifts cancel at fixed uncertainties, with a nonzero-rejection witness | Not equivariance of actual nonlinear fits under arbitrary data-space injections; no claim of zero population power. |
| `StagingAudit.self_in_upperSet`, `upperCard_positive`, `tail_card_le`, `uniform_index_tail_bound`, `nominal_level_bound`, `rank_zero_never_rejects`, `twenty_null_rank_bound` | Exact inclusive upper-rank counting for all finite real score vectors, including ties | Transfer to a predetermined future index requires exchangeability. |
| `StagingAudit.sum_rankMass_le`, `balanced_rankMass_bound` | Actual weighted finite-law bound under nonnegative normalized weights and equal index marginal masses | Equal marginal masses are explicit hypotheses; actual real-data fitted-anchor exchangeability is not established. |
| `StagingAudit.omission_rejection_iff`, `omission_rejections_eq`, `omission_rejections_card`, `interpolated_counterexample_rate` | Exact legacy-cutoff rejection set {19,20} and rate 2/21>1/20 | Python separately constructs/sorts all actual omitted arrays to establish the interpolation bridge. |

All 16 new theorems are included in the 208-theorem raw axiom audit
`axiom_audit_staging_2026-10-02.txt`. The repaired future-run threshold and
independent validator preserve frozen inputs, finite firing, and measured
detection-grid values. A population-level real-data significance guarantee
is a distinct statistical applicability obligation.

## Imported duality and composition review (2026-10-02)

| decl | paper_claim | kind | tier | narrowing | experiment | scope_disclaimer |
|---|---|---|---|---|---|---|
| `CapacityScale.area_attained`, `area_supergradient` | Finite cut objective and capacity ledger | theorem | constructed finite real | Nonempty finite cut family; nonnegative data needed for nonnegative area. | imported Q5 graph | Scalar area is a dual value, not the incidence vector of edge prices. |
| `CapacityScale.flow_potential_identity`, `flow_cut_weak_duality`, `flow_value_le_area`, `tight_flow_optimal` | Flow/cut LP-duality bridge | theorem | faithful finite real | Capacity bounds, conservation, lawful potentials; the final optimizer return needs a tight feasible flow. | imported Q5 graph | General graph tight-flow existence is not locally mechanized; 254 source instances checked separately with exact rational certificates. |
| `CapacityScale.area_scale`, `area_scale_hasDerivAt`, `area_reparameterized_hasDerivAt` | A scalar price comparable with the closure budget price | theorem | constructed repair | Fixed capacity shape, explicit common scale; derivative at positive scale. | imported Q5 graph | Changed units change the price. No canonical area/multiplier or physical Lambda identity. |
| `CapacityScale.scale_value_attained`, `scale_kkt_optimal`, `scale_kkt_active`, `scale_kkt_slack`, `scale_kkt_boundary` | Active/slack scalar-price structure | theorem | constructed repair | Additional throughput ceiling; zero lower-bound multipliers in a sufficient KKT certificate. | new scale controller | Ceiling is an added constraint; kink prices are nonunique, and active does not imply positive price. |
| `CapacityScale.single_edge_area`, `area_not_individual_price`, `series_path_area` | Distinguish dual value from prices; min-plus path cut law | theorem | faithful finite examples | Actual one-edge / two-edge-path cut families. | exact controls | These are finite graph constructions, not continuum RT. |
| `TensorComposition.input_self_contraction`, `normalized_contraction_gram`, `contraction_entropy_strictly_decreases`, `entropy_not_boundary_minplus` | Universal shared Born/area composition claim | theorem | exact counterexample | Real nonnegative Schmidt-diagonal pair, contracted over one common index and normalized. | exact qubit control | Refutes the proposed universal min-plus entropy law, not all possible composition laws. |

Here `CapacityScale` and `TensorComposition` abbreviate
`SbtCosmo.Derivation.CapacityScale` and
`SbtCosmo.Derivation.TensorComposition`. Full derivations and unresolved original
returns are in `math/IMPORTED_DUALITY_PROOFS_2026-10-02.md`. The original paper is
unchanged. This packet does not promote imported finite recognition to a physical
or continuum identification.

## Adopted mediator strengthening and inherited fork review (2026-10-02)

| decl | paper_claim | kind | tier | narrowing | experiment | scope_disclaimer |
|---|---|---|---|---|---|---|
| `AccessFork.joint_mediator_iff_full_state`, `joint_mediator_iff_injective` | Adopted: every deterministic mediator determining both readouts retains all four coordinates | theorem | exact all-mediator strengthening | Original four-bit carrier; explicit full-state decoder from endpoint decoders; arbitrary record type/map. | source Q1/Q2 | Uniqueness of information partition, not physical architecture. No record-field-count or efficient algorithm claim. |
| `AccessFork.mediator_range_card`, `mediator_card_lower_bound`, `identity_mediator_sharp`, `xorMemory_mediator` | Sharp minimum of 16 distinct records | theorem | faithful finite | Domain has exactly sixteen distinct complete mode states; XOR encoding verifies recoverability meaning. | source Q1/Q2 | An infinite codomain is permitted; exactly sixteen records are realized. Extra raw-field information is outside this domain. |
| `AccessFork.overlapping_readouts_iff_full_modes` | Generic all-four-coordinate retention | theorem | exact generic | Arbitrary coordinate types and carrier; the mode map need not be injective. | field provenance / source Q1 | Recovers all coarse modes, not underlying raw fields unless they are faithfully encoded by those modes. |
| `AccessFork.qm_not_determine_gr`, `gr_not_determine_qm`, `qm_augmented_still_not_determine_gr` | Access fork and failure of redundant shadows to repair it | theorem | faithful original finite | Two explicit split pairs; arbitrary deterministic functions of the existing endpoint record. | source Q1/Q2 | No physical common-carrier or all-quantum-gravity no-go conclusion. |
| `AccessFork.qm_completion_is_conditional_mean`, `gr_completion_is_conditional_mean`, `completion_composition_overlap`, `original_defect_empty` | Original quantize/curve non-commutation import | theorem | exact refutation on declared carrier | Actual uniform Boolean fiber averages; idempotent and commuting on every real observable. | source Q2 | Non-factorization does not imply non-commutation; 0.5 was an encoding-dependent table distance. |
| `FieldAccessBlock.phase_mean_is_conditional`, `geometry_mean_is_conditional`, `phase_mean_idempotent`, `geometry_mean_idempotent`, `commutator_value`, `field_block_conditionals_do_not_commute` | Construct a scoped finite fork with genuine non-commuting completions | theorem | additional provenance-backed finite construction | Source density-4 block has three cells of multiplicity 5,1,3; direct full endpoint triples; uniform weighting of the 54 supplied records. | source Q1 field sample | Potential-only control is material; its deletion restores commutation. Field-to-cell data bridge is exact Python, not Lean reification of complex fields. No physical vacuum-discrepancy bridge. |

Here `AccessFork` and `FieldAccessBlock` abbreviate the corresponding
`SbtCosmo.Derivation` modules. The all-mediator strengthening was explicitly
adopted by the user. The original Boolean completion pair remains commuting;
the new field-record construction is not silently substituted for it.
Detailed scope and evidence are in `math/ACCESS_FORK_PROOFS_2026-10-02.md`.

## Native fixed points and budget demarcation (2026-10-02)

| decl | paper_claim | kind | tier | narrowing | experiment | scope_disclaimer |
|---|---|---|---|---|---|---|
| `GroundState.energy_identity`, `kineticEnergy_nonneg`, `constant_potential_lower_bound` | Native finite Hamiltonian and ground-energy comparison | theorem | exact original matrix | Eight-site periodic cycle; arbitrary real fields and potentials. | original Step26 | Real energy identity; complex ground bridge is written mathematics. |
| `GroundState.normalized_nonnegative_eigen_positive` | Strict positive ground representative | theorem | exact finite child | Normalized nonnegative eigenvector supplied; zero entry propagates around actual connected cycle. | original Step26 | Local theorem proves positivity, not existence or continuity of a ground selector. |
| `GroundState.constant_background_fixed_point`, `all_constant_parameters_admitted`, `constant_background_no_forced_value` | Existential audit does not select a background | theorem | constructed exact sector | Every constant real background and real coupling; explicit unit ground witness and lower energy bound. | exact uniform control | Original nonconstant template is covered by a separate written Brouwer proof, not this sector alone. Does not forbid new selectors. |
| `GroundState.relaxed_fixed_iff`, `normalizedRelaxed_fixes` | Fixed-point existence versus damped solver behavior | theorem | exact explicit maps | Affine equivalence before normalization; normalization preservation of supplied unit fixed point. | relaxation control | No general normalized converse, convergence rate or solver-budget guarantee. |
| `GroundState.relaxed_real_mode_stable_iff`, `unstable_mode_stabilized_by_damping` | Coupling stability alternative | theorem | exact scalar child | Real mode, positive mix; explicit unstable-to-stable control. | analytic Jacobian audit | Spectrum/convergence are not assumed to be mechanized; floating Jacobian bridge is separately checked. Both background and coupling can change stability. |
| Written positive-selector/simplex construction in `GROUND_STATE_PROOFS_2026-10-02.md` | Every finite native background and coupling admits an exact self-consistent ground state | mathematical proof | original native all-parameter | Connected cycle, polynomial real sourcing, compact simplex; verified Brouwer theorem statement and proof source. | original Step26/Step54 | Not a local Lean declaration, not interval-certified floating output, and not a physical Lambda derivation. Refutes an existential coupling boundary. |

Here `GroundState` abbreviates `SbtCosmo.Derivation.GroundState`.
The frozen source's phase-sign error is exhibited and corrected in the local
review helper; historical source and CSVs remain unchanged. See the written
derivation and `results/ground_state_2026-10-02/verification.json`.

## All-parameter native existence and complex return (2026-10-03)

This supersedes the unmechanized all-background and complex-return statuses in
the dated section above. Historical receipts remain unchanged.

| decl | exact return | premises and boundary |
|---|---|---|
| `GroundState.exists_positive_ground`, `positive_ground_unique`, `continuous_positiveGround` | Constructed continuous positive unit ground selector for every real supplied potential | Actual eight-site connected cycle; no existence or continuity premise, no sign constraint on potential. |
| `GroundState.ground_abs`, `lowest_eigen_zero_forces_zero`, `real_lowest_eigen_span` | One-dimensional real lowest eigenspace, including signed vectors | Ground vector in these child lemmas is supplied by `exists_positive_ground` for every potential. Not uniqueness of a nonlinear solution. |
| Imported `Brouwer` | Every continuous self-map of the standard probability simplex has a fixed point | Positive finite size and continuity; vendored Scarf proof checked transitively, not an axiom. |
| `GroundState.exists_selfConsistent_ground`, `every_background_offset_admitted` | Every original real background and coupling admits a positive unit self-consistent lowest eigenvector | Constructed polynomial source map, selector continuity and simplex return. Any nonconstant template and any offset included. |
| `GroundState.background_offset_no_forced_value`, `coupling_no_forced_value` | Existence alone cannot force a unique parameter value | Witnesses constructed at zero and one. Does not forbid additional selectors or imply background-blind dynamics. |
| `GroundState.exists_native_complex_ground`, `complex_lowest_eigen_span` | Exact complex normalization, sourcing, ground eigen equation and minimality against all complex fields; single complex lowest-eigenvalue line | Explicit real/imaginary bridges to the native complex Hamiltonian. No convergence, physical Lambda or continuum theorem. |

The 380-declaration raw receipt includes all 52 new local theorems and imported
`Brouwer`; only the three standard disclosed axioms occur transitively.
Source/license hashes, every port difference and implicit-variable settings are
disclosed in `Gametheory/PROVENANCE.json`. See
`math/GROUND_EXISTENCE_LEAN_2026-10-03.md` and
`results/ground_existence_2026-10-03/verification.json`.

## Exact growth-IVP comparison and record histories (2026-10-03)

This supersedes the earlier unmechanized growth-comparison status. Global
existence, parameter dependence, the infinity limit and the complete continuum
endpoint theorem remain outside this module's local mechanization.

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthComparison.cooperative_nonnegative`, `cooperative_positive`, `cooperative_strict_forcing` | Constructed cone invariance and strict positivity for the forced two-coordinate system | Actual differential equations, compact coefficient bound, source and initial signs; no evolving-coordinate sign premise. |
| `GrowthComparison.coefficient_bounded`, `live_of_horizon`, `scale_log_horizon` | Supplies the comparison theorem's coefficient applicability conditions | Original `lambda>-1/A³`, `a0>0`, `a0 exp(L)=A`; compact bounds constructed for each live lambda. |
| `GrowthComparison.scale_acceleration_bridge`, `log_growth_derivative`, `log_velocity_derivative` | Exact original implemented ODE and chain-rule return | Nonzero scale and live H²; no substituted update law. |
| `GrowthComparison.growth_positive`, `growth_strict_in_time`, `growth_strict_parameter`, `growth_unique` | Signs, strict growth ordering and IVP uniqueness derived for original solutions | `GrowthSolution` supplies continuity, ODE and initial data only. All-lambda existence is still a separate construction. Strict parameter ordering is at positive log scale. |
| `GrowthComparison.matter_solution` | Actual lambda-zero IVP solution `D=v=exp(x)` | Constructed witness; no growth value supplied. |
| `GrowthComparison.ever_collapse_iff_final`, `record_history_iff_threshold`, `record_gate_parameter_downward` | Full continuous collapse-history/threshold equivalence and downward lambda closure of fixed-tag record gate | Nonnegative realized amplitudes, fixed tags, positive attained tagged maxima where used, live solutions. Does not certify floating integrator samples or altered tag distributions. |

Here `GrowthComparison` abbreviates `SbtCosmo.Derivation.GrowthComparison`.
The fresh 408-declaration transitive audit includes all 28 new theorems, using
only the disclosed standard axioms. Self-review and the next explicit IVP
quadrature construction are in `math/GROWTH_COMPARISON_LEAN_2026-10-03.md`;
verification is in `results/growth_comparison_2026-10-03/verification.json`.

## Constructed growth solutions, continuity and scale return (2026-10-03)

This closes the all-lambda existence and continuity obligations in the preceding
dated packet. Differentiability in lambda, the infinity limit, ranked-seed
aggregation and the complete upper-endpoint theorem remain outside this packet.

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthExistence.primitive_derivative`, `growth_derivative`, `velocity_derivative`, `growth_initial`, `velocity_initial` | Explicit integral solution with both exact log-time equations and initial values | Root positivity constructed on the live interval; actual integrability, measurability and FTC hypotheses established, including endpoint derivatives. |
| `GrowthExistence.rootSquared_bridge`, `rate_eq_coefficient`, `constructed_growthSolution`, `exists_growthSolution_of_horizon` | Populates the original IVP for every live lambda | Original scale/horizon inputs only; no supplied solution or desired qualitative property. |
| `GrowthExistence.primitive_continuous_parameter`, `growth_continuous_parameter`, `velocity_continuous_parameter` | Parameter continuity of the exact quadrature | Regularized integral agrees locally on the entire integration interval; no clipped-model substitution. |
| `GrowthExistence.finalGrowth_continuousAt`, `finalGrowth_strictAntiOn`, `finalGrowth_at_zero` | Constructed continuous strictly decreasing endpoint growth and matter control | Nonnegative horizon; positive a0 and positive horizon for strict ordering. |
| `GrowthScaleReturn.native_growth_derivative`, `native_velocity_derivative`, `exists_original_scale_solution` | Returns constructed existence to both implemented scale-factor equations and native initial values | `a0>0`, `A>=a0`, `lambda>-1/A³`; both inverse chain rules checked. |
| `GrowthScaleReturn.native_positive`, `native_endpoint_continuousAt`, `native_endpoint_strictAntiOn` | Positive native solution and continuous strictly decreasing original endpoint | No assumed family, signs or monotonicity. Strict parameter comparison requires `A>a0`. |

Here both namespaces are below `SbtCosmo.Derivation`. The fresh 444-declaration
audit includes all 36 new theorems with only the standard disclosed axioms.
Derivation, self-review and remaining construction are in
`math/GROWTH_EXISTENCE_LEAN_2026-10-03.md`; current receipts are in
`results/growth_existence_2026-10-03/`.

## Quantitative infinity limit and exact native record window (2026-10-03)

This closes the infinity-limit and unique threshold-endpoint obligations of the
preceding packet. It does not reify the twelve populations or construct their
aggregate rank, and does not certify the floating edge location.

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthLimit.forced_free_bound` | Forced free ODE with zero initial differences gives `0<=D(x)<=epsilon*x/2` | Continuous solutions and both derivative equations; forcing in `[0,epsilon]`. Signs are derived through the cone lemma. |
| `GrowthLimit.coefficient_nonnegative_bound`, `growth_matter_bound`, `growth_free_bound` | Supplies actual IVP forcing bounds and quantitative error from the finite-start limiting solution | Positive a0, nonnegative horizon and lambda; matter control is the exact IVP, not a substituted a=0 growing mode. |
| `GrowthLimit.finalGrowth_free_bound`, `finalGrowth_tendsto_atTop` | Exact endpoint error bound and limit `3/2-exp(-2L)/2` | No supplied limiting-growth hypothesis; positive a0 and nonnegative L. Zero-length horizon allowed. |
| `GrowthWindow.exists_unique_positive_endpoint`, `exists_unique_threshold_window` | Constructs a unique positive threshold endpoint and exact half-open log-scale window | Positive a0 and L; `Ginf<T<exp(L)`; exact horizon identity. Continuity, ordering, limit and live region are proved inputs. |
| `GrowthWindow.live_iff_horizon`, `exists_unique_native_threshold_window` | Original live cutoff and original scale-factor window | Positive a0, `A>a0`, `Ginf<T<A/a0`. Threshold equality included; turnaround equality excluded. |
| `GrowthWindow.native_ever_collapse_iff_final`, `native_record_history_iff_threshold`, `exists_unique_native_record_window` | Original continuous collapse history and fixed-tag record-bearing window | Nonnegative amplitudes, fixed tags, positive attained maxima; explicitly stated threshold inequalities. No claim that sampled random draws or the aggregate rank have been reified here. |

All names above are under `SbtCosmo.Derivation`. The fresh 461-declaration audit
includes all 17 new theorems with only the disclosed standard axioms. See
`math/GROWTH_WINDOW_LEAN_2026-10-03.md` for the proof, target return and
adversarial self-review, and `results/growth_window_2026-10-03/verification.json`
for verification. Earlier dated receipts remain historical evidence.

## Original twelve-seed aggregate window and input reification (2026-10-03)

This closes the original fixed-population aggregate-rank obligation. The exact
continuous ODE model and reified input realization are proved in Lean; NumPy
input provenance is checked by reproducible generation and separate capture
of the original sampler. Numerical integration accuracy and physical return
are not inferred from these proofs.

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthPopulation.finite_attained_maximum`, `exists_positive_tagMaximum` | Constructs maxima in the actual finite carrier | Nonempty finite set; a positive patch of the given tag for positivity. No supplied maximum witness. |
| `GrowthPopulation.passingCount_iff_rank`, `exists_count_threshold` | Seed-count gate is precisely the k-th threshold inequality, with ties retained | Rank counts are explicit in the first theorem and constructed in the second for `0<k<=number of seeds`; candidate set deduplication never deduplicates seed counts. |
| `GrowthPopulation.native_record_count_eq`, `native_aggregate_iff_threshold`, `exists_unique_native_aggregate_window` | Returns continuous native histories and count aggregation to the exact half-open window | Explicit fixed population, positive tagged maxima and finite rank certificates; the ODE solution, signs, limit and endpoint are constructed. |
| `WindowSampleData.rational_maxima_certificate`, `rational_threshold_certificate`, `rational_rank_certificate`, `rational_window_bounds` | Exact finite population, maxima, thresholds, counts 9/10 and threshold bounds | Explicit 12×64 IEEE rational inputs and Bool tags; checked with `decide +kernel`, not `native_decide`. No formal RNG-law claim. |
| `WindowSample.sampled_maxima`, `seedThreshold_eq`, `sampled_rank_counts`, `sampled_count_iff_threshold` | Transfers every finite certificate to the original real growth domain | No supplied seed population property or rank assumption. |
| `WindowSample.seed_fraction_iff`, `realized_gate_iff_seed_fraction`, `realized_gate_iff_threshold` | Original 80% gate is ten passing seed histories and one exact threshold | Declared decimal parameters; both tag values are required in every passing seed. The expanding-branch cutoff is excluded at equality. |
| `WindowSample.exists_unique_realized_window` | Original fixed twelve-seed realization has a unique positive endpoint and gate `(-1/8000,upper]` | No theorem hypotheses; explicit input realization and decimal model constants. NumPy-to-input provenance is computationally checked, not a Lean RNG proof. No interval-certified numeric edge or physical Lambda claim. |

All names above are under `SbtCosmo.Derivation`. The fresh 484-declaration audit
includes all 23 new theorems with only the disclosed standard axioms. Derivation,
provenance boundary and adversarial self-review are in
`math/WINDOW_POPULATION_LEAN_2026-10-03.md`; current receipts are in
`results/window_population_2026-10-03/`. Earlier dated receipts remain
historical evidence.

## Constructed endpoint and population sensitivity (2026-10-03)

This packet mechanizes continuity and ordering for the actual boundary function
and fixed-tag population perturbations. Smooth sensitivity remains a separate
obligation; continuity and Lipschitz threshold maps do not establish it.

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthRankSensitivity.rankThreshold_spec`, `rankThreshold_eq_of_certificate` | Constructs the finite rank function and identifies any correct rank certificate | `0<k<=number of seeds`; the earlier finite construction supplies the rank. |
| `GrowthRankSensitivity.rankThreshold_abs_le`, `rankThreshold_lipschitz`, `rankThreshold_mono`, `rankThreshold_mul_pos` | Uniform perturbation bound, global 1-Lipschitz stability, monotonicity and positive homogeneity | Finite maximum metric; ties retain seed multiplicity and introduce no jumps. No derivative claimed. |
| `GrowthEndpointSensitivity.endpoint_spec`, `endpoint_continuousAt`, `endpoint_strictAntiOn` | Constructed unique positive endpoint, continuous and strictly decreasing with threshold | Positive a0,L and `Ginf<T<exp(L)`. No assumed inverse, monotonicity or continuity field. |
| `GrowthEndpointSensitivity.endpoint_strict_horizon` | Positive edge increases with available log-scale horizon | Same threshold admissible at both positive horizons; coefficient and finite-start IVP unchanged. |
| `GrowthPopulationSensitivity.tagMaximumValue_spec`, `tagMaximumValue_positive`, `tagMaximumValue_lipschitz` | Constructed attained tagged maxima, positive when a positive patch exists; global 1-Lipschitz stability | Fixed tags. Empty tag sets have fallback zero only in the total definition; record theorems require positive tagged patches. |
| `GrowthPopulationSensitivity.aggregateThreshold_continuousAt`, `populationEndpoint_continuousAt`, `populationEndpoint_native_window` | Actual amplitude/delta perturbations return to the native aggregate record boundary | Continuous inputs, nonzero tagged maxima and admissible rank threshold; native applicability additionally uses nonnegative amplitudes and positive patches of both tags. Ranking/maximizing-patch switches allowed. |
| `WindowSensitivity.scaled_aggregate_threshold`, `scaled_endpoint_native_window` | Original fixed realization under exact common amplitude rescaling has `T=T0*delta/(delta0*s)` and its native window | Positive delta and scale, admissible threshold. Preserves reified tags/amplitudes; not a proof about independently rounded or reseeded populations. |
| `WindowSensitivity.robustness_rectangle_admissible`, `robustness_rectangle_native_window`, `scaled_endpoint_continuous_rectangle`, `scaled_endpoint_strict_delta`, `scaled_endpoint_strict_amplitude` | Entire declared delta/scale rectangle has an exact record window, continuous endpoint and strict directional ordering | `delta in [1.2,2]`, `s in [1/3,3]`; threshold applicability derived from checked original inputs. Fixed a0=1/1000,A=20; no smoothness, N-continuity or interval-certified edge claim. |

Names are under `SbtCosmo.Derivation`. All 40 new theorems are covered by the
fresh 524-declaration standard-only transitive audit. Derivation and adversarial
self-review are in `math/WINDOW_SENSITIVITY_LEAN_2026-10-03.md`; current
verification is in `results/window_sensitivity_2026-10-03/`.


## Actual parameter derivatives and C1 endpoint return (2026-10-03)

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthParameter.primitive_parameter_differentiation` | Differentiates the actual integral and constructs integrability of its derivative | Nonnegative time and positive final root square; uniform parameter/time margin and domination derived. No supplied differentiability or bound. |
| `GrowthParameter.growth_parameter_derivative`, `velocity_parameter_derivative` | Explicit parameter derivatives of the same finite-start growth/velocity family | Nonnegative time, positive root square. No clipping of the model. |
| `GrowthParameter.growthParameter_time_derivative`, `velocityParameter_time_derivative` | Actual sensitivities satisfy the variational ODE | Live root on [0,L]; direct product/quotient/FTC proof, no assumed mixed-derivative interchange. |
| `GrowthParameter.sensitivity_strict_negative`, `finalSensitivity_negative` | Both sensitivities strictly negative at positive time; G'(lambda)<0 | Live original IVP; positive a0 and positive final time for lambda derivative. Zero at initial time proved separately. |
| `GrowthParameter.native_parameter_derivative`, `native_velocity_parameter_derivative` and their negative-derivative theorems | Returns lambda derivatives to original D(a) and p(a) on the whole native live horizon | a0>0, A>=a0, lambda>-A^-3, a in [a0,A]; strict negativity needs a>a0. |
| `GrowthParameter.finalSensitivity_continuousAt`, `GrowthEndpointDerivative.finalGrowth_c1` | Continuous final parameter derivative and C1 growth on the entire open live domain | a0>0, L>=0 for C1 domain; root margin locally derived. No spectral or physical statement. |
| `GrowthEndpointDerivative.endpoint_parameter_derivative`, `endpointSensitivity_negative`, `endpoint_c1` | C1 unique positive endpoint, E'(T)=1/G'(E(T))<0 | a0,L>0 and Ginf<T<exp(L); inverse existence/continuity and nonzero derivative derived. No claim at inadmissible fallback/boundary thresholds. |
| `GrowthEndpointDerivative.scaled_endpoint_delta_derivative`, `scaled_endpoint_amplitude_derivative` and their sign theorems | Exact strictly signed partial derivatives for the original coupled rescaling | s>0, admissible threshold; positive delta for amplitude sign. Same reified inputs and fixed tags. |
| `GrowthEndpointDerivative.scaled_endpoint_c1`, `robustness_rectangle_c1` | Full two-variable C1 dependence, at every rectangle point including boundaries | delta in [6/5,2], s in [1/3,3]; admissibility derived from original exact population. No smoothness in discrete N, arbitrary reseeding, arbitrary rank switches, or infinite-order claim. |

Names are under `SbtCosmo.Derivation`. The full 8073-job default build and
564-declaration standard-only axiom audit cover all 40 new theorems. Twenty-five
exported statements are checked separately. Derivation and adversarial
self-review: `math/GROWTH_PARAMETER_LEAN_2026-10-03.md`; fresh receipts:
`results/growth_parameter_2026-10-03/`. Historical packets remain unchanged.


## Certified native-quadrature endpoint bracket (2026-10-03)

| decl | exact return | premises and boundary |
|---|---|---|
| `GrowthQuadrature.primitive_native_bridge`, `native_growth_quadrature` | Exact original-scale growth integral with finite-start term and prefactor retained | a0>0, A>=a0, lambda>=0; positive-edge scope. Earlier full live-domain results retain their domains. |
| `GrowthQuadrature.density_cell_bounds`, `integral_grid_bounds` | Whole-cell rational square bounds return to the entire integral | Nonnegative lambda, positive ordered grid, both cell inequalities; no unsampled interpolation or monotonicity of the density assumed. |
| `GrowthQuadratureData.grid_endpoints`, `lower_cells`, `upper_cells`, `lower_sum`, `upper_sum` | Exact 264-cell certificates with integral lower 2227/10000 at lambda=3 and upper 187/1000 at lambda=4 | Generated Fraction/isqrt arithmetic; all data claims proved by decide +kernel. No RNG or ODE solver dependency. |
| `WindowEdgeCertified.native_growth_at_three_lower`, `native_growth_at_four_upper`, `sampled_threshold_tight_bounds` | D(3)>964, D(4)<936 and 960<T*<961 | No theorem hypotheses; actual IVP family and original reified population. |
| `WindowEdgeCertified.upper_certified_bounds`, `upper_eq_scaled_endpoint` | 3<upper<4 for the same earlier C1 endpoint at the original inputs | Unique root, exact quadrature certificate and original rank derived; no supplied bracket. |
| `WindowEdgeCertified.paper_bracket_certified`, `paper_inside_outside`, `inside_three_outside_four` | Exact original 2.33/5.31 inside/outside witnesses and stronger 3/4 witnesses | Exact decimal rationals and continuum native history gate; does not certify SciPy total correctness or individual-seed uniform verdicts. |
| `WindowEdgeCertified.exists_unique_certified_window` | Unique original aggregate continuum window (-1/8000,upper] with 3<upper<4 | No theorem hypotheses; all exact input and endpoint obligations discharged. No physical Lambda or integrated crunch claim. |

Names are under `SbtCosmo.Derivation`. The full 8076-job build, fresh
593-declaration standard-only axiom audit and 23 exported statement checks
cover this packet. Exact generation replay and the false-certificate control
pass. Proof and adversarial self-review: `math/GROWTH_QUADRATURE_LEAN_2026-10-03.md`;
receipts: `results/growth_quadrature_2026-10-03/`. Historical packets are retained.

## Original first-collapse and ratio return (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthFirstRecord.exists_unique_first_time`, `firstTime_spec`, `firstTime_iff_threshold` | Constructed unique first threshold time and all-time collapse equivalence | Positive initial scale, ordered horizon, lambda>=0, threshold>1 and reachable by horizon; no supplied time witness. |
| `GrowthFirstRecord.any_patch_collapse_iff`, `firstTime_lower_matter`, `firstTime_strict_parameter` | Attained amplitude maximum, matter-bound time lower bound and strict parameter ordering | Nonnegative actual growth, positive attained maximum; reachability premises explicit in general API. |
| `WindowFirstRecordData.first_threshold_bounds`, `lower_cells`, `lower_sum` | All twelve original first thresholds in (500,897); exact 384-cell prefix bound >=204/1000 | Unchanged original population imported, natural adjacent indices, every cell/sum checked with decide +kernel. |
| `WindowFirstRecord.maximum_spec`, `time_iff_any_collapse`, `time_is_first_collapse` | Actual earliest collapse of ANY original patch, with all maximum/reachability premises derived | Every original seed, 0<=lambda<=3; first time differs from the both-tag gate time. |
| `WindowFirstRecord.ratio_density_readout`, `ratio_strictMono`, `ratio_upper_sharp` | Exact original matter ratio, strict increase, R<=8*lambda | Native declared units and exact continuum IVP; no SciPy error/interpolation certificate. |
| `WindowFirstRecord.ratios_arbitrarily_small`, `ratio_zero`, `gate_on_interval` | All twelve ratios simultaneously arbitrarily small at positive lambda with aggregate gate passing; zero case and gate on [0,3] | No universal positive coincidence pinch; no measure/typicality conclusion. |
| `WindowFirstRecord.ratios_at_three`, `ratios_one_to_three`, `three_near_upper` | 3/8<R(3)<=24 and 1/8<R<=24 on [1,3]; 3 above 75% of endpoint | Original population; exact endpoint ratio and arbitrary-population bounds not asserted. |

Names are under `SbtCosmo.Derivation`. The 8079-job default build, fresh
629-declaration standard-only axiom audit and 36 exported statement checks cover
all 36 new theorems. Exact generator byte replay and false-certificate control
also pass. Derivation: `math/FIRST_RECORD_LEAN_2026-10-03.md`; receipts:
`results/first_record_2026-10-03/`. Historical evidence is retained unchanged.

## Actual positive endpoint ratio (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthQuadratureSharp.densitySquare_derivative`, `density_monotone`, `density_antitone` | Actual squared-integrand derivative and derived increase/decrease on either side of 2*lambda*a^3=1 | Nonnegative scale and lambda, denominator strictly positive; actual mean-value hypotheses proved. |
| `GrowthQuadratureSharp.density_global_upper`, `density_cell_lower`, `density_cell_upper`, `integral_grid_bounds` | Correlation-preserving whole-cell enclosures and their actual integral return | Both lower endpoints; upper endpoint with side condition or global peak; positive lambda for global-peak/upper law. |
| `WindowEndpointRatioData.grid_endpoints`, `lower_cells`, `upper_cells`, `lower_sum`, `upper_sum` | 704 exact horizon cells, 512 exact prefix cells and rational sums | Same grid, natural adjacent indices, decide +kernel; no native_decide or disabled linter. |
| `WindowEndpointRatio.integral_prefix_lower`, `integral_horizon_upper`, `prefix_growth_lower`, `horizon_growth_upper`, `upper_tight_bounds` | D(17/5,5/2)>901, D(17/5,20)<960 and 3<upper<17/5 | Exact finite-start term, same original endpoint; no supplied numerical bracket/error/solver law. |
| `WindowEndpointRatio.time_spec`, `time_iff_any_collapse`, `time_is_first_collapse`, `time_lower`, `time_upper` | SAME first-time function returns actual earliest original patch collapse with time in (1/2,5/2] | Entire [0,upper], every original seed; fallback excluded by derived reachability. |
| `WindowEndpointRatio.time_strictMono`, `ratio_strictMono`, `ratio_upper_linear` | Strict first-time and ratio ordering; R<=125*lambda/8 | Nonnegative admitted parameter domain; no rank-switch derivative or assumed time continuity. |
| `WindowEndpointRatio.endpoint_ratios`, `near_edge_ratios`, `positive_window_ratios` | 3/8<R<425/8 at actual endpoint and on [3,upper]; R<425/8 on entire nonnegative admitted window | Original fixed population/native units; no arbitrary-population, sampled-statistic, measure or physical claim. |

Names are under `SbtCosmo.Derivation`. The full 8082-job default build,
663-declaration standard-only axiom audit and 34 exported statement checks cover
all 34 new theorems. Exact generator byte replay and both false-certificate
controls pass. Derivation: `math/ENDPOINT_RATIO_LEAN_2026-10-03.md`; receipts:
`results/endpoint_ratio_2026-10-03/`. Earlier evidence packets are retained.

## First records throughout the original signed window (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthFirstRecordLive.native_initial`, `exists_unique_first_time`, `firstTime_spec`, `firstTime_iff_threshold` | Actual unique threshold root on the full live native interval | Positive ordered scale interval, lambda>-1/A^3, 1<T<=D(A); actual reachability explicit in general API. |
| `GrowthFirstRecordLive.firstTime_eq_nonnegative`, `native_matter_at_zero`, `native_matter_lower`, `firstTime_nonpositive_upper`, `firstTime_at_zero` | Equality with prior positive choice, exact finite-start matter comparison, nonpositive time bound and exact zero time | Both defaults excluded on overlap; shorter-horizon cutoff derived; lambda<=0 comparison reversed correctly. |
| `GrowthFirstRecordLive.firstTime_strict_parameter`, `WindowSignedRecord.time_strictMono` | Strict increase of first time across the entire signed admitted domain | Actual parameter/time ordering and positive root; no full signed ratio ordering inferred. |
| `WindowSignedRecord.gate_iff_window`, `final_above_threshold`, `time_spec`, `time_iff_any_collapse`, `time_is_first_collapse` | Every original seed's actual earliest patch collapse throughout (-1/8000,upper] | Checked all-patch threshold below original aggregate threshold; gate premise, no supplied first-time witness. |
| `WindowSignedRecord.time_at_zero`, `time_nonpositive_small`, `negative_ratios` | Exact zero time T_first/1000; negative first time <897/1000 and 0<R<1/8000 | Admitted parameters only; no records-before-erasure claim for excluded histories. |
| `WindowSignedRecord.time_eq_nonnegative`, `ratio_eq_nonnegative`, `full_window_ratios`, `endpoint_ratios`, `ratios_arbitrarily_small` | Certified signed readout agrees with previous positive readout; 0<=R<425/8 on full signed window; endpoint and no-pinching retained | Original population/native units; no sampled statistic, SciPy error, probability measure or physical claim. |

Names are under `SbtCosmo.Derivation`. The full 8084-job default build, fresh
694-declaration standard-only axiom audit and 31 exported statement checks cover
all 31 new theorems. No new numeric certificates are introduced. Derivation:
`math/SIGNED_RECORD_LEAN_2026-10-03.md`; receipts:
`results/signed_record_2026-10-03/`. Earlier evidence packets are unchanged.


## Original negative outside collapse and toy erasure (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthNegativeBounds.integralBarrier_derivative`, `growth_linear_upper`, `native_linear_upper` | Actual finite-start growth strictly below 5*a/(3*a0) | Live nonpositive parameter; singular endpoint excluded. |
| `GrowthNegativeLower.lowerGrowth_derivative`, `lowerVelocity_derivative`, `lower_matter_bounds`, `forcing_nonnegative`, `growth_lower`, `native_lower` | Constructed subsolution and actual IVP lower bound from derived cooperative forcing | Nonnegative s=-lambda*a0^3, x>=0 and live compact interval; no supplied bound. |
| `WindowErasureData.count_at_lower`, `gap_certificate`, `tags_at_lower` | Original seed-1100 exact count 58, unchanged collapse set between 17000 and 26000, both tags | Imported unchanged NumPy-realized population; kernel arithmetic, separate provenance replay. |
| `WindowErasureWitness.exists_unique_turnaround`, `turnaround_spec`, `live_before_turnaround`, `turnaround_zero` | Actual cubic turnaround in (15.4,15.5) and strict expanding cutoff before it | Exact original binary negative parameter; no physical time/crunch evolution. |
| `WindowErasureWitness.growth_at_fifteen`, `growth_before_turnaround`, `preCollapsed_iff`, `pre_count`, `pre_both_tags` | Exactly 58 actual pre-turnaround collapses, both tag values | Original exact mathematical model a0 and delta; no floating solver error claim. |
| `WindowErasureWitness.stopScale_bounds`, `stoppedCollapsed_iff`, `stopped_count`, `stopped_both_tags` | Same exact 58 collapses before the turnaround buffer | Exact mathematical counterpart of original buffer, no IEEE pow/solver certification. |
| `WindowErasureWitness.outside_excluded`, `no_retained`, `final_count`, `final_not_bearing` | Outside fails full-horizon gate; zero retained records and no final record-bearing | Declared toy erasure policy visible; historical clipped distinct_tags_final is not retained-set cardinality. |

Names are under `SbtCosmo.Derivation`. The full 8088-job default build, fresh
728-declaration standard-only axiom audit and 34 exported statement checks cover
all 34 new theorems. Original-input replay and false count/gap controls pass.
Derivation: `math/NEGATIVE_ERASURE_LEAN_2026-10-03.md`; receipts:
`results/negative_erasure_2026-10-03/`. Earlier evidence packets are unchanged.


## Actual patch-count robustness populations (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `WindowPatchCountData.rational_maxima_certificate`, `rational_threshold_certificate`, `rational_rank_certificate` | Original 12×32 and 12×128 binary amplitudes/tags, 48 attained positive maxima, 24 exact seed thresholds and two rank certificates | Kernel arithmetic; pinned NumPy provenance/byte replay is computational, not an RNG theorem. |
| `WindowPatchCountData.rational_window_bounds`, `rational_tight_bounds`, `rational_threshold_order` | Admissibility, 1252<T32<1253, 804<T128<805 and T128<T64<T32 | Original fixed populations; unchanged N=64 data imported. |
| `WindowPatchCounts.sampled_maxima`, `seedThreshold_eq`, `sampled_rank_counts`, `sampled_count_iff_threshold` | All data premises transported to real tagged maxima and ten-pass rank equivalence | No assumed maxima, rank law or record-count surrogate. |
| `WindowPatchCounts.realized_gate_iff_seed_fraction`, `realized_gate_iff_threshold`, `exists_unique_realized_window`, `upper_spec` | Actual original collapse histories, 80%-of-twelve criterion and unique all-real windows (-1/8000,upper_N] | Original native IVP and exact mathematical model scalars; no solver-error or physical bridge. |
| `WindowPatchCounts.threshold_order`, `upper_order`, `gate_inclusions`, `strict_gate_witnesses` | Strict ordering and nesting of actual N=32/N=64/N=128 continuum gates | Actual separately realized thresholds; no population inclusion, tag coupling or universal reseeding monotonicity. |
| `WindowPatchCounts.zero_passes`, `cutoff_fails` | Original aggregate gate passes zero and fails at the strict negative cutoff for both new populations | Equality at positive threshold retained; singular turnaround excluded. |

Names are under `SbtCosmo.Derivation`. The full 8090-job default build, fresh
751-declaration standard-only axiom audit and 23 exported statement checks cover
all 23 new theorems. Exact byte/input replay and false rank controls pass.
Derivation: `math/PATCH_COUNT_WINDOWS_LEAN_2026-10-03.md`; receipts:
`results/patch_count_2026-10-03/`. Earlier evidence is unchanged.


## Actual infinite-time growth and perpetual-record returns (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthInfinite.integrable_integrand`, `primitive_tendsto`, `growth_tendsto`, `native_tendsto` | Constructed improper-integral and actual native IVP time limit | Positive c or a0,lambda; no supplied asymptotic law. |
| `GrowthInfinite.infiniteIntegral_continuousAt`, `infiniteGrowth_continuousAt`, `growth_gap_strictMono`, `infiniteGrowth_strictAntiOn` | Dominated parameter continuity and strict limiting ordering from actual increasing gap | Strict finite ordering alone is not used to infer strict limiting order. |
| `GrowthInfinite.native_lt_infinite`, `native_eventual_threshold_iff`, `native_global_bound`, `native_infinite_parameter_limit` | Finite values strictly below limit, strict attainment criterion, global bound and parameter-infinity limit 3/2 | Every finite epoch a>=a0, not merely a fixed formation horizon. |
| `GrowthEternalWindow.exists_unique_infinite_endpoint`, `infiniteEndpoint_spec`, `perpetual_threshold_window`, `finite_endpoint_lt_infinite` | Constructed unique positive roots for every T>3/2, exact [0,u_infinity) and finite endpoint strictly lower | Selector guard discharged; finite formation, declared perpetual horizon convention. |
| `GrowthEternalWindow.perpetual_horizon_iff` | All finite strict horizon cutoffs iff lambda>=0 | Algebraic expanding-horizon condition, not physical crunch dynamics. |
| `WindowEternalRecords.gate_at_horizon_iff`, `eternal_gate_iff`, `eventual_record_iff`, `endpoint_eventual_count` | Actual original population at arbitrary finite horizon; [0,u_infinity) and exactly nine eventual endpoint passes | Original 80%-of-twelve requires ten; closing the endpoint is false for this predicate. |
| `WindowEternalRecords.fixed_deadline_gate_iff`, `finite_upper_lt_eternal` | Distinct fixed formation deadline plus perpetual retention gives [0,u_20], with u_20<u_infinity | No change of predicate is hidden in the eternal return. |
| `WindowEternalRecords.rational_starvation_margin`, `amplitude_starvation_margin`, `no_records_ever` | Kernel margin and actual all-time no-collapse at lambda>=10^9 | Coarse sufficient cutoff for unchanged N=64; not a sharp edge or a solver-error certificate. |

All names are under `SbtCosmo.Derivation`. The default build passes 8093 jobs;
the fresh ordered 798-declaration standard-only audit and 47 statement checks
cover all 47 new theorems. See `math/ETERNAL_WINDOW_LEAN_2026-10-03.md` and
`results/eternal_window_2026-10-03/`. Earlier proof/evidence packets and the
paper are unchanged. The unqualified closed infinite-horizon endpoint needs
a one-point correction if formation may occur at any finite epoch.


## Quantitative horizon limits and eternal robustness (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthInfiniteTail.velocity_upper`, `growth_tail_bound`, `native_tail_bound` | Derived actual velocity decay and explicit native remaining-growth bound | Positive a0,lambda and A>=a0; no supplied tail law. |
| `GrowthHorizonLimit.finite_horizon_admissible`, `finiteEndpoint_spec`, `finiteEndpoint_lt_infinite` | Actual finite-root selector guards, equation and strict order below infinite root | T>3/2 and A>a0*T; default branch excluded. |
| `GrowthHorizonLimit.finiteEndpoint_strictMonoOn`, `finiteEndpoint_tendsto` | Actual finite roots increase strictly and converge to the constructed infinite root | Moving-root limit earned using fixed lower/upper order tests. |
| `WindowEternalBounds.limiting_growth_at_four_upper`, `infinite_upper_bracket` | D_infinity(4)<937 and 3<u_infinity<4 for original N=64 | Existing certified quadrature plus derived tail; no solver rerun. |
| `WindowEternalBounds.finite_horizon_gate_iff`, `formationUpper_at_twenty`, `formationUpper_strictMonoOn`, `formationUpper_tendsto` | Actual original gates at arbitrary sufficiently long A, old A=20 endpoint identity and convergence | Same exact population/rank and native IVP; signed strict turnaround cutoff retained. |
| `WindowEternalBounds.eternal_window_closure` | Closure of actual eventual record window is [0,u_infinity] | Closure membership does not supply finite records at the endpoint. |
| `WindowEternalPatchCounts.eternal_gate_iff`, `eventual_record_iff`, `endpoint_eventual_count`, `finite_upper_lt_eternal` | Actual N=32/N=128 [0,u_infinity,N), nine endpoint passes, finite endpoints strictly smaller | Unchanged separately realized data; ten passes required. |
| `WindowEternalPatchCounts.upper_order`, `gate_inclusions`, `strict_gate_witnesses`, `fixed_deadline_gate_iff` | Strict eternal nesting with N=64 and distinct fixed-deadline closed windows | No population inclusion, universal reseeding order or discrete-N derivative. |
| `WindowEternalPatchCounts.rational_starvation_margin`, `amplitude_starvation_margin`, `no_records_ever` | Kernel margins and no patch ever collapsing at lambda>=10^9 for both robustness populations | Coarse sufficient cutoff at every finite a>=a0; no numerical edge claim. |

All names are under `SbtCosmo.Derivation`. Full build: 8097 jobs. All 32 new
statements and transitive axiom closures are freshly checked. The cumulative
audit covers 830 ordered declarations using the exact immutable previously
audited 798 prefix and new 32 suffix, with old proof/toolchain byte identity
checked; the entire 830-declaration command was not rerun. See
`math/HORIZON_LIMIT_LEAN_2026-10-03.md` and `results/horizon_limit_2026-10-03/`.


## Actual first-record ratios at the infinite edge (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `WindowEternalRatioData.grid_endpoints`, `upper_cells`, `upper_sum` | Exact 1024-cell upper bounds and sum <=4159/20000 at lambda=17/5 | Kernel arithmetic; whole native interval, no floating premise. |
| `WindowEternalRatioCertified.integral_horizon_upper_sharp`, `horizon_growth_upper_sharp`, `limiting_growth_upper_sharp`, `infinite_upper_tight_bounds` | Actual D(3.4,20)<959, D_infinity(3.4)<960 and 3<u_infinity<3.4 | Derived native tail and original IVP retained. |
| `WindowEternalRatio.prefix_above_threshold`, `final_above_threshold`, `time_spec` | Original first-time guards earned throughout [0,u_infinity] | All original seeds; fallback excluded, same existing selector. |
| `WindowEternalRatio.time_iff_any_collapse`, `time_is_first_collapse` | Actual earliest first patch collapse at every finite a>=a0 | First-any-patch, distinct from both-tag aggregate criterion. |
| `WindowEternalRatio.time_lower`, `time_upper`, `time_strictMono`, `time_at_zero` | Time in (1/2,5/2], strict parameter order and exact zero time T_first/1000 | Original N=64 inputs and mathematical model scalars. |
| `WindowEternalRatio.ratio_strictMono`, `ratio_upper_linear`, `near_edge_ratios`, `endpoint_ratios`, `eternal_window_ratios` | Actual ratios throughout the enlarged domain, 3/8<R<425/8 at infinite endpoint | Historical sample maximum 17.4 is not a continuum supremum certificate. |
| `WindowEternalRatio.arbitrarily_small_ratios` | Every eps>0 has positive admitted lambda with all twelve 0<R<eps | No measure/typicality premise; endpoint remains excluded by nine vs ten tag passes. |

All names are under `SbtCosmo.Derivation`. Full build: 8100 jobs. All 25 new
statements/closures are freshly checked; the cumulative 855-declaration audit
preserves the exact earlier 830 prefix with source/toolchain identity checked.
The full cumulative command was not rerun. Exact byte replay and false cell/sum
controls pass. See `math/ETERNAL_RATIO_LEAN_2026-10-03.md` and its receipts.


## Original all-time starvation at lambda>=32 (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `WindowStarvationData.grid_endpoints`, `upper_cells`, `upper_sum` | Exact 64-cell native upper integral certificate <=341/10000 at lambda=32 | Kernel arithmetic over [1/1000,4]; no floating premise. |
| `GrowthStarvationCertified.integral_upper`, `finite_growth_upper`, `limiting_growth_upper` | Original finite-start D(32,4)<9651/20 and actual D_infinity(32)<485 | Initial homogeneous contribution retained, time tail independently derived. |
| `GrowthStarvationCertified.global_growth_upper`, `patch_never_collapses`, `no_native_record` | Every lambda>=32 and finite a>=a0 has growth<485; explicit nonnegative amplitude margins imply no collapse/record | Generic amplitude margin is a visible input, earned below for original data. |
| `WindowGlobalStarvation.rational_margin_original`, `rational_margin_robustness`, `amplitude_margin_original`, `amplitude_margin_robustness` | Kernel maxima margins and every original N=32,64,128 amplitude has 485*amplitude<delta_c | All thirteen seeds; original separately realized populations retained. |
| `WindowGlobalStarvation.no_original_patch_ever`, `no_robustness_patch_ever`, `no_original_record`, `no_robustness_record` | No original patch ever collapses at any finite epoch, and no original both-tag history at any horizon | Sufficient cutoff 32; no exact optimum, universal random-population or physical Lambda claim. |
| `WindowGlobalStarvation.original_record_count_zero`, `robustness_record_count_zero` | Original twelve-seed both-tag record count equals zero at every horizon | Returned through actual native record histories. |

All names are under `SbtCosmo.Derivation`. Full build: 8103 jobs. All 19 new
statements/transitive closures are freshly checked. The standard-only cumulative
audit has 874 ordered declarations, preserving the exact earlier 855 prefix
with proof/toolchain identity checked. The entire cumulative command was not
rerun. Exact cell/sum/tail replay and controls, and all 2688 original amplitude
margins, pass. See `math/GLOBAL_STARVATION_LEAN_2026-10-03.md` and its receipts.


## Derived original allocation value regularity (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `AllocationSensitivity.marginal_sub_identity`, `marginal_sub_bounds`, `marginal_strictAntiOn`, `demand_stationary_of_positive`, `demand_antitone` | Independent exact original marginal bounds and clipped-demand parameter order | Nonnegative allocations; strict marginal order needs c>0, demand laws w,c>0. |
| `AllocationSensitivity.priceModulus_nonnegative`, `selected_price_antitoneOn`, `price_difference_bound`, `price_abs_difference_bound`, `selected_price_lipschitzOn`, `selected_price_continuousOn` | Actual chosen KKT price Lipschitz with K=sum_i(w_i+c_i), all positive budgets | Finite families, including empty; positive w,c, arbitrary heterogeneous offsets; no fixed active set. |
| `AllocationSensitivity.cost_remainder_bounds`, `cost_value_hasDerivAt`, `cost_value_deriv`, `cost_value_deriv_lipschitzOn`, `cost_value_contDiffOn_one` | Derived quadratic remainder, actual V'(B)=-price(B), C1 value and Lipschitz derivative on B>0 | No supplied differentiability or optimizer regularity; original cost/optimizer retained, including switch points. |
| `AllocationSensitivity.actual_strict_sensitivity_iff` | Actual negative derivative exactly when 0<B<S(0) | B>0 domain; binding alone does not force positive price/strict sensitivity. |
| `AllocationSensitivity.central_difference_price_error` | Exact central finite-difference error relative to -price <=K*h/2 | 0<h<B; floating value/solver error and empirical numerical agreement remain separate. |
| `AllocationSensitivity.demo_actual_derivative`, `changed_weights_actual_derivative`, `active_zero_derivative_control` | Existing heterogeneous demos actual derivatives -1/-2, and active singleton with derivative/price0 | Controls preserve parameter dependence and active-zero boundary. |

All names are under `SbtCosmo.Derivation`. Full build: 8104 jobs. All 21 new
statements/transitive closures are freshly checked. The standard-only cumulative
audit has 895 ordered declarations using exact immutable earlier 874 prefix
with proof/toolchain identity checked. The full cumulative command was not
rerun. See `math/ALLOCATION_SENSITIVITY_LEAN_2026-10-03.md` and its receipts.


## Constructed scalar convex price and actual Schur return (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ConvexClosurePrice.feasible_costs_mono`, `value_le_candidate`, `optimum_value`, `value_isGLB` | Actual feasible-cost infimum and primal optimizer/value identity | Nonempty/bounded-below guards expose meaningful real infima; ordinary optimizer is an original conditional input. |
| `ConvexClosurePrice.derivative_le_of_right_support`, `derivative_global_support`, `strict_sensitivity_forces_activity`, `positive_price_certificate` | Convex primal mixing constructs price=-V'(B)>0 and earns activity/global Lagrangian certificate | Real-valued convex objective/energy on convex A, actual optimum, finite value near B and actual derivative<0. No supplied dual/activity/value-support law. |
| `ConvexClosurePrice.certificate_primal_optimum`, `certificate_lagrangian_minimum`, `certificate_dual_isGLB`, `weak_duality`, `certificate_strong_duality`, `certificate_value_support`, `certificate_price_identification` | Earned certificate returns actual optimizer, guarded finite dual infimum equality and price-derivative identity | Competing finite dual values require nonnegative price and bounded-below Lagrangian image; no unbounded/empty real default is a dual answer. |
| `SchurClosurePrice.gram_energy_nonnegative`, `gram_energy_mix`, `gram_energy_convex`, `schur_energy_gram`, `schur_energy_convex`, `affine_schur_energy_convex`, `positive_schur_price` | Independently derive actual weighted Schur energy convexity and scalar price return, including singular native rank | Fixed native L and PSD W, affine dissolving D; generic optimum/local finite value/derivative inputs remain explicit. |
| `SchurClosurePrice.positiveDefinite_return`, `original_lagrangian_return` | Exact compatibility with unchanged original positive-definite Schur energy and scalar Lagrangian | No allocation-sum, physical density or stress-energy substitution. |
| `SchurClosurePriceExamples.energy_eq`, `objective_convex`, `local_finiteness`, `sqrt_primal_optimum`, `actual_value_formula`, `actual_value_derivative`, `actual_positive_schur_certificate`, `actual_slater_and_singular_native` | Complete actual L=0,W=1,D(x)=x,J=(x-2)^2 example; sqrt(B) optimizer, value derivative-1 and price1 at B1 | Final certificate example has no supplied optimizer/value/derivative premise; Slaterx0 and native singularity explicitly inhabited. |
| `SchurClosurePriceExamples.varying_native_values`, `varying_native_nonconvex` | Affine varying native L(x)=x, fixed D=W=1 has energy0 at +/-1 and energy1 at0 | Refutes automatic convexity for jointly changing native data; fixed-native/generic convexity restriction remains substantive. |

All names are under `SbtCosmo.Derivation`. Full build8107; all34 new statements/
transitive closures freshly checked. Cumulative929 uses exact immutable earlier
895 prefix plus fresh34 suffix with proof/toolchain identity checked; full
cumulative command not rerun. See `math/CONVEX_CLOSURE_PRICE_LEAN_2026-10-03.md`.
Extended-real split stationarity, Loewner matrix duality and physical Lambda
identification retain their separate scope.

## Extended-objective scalar price and actual Schur return (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ExtendedClosurePrice.finite_cost_guards`, `value_domain_return`, `finite_value_domain_return`, `primal_domain_return`, `optimum_value` | Actual extended infimum exactly equals the restricted finite real infimum; guards earned from actual finite value | Objective is nowhere minus infinity on A; finite-domain exclusion of plus infinity is explicit. |
| `ExtendedClosurePrice.epigraph_domain_convex`, `epigraph_objective_convex`, `positive_price_certificate` | Convex epigraph earns effective-domain convexity and positive actual marginal price with derived activity | Ordinary primal optimum, convex real energy, actual value finite near B and negative actual derivative remain original premises. |
| `ExtendedClosurePrice.certificate_domain_return`, `certificate_primal_optimum`, `certificate_strong_duality`, `weak_duality`, `certificate_dual_finite` | Global original extended Lagrangian certificate, primal optimality, actual finite primal/dual equality and weak bound for competing prices | Competing complete-lattice duals may be minus infinity; no real fallback value. Separate split stationarity is not inferred. |
| `ExtendedSchurClosurePrice.positive_schur_price` | Actual extended objective price returned to constructed singular-support Schur residual | Fixed native L, PSD W, affine D earn energy convexity; no energy-convexity or activity field supplied. |
| `ExtendedClosurePriceExamples.objective_no_bottom`, `objective_domain`, `epigraph_eq`, `objective_epigraph_convex`, `sqrt_primal_optimum`, `actual_value_formula`, `local_finiteness`, `actual_value_derivative`, `actual_positive_certificate` | Genuine infinite-objective Schur instance, earned domain/optimizer/value/derivative and zero-premise price1 certificate | e=x^2, J=(x-2)^2 on x>=0 and top otherwise; original value1 at B1. |
| `ExtendedClosurePriceExamples.unrestricted_toReal_false_value` | Exact control: blind conversion gives actual real value0 through forbidden x=-1, while true extended value1 | Earned domain restriction is essential to preserving the original program. |

All names are under `SbtCosmo.Derivation`. Full build8110; all24 new statements
and transitive closures freshly checked. Cumulative953 preserves exact earlier929
plus fresh24, with proof/toolchain identity checked; full cumulative command not
rerun. See `math/EXTENDED_CLOSURE_PRICE_LEAN_2026-10-03.md`. Qualified split
subdifferentials/normal cones, matrix/Loewner pricing and physical identification
remain outside this packet.

## Constructed differentiable-value matrix price (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ConeClosurePrice.value_le_candidate`, `optimum_value`, `derivative_nonpositive_on_cone`, `derivative_global_support`, `price_certificate`, `strict_sensitivity_nonzero` | Actual conic value derivative constructs cone-positive price, global Lagrangian support and complementarity | Ordinary primal optimum, convex objective/conic energy, locally nonempty/bounded-below costs and actual Frechet derivative remain explicit. |
| `ConeClosurePrice.certificate_primal_optimum`, `certificate_dual_isGLB`, `certificate_strong_duality` | Earned dual returns primal optimality and actual finite primal/dual equality | Dual infimum guards follow from attained global minimum; no unbounded real defaults. |
| `MatrixPriceRepresentation.symmetrize_symmetric`, `symmetrize_transpose`, `price_matrix_symmetric`, `trace_representation`, `rank_one_pairing`, `price_matrix_positive`, `price_matrix_nonzero` | Explicit matrix-unit construction of the exact symmetric trace representative, PSD and nonzero returns | Positive linear functional is earned downstream from actual conic value; no assumed matrix dual or self-duality field. |
| `MatrixClosurePrice.cone_laws`, `gram_mix_gap`, `residual_mix_gap`, `residual_loewner_convex`, `affine_residual_loewner_convex`, `matrix_price` | Actual support-residual Loewner convexity and constructed nonzero PSD price with global trace Lagrangian and actual finite dual equality | Symmetric budget topology, fixed native L, affine D, real objective and actual Frechet value derivative; general nonsmooth Slater theorem remains separate. |
| `MatrixClosurePriceExamples.coordinate_budget`, `budget_coordinate`, `energy_eq`, `budget_positive_iff`, `feasible_iff`, `costs_return`, `value_return`, `actual_value_derivative`, `actual_matrix_price` | Actual one-by-one matrix Schur program, exact scalar return, independently constructed derivative and zero-premise matrix price | No optimizer/value/derivative fields supplied in final example theorem. |
| `MatrixClosurePriceExamples.partial_slack_control` | Nonzero PSD P=diag(1,0), S=diag(0,1) with trace(P*S)=0 | Refutes full zero matrix slack from nonzero PSD price and complementarity. |

All names are under `SbtCosmo.Derivation`. Full build8114; all32 new statements/
transitive closures freshly checked. Cumulative985 preserves exact earlier953
plus fresh32 with proof/toolchain identity checked; full cumulative command not
rerun. See `math/MATRIX_CLOSURE_PRICE_LEAN_2026-10-03.md`. Qualified split
stationarity, general nonsmooth Slater duality, matrix extended objectives and
physical identification remain outside this result.

## Extended-objective conic and Schur matrix price (2026-10-03)

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ExtendedConeClosurePrice.finite_cost_guards`, `value_domain_return`, `finite_value_domain_return`, `primal_domain_return`, `optimum_value` | Actual extended conic infimum exactly equals the guarded finite-domain real conic infimum; ordinary optimizer returns | Original vector/matrix cone feasibility is retained; no scalar proxy or blind toReal conversion. |
| `ExtendedConeClosurePrice.certificate_domain_return`, `certificate_primal_optimum`, `certificate_strong_duality`, `weak_duality`, `certificate_dual_finite`, `price_certificate` | Earned conic price restored to the whole original domain; actual finite extended primal/dual equality | No-minus-infinity objective, convex real epigraph, cone-convex energy, ordinary optimum, local actual value finite and actual Frechet derivative remain explicit. |
| `ExtendedMatrixClosurePrice.matrix_price` | Actual extended Schur matrix price, exact trace representation, nonzero PSD, complementarity, global inequality and complete finite dual infimum | Fixed native L, affine D and symmetric budget topology; negative derivative in a PSD direction. General nonsmooth Slater duality/split KKT remain separate. |
| `ExtendedMatrixClosurePriceExamples.costs_return`, `value_return`, `actual_value_derivative`, `actual_matrix_price` | Complete original extended matrix program; exact cost/value return, independently constructed derivative and zero-premise price with actual primal/dual value1 | Actual one-by-one Schur residual x^2, J=(x-2)^2 on x>=0 and top otherwise. |
| `ExtendedMatrixClosurePriceExamples.converted_value_return`, `unrestricted_toReal_false_value` | Exact false control: unrestricted converted matrix infimum0 versus actual extended value1 and J(-1)=top | Proved effective-domain restriction is essential to preserving the actual program. |

All names are under `SbtCosmo.Derivation`. Full build8117; all18 new statements/
transitive closures freshly checked. Cumulative1003 preserves exact earlier985
plus fresh18 with proof/toolchain identity checked; full cumulative command not
rerun. See `math/EXTENDED_MATRIX_PRICE_LEAN_2026-10-03.md`. Matrix extended-objective
reduction is now mechanized; general nonsmooth duality, qualified split stationarity
and physical identification remain outside this result.


## Nonsmooth Slater price and original extended Schur matrix return

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ConvexValueSupport` | Actual strict-epigraph separation earns support; continuity from finite-dimensional convexity | Open convex budget neighborhood, no derivative assumption. Arbitrary normed spaces require continuity. |
| `NonsmoothConePrice.value_convex`, `support_nonpositive`, `support_global`, `price_certificate` | Actual guarded conic value convexity and local-support-to-global certificate return | Convex objective/domain, cone-convex energy and ordinary primal optimum; local finite-cost guards on this route. |
| `NonsmoothConePrice.slater_local_finiteness`, `slater_price_certificate` | Interior Slater slack earns actual local nonempty/bounded-below costs; constructs dual without derivative | Finite-dimensional budget, ordinary primal attainment supplied; no compactness/attainment or split sum rule claimed. |
| `NonsmoothConePrice.certificate_value_support`, `certificate_strict_price`, `certificate_nonzero` | Actual value support and strict-decrease price/nonzero consequences | Nonempty real competing cost sets guard real infimum semantics. |
| `ExtendedNonsmoothConePrice` | Original EReal/domain return, actual finite primal/dual equality under Slater, nonzero from actual decrease | No minus-infinity objective and convex real epigraph; whole original domain including top objectives. |
| `MatrixSlaterTopology` | Positive-definite actual symmetric slack lies in interior of PSD cone | Compact unit sphere and tube lemma; no openness in full matrix space. |
| `NonsmoothMatrixPrice` | Actual extended Schur matrix Slater duality; strict actual PSD-direction decrease earns nonzero price | Fixed L and affine D; no derivative/local-value/dual or full-activity premise. Qualified split stationarity separate. |
| `NonsmoothPriceExamples` | Actual V=max(-B,-2B) kink and nonzero dual; original infinite-objective Schur matrix price with actual dual1 through Slater alone | Both final examples have zero premises; no original solver/RNG rerun. |

All names are under `SbtCosmo.Derivation`. Full build8123; all27 new statements/
transitive closures freshly checked. Cumulative1030 preserves exact earlier1003
plus fresh27 with proof/toolchain identity checked; full cumulative command not
rerun. See `math/NONSMOOTH_PRICE_LEAN_2026-10-03.md`. General nonsmooth Slater dual
construction and actual extended Schur return are now mechanized; qualified
split stationarity and physical identification remain outside this result.


## Constructed sum splitting and actual Schur stationarity

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ConvexSubgradient.restricted_subgradient_iff`, `indicator_subgradient_iff`, `real_subgradient_iff`, `zero_subgradientOn_iff`, `normal_univ_iff` | Exact actual restriction/indicator/normal-cone/finite-real and minimization return | Restricted objective support is not ambient objective support. |
| `ConvexSubgradient.real_subgradient_add`, `remove_smooth_summand`, `smooth_real_subgradient_eq` | Actual support addition and derivative-based smooth summand removal/uniqueness | Objective convexity and actual smooth summand derivative; no objective differentiability assumed. |
| `ConvexSumSplit.split_real_of_continuous`, `split_real`, `split_extended` | Separation earns supports of restricted objective and finite global convex summand | One summand finite/continuous on entire ambient space; continuity earned in finite dimensions. Original extended domain returned. |
| `ConvexSumSplit.finite_objective_stationarity` | Ambient objective support, actual constraint derivative and admissibility normal sum to zero | Finite ambient convex J; ordinary optimizer and smooth global convex g. General extended RI split separate. |
| `SchurStationarity.affine_probe_differentiable`, `schur_energy_differentiable`, `trace_energy_convex`, `trace_energy_differentiable` | Actual fixed-native affine-probe Schur trace convexity and smoothness | Normed finite-dimensional primal ambient space for smoothness; singular native blocks retained. |
| `SchurStationarity.matrix_stationarity`, `matrix_stationarity_nonzero` | Full finite-objective split with original Slater matrix price/complementarity; nonzero under strict actual value decrease | No constraint derivative, subgradient, normal or stationarity supplied. Derivative is of actual scalar trace pairing; explicit matrix Jacobian/adjoint separate. |
| `SchurStationarity.matrix_restricted_stationarity` | Exact actual extended restricted-objective support equals minus actual trace-constraint derivative | Original objective including top points; general ambient extended objective/normal split remains open. |
| `StationarityExamples.actual_nonsmooth_stationarity`, `actual_schur_stationarity` | Complete nonsmooth finite J and original nonzero Schur stationarity examples | Final statements have zero premises; no objective/constraint derivative or stationarity supplied. |
| `StationarityExamples.boundary_no_bottom`, `boundary_epigraph_convex`, `boundary_restricted_support`, `boundary_no_ambient_support`, `missing_qualification_no_split` | Actual convex extended boundary objective has restricted zero support and no ambient objective support/full split | Refutes dropping the domain qualification; not the qualified original theorem. Relative-interior computation explanatory, not separately mechanized. |

Full build8127; all26 new statements/transitive closures freshly checked.
Cumulative1056 preserves exact earlier1030 plus fresh26; full cumulative command
not rerun. See `math/STATIONARITY_SPLIT_LEAN_2026-10-03.md`. General relative-interior-
qualified extended-objective splitting and physical identification remain open.


## Relative-interior-qualified extended objective/normal split

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `RelativeConvexContinuity` | Intrinsic-interior continuity, actual chart domain neighborhoods and bounded costs | Finite-dimensional real normed ambient space for convex continuity; membership neighborhood alone needs no finite dimension. |
| `RelativeDifference` | Constructed surjective difference into sum of affine-span directions, actual bounded-cost local witnesses | Budget space may be a proper ambient subspace; no ambient full-dimensional domain assumption. |
| `RelativeEqualitySupport` | Midpoint-earned nonempty/bounded-below equality cost infima; actual value support | Ordinary attained zero-budget optimum and local bounded-cost witnesses; both supplied by the application, no support premise. |
| `RelativeSumSplit.split_real_relative`, `split_real_support_relative`, `split_subgradient` | Earned objective support/admissibility normal from actual common relative-interior point | Finite-dimensional, convex domains; original extended epigraph/no bottom. No split, local finite-value or objective derivative premise. |
| `RelativeSumSplit.join_subgradient`, `subgradient_sum_iff`, `objective_indicator_eq_restriction`, `subgradient_add_indicator_iff` | Exact bidirectional sum rule, including literal original J+indicator | Join needs no qualification; literal extended sum identity uses no bottom. |
| `RelativeSchurStationarity` | Full qualified original extended Schur stationarity, PSD price/complementarity, nonzero under actual strict value decrease | Ordinary finite primal attainment, finite-cost PD Slater, fixed L/affine D and common RI point. Explicit matrix Jacobian/adjoint still separate. |
| `RelativeSplitExamples` | Exact lower-dimensional extended domain/RI, empty ambient interior, zero-premise forced nonzero ambient support with cancelling normal | Does not replace the earlier missing-qualification control; that counterexample stays fixed. |

Full build8133; all27 fresh statements/closures checked. Cumulative1083 preserves
exact earlier1056 plus fresh27; full cumulative command not rerun. See
`math/RELATIVE_SPLIT_LEAN_2026-10-03.md`. The general RI-qualified extended-objective
split is proved; physical identification and broader paper completion are not.


## Explicit Schur Jacobian and trace-dual adjoint

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `MatrixDifferential` | Actual rectangular product rule, transpose and trace calculus in existing matrix norm | Generic calculus accepts actual factor derivatives; no final Schur derivative premise. |
| `SchurDifferential.jacobian_apply`, `jacobian_symmetric`, `hasFDerivAt_residual`, `fderiv_residual` | Constructed two-term matrix Jacobian of actual spectral-support Schur residual and symmetric range | Fixed L, including singular native Gram; rectangular probes. |
| `SchurDifferential.traceAdjoint_pairing`, `trace_jacobian_formula`, `trace_jacobian_psd` | Trace-dual adjoint; general P+P^T formula and PSD-earned factor two | Adjoint maps to continuous dual; no unspecified primal inner product or nonsymmetric shortcut. |
| `SchurDifferential.hasFDerivAt_composed_residual`, `hasFDerivAt_composed_trace_gap` | General genuinely differentiable-probe chain return | Actual probe derivative supplied, not a Schur derivative; no finite-dimensional primal requirement. |
| `SchurDifferential.hasFDerivAt_probe`, `hasFDerivAt_affine_residual`, `fderiv_affine_residual`, `hasFDerivAt_trace_gap`, `fderiv_trace_gap`, `pricePullback_eq_adjoint_fderiv`, `pricePullback_psd` | Earned actual affine probe derivative, original matrix/trace derivative, exact adjoint identity and explicit price evaluation | Finite-dimensional primal for earned affine continuity; budget/native projector fixed. |
| `SchurAdjointStationarity` | Full original extended qualified literal D_Xi*P stationarity, every-direction formula, complementarity/nonzero price | Ordinary finite optimizer, common RI point, finite-cost PD Slater; nonzero from strict original value decrease. |
| `SchurDifferentialExamples` | Actual singular-native complement, rectangular derivative2*x*h, wrong-term and wrong-symmetry controls | No moving native calculus or physical interpretation claimed. |

Full build8137; all28 fresh statements/closures checked. Cumulative1111 preserves
exact earlier1083 plus fresh28; full cumulative command not rerun. Explicit
fixed-native Jacobian/adjoint obligation is closed; broad paper is incomplete.


## Canonical scalar sensitivity and qualified stationarity

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ScalarPriceStationarity.certificate_real_domain_return`, `certificate_price_identification`, `certificate_price_unique` | Guarded reverse extended-domain certificate return; every scalar certificate equals minus actual value derivative; uniqueness across different optimizers | Actual locally finite EReal value derivative; no optimizer/support/matrix-price uniqueness claim. |
| `ScalarPriceStationarity.certificate_stationarity` | Full nonsmooth objective/energy/normal split for any earned positive scalar certificate | Actual common RI point, ambient finite convex energy, no-bottom convex extended epigraph; helper certificate premise is constructed by full endpoint. |
| `ScalarPriceStationarity.positive_price_stationarity`, `positive_price_smooth_stationarity` | One p=-V'(B)>0 supplies derived activity, original extended duality/certificate and qualified stationarity | General finite convex energy may be nonsmooth; only smooth specialization accepts actual energy derivative. Optimizer and local finite negative value derivative supplied. |
| `ScalarSchurStationarity` | Earned actual Schur energy derivative, scalar-price-scaled matrix adjoint and explicit every-direction full stationarity | Fixed native/affine probe, singular native retained; scalar constraint, matrix audit price p*W. |
| `ScalarStationarityExamples` | Original infinite-cost Schur application/price uniqueness; energy(x,y)=x+abs(y), actual value=-B, nondifferentiable energy and zero-premise full nonsmooth stationarity | Discriminates nonsmooth scope; no general attainment/physical bridge. |

Full build8140; all19 fresh statements/closures checked. Cumulative1130 preserves
exact earlier1111 plus fresh19; full cumulative command not rerun. Corrected
scalar Theorem S assembly is closed. Broader original-target coverage remains.


## General matrix-map price and qualified stationarity

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ExtendedSmoothStationarity` | Actual extended restricted support from smooth summand removal; qualified ambient J/normal split | Actual local summand derivative; no summand convexity assumed. Common RI/finite dimension only for ambient split. |
| `GeneralMatrixPrice.tracePrice_apply`, `tracePrice_priceMatrix` | Actual continuous trace price and whole symmetric-budget functional representation | Existing elementwise matrix norm; no invented primal Hilbert adjoint. |
| `GeneralMatrixPrice.matrix_price`, `matrix_price_nonzero` | Arbitrary Loewner-convex map; earned PSD price/original certificate/finite EReal duality; nonzero under actual strict value decrease | No affine/quadratic map or value derivative. PD Slater/ordinary optimizer supplied. |
| `GeneralMatrixPrice.certificate_trace_energy_convex` | Earned trace-energy convexity from actual cone-positive certificate | Full ambient finite Loewner-convex extension; not inferred from convexity only on A. |
| `GeneralMatrixStationarity.hasFDerivAt_trace_gap`, `certificate_stationarity` | Actual matrix derivative earns scalar trace derivative and qualified stationarity for an earned certificate | Actual local matrix derivative; helper certificate constructed by full endpoints. |
| `GeneralMatrixStationarity.matrix_stationarity`, `matrix_stationarity_nonzero`, `matrix_stationarity_fderiv` | Full general smooth matrix Theorem S with actual adjoint, original certificate/finite duality and optional nonzero P | Loewner convexity only on A; actual derivative/DifferentiableAt at optimizer; common RI. No final price/split outputs supplied. |
| `GeneralMatrixStationarity.matrix_nonsmooth_stationarity` | Qualified full split with ambient support of actual scalar trace energy | Finite ambient Loewner-convex extension; no fictitious matrix derivative. |
| `GeneralMatrixExamples` | Actual nonlinear Schur x^4, derivative/Slater/RI/values/nonzero stationarity; nonquadratic entry; nondifferentiable matrix map/full nonsmooth stationarity; restricted-convexity/off-A support control | Zero-premise concrete constructions. Off-A no-support control has p>0 input; does not refute the smooth theorem. |

Full build8144; all28 fresh statements/closures checked. Cumulative1158 preserves
exact earlier1130 plus fresh28; full cumulative command not rerun. Corrected
general smooth matrix Theorem S is mechanized. Broad original-target audit remains.


## Full matrix sensitivity and same-price stationarity

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `ConePriceSensitivity` | Actual certificate support earns local minimum; whole price=-actual value derivative; exact extended/real return; Slater earns local finite original values | No finite budget dimension needed for identification; derivative legitimate premise. |
| `MatrixPriceSensitivity` | Hermitian matrix reconstructed from whole symmetric trace dual; every PSD certificate identified; uniqueness across different optimizers | Whole budget derivative required; no optimizer/support uniqueness. |
| `MatrixSensitivityStationarity` | One nonzero PSD price supplies sensitivity, matrix identity, actual smooth-adjoint or nonsmooth-support stationarity, complementarity/certificate/strong duality | Actual optimum, PD Slater, common RI and full value derivative; nonsmooth ambient extension explicit. |
| `MatrixSensitivityExamples` | Original infinite-cost Schur full price1 construction; actual nonsmooth matrix value/derivative/price1 stationarity; antisymmetric and one-direction controls | Zero-premise constructions; candidate-price test accepts actual certificate. |

Full build8148; all26 fresh statements/closures checked. Cumulative1184 preserves
immutable1158 plus fresh26; full cumulative command not rerun. Matrix price
identification is closed conditionally; broader original-target audit remains.


## Robustness-rectangle actual first records and uniform no-pinching

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `WindowRobustRecord` | Actual scaled maximum/threshold; first-time root, ANY-patch collapse equivalence/minimality and strict signed parameter ordering across entire declared rectangle | Original population/tags, exact coupled real scaling, actual native gate. No floating-array identity. |
| `WindowRobustRatio.endpoint_corner_bounds`, `common_positive_window` | Actual corner roots uniformly bound the original native boundary and earn a common positive window | Full rectangle, no assumed endpoint bound. |
| `WindowRobustRatio.full_window_ratios`, `endpoint_ratios` | Uniform finite signed ratios and positive endpoint lower bound; negative R<1/125 | Bounds use actual corner roots, not a numerical order-unity certificate. |
| `WindowRobustRatio.ratios_uniformly_arbitrarily_small` | One lambda>0 works for every rectangle point and all thirteen seeds simultaneously | Strong uniform no-pinching; epsilon arbitrary positive. |
| `WindowRobustRatio.equal_factor_return`, `compensated_original_return` | Equal scaling factors preserve actual endpoints/times/ratios; two changed knobs inside rectangle return original readouts | Exact coupling, not arbitrary independently sampled populations. |

Full build8150; all39 fresh statements/closures checked. Cumulative1223 retains
immutable1184 plus fresh39; full cumulative command not rerun. Broad completion
and tighter numerical robustness-edge ratio estimates remain open.


## Explicit numerical robustness-edge ratios

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `RobustEdgeLowerData`, `RobustEdgePrefixData`, `RobustEdgeUpperData` | 1925 exact unimodal cells, endpoints and rational sums checked by kernel | Three fixed profiles, no floating sampling. |
| `RobustEdgeQuadrature` | Actual integral returns from whole-cell certificates | Lower helper requires lambda>=1; fixed applications earn it. |
| `GrowthRescaledCertificate` | Exact native scale covariance, rescaled start range, actual finite-start term/prefactor bounds and three uniform original-growth inequalities | Full original IVP retained; c in(1/5,4), not an asymptotic replacement. |
| `WindowRobustEdge` | Actual3<u*c^3<7/2, actual endpoint first time c/2<a<=(8/3)c, every seed3/8<R<1792/27 throughout rectangle; every signed admitted0<=R<1792/27 | Exact original coupled population, no sharp typicality or physical bridge. |

Full build8156; all28 fresh statements/closures checked. Cumulative1251 retains
immutable1223 plus fresh28; full cumulative command not rerun. Numerical
full-rectangle ratio obligation is closed at the displayed explicit constants;
other populations and broad original-target completion remain open.


## Separately realized patch-population first-record numerical ratios

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `WindowPatchCountFirstData` | Exact rational first-threshold/scale bounds and existential failure of the original500 normalized lower bound | Immutable original N32/N128 data; no new sampling. |
| `WindowPatchCountRatio.maximum_spec`, `time_spec`, `time_iff_any_collapse`, `time_is_first_collapse` | Actual first-ANY-patch unique root, collapse equivalence and minimality throughout both full signed gates | Actual separately sampled inputs; no two-tag readout substitution. |
| `WindowPatchCountRatio.endpoint_normalized_bounds`, `endpoint_numerical`, `endpoint_time_bounds`, `endpoint_ratios` | Actual3<u*c^3<7/2, N32 u in(1.3,1.7), N128 u in(5,6.25), all24edge ratios in(2187/8000,1792/27) | Broad finite certificates, no sharp typicality. c is an analytic normalization. |
| `WindowPatchCountRatio.full_window_ratios`, `ratios_uniformly_arbitrarily_small` | All signed admitted0<=R<1792/27; one positive lambda makes all24ratios arbitrarily small | Honest no-pinching; N discrete, not a smooth parameter. |

Full build8158; all33 fresh statements/closures checked. Cumulative1284 retains
immutable1251 plus fresh33; full cumulative command not rerun. Other-population
numerical edge-ratio obligation closed at stated constants; broader completion open.


## Actual first-time joint continuity and earned knob derivatives

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthFirstContinuity` | Joint relative continuity on actual signed domain, ambient continuity under earned strict slack; threshold derivative1/nativeVelocity>0 and C1 | Horizon-equality matter fallback proved ambiently discontinuous. No supplied selector continuity/inverse. |
| `FirstPopulationContinuity` | Actual attained1-Lipschitz finite maximum; arbitrary continuous-input first-time stability; ANY-patch return | Domain margins explicit; tied maximum and actual first time proved nondifferentiable. |
| `WindowFirstRegularity` | Earned strict first-threshold slack; actual coupled time/ratio joint continuity; fixed-lambda knob C1/exact signed partials; endpoint continuity; all N32/N64/N128 signed readout continuity | Exact coupled scaling and separate realized populations retained; no joint C1/lambda derivative asserted. |

Full build8161; all38 fresh statements/closures checked. Cumulative1322 retains
immutable1284 plus fresh38; full cumulative command not rerun. Joint continuity
and knob C1 obligations closed; broader original-target completion remains open.


## Actual joint first-time C1 and signed implicit sensitivity

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GrowthJointContinuity` | Earned root margins and joint primitive/growth/velocity/sensitivity continuity, with native returns | Clipping agrees on actual intervals; original IVP unchanged. |
| `GrowthUnitDifferential` | Actual joint kernel derivative, compact uniform norm bound, all under-integral inputs, exact unit-interval transport and original primitive joint derivative | x>=0 and actual root positivity; includes x=0. |
| `GrowthJointDifferential` | Earned actual joint growth/native derivative; coordinate restrictions identify coefficients only after joint differentiability; native C1 | Live native domain; no joint differentiability inferred from partial derivatives alone. |
| `GrowthFirstDifferential` | Explicit triangular inverse, earned actual local root identity, joint selector C1 and exact positive parameter derivative -S/V | Strict final slack; no supplied selector derivative/continuity/inverse. |
| `WindowFirstDifferential` | All original N32/N64/N128 times C1 inlambda; N64 rectangle joint C1 in(d,s,lambda); actual endpoint times/ratios jointly C1 in knobs | Actual ratios C1 away fromlambda0 and proved nondifferentiable at0. Gates earn slack; no arbitrary max/rank-switch C1. |

Full build8166; all61 fresh statements/closures checked. Cumulative1383 retains
immutable1322 plus fresh61; full cumulative command not rerun. Joint first-time
C1 and implicit signed sensitivity obligation closed; broader completion open.


## Combined original population/knob robustness

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `CombinedEdgeLowerData`, `CombinedEdgePrefixData`, `CombinedEdgeUpperData`, `CombinedEdgeQuadrature` | Kernel-checked1914 whole cells, endpoints and sums; three new actual integral bounds | Exact rational arithmetic, byte replay and false-cell controls; original certificates fixed. |
| `GrowthCombinedCertificate` | Wider finite-start covariance/initial term/prefactor estimates on1/6<c<5 | Includes actual combined corners outside old1/5<c<4 domain. |
| `WindowPatchRobust` | Actual N32/N128 signed windows over full d/s rectangle; aggregate rank return, first-ANY collapse iff/minimality, original identities, strict N32<N64<N128 endpoint/gate ordering | Separately realized fixed populations/tags; exact real common scaling; no nested sampling. |
| `WindowPatchRobustRegularity` | Actual endpoint C1 and derivative signs; joint first time C1 in(d,s,lambda), exact positive parameter sensitivity, endpoint time/ratio C1 | Ratio continuous everywhere, C1 away from0, proved nondifferentiable at0; strict slack earned. |
| `WindowPatchRobustEdge` | Normalized endpoint in(5/2,7/2), endpoint ratios in(3645/16000,1792/27), full signed upper bound, one positive lambda for all36 ratios throughout rectangle | Broader domain retains stronger prior narrower bounds; no sharp clustering/measure/physical identification. |

Full build8174; all81 fresh statements/closures checked. Cumulative1464 retains
immutable1383 plus fresh81; full cumulative command not rerun. Combined exact
toy robustness obligation closed; broader original-target completion open.


## Actual smooth full-support prior counterexample

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `WindowSmoothPrior` | C-infinity positive density, actual antiderivative/integrability, full positive-window normalization, exact prefix mass; one rate/prefix puts mass>1-eta on actual all36 R<epsilon across entire knob rectangle | Actual low-ratio event inclusion and interval-mass certificate; no separately mechanized probability object/abundance pushforward, signed negative sliver or physical prior. |

Full build8175; all10 fresh statements/closures checked. Cumulative1474 retains
immutable1464 plus fresh10; full cumulative command not rerun. Already false
local-nonsingularity sufficiency is formally obstructed; broader completion open.


## Original32-patch allocation carrier and actual controls

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `AllocationSampleData` | Original pinned32 coefficients/10 budgets/3 offsets;160 rational response cells, sums, activity/slack and control certificates | Exact reified IEEE arithmetic; formatted-data computational bridge, no historical bit recovery or numerical optimizer error proof. |
| `AllocationScreening` | Marginal response enclosures, selected-price bracketing, exact intrinsic selected screening and cost-value return | Generic positivity/activity/rebased-price guards explicit; concrete guards earned in sample. |
| `AllocationSample` | Actual price in(0.46112,0.46113), activity/shared stationarity/heterogeneity, global optimum/uniqueness, actual value derivative, all original sweep cases, screening on[-1/4,1/4] | Original objective/constraints retained; no Schur-budget or physical Lambda identification. |
| `AllocationSampleControls` | True local-budget selected optimizer/unequal prices and exact total B; no-budget unique unconstrained optimizer and actual patch8 movement>1/2 at both original IEEE offsets | Strong support has no competitor mass guard; controls change actual constraint/coupling, not record labels. Sharper floating maxima unclaimed. |

Full build8179; all54 fresh statements/closures checked. Cumulative1528 retains
immutable1474 plus fresh54; full cumulative command not rerun. Original carrier
mechanics strengthened; broader original-target completion remains open.


## Actual Step26 alternating-sector nonlinear iteration

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GroundAlternating` | Actual positive ground response from the full eight-site Hamiltonian and unchanged sourcing; positive normalized paired fields, selected field/contrast returns and earned derivative -k*b/8 | Constant background, positive alternating slice; no supplied eigenmode/solution/derivative. |
| `GroundAlternatingRelaxation` | Actual normalized mixing, nonzero normalization, invariant field/contrast returns, actual derivative1-m-m*k*b/8, half-mode criterion and local nonlinear gain bounds | Linear mode criterion is not all-mode stability; convex mixing guards earned; boundaries excluded from nonlinear verdict. |
| `GroundAlternatingOrbit` | Every actual finite field/contrast iterate, local geometric convergence to uniform and finite escape from a fixed contrast neighborhood; exact half-mixing returns and parameter controls | Slice attraction only; escape does not mean unbounded growth/nonexistence/permanent nonconvergence. Original nonconstant-template crossing remains open. |

Full build8182; all65 fresh statements/closures checked. Cumulative1593 retains
immutable1528 plus fresh65; full cumulative command not rerun. Scoped original
iteration support strengthened; no background-blindness restoration or full
original-target completion.


## Actual nonconstant-ground/source/normalized Jacobians

| Declaration group | Exact coverage | Boundary |
|---|---|---|
| `GroundBorder`, `GroundEquations` | Actual normalized eigen equation, full polynomial derivative, earned invertible border from ground simplicity/normalization; derived implicit-function hypotheses | Arbitrary Fin8 real potentials; no supplied inverse/derivative/gap. |
| `GroundSmooth` | Existing-selector return through continuity and local implicit uniqueness; C-infinity actual ground and energy; actual derivative from inverse border, uniqueness/tangency/eigen equation | No global uniform gap, analyticity or nonlinear self-consistent branch uniqueness. |
| `GroundSourceJacobian` | Original quadratic source derivative and C-infinity positive-representative groundMap; actual full real J for arbitrary nonconstant backgrounds | Declared positive real ground representative; frozen complex phase trajectory not returned. |
| `GroundNormalizedJacobian` | Actual normalization/projection derivative, exact tangent damping return, real-eigenmode law; all-parameter positive fixed points/Jacobians and original zero-coupling controls | Fixed-point/unit/tangent/eigenmode guards explicit where needed; no sampled branch, spectral crossing or all-mode stability certificate. |

Full build8187; all51 fresh statements/closures checked. Cumulative1644 retains
immutable1593 plus fresh51; full cumulative command not rerun. Earned original
nonconstant derivative obligation closed; numerical branch/spectral obligations
and broader original-target completion remain open.

## Original-template a posteriori root and spectral certificates

| Export/artifact | Earned conclusion | Boundary |
| --- | --- | --- |
| `GroundRootCertificate.residual_hasFDerivAt`, `residualDerivative_apply` | Actual nonlinear sourced eigen residual and full derivative | Arbitrary real background/coupling, original eight-site source. |
| `positive_root_return`, `root_half_mixing_derivative`, `half_mixing_jacobian_apply` | Positive root is selected ground fixed point; actual normalized derivative A=(I-uu^T+J)/2 | Unit/eigen conditions derived from residual; positive representative. |
| `certified_positive_root` | Unique residual root in a positive closed ball, actual ground-map return | Explicit injective correction, derivative/residual bounds and q<1; no global uniqueness. |
| `de_ground_interval_certificate.py`, `certificates.json` | Exact interval checks of30 root balls,28 stable half-mixing real tangent spectra and unstable modes at20/30 | Python computational foundation, not concrete Lean instantiations; no continuous branch or frozen run. |

Full build8188;11 fresh statements/standard-only closures. Cumulative1655 preserves1644 immutable plus11; full cumulative command not rerun. All30 exact replays and false-certificate controls checked. Coupling15 is spectrally stable at its certified positive root (<0.911617); the original finite-budget failure is separate.

## Actual nonlinear all-direction and zero-coupling orbit return

| Export | Earned conclusion | Guard/foundation |
| --- | --- | --- |
| `GroundLocalDynamics.positive_root_groundPair_return`, `positive_root_jacobian_return` | Entire root pair is selected ground/energy; sourced border solutions are actual J | Positive residual root; no supplied ground status or energy identification. |
| `normalized_smooth_at`, `coordinate_hasFDerivAt`, `coordinate_iterate_return` | Actual normalization C-infinity; actual derivative and full iteration conjugacy | Unit ground-map fixed point, fixed continuous linear equivalence. |
| `actual_local_attraction`, `actual_local_attraction_of_rows` | Nonlinear local convergence of actual real iteration in all8 directions; geometric coordinate error | Strict norm/row bound on the earned actual normalized derivative. |
| `GroundZeroCouplingOrbit.native_orbit_unit_nonnegative` | Original all-background/all-coupling nonnegative unit invariant | Nonnegative unit initial field,0<m<=1; no convergence inference. |
| `actual_zero_coupling_global_convergence`, `actual_zero_coupling_distance_bound` | Original zero-coupling global convergence and explicit rate for every background | Nonnegative real unit initial field,0<m<=1; no spectral/derivative/solver premise. |

Full build8190;40 fresh statements/standard-only closures; cumulative1695 preserves1655 immutable plus40. Read-only exact replay confirms28 original sample row-norm bounds supporting mathematical local return; concrete kernel instantiations, numerical basin radii and original complex trajectory remain separate.

## Original native complex update, 2026-10-03

| Export | Mathematical coverage | Scope / remaining obligations |
| --- | --- | --- |
| `GroundNativePhase.source_pack`, `nativePhase_ratio`, `GroundNativeControls.real_eigensolver_phase_return` | Original modulus-square source, original exp(-i arg) phase rule, real eigensolver sign ambiguity | Active overlap branch; real lowest unit eigenvector; no arbitrary complex phase covariance. |
| `GroundNativeJacobian.nativePairMap_hasFDerivAt`, `imaginary_phase_mode`, `half_mixing_imaginary_projection` | Earned full native real derivative; imaginary phase1-2m, tangent1-m | Actual positive unit fixed point; earned local source guards. |
| `GroundNativeLocal.native_complex_local_attraction_of_rows` | Actual complex nonlinear convergence with phase/normalization guards at every iterate | Strict row bounds of earned transformed real/imaginary blocks. |
| `GroundNativeControls.exists_legal_native_fixed` | Legal native complex fixed point for every real background/coupling/mixing | Every threshold0<=τ<1; no stability inferred. |
| `real_mode_full_return`, `native_half_imaginary_illegal` | Real eigenmode embeds; exact unit imaginary cancellation exposes illegal normalization | Linear instability does not establish nonlinear escape; no totalized zero iterate attributed to runtime. |

87 fresh statements/standard-only closures; cumulative1782 retains1695 immutable
plus87. Exact Python replay yields30 imaginary bounds and28 full complex local
returns. Concrete sampled kernel instantiation, frozen complex initialization's
basin, finite-budget success and continuous branch remain separate.

## Original coupling continuum and actual minus-one contacts, 2026-10-03

| Export | Earned mathematical content | Explicit scope / remaining obligation |
| --- | --- | --- |
| `GroundParameterEquations.defect_bijective`, `defect_preconditioner_bijective`, `jointResidual_partial` | Actual nonlinear partial and proposed preconditioner invertible from strict defect; joint polynomial regularity | Strict actual Newton-defect norm bound. |
| `GroundParameterBranch.certified_local_positive_branch`, `branch_ground_eventually` | Actual local C-infinity positive root/ground pair with local uniqueness | Positive actual root and strict defect, no supplied branch/inverse. |
| `GroundParameterTube.TubeCertificate.positive_root_exists`, `root_implicit_germ`, `root_continuous_on` | Uniform roots, strict interior and C-infinity boundary germs; continuity derived | Explicit uniform rate/residual/positivity quantitative bounds on a tube. |
| `common_root_glues` | Two tube roots equal at a certified common root | Same coupling and actual root in both boxes; floating proximity alone unused. |
| `GroundParameterSpectrum.actual_minus_one_crossing` | Nonzero tangent -1 mode at an interior coupling, actual native complex derivative return | Continuous actual fixed branch and opposite determinant signs; no nonlinear escape. |

31 fresh statements/standard-only closures; cumulative1813 retains1782 immutable
plus31. Exact computation supplies286 tubes,287 anchors and all12 original root
returns, earning a connected branch and two minus-one contacts. Concrete kernel
instantiation, concrete global finite patch definition and stronger dynamical
classification remain open; see `GROUND_COUPLING_BRANCH_2026-10-03.md`.


## Finite quantitative branch assembly, 2026-10-04

| Export | Earned mathematical content | Explicit obligations and limits |
| --- | --- | --- |
| `GroundParameterPatch.TubeCover.tube_root_eq`, `root_eq`, `root_spec` | Constructed global positive actual root from owning tube; overlap identity derived | Quantitative tubes and a certified common-root ball contained in both overlap boxes. |
| `TubeCover.root_continuous_on`, `root_implicit_germ`, `root_smooth_on` | Finite closed pasting, C-infinity germ across seams and ContDiffOn union | Finite index and closed patch sets; no supplied branch/continuity premise. |
| `TubeCover.groundPair_return`, `GroundParameterPatchReturn.certified_sample_return` | Full actual ground/energy return and certified sample root identity | Actual equations/positivity derived; numerical ball containment remains explicit. |
| `native_fixed_legal` | Legal fixed points of unchanged native complex update | Threshold in[0,1); no arbitrary-input convergence. |
| `minus_one_contact`, `two_distinct_contacts` | Distinct actual tangent -1 modes with full native derivative return | Interval coverage and opposite actual determinant signs; continuity/fixedness derived. |

17 fresh standard-only closures; cumulative1830 preserves1813 immutable plus17.
Full build8202. Generic global assembly is mechanized; concrete286-tube cover,
coverage and sign/norm proof terms remain a kernel-instantiation obligation.
Previous exact numerical replay is protected, not claimed fresh. See
`GROUND_FINITE_PATCH_2026-10-04.md`; overall original-target goal incomplete.


## Concrete original kernel tube, 2026-10-04

| Export | Earned mathematical content | Scope and remaining work |
| --- | --- | --- |
| `GroundRationalInterval.Interval.mul_sound`, `Expr.enclose_sound` | Exact signed rational enclosure of real expression values | Four-corner products handle negative and zero-crossing boxes; kernel arithmetic. |
| `GroundPointCoordinates.operator_norm_le_rows`, `matrixMap_apply` | Actual nine-coordinate product sup operator norm and matrix action | Field coordinates followed by energy; no Euclidean norm substitution. |
| `GroundResidualEnclosure.residualExpr_return`, `derivativeExpr_return`, `defect_norm_bound` | Polynomial enclosures return to actual nine equations, actual derivative and Newton defect norm | Rational box membership and row comparisons explicit in general theorem. |
| `GroundKernelTube.tube`, `certified_actual_root` | Uniform actual Newton tube from exact rational arithmetic certificate | Real bounds and preconditioner injectivity earned. |
| `GroundOriginalFirstTube.arithmetic`, `original_positive_root`, `original_smooth_branch` | First original nonconstant-background tube fully instantiated in kernel; actual roots and C-infinity branch throughout[0,15/128] | Radius1/256, Newton q<=1/10, center residual<=3/1000; arithmetic has no hypotheses. |
| `zero_preconditioner_rejected`, `false_residual_budget_rejected` | Kernel rejection of substantive false certificate controls | Actual defect row and strict invariance. |

40 fresh standard-only closures; cumulative1870 preserves1830 immutable plus40.
Full build8207. One of286 concrete uniform tubes now has kernel proof terms;
remaining tube/anchor/sample/coverage/sign instantiations and original-init basin
remain open. Newton correction contraction does not imply native convergence.
See `GROUND_KERNEL_TUBE_2026-10-04.md`; original-paper goal remains incomplete.


## Original full coupling continuum in the kernel, 2026-10-04

| Declaration | Mathematical return | Remaining scope |
|---|---|---|
| `GroundContinuation.Tube001`–`Tube285`, `Anchor000`–`Anchor286` arithmetic | 572 closed actual full-box rational certificates | First tube reuses preceding immutable proof; all286 tubes and287 anchors instantiated. |
| `GroundKernelChain.Data.ball_subset`, `Chain.ordered_overlap`, `Chain.cover` | Actual product sup ball containment and common-root overlap from populated chain | Every field supplied by concrete kernel facts. |
| `GroundKernelChainCoverage.finite_interval_union`, `chain_cover_domain` | Exact finite consecutive closed-interval coverage | Induction, not sampled endpoint coverage. |
| `GroundOriginalContinuation.whole_smooth`, `whole_ground` | Actual C-infinity positive unit ground/energy branch for every real coupling in[0,30] | Only coupling-range premise; ball uniqueness does not imply global root uniqueness. |
| `GroundOriginalContinuation.whole_native_fixed` | Legal unchanged native complex fixed branch, exact original tolerance | Arbitrary mixing; fixedness does not supply a frozen-init basin or convergence. |

589 fresh standard-only closures; cumulative2459 preserves1870 plus589.
Full build8782. Sample thin boxes/identities and spectral signs are not yet all
kernel instantiated; nonlinear escape, all-interval stability, frozen-init basin
and physical Lambda remain separate. See `GROUND_KERNEL_CONTINUATION_2026-10-04.md`.
Paper and runtime unchanged; original-paper goal remains incomplete.


## Native nonlinear local escape, 2026-10-04

| Declaration | Mathematical return | Explicit boundary |
|---|---|---|
| `GroundNativeEscape.c2_quadratic_remainder` | Actual quadratic remainder from C2 via locally Lipschitz derivative and mean value | Earned neighborhood and constant. |
| `quadratic_tracking`, `finite_eigenmode_escape`, `c2_eigenmode_escape_within` | Uniform finite tracking, fixed-radius escape from arbitrarily close inputs, within any prescribed local chart | Norm(L)<abs(l)^2 is an explicit sufficient linear gap. |
| `c2_eigenmode_output_escape`, `nativeUpdate_unit` | Start escape at a legal actual output; unit complex normalization earned | No zero-denominator execution. |
| `displacement_smooth`, `displacement_hasFDerivAt`, `displacement_iterate_return` | Actual unchanged native C-infinity map, actual derivative, exact affine coordinate orbit return | Phase convention retained; coordinate equivalence is not asserted isometric. |
| `native_complex_local_escape` | Arbitrarily close unit complex inputs escape a fixed neighborhood in finitely many actual native steps, guards throughout | Ground/tolerance and actual expanding-mode/norm-gap inputs explicit. Concrete20/30 spectral kernel instances pending; mathematical return uses immutable exact certificates. |

18 fresh standard-only closures; cumulative2477 preserves2459 plus18; full build8783.
No frozen-seed outcome, unbounded runaway, all-orbit escape, all-interval instability
or physical Lambda bridge. See `GROUND_NATIVE_ESCAPE_2026-10-04.md`; paper unchanged.


## Original coupling thin roots and actual Jacobian entries, 2026-10-04

| Declaration | Mathematical return | Remaining boundary |
|---|---|---|
| `GroundSamples.Point000`–`Point013` arithmetic | Twelve original coupling roots plus two crossing probes certified in the kernel | Radius2^-32; eight closed actual full-box tests each. Eighteen offset roots not yet instantiated. |
| `GroundOriginalSamples.root_eq_branch`, `branch_in_sample_ball` | Full thin root/energy identity and exact box membership for the actual[0,30] branch | Concrete interval ownership and all nine-coordinate containment comparisons. |
| `GroundBorderResponse.linear_response_error_mul`, `response_equation`, `response_field` | Actual selector response with earned (1-q) error loss; field part equals actual ground-map derivative | Border and nonlinear residual derivative distinguished; no numerical inverse assumed. |
| `GroundResponses.Point000`–`Point013` arithmetic | Fourteen closed whole-box border-defect/response-budget certificates | Seven kernel comparisons each; lawful zero-coupling zero budgets. |
| `GroundOriginalResponses.actual_half_entries` | Kernel containment of every actual normalized half-mixing derivative entry at all14 roots | Only finite indices; projection, energy response and source feedback retained. Basis/norm and determinant tests still pending. |
| `GroundResponseControls.zero_border_preconditioner_rejected`, `zero_error_budget_rejected` | Kernel rejection of substantive false certificates at20 | Does not assert strictly positive actual error at every root. |

57 fresh standard-only closures; cumulative2534 preserves2477 plus57; full build8815.
No new numerical attraction/escape/contact, original-seed basin, finite-step outcome
or physical Lambda bridge. See `GROUND_KERNEL_SAMPLES_2026-10-04.md`; paper unchanged.


| Original coupling coordinate packet | Exact two-sided real and imaginary basis inverses, actual full derivative norm bounds at all12 coupling samples, actual native complex local attraction at10 samples through15 | GroundMatrixCoordinates; GroundCoordinates.Point000–011; GroundOriginalCoordinates; GroundCoordinateControls | Populated kernel arithmetic; two false-certificate controls; standard-only transitive axiom checks required | Determinant signs/eigenmodes and native escape instantiation remain pending; no frozen-seed basin or all-parameter attraction claim |


| Original spectral packet | Seven actual shifted determinant signs; two distinct minus-one contacts; two full unit expanding modes; finite guarded nonlinear native escape from arbitrarily close unit complex starts at20/30 | GroundDeterminantDefect; GroundTriangularSign; GroundTriangularArithmetic; GroundSpectralEnclosure; GroundRealModeNormalize; GroundSpectralTests.Test000–006; GroundOriginalSpectrum; GroundSpectralControls | Populated kernel integer factorizations and interval rows; two substantive false-certificate controls; standard-only transitive axiom audit | Frozen initialization basin and finite source outcomes remain pending; no first/simple/transverse contact, all-orbit escape, unbounded amplitudes or universal runaway |


| Original negative representatives | Legal active native fixedness on[0,30]; actual local complex attraction at10 samples through15; finite guarded escape at20/30 around negative representatives | GroundNativeReflection; GroundOriginalReflection; GroundReflectionControls | Source-evenness, active original phase reflection and exact orbit transfer; substantive unit/legal inactive-phase counterexample; standard-only closures required | The floating scout supplies no frozen-seed basin; no unconditional oddness, arbitrary phase equivalence, all-orbit escape or universal runaway |


| Global native zero coupling and original seed | Global complex half-mixing convergence for every background with signed real overlap above threshold; geometric decay and all active/legal guards; closed original-seed return to negative branch ground at0 | GroundNativeZeroGeometry; GroundNativeZeroScalar; GroundNativeZeroOrbit; GroundOriginalSeed | Exact source return and scalar polynomial estimates;16 reified seed coefficients and three closed kernel comparisons; actual root-box enclosure and negative overlap below-1/5;44 fresh standard-only closures required | Exact mathematical reification, with both initialization normalizations; no60-step floating verdict, IEEE per-operation emulation, positive-coupling basin or all-complex-initial-fields theorem |

| Finite native zero-coupling seed distance | Actual original seed enters overlap1/2 region after one step; squared Euclidean distance below(2e-9)^2 at60 and below(3e-9)^2 at59 | GroundNativeZeroFinite; GroundOriginalSeedFinite | Polynomial half-contraction, whole-root-box radius return, two rational kernel comparisons, exact guarded native iteration/reflection;17 fresh standard-only declarations | Exact mathematical model; all four source residual bounds and IEEE per-operation return pending |

| Original four source tests at zero coupling | Exact mathematical original-seed orbit passes all four original convergence thresholds after60, with both diagnostic phase guards and all native guards | GroundComplexEuclidean; GroundComplexResidual; GroundSourceDiagnostics; GroundOriginalResiduals; GroundSourceDiagnosticControls | Exact Euclidean bridge; phase-movement/triangle estimates; actual symmetric cycle budget and quadratic Rayleigh error; closed background arithmetic; actual double-gap control;51 fresh standard-only declarations | Source formulas and exact IEEE coefficients/thresholds are reified; per-operation IEEE execution and positive-coupling seed basins remain pending; sourcing diagnostic compares identical expressions |

| Original-seed native prefix at coupling0.3 | Actual16-step original-seed orbit enclosure, unit norm and active/legal guards; State sup-coordinate distance below1e-5 to negative actual continuation ground | GroundBackgroundKernel; GroundIntervalReciprocal; GroundNativeBox; GroundNativePrefixInitial; GroundNativePrefix.Step000–015; GroundOriginalNativePrefix | Whole sourced-potential Newton boxes, two reciprocal guards, closed kernel step certificates and complete seams;65 fresh standard-only declarations | Finite nearness does not establish basin entry into an unknown radius; explicit quantitative basin, infinite positive-coupling seed convergence,60 source tests and IEEE execution remain pending |

| Explicit original-seed basin at original coupling0.3 | Whole-ball radius1/40000, derivative bound3/5, reflected16-step entry≤1/48000; original infinite orbit converges to negative actual branch ground with all unit/active/legal states | GroundNativeGeneralDerivative; GroundBackgroundResponse; GroundNativeQuantitativeBall; GroundNativeDerivativeBox; GroundStateRows; GroundBasin.Point002Data/Arithmetic/Bridge; GroundOriginalBasin | Uniform actual selector response, all16 transformed columns with both cross blocks, checked outward cache inclusions, convex mean-value contraction and active-only reflection;86 fresh standard-only declarations | Four60-update source tests at0.3, other positive seed basins,18 offset instances and IEEE execution remain pending |

| Exact original-seed sixty-update source tests at original coupling0.3 | All four original source thresholds, actual sourced candidate and Rayleigh energy, both phase guards, all native iterate guards | GroundComplexNormBridge; GroundComplexResidualBudget; GroundOriginalBasinEstimates; GroundOriginalPositiveResiduals | Actual selector Lipschitz on the earned basin, full Euclidean norm bridge, actual sourced potential/energy budgets and geometric59/60 tail;28 fresh standard-only declarations | IEEE execution, first stopping index, independent sourcing consistency, other seed basins and18 offset instances remain separate |

| All18 original background-offset roots and actual readouts | Whole background boxes cover exact and rounded inputs; positive unit actual sourced ground/energy pairs, local root uniqueness, all-mixing legal native real fixed points; site0 field gap>3/10 and density gap>9/100 at-8/+10; offset0 actual branch identity | GroundUncertainBackgroundTube; GroundOffsets.Point000–017; GroundOriginalOffsets |18 fresh closed kernel root certificates;71 fresh standard-only declarations; actual coordinate positivity/density bridges and local uniqueness return | Native local stability, frozen-seed60-step offset verdicts, global nonlinear uniqueness, IEEE execution and physical Lambda remain separate; Newton contraction is not native contraction |

| All18 original background-offset native complex local attractors | Both signs, exact/rounded inputs and every background in their hulls; actual16-coordinate derivative norm<1; existential local radius and all native iterate guards | GroundUncertainBorderResponse; GroundOffsetStability.Point000–017; GroundOriginalOffsetStability | Distinct selector bordered response with inverse loss; two-sided kernel basis inverses; outward entry-cache inclusions; real/imaginary operator bounds and C1 native contraction;162 fresh standard-only declarations | Frozen-seed entry, sixty-update offset tests, uniform radius, global nonlinear uniqueness, IEEE execution and physical Lambda remain separate |

| All18 original background-offset explicit native basins | Both signs and whole input hulls; common coordinate radius1/400000, first17 radius1/40000; full16-column derivative contraction and all iterate guards with geometric errors | GroundUncertainNativeBox; GroundUncertainNativeBasin; GroundComplexIntervalBudget; GroundOffsetBasins.Point000–017; GroundOriginalOffsetBasins | Populated whole-ball selector/response/reciprocal/row arithmetic; outward caches; actual root ball geometry; active-only reflection;261 fresh standard-only declarations | Frozen-seed entry, sixty-update offset verdicts, IEEE execution, global nonlinear uniqueness and physical Lambda remain separate; no continuous scalar-offset interval claim |

| All18 rounded-offset original-seed infinite returns | Actual negative self-consistent ground limit, all native guards/unit states, geometric coordinate errors; site density limits and eventual endpoint site0 gap>9/100 | GroundCertifiedNativePrefix; GroundOffsetPrefixInitial; GroundCertifiedNativeEntry; GroundOffsetSeedReturn; GroundOffsetPrefix.Point000–017; GroundOriginalOffsetSeed |421 closed kernel steps, earned seams and actual root distance/explicit ball entry;956 fresh standard-only declarations | Exact uniform-offset and whole input-hull seed returns, sixty-update verdicts, IEEE execution, global nonlinear uniqueness and physical Lambda remain separate |

| All18 rounded-offset original-seed sixty-update verdicts | Fifteen pass all four source diagnostics; -5/-3/+10 fail the actual update tolerance while retaining eventual convergence | GroundComplexCoordinateBudget; GroundComplexFiniteBudget; GroundOffsetSelectorBudget; GroundOffsetSixtyPrefix; GroundOffsetSixtyTests; GroundOriginalOffsetSixty |132 fresh closed kernel extension steps; actual-current-source candidate and Rayleigh bounds; full16-column selector tails; both source phase calls;423 fresh standard-only declarations | Exact uniform-offset and whole input-hull seed returns, IEEE execution, first stopping index and physical Lambda remain separate; sourcing compares identical expressions |


## Registered native integration, 2026-10-06

The exact original twelve-sample aggregate and original eighteen-control
readout theorem supersede the corresponding historical pending statuses above.
All targets remain scoped to the declared mathematical source models.

| Registered group | Modules | New declarations | Exact scope |
|---|---:|---:|---|
| Native source campaign | 1734 | 20628 | Original12 finite/infinite returns; no classification of all intervening couplings. |
| Real seed returns | 4 | 6 | Supplied real initializations under declared guards. |
| Additional constructions | 29 | 132 | Specified background/coupling neighborhoods and cycle basins. |
| Mathematical execution | 3 | 18 | Guarded finite Option iteration, without IEEE emulation. |
| Normalization failure | 1 | 5 | Supplied unit starts and phase-related execution split. |
| Original-readout nonidentifiability | 1 | 9 | Two Boolean readouts fail to recover all18 original controls; richer readouts remain available. |
| Total | 1772 | 20798 | Full fresh registered statement audit and32574-query cumulative transitive-axiom audit. |

The repaired aggregate retains all eleven theorem headers. The exact mediator
strengthening recovers all four coordinates when both declared readouts factor
through a deterministic mediator; it does not prove an encoding-dimension lower
bound. Physical Lambda/spacetime transfer is outside the revised scope. The
unrevised paper is unchanged; the model results do not validate its unsupported
universal or physical claims. The actual registered receipts are in
`results/native_registered_stack_integration_run_2026-10-06`.
