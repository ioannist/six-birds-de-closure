# SbtCosmo Lean Project

This directory is the isolated Lean 4 project for Six Birds cosmology audit
receipts. The toolchain is pinned in `lean-toolchain` to
`leanprover/lean4:v4.28.0`.

Mathlib is now an explicit pinned dependency for the T3 Schur/adequacy target
and the LT1 derivation capstone target. The `mathlib` revision is recorded in `lake-manifest.json`
(`8f9d9cff6bd728b17a24e163c9402775d9e6a365` at R3). The mathlib-free root
target `SbtCosmo` does not import T3 or derivation capstones; the mathlib-backed
targets are `SbtCosmoAdequacy` and `SbtCosmoDerivation`.

Disclosure tiers and deferred items are tracked in
`manifests/coverage_table.md`. Kernel axiom closures for delivered theorems are
tracked in `manifests/trust_base.txt`.

## Modules

- `SbtCosmo.Common`: mathlib-free finite carrier and exact rational defect
  vocabulary shared by T1/T2.
- `SbtCosmo.Idempotence`: T1, certifying idempotent packaging fixed points and
  zero idempotence defect for packaged states.
- `SbtCosmo.RouteMismatch`: T2, certifying route-mismatch nonnegativity,
  zero-iff-commutation, and an explicit positive finite toy witness.
- `SbtCosmo.LocalGlobal`: T4, certifying the finite F4 local-global
  four-status classifier and the SN/BAO `eta != 1` compatible-non-global
  example.
- `SbtCosmo.Adequacy.Reconciliation`: T3, certifying the faithful
  positive-definite Schur PSD core and the exact-adequacy easy chain; this is
  a mathlib-backed module.
- `SbtCosmo.Adequacy.Support`: constructed finite real Moore-Penrose inverse,
  singular-support Schur positivity, full exact-adequacy cycle, optimal-residual
  identity, and faithful scalar-weight detection.
- `SbtCosmo.Derivation.AllocationPrice`: the original finite log/quadratic
  allocation family, constructed KKT existence, global optimality/uniqueness,
  price support and conditional sensitivity, with offset and boundary controls.
- `SbtCosmo.Derivation.ClosurePrice`: LT1/LT2 structural closure-price
  capstone, certifying the active-constraint zero-multiplier witness, the
  strict-sensitivity positive-multiplier witness, and the Schur-energy
  Lagrangian pairing. It proves no physical dark-energy bridge.
- `SbtCosmo.Holonomy`: T6, certifying a finite route-graph Hubble-holonomy
  nonzero-residue iff and the current-trivial / predictive-nontrivial witness.
- `SbtCosmo.PhantomStableReadout`: T5, certifying the finite P4 witness for
  P-dens plus S-stab/no-growing-mode by a rational Gershgorin certificate; it
  does not certify P-adeq or ghost absence.
- `SbtCosmo.AORStatus`: T7, certifying the canonical AOR status vocabulary and
  no-unstatused-residual well-formedness.
- `SbtCosmo.Derivation.AnalyticReadout`: a positive analytic density, its
  derivative, the phantom threshold, and consistency of the finite T5 samples.
- `SbtCosmo.Derivation.BackgroundSelection`: two admitted values refute a value
  forced by that predicate; equal records with different values obstruct
  factorization; the actual Step26 potential is background-dependent.

The October 2026 review corrects P-adeq to test `C * symC C R`, derives joint
Gram PSD, requires duplicate-free global states and closed route loops, and
adds conditional linear-offset KKT lemmas. The support extension now mechanizes
the finite real singular-native cycle. General convex duality and arbitrary
low-rank rewrite selection remain outside the local mechanization.

## Build

Run from this directory:

```bash
lake build
```

For a fresh transitive axiom disclosure, run:

```bash
lake env lean manifests/check_axioms.lean
```

The current 751-declaration raw receipt is
`manifests/axiom_audit_patch_count_2026-10-03.txt`.
Earlier dated receipts are preserved as historical evidence.

For a clean receipt:

```bash
lake clean
lake build
```

## Additional construction modules (2026-10-01)

`SbtCosmo.Derivation.GaugeClosure` derives the nonlinear density ledger from
the original feedback coefficient, proves optimizer and force-shift invariance,
and mechanizes simplex-projection uniqueness and every finite projected-gradient
history. Its maximal relative-record quotient gives an explicit non-descent
witness and excludes equivariant absolute-value selectors. This is a new
global-ledger carrier with signed equality prices, not unchanged Step26 or a
physical Lambda theorem.

`SbtCosmo.Derivation.PriorObstruction` proves a general weighted-mixture bound
and the 44-node frozen base instance: the original top-decade probability is
at most 8/11, below the 4/5 gate, under any lambda-only weighting retaining
that band. The CSV count premise is independently checked by
`scripts/de_restoration_constructions.py` using exact rational decimals.

The 2026-10-01 restoration axiom audit is
`manifests/axiom_audit_restoration_2026-10-01.txt`; the original 56-theorem
audit remains baseline evidence. Scope and unmechanized analytic arguments
are in `math/RESTORATION_CONSTRUCTIONS_2026-10-01.md`.

## Original-carrier proofs (2026-10-02)

`SbtCosmo.Derivation.CPLReadout` proves the actual audit's CPL density,
power/exponential bridge, derivative, positive expansion, same-history chart
identity, and exact phantom-crossing equation. Chart regularity does not prove
physical stability or ghost absence.

`SbtCosmo.Derivation.WindowRecords` proves the Boolean record equivalence,
tag-dependence counterexample, attained-amplitude threshold reduction, negative
horizon bound, and IID population-expression monotonicity. The original growth
ODE's strict lambda comparison, parameter sensitivity, and two-sided interval
proof are mathematical arguments in
`math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md`, not local Lean theorems.

The 113-theorem original-carrier axiom audit is
`manifests/axiom_audit_original_claims_2026-10-02.txt`, generated by
`manifests/check_axioms.lean`. Earlier audits remain historical evidence.

## Singular-support extension (2026-10-02)

`SbtCosmo.Adequacy.Support` constructs the inverse from a checked spectral
theorem, verifies all four Penrose identities and uniqueness, and proves
residual positivity, the complete four-way exact-adequacy equivalence, and
Loewner optimality at arbitrary native rank. It returns through an invertible
whitening map and agrees exactly with the older positive-definite residual.
The scalar audit theorem requires a faithful weight to detect zero residual.
Exact singular and zero-native examples are included.

The 155-theorem singular-support snapshot is
`manifests/axiom_audit_support_2026-10-02.txt`. Scope, original corpus targets,
and verification are in `math/SINGULAR_ADEQUACY_PROOFS_2026-10-02.md` and
`results/singular_adequacy_2026-10-02/verification.json`. The legal energy
quotient, empirical matrix realization, and physical Lambda bridge are not
constructed by these theorems.

## Original allocation carrier (2026-10-02)

`SbtCosmo.Derivation.AllocationPrice` constructs the original log/quadratic
carrier's KKT solution for all positive weights and curvatures and all
nonnegative budgets, including arbitrary offsets. It derives global
optimality, uniqueness, price monotonicity, active/slack behavior, and
`price=-V'` when the actual optimal cost value is differentiable at B>0.
Screening requires activity and a nonnegative rebased price. Exact controls
show weight-dependent prices, negative-offset slackness and zero-budget
price nonuniqueness.

The allocation snapshot covers 192 theorems, including all 37 in this module.
See `math/ALLOCATION_PRICE_PROOFS_2026-10-02.md` and
`results/allocation_price_2026-10-02/verification.json`. This strengthens the
original finite carrier; it does not mechanize unrestricted convex duality,
equate its allocation budget to Schur energy, or supply a physical bridge.

## Finite staging-rank law (2026-10-02)

`SbtCosmo.Derivation.StagingAudit` proves inclusive rank-tail cardinality
bounds for every score vector, including ties, and the finite weighted-law
return under equal index marginal masses. It proves common estimate-shift
invariance and an exact omission control refuting interpolated p95 as a
universal 5% rule with 20 mocks. Exchangeability is a separate applicability
premise; the real-data fitted anchor does not automatically supply it.

The historical staging audit covers 208 theorems, including all 16 in this module.
See `math/STAGING_RANK_PROOFS_2026-10-02.md` and
`results/staging_rank_2026-10-02/verification.json`. The repaired rank cutoff
preserves the original finite firing and detection-grid amplitudes. The frozen
preregistered tables retain their original empirical-quantile protocol.

## Imported duality and tensor-composition review (2026-10-02)

`SbtCosmo.Derivation.CapacityScale` constructs a finite cut minimum, its
supergradient, common-scale homogeneity and derivative, changed-unit sensitivity,
and the flow/potential pairing and weak-duality return. An explicit throughput
ceiling gives constructed active, slack and kink KKT certificates and optimizers.
The one-edge and two-edge-path examples distinguish area from edge prices and
prove path min-plus composition. A tight flow certificate is conditional on
its actual feasibility and tightness; general graph max-flow existence is not
locally mechanized. The imported 254-region graph is independently checked by
exact Python rational certificates, not reified in Lean.

`SbtCosmo.Derivation.TensorComposition` constructs Schmidt-diagonal pair tensors,
actual index contraction, reduced Gram and trace bridges, legal normalization,
and an exact entropy obstruction to the proposed min-plus gluing rule.

These modules do not justify the unchanged paper's intrinsic area-as-multiplier
identity, shared universal Born/area composition, or physical Lambda bridge.
The scalar-price repair requires a declared capacity shape and scale coordinate;
slack collapse needs the added ceiling. Scope, derivations and paper-phase options
are in `math/IMPORTED_DUALITY_PROOFS_2026-10-02.md`.
The 255-declaration raw audit includes all 47 new theorems from these modules.

## Adopted mediator strengthening and access fork (2026-10-02)

`SbtCosmo.Derivation.AccessFork` proves the adopted all-mediator strengthening:
on the declared four-bit carrier, determining both endpoint readouts is equivalent
to full-state recoverability and to injectivity. It constructs the full-state
decoder from the two endpoint decoders, gives the sharp 16-record bound, and
quantifies over all deterministic mediators rather than a finite competitor
list. Its generic four-mode version recovers coarse mode tuples on an arbitrary
carrier without claiming raw-field recovery. An XOR encoding is a positive
control. The actual uniform Boolean conditional means are separately constructed
from their fibers and proved idempotent and commuting, contrary to the old import.

`SbtCosmo.Derivation.FieldAccessBlock` constructs a non-commuting finite alternative
from the source's field-record density sector 4: the three mode-cell multiplicities
5,1,3 give actual weighted fiber averages and an exact 1/16 commutator on the
indicator of the potential-only perturbed cell. The source field-to-cell bridge
and full 54-record operators are independently checked in rational Python.
Removing that control restores commutation. This is an additional finite
construction with an explicit empirical record measure and variable background,
not non-commutation of the original uniform Boolean pair or physical quantization.

The 307-declaration access-fork audit includes all 52 new theorems in these modules.
The adopted theorem, derivations, controls and remaining physical bridge duties
are documented in `math/ACCESS_FORK_PROOFS_2026-10-02.md`. The source's 54 records
realize 15 full mode tuples; its marginal sizes 1,2,8,3 do not imply all 48
combinations occur. The paper and frozen experiment outputs remain unchanged.

## Native ground states and solver budgets (2026-10-02)

`SbtCosmo.Derivation.GroundState` constructs the actual eight-site real cycle
Hamiltonian, its energy identity and positivity propagation. It constructs the
uniform normalized lowest eigenvector and self-consistent fixed point for every
constant background and every real coupling, then returns this to a proof that
existence does not force one background value. It separately proves relaxation
fixed-point and normalized fixed-point preservation, and a scalar damping
stability criterion with an unstable-to-stable control.

The written proof covers every nonconstant real background and coupling using
the continuous positive ground selector and Brouwer. That proof is not locally
mechanized; no imported Brouwer axiom has been introduced. Native reruns give
15/18 background passes at 60 iterations and 18/18 at 120. Independent analytic
Jacobians check floating stability diagnostics on 30 approximate solutions.
The frozen source has a phase-sign error: its gap need not be a ray distance.
A corrected local helper and counterexample are tested; pinned runs are retained.
See `math/GROUND_STATE_PROOFS_2026-10-02.md` and
`results/ground_state_2026-10-02/`. The 327-declaration audit includes all 20
new GroundState theorems. This does not restore an existential coupling boundary
or prove background-independent dynamics or a physical cosmological value.

## All-parameter native ground existence (2026-10-03)

`GroundSelector` constructs the unique positive unit lowest eigenvector for
every real supplied potential and proves continuity. `GroundSimple` proves
simplicity for arbitrary signed lowest eigenvectors. `GroundFixedPoint` constructs
the continuous probability-simplex map and applies a vendored, kernel-checked
Brouwer proof to obtain a self-consistent ground vector for every original real
background and coupling. `GroundComplex` returns the eigen equation, sourcing,
normalization and minimality against every complex competitor, and proves the
complex lowest eigenspace is one-dimensional.

The additional default target `SbtCosmoBrouwer` builds the pinned MIT-licensed
Scarf/Brouwer import. Its complete source provenance and 4.28.0 port are in
`Gametheory/PROVENANCE.json` and `Gametheory/port.patch`; no toolchain upgrade or
Brouwer axiom is used. Only those two upstream modules enable automatic implicit
variables; the local package settings remain unchanged. The expanded audit
includes imported `Brouwer` and all 52 new local theorems. Its 380 transitive
closures use only `propext`, `Classical.choice` and `Quot.sound`.

The new theorem supersedes the earlier unmechanized all-background status, while
the earlier 2026-10-02 receipts remain historical. See
`math/GROUND_EXISTENCE_LEAN_2026-10-03.md` and
`results/ground_existence_2026-10-03/verification.json`. Exact existence does not
imply numerical convergence, nonlinear uniqueness, a stability boundary,
background-blind dynamics or a physical Lambda bridge.

## Exact growth comparison and history return (2026-10-03)

`SbtCosmo.Derivation.GrowthComparison` proves a cooperative cone estimate from
squared negative parts and Grönwall, strict positivity, strict growth ordering
in time and lambda, and uniqueness for the exact original IVP. It constructs
coefficient bounds on the live compact interval and derives that interval's
positivity from the original horizon cutoff. The scale-factor acceleration and
both chain-rule bridges return to the implemented equation. The lambda-zero
solution is constructed. Full record histories return to the attained-amplitude
threshold, and the fixed-tag gate is downward closed in lambda on the live branch.

The supplied `GrowthSolution` record contains the differential equations and
initial conditions only, with continuity; it assumes none of the conclusions.
Constructing it for every live lambda, parameter dependence, the infinity limit
and the complete upper-endpoint certificate remain pending. The new note gives
an explicit quadrature construction for the next step. See
`math/GROWTH_COMPARISON_LEAN_2026-10-03.md` and
`results/growth_comparison_2026-10-03/verification.json`. The 408-declaration
transitive audit includes all 28 new theorems and only the three disclosed axioms.

## Constructed growth IVP and continuity (2026-10-03)

`GrowthExistence` constructs the original log-time solution at every live
lambda using an explicit square-root/integral formula. Both equations, both
initial values, integrability, endpoint derivatives and the exact coefficient
bridge are proved. A locally identical regularized integral proves parameter
continuity without changing the solution. The previously conditional comparison
theorems now apply to this constructed family; final growth is continuous and
strictly decreasing on the live branch.

`GrowthScaleReturn` proves the inverse change of variable and returns both
derivatives and native initial values to the implemented scale-factor IVP.
Its endpoint continuity and strict lambda ordering use only the original
positive scales and live horizon cutoff. This supersedes the all-lambda
existence/continuity gap in the preceding dated packet. Differentiability in
lambda, the infinity limit and the complete ranked-seed endpoint certificate
remain pending locally.

The 444-declaration transitive audit includes all 36 new theorems (27 quadrature
and continuity, 9 scale-return). The default build passes 8062 jobs with warnings
as errors. See `math/GROWTH_EXISTENCE_LEAN_2026-10-03.md` and
`results/growth_existence_2026-10-03/verification.json`. Paper, runtime code and
frozen experiment artifacts remain unchanged.

## Constructed infinity limit and native record window (2026-10-03)

`GrowthLimit` bounds the actual finite-start IVP error for lambda>=0 by
`(3/2) exp(L) L/(1+lambda*a0³)` and proves that its endpoint tends to
`3/2-exp(-2L)/2`. The proof compares with the matter IVP, bounds the forcing,
and applies integrating-factor derivative fences. No asymptotic law is a premise.

`GrowthWindow` uses that limit, the proved parameter continuity and strict
ordering to construct a unique positive endpoint for every threshold strictly
between the limiting and matter growth values. It proves the exact window
`(-A^-3,upper]`, returns it to native scale factor, and proves the same result
for the original two-tag continuous collapse history. Fixed nonnegative
amplitudes, positive attained tagged maxima and the two threshold inequalities
are explicit premises of the record theorem. No endpoint or solution is supplied.

The full default build passes; the 461-declaration transitive audit includes
all 17 new theorems (10 limit and 7 window). The proof and adversarial self-review
are in `math/GROWTH_WINDOW_LEAN_2026-10-03.md`, with fresh verification in
`results/growth_window_2026-10-03/`. Formal construction of the twelve-seed
aggregate rank, parameter differentiability and interval-certified numerical
edge locations remain separate obligations. Paper, frozen source and runtime
code remain unchanged in this packet.

## Original twelve-seed aggregate continuum window (2026-10-03)

`GrowthPopulation` constructs finite attained maxima and a finite k-th
threshold, proves rank/count equivalence without dropping ties, and returns
native continuous record histories to seed-count aggregation. Its general
window theorem states all population and rank certificate inputs explicitly.

`WindowSampleData` reifies the original 12×64 amplitude/tag arrays and checks
all 24 tagged maxima, exact seed thresholds and rank counts with
`decide +kernel`. `WindowSample` transfers these rational proofs to the real
ODE domain, proves that 80% of twelve means at least ten passes, and discharges
all inputs of the original aggregate continuum window. Its final theorem has
no supplied solution, maxima, rank or threshold-inequality premise:

```
exists unique upper>0,
  D_native(upper,20)=971912828383572000768/1012057850670495125,
  and for every real lambda the realized gate holds iff -1/8000<lambda<=upper.
```

The gate is the expanding-branch persistence cutoff and ten seed record
histories containing both tag values. The exact model uses the declared decimal
a0=1/1000, A=20 and delta=843/500; realized IEEE amplitudes are represented
exactly. The NumPy RNG and floating integration are not formalized. Reproduce
and verify the input bridge with the sbt-de Python:

```
python scripts/de_window_reification.py
python scripts/de_window_reification_check.py
```

The first command regenerates expected bytes in memory and compares both
artifacts; use `--write` explicitly to regenerate them. The second captures
actual arrays from the original `run_seed` sampler without a growth solve,
compares every amplitude/tag, and checks mutation controls. The sampler's
record verdict under the capture stub is not used as evidence.

The full default build passes 8067 jobs. The fresh 484-declaration transitive
audit includes all 23 new theorems (8 population, 4 rational data, 11 sample).
Only the previously disclosed standard axioms are permitted; no `native_decide`
is used. See `math/WINDOW_POPULATION_LEAN_2026-10-03.md` and
`results/window_population_2026-10-03/verification.json`. Numerical edge
accuracy, parameter differentiability and the physical bridge remain separate
obligations. The paper and original runtime/frozen source are unchanged.

## Continuous endpoint and population sensitivity (2026-10-03)

`GrowthRankSensitivity` constructs the finite rank function from the earlier
existence proof and proves its monotonicity, positive homogeneity and global
1-Lipschitz bound in the finite maximum metric. `GrowthEndpointSensitivity`
constructs the unique positive endpoint function, proves continuity and strict
threshold decrease, and proves strict positive-edge increase with log horizon
when the same threshold is admissible at both horizons.

`GrowthPopulationSensitivity` constructs the actual fixed-tag maximum
functions, proves them 1-Lipschitz, and returns continuous amplitude/delta
perturbations through maxima, rank and endpoint. Ranking and maximizing-patch
switches are allowed. Nonzero tagged maxima and an admissible aggregate
threshold are explicit; the native window theorem derives its positive maxima
from positive tagged patch witnesses and preserves the original record gate.

`WindowSensitivity` identifies these constructed functions with the original
reified maxima/rank. For exact common amplitude multiplier s and collapse
threshold delta it proves `T(delta,s)=T0*delta/(delta0*s)`, an exact native
aggregate window throughout `delta in [1.2,2]`, `s in [1/3,3]`, continuity on
that entire rectangle, strict endpoint decrease with delta and strict increase
with s. The coupling retains the same amplitudes/tags before real rescaling;
no claim equates separately rounded/reseeded runtime populations.

The full default build passes 8071 jobs. The fresh 524-declaration audit
includes all 40 new theorems (8 rank, 6 endpoint, 13 population, 13 original
realization). Only the disclosed standard axioms are permitted. See
`math/WINDOW_SENSITIVITY_LEAN_2026-10-03.md` and
`results/window_sensitivity_2026-10-03/verification.json`. Differentiability
and smooth sensitivity remain unmechanized; continuity is not substituted for
them. Numerical edge accuracy and the physical bridge remain separate. Paper,
original Python runtime, reified input data and frozen source are unchanged.


## Actual growth derivatives and C1 endpoint sensitivity (2026-10-03)

`GrowthParameter` differentiates the actual finite-start quadrature using a
constructed uniform root margin and compact domination. It proves the time
variational equations directly, zero sensitivity at the initial time, and
strictly negative growth/velocity sensitivities at every positive live time.
It returns parameter derivatives and strict negativity to both original
scale-factor growth and its scale derivative for all lambda > -A^-3.
Parameter sensitivity is continuous on the live domain.

`GrowthEndpointDerivative` proves C1 growth on the entire open live horizon
and C1 threshold-to-endpoint dependence on the admissible threshold interval.
The endpoint derivative is the reciprocal of the strictly negative final
growth derivative. For the original population under exact common amplitude
rescaling, the two-variable endpoint is C1 at every point of the full declared
delta/scale rectangle, including its boundary points. The exact delta
partial derivative is negative, and the amplitude-scale partial is positive.
This proves continuous first derivatives; no infinite-order differentiability
or smoothness through arbitrary maximizing/ranking switches is asserted.

The full default build passes 8073 jobs. All 40 new theorems (29 growth,
11 endpoint) are included in the fresh 564-declaration transitive axiom audit,
with only the previously disclosed standard axioms. Twenty-five exported
statements are checked separately. See
`math/GROWTH_PARAMETER_LEAN_2026-10-03.md` and
`results/growth_parameter_2026-10-03/verification.json`. Numerical edge
certification and physical identification remain separate obligations. Paper,
original runtime, reified inputs and frozen source are unchanged. Earlier
packet receipts retain their historical scope.


## Certified original-population endpoint bracket (2026-10-03)

`GrowthQuadrature` proves the exact native-scale growth quadrature with its
parameter-dependent finite-start term and prefactor. It proves whole-cell
polynomial/square enclosures for the native integrand and returns their finite
sums to the entire native integral.

`GrowthQuadratureData` checks all 264 rational cells and both sum bounds with
`decide +kernel`. Generate/replay with the sbt-de Python:

```
python scripts/de_growth_quadrature_certificate.py
```

The default command replays expected bytes. --write explicitly regenerates the
Lean certificate and cells.json. Only Fraction arithmetic and integer isqrt
are used; a deliberately false lower certificate is rejected. No floating
arithmetic or solver output is used as a proof dependency.

`WindowEdgeCertified` proves D_native(3,20)>964, D_native(4,20)<936 and
960<T*<961, and therefore 3<upper<4. It identifies upper with the earlier
C1 scaling endpoint at the original delta and scale. The paper's 2.33-inside
and 5.31-outside witnesses are proved for the exact continuum gate. A unique
certified-window theorem retains the same twelve reified populations and
native history gate for all real lambda.

The full default build passes 8076 jobs. The 593-declaration transitive axiom
audit includes all 29 new theorems (12 quadrature, 5 data, 12 endpoint); only
the disclosed standard axioms are permitted. Twenty-three exported statements
are checked separately. See `math/GROWTH_QUADRATURE_LEAN_2026-10-03.md` and
`results/growth_quadrature_2026-10-03/verification.json`. This certifies the
mathematical bracket, not the original floating solver's error or total
correctness. Paper, original runtime, population reification and frozen source
are unchanged. Ratio/record-time certification and physical identification
remain separate obligations.

## Original first-record times and coincidence ratios (2026-10-03)

`GrowthFirstRecord` constructs the unique first-threshold time from the actual
native IVP and proves its threshold equivalence, matter lower bound and strict
parameter ordering. `WindowFirstRecord` constructs the all-patch maximum of
the original population, rather than using its both-tag record threshold. It
returns the chosen root to the earliest collapse of any original patch. The
ratio is exactly abs(lambda)*a_first^3, the original lambda-to-matter readout.

`WindowFirstRecordData` imports the unchanged population and checks all twelve
first thresholds between 500 and 897. A separate 384-cell prefix certificate
proves integral(3,1/1000,2)>=204/1000 and D_native(3,2)>901. Thus all original
first times are in (1/2,2] on [0,3]. The ratio is strictly increasing there,
R<=8*lambda, 1/8<R<=24 on [1,3], and 3/8<R(3)<=24. The earlier endpoint
bracket proves 3/4<3/lambda_plus<1. These are original-population bounds in
declared native units, not universal bounds for arbitrary input populations.

For every epsilon>0, a single positive lambda<=1 passes the aggregate gate
while all twelve ratios lie in (0,epsilon). This is a continuum strengthening
of the paper's finite-grid no-pinching negative. No limiting-time or
solver-convergence premise is supplied.

```bash
python scripts/de_first_record_certificate.py
cd lean
lake build
lake env lean manifests/check_first_record_statements.lean
lake env lean manifests/check_axioms.lean
```

The replay command checks exact generated bytes and a false lower-certificate
control. All rational cell/sum inequalities are independently checked by Lean's
kernel. The full build passes 8079 jobs; the fresh 629-declaration audit includes
all 36 new theorems (9 general, 4 data, 23 original-return), and all 36 exported
statements are separately checked. See `math/FIRST_RECORD_LEAN_2026-10-03.md`
and `results/first_record_2026-10-03/verification.json`. The exact positive
endpoint ratio, other robustness populations and floating solver errors remain
outside this packet's coverage.

## Ratios at the actual positive endpoint (2026-10-03)

`GrowthQuadratureSharp` proves the derivative of the actual integrand's square,
its increase/decrease on either side of 2*lambda*a^3=1, and its global peak
bound by an exact polynomial factorization. Lower endpoint bounds and either
an upper endpoint or the global peak then enclose each entire cell. The actual
interval integrals return these bounds without sampled interpolation.

`WindowEndpointRatioData` kernel-checks 704 cells over [1/1000,20] and their
512-cell prefix ending at 5/2, for lambda=17/5. Exact integral bounds give
D_native(17/5,20)<960 and D_native(17/5,5/2)>901. `WindowEndpointRatio` proves
3<lambda_plus<17/5 and extends the SAME first-time and ratio functions to the
entire [0,lambda_plus] domain. It proves actual collapse attainment and no
earlier collapse for every seed, with choice defaults excluded.

For all original seeds, 1/2<a_first<=5/2 and R<=125*lambda/8 throughout that
domain. Consequently R<425/8=53.125 throughout the entire nonnegative admitted
window, and 3/8<R<425/8 on [3,lambda_plus], including the actual endpoint.
First time and ratio are strictly increasing on [0,lambda_plus]. This gives
continuum support for the original toy's qualitative upper-edge ratio claim;
the earlier simultaneous arbitrarily small positive ratios retain the
no-pinching negative. The result is scoped to the original population and
declared units, and does not certify the finite-grid maximum 17.4 as a
continuum maximum.

```bash
python scripts/de_endpoint_ratio_certificate.py
cd lean
lake build
lake env lean manifests/check_endpoint_ratio_statements.lean
lake env lean manifests/check_axioms.lean
```

The exact byte replay and false lower/upper certificate controls pass. Numeric
vector syntax is chunked into at most 128 entries while all cells use natural
adjacent indices. Kernel checking and all existing lint/build settings remain
enabled. The full default build passes 8082 jobs. The fresh 663-declaration
standard-only axiom audit includes all 34 new theorems (9 sharp-integrand,
5 data, 20 original-return); all 34 statements are separately checked. See
`math/ENDPOINT_RATIO_LEAN_2026-10-03.md` and
`results/endpoint_ratio_2026-10-03/verification.json`. Negative-parameter first
times, other sampled robustness populations, floating solver error and physical
identification remain separate obligations.

## Actual first records on the entire signed window (2026-10-03)

`GrowthFirstRecordLive` constructs the first-threshold root whenever
lambda>-1/A^3, the native interval is positive and ordered, and 1<T<=D(A).
It derives the native initial value on this full live domain and proves root
existence/uniqueness, threshold equivalence, strict parameter ordering and
equality with the prior nonnegative-domain choice. The old positive definition
is unchanged; its fallback is not used as a negative first-record witness.

For live nonpositive lambda, the exact matter IVP and parameter comparison give
D_lambda(a)>=a/a0, hence firstTime<=a0*T. At zero firstTime=a0*T exactly.
`WindowSignedRecord` discharges reachability for every original seed from the
actual original aggregate gate and checked first thresholds. It returns the
new live-domain choice to actual earliest collapse, with no earlier collapse,
throughout (-1/8000,lambda_plus]. Both choice defaults are excluded wherever
their equality is asserted.

For every admitted negative lambda and original seed,
0<firstTime<897/1000 and 0<R<1/8000. Equality on the nonnegative overlap returns
the prior upper bound to the entire signed window: 0<=R<425/8=53.125.
The actual endpoint bound 3/8<R<425/8 and simultaneous arbitrarily small
positive ratios are retained for this same signed readout. First time is
strictly increasing across the signed domain; no full signed ratio ordering
is claimed. At zero firstTime=T_first/1000 and R=0.

```bash
lake build
lake env lean manifests/check_signed_record_statements.lean
lake env lean manifests/check_axioms.lean
```

The full default build passes 8084 jobs. The fresh 694-declaration standard-only
axiom audit includes all 31 new theorems (10 general live-domain, 21 original
signed return), and all 31 exported statements are separately checked.
There are no new numeric certificates; previous certificate artifacts are
unchanged. See `math/SIGNED_RECORD_LEAN_2026-10-03.md` and
`results/signed_record_2026-10-03/verification.json`. The subsequent packet below now constructs the negative outside history.
Separately sampled patch-count controls, floating solver errors and physical
identification remain separate obligations.


## Negative outside history and declared erasure (2026-10-03)

`GrowthNegativeBounds` derives the generic native bound D<5*a/(3*a0) for every
live nonpositive parameter. `GrowthNegativeLower` constructs an exponential
subsolution, proves its residual sign from the actual coefficient and applies
the cooperative theorem to derive a lower bound for the actual finite-start IVP.
No growth bound, count or subsolution witness is supplied as a return premise.

`WindowErasureData` checks the original seed-1100 count of 58 and the exact gap
between growth 17000 and 26000, plus explicit opposite-tag witnesses. It imports
the unchanged original population. `WindowErasureWitness` constructs turnaround
in (15.4,15.5), proves actual growth at 15 exceeds 17000 and is below 26000
throughout the expanding branch, and returns the exact count to actual collapse
histories. All 58 collapses occur before the original turnaround buffer.
The original declared erasure gives zero retained records and failure of final
record-bearing. No physical evolution through a crunch is asserted.

The witness uses the exact binary parameter from the full-precision original
readout (-0.00027000000000000006), rather than the rounded CSV field.
Initialization and delta remain the declared exact decimal mathematical model
scalars, as in earlier continuum packets. Floating solver arithmetic is separate.
The historical distinct_tags_final column is a clipped bookkeeping indicator,
not an actual final retained-set cardinality; it is not interpreted as one.

```bash
lake build
lake env lean manifests/check_negative_erasure_statements.lean
lake env lean manifests/check_axioms.lean
python3 ../scripts/de_negative_erasure_check.py
```

The full default build passes 8088 jobs. The fresh 728-declaration standard-only
axiom audit includes all 34 new theorems, and all 34 exported statements are
separately checked. Original-input replay and false count/gap controls pass.
See `math/NEGATIVE_ERASURE_LEAN_2026-10-03.md` and
`results/negative_erasure_2026-10-03/verification.json`. The paper, original
runtime, reified population and earlier evidence packets are unchanged.


## Original patch-count robustness windows (2026-10-03)

`WindowPatchCountData` reifies all amplitudes and tags of the separately realized
N=32/N=128 original twelve-seed populations. It kernel-checks all 1,920 inputs,
48 attained positive tagged maxima, seed thresholds, nine-below/ten-at ranks,
admissibility bounds and exact threshold ordering against unchanged N=64.
False denotes N=32 and true N=128 in the finite variant API.

`WindowPatchCounts` returns these certificates to the actual continuous native
collapse histories, the original 80% aggregate criterion, and each unique
positive endpoint. All real lambdas have the exact window (-1/8000,upper_N].
It proves upper_32 < the unchanged upper_64 < upper_128, actual gate inclusions,
strict endpoint witnesses, zero-parameter passes and failure at the cutoff.
The ordering is derived from actual thresholds and actual IVP antitonicity.
Changing N shifts tag draws; no population inclusion or universal reseeding
monotonicity is assumed. A derivative in discrete N is not asserted.

```bash
lake build
lake env lean manifests/check_patch_count_statements.lean
lake env lean manifests/check_axioms.lean
/mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin/python ../scripts/de_patch_count_reification.py
```

The full default build passes 8090 jobs. The fresh 751-declaration standard-only
axiom audit includes all 23 new theorems, and all 23 exported statements are
separately checked. Exact byte replay includes the unchanged N=64 population;
false rank controls pass. No solver or Python test-suite rerun is claimed.
See `math/PATCH_COUNT_WINDOWS_LEAN_2026-10-03.md` and
`results/patch_count_2026-10-03/verification.json`. Earlier proof modules,
original runtime and inputs, paper, frozen external source and receipts are
unchanged. Fine numeric edges and ratios for these new populations and the
eternal-persistence limit remain separate obligations.


## Actual infinite-time growth and perpetual records (2026-10-03)

`GrowthInfinite` constructs the positive-lambda time limit of the original IVP
using a proved integrable improper integral, dominated-convergence parameter
continuity and the actual increasing velocity/growth gap. It proves finite
values strictly below the limit, a global bound and the parameter-infinity
limit 3/2. `GrowthEternalWindow` constructs unique positive limiting roots for
every a0>0,T>3/2, exact finite-epoch attainment and perpetual horizon cutoff.
`WindowEternalRecords` returns these results to the unchanged original twelve
seed populations. The eventual-formation/perpetual-retention window is exactly
[0,u_infinity), u_20<u_infinity; at u_infinity only nine seeds can ever form
both tag records. The required count is ten. Fixed formation by a=20 with
perpetual retention instead gives [0,u_20]. Sufficiently large lambda prevents
any original patch collapsing at any finite epoch (coarse cutoff 10^9).

```bash
lake build
lake env lean manifests/check_eternal_window_statements.lean
lake env lean manifests/check_axioms.lean
python3 ../scripts/de_eternal_window_verify.py
```

The default build passes 8093 jobs; the fresh standard-only axiom audit covers
798 declarations, including all 47 new theorems, whose statements are also
checked. See `math/ETERNAL_WINDOW_LEAN_2026-10-03.md` and
`results/eternal_window_2026-10-03/verification.json`. The paper and previous
proof/evidence packets are unchanged. No original solver, reification or Python
test-suite rerun is claimed. These are exact declared-toy returns, with no
physical Lambda identification or integrated physical crunch asserted.


## Quantitative horizon limit and eternal robustness (2026-10-03)

`GrowthInfiniteTail` derives an explicit native remaining-growth bound from
the actual velocity. `GrowthHorizonLimit` proves guards, strict ordering and
convergence of actual finite-horizon roots. `WindowEternalBounds` returns this
to the original gate, identifies its a=20 root with the old endpoint, certifies
3<u_infinity<4, and proves the actual open window's closed envelope.
`WindowEternalPatchCounts` constructs the actual N=32/N=128 eternal windows,
strict nesting with N=64, exact nine-pass endpoint controls and all-time
record starvation. Original populations and proof modules are unchanged.

```bash
lake build
lake env lean manifests/check_horizon_limit_statements.lean
lake env lean manifests/check_horizon_limit_axioms.lean
python3 ../scripts/de_horizon_limit_verify.py
```

The default build passes 8097 jobs. All 32 new statements and transitive axiom
closures are freshly checked; the 830-declaration cumulative audit preserves
the exact previously audited 798-declaration prefix, with proof-source and
toolchain identity checked. The entire 830-declaration command was not rerun;
`lake env lean manifests/check_axioms.lean` remains the full recomputation.
See `math/HORIZON_LIMIT_LEAN_2026-10-03.md` and
`results/horizon_limit_2026-10-03/verification.json`. No original solver,
reification or Python test-suite rerun is claimed. The paper is unchanged.


## Actual first-record ratios at the infinite edge (2026-10-03)

`WindowEternalRatioData` kernel-checks an exact refined 1024-cell upper
certificate. `WindowEternalRatioCertified` derives 3<u_infinity<17/5 from that
finite native quadrature and the actual remaining-growth bound.
`WindowEternalRatio` discharges the existing first-time selector's guards on
all of [0,u_infinity] and proves global finite-epoch earliestness for the same
original first-any-patch readout. First time lies in (1/2,5/2], is strictly
increasing, and gives 3/8<R<425/8 at the infinite edge. Every epsilon>0 has a
positive admitted lambda with all twelve ratios positive and below epsilon.

```bash
lake build
lake env lean manifests/check_eternal_ratio_statements.lean
lake env lean manifests/check_eternal_ratio_axioms.lean
python3 ../scripts/de_eternal_ratio_certificate.py
python3 ../scripts/de_eternal_ratio_verify.py
```

All 25 new statements/closures pass; the full default build passes 8100 jobs.
The cumulative standard-only audit covers 855 declarations using the exact
immutable previously audited 830 prefix and freshly checked 25 suffix, with
old proof/toolchain identity checked. The entire cumulative command was not
rerun. See `math/ETERNAL_RATIO_LEAN_2026-10-03.md` and
`results/eternal_ratio_2026-10-03/verification.json`. The nine eventual both-tag
passes at the upper endpoint still fail the ten-pass aggregate criterion.
The paper and previous proof/evidence packets are unchanged.


## Original all-time starvation at lambda>=32 (2026-10-03)

`WindowStarvationData` kernel-checks an exact 64-cell native upper certificate
at lambda=32. `GrowthStarvationCertified` combines the original finite-start
quadrature with the derived actual time tail to prove D_infinity(32)<485,
then parameter ordering gives D(lambda,a)<485 for every lambda>=32 and finite
a>=a0. `WindowGlobalStarvation` earns the amplitude margins for every original
N=32,64,128 patch, proves no collapse ever, and returns zero original both-tag
record counts at every horizon. This sharpens the previous sufficient cutoff
10^9 without changing populations or asserting an optimal starvation cutoff.

```bash
lake build
lake env lean manifests/check_global_starvation_statements.lean
lake env lean manifests/check_global_starvation_axioms.lean
python3 ../scripts/de_global_starvation_certificate.py
python3 ../scripts/de_global_starvation_verify.py
```

The full default build passes 8103 jobs. All 19 new statements/transitive
closures are freshly checked. The standard-only cumulative audit has 874
ordered declarations, using an exact immutable previously audited 855 prefix
plus fresh 19 suffix, with earlier proof/toolchain identity checked. The entire
cumulative command was not rerun. Exact replay/false-certificate controls and
independent rational checks of all 2688 original patch margins pass. See
`math/GLOBAL_STARVATION_LEAN_2026-10-03.md` and its evidence packet. The paper,
original runtime/populations, and previous proof/evidence packets are unchanged.


## Derived original allocation value regularity (2026-10-03)

`AllocationSensitivity` derives the original carrier price's Lipschitz bound
with K=sum_i(w_i+c_i), then bounds the actual optimal cost's quadratic remainder.
It constructs HasDerivAt V (-price(B)) B for every B>0, and proves C1 value with
Lipschitz derivative through arbitrary patch active-set and active/slack switches.
It also derives negative derivative iff B<S(0), and certifies exact central
finite-difference price error <=K*h/2 for 0<h<B. Concrete existing heterogeneous
examples have derivatives -1/-2; an active one-patch budget has price/derivative0.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_allocation_sensitivity_statements.lean
lake env lean -DwarningAsError=true manifests/check_allocation_sensitivity_axioms.lean
python3 ../scripts/de_allocation_sensitivity_verify.py
```

All 21 new statements/transitive closures pass; full default build 8104 jobs.
The standard-only cumulative audit has 895 ordered declarations, preserving an
exact immutable previously audited 874 prefix plus fresh 21 suffix with old
proof/toolchain identity checked. The full cumulative command was not rerun.
See `math/ALLOCATION_SENSITIVITY_LEAN_2026-10-03.md` and its receipts. The paper,
original optimizer/runtime and previous proof/evidence packets are unchanged.
No B=0 derivative, C2 value, differentiable price, Schur-budget equivalence,
physical Lambda bridge or floating solver correctness is claimed.


## Constructed scalar convex price and actual Schur return (2026-10-03)

`ConvexClosurePrice` defines the actual feasible-cost infimum and constructs a
positive scalar dual certificate from convex primal mixing and its actual
negative value derivative. Activity is derived. Global Lagrangian minimization,
finite primal/dual equality, guarded weak duality and identification of every
certificate price with the derivative are proved. Ordinary optimizer existence,
local finite value and differentiability remain explicit generic inputs.

`SchurClosurePrice` derives convexity of the actual singular-support Schur energy
for affine dissolving probes, fixed native probes and PSD W, then returns to the
unchanged positive-definite energy/Lagrangian. `SchurClosurePriceExamples` earns
its own sqrt(B) optimizer, actual finite value and derivative in a singular-native
Schur program, constructing price1 at B1. A varying-native midpoint example is
proved nonconvex; fixed-native convexity is not silently generalized.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_convex_closure_price_statements.lean
lake env lean -DwarningAsError=true manifests/check_convex_closure_price_axioms.lean
python3 ../scripts/de_convex_closure_price_verify.py
```

Full build8107; all34 new statements/transitive closures pass. Cumulative929
uses exact immutable earlier895 prefix plus fresh34 suffix with prior proof/
toolchain identity checked; the entire cumulative command was not rerun.
See `math/CONVEX_CLOSURE_PRICE_LEAN_2026-10-03.md` and its receipts. The paper,
original runtime and previous proof/evidence are unchanged. Generic real-value
hypotheses are explicit; full extended-real split subdifferentials, Loewner
matrix duality and physical Lambda identification are not claimed mechanized.

## Extended-objective scalar price and actual Schur return (2026-10-03)

`ExtendedClosurePrice` starts from the actual EReal infimum and a convex real
epigraph with no minus-infinity objective values on A. It earns the effective
domain, its real objective convexity, finite real-cost guards and exact infimum
equality. Local equality transfers the actual finite-value derivative to the
constructed scalar theorem. The returned extended certificate covers every
original point, derives activity, and has actual finite primal/dual equality.
Competing nonnegative prices obey complete-lattice weak duality, including
minus-infinity dual infima without real default values.

`ExtendedSchurClosurePrice` earns actual support-residual energy convexity for
fixed native L, PSD W and affine D. `ExtendedClosurePriceExamples` applies it to
e=x^2 and J=(x-2)^2 on x>=0, plus infinity otherwise. It independently proves
the optimizer/value/derivative and constructs price1 at B1. A control certifies
that unrestricted toReal admits the forbidden x=-1 and yields value0 instead
of the true extended value1.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_extended_closure_price_statements.lean
lake env lean -DwarningAsError=true manifests/check_extended_closure_price_axioms.lean
python3 ../scripts/de_extended_closure_price_verify.py
```

Full build8110; all24 statements/transitive closures freshly checked.
Cumulative953 uses exact immutable earlier929 plus fresh24, with prior proof/
toolchain identity checked; full cumulative command not rerun. See
`math/EXTENDED_CLOSURE_PRICE_LEAN_2026-10-03.md` and its receipts. Paper, original
runtime and prior evidence unchanged. Objective-domain reduction is now proved;
separate qualified subdifferential/normal-cone splitting, matrix duality and
physical Lambda identification remain separate obligations.

## Constructed differentiable-value matrix closure price (2026-10-03)

`ConeClosurePrice` constructs minus the actual finite infimum's Frechet
derivative as a cone-positive dual. Primal mixing earns global support and
complementarity; certificate-derived guards give actual finite primal/dual
equality. Ordinary optimizer, local nonempty/bounded-below actual costs and
actual derivative remain explicit inputs.

`MatrixPriceRepresentation` constructs a symmetric trace representative from
symmetrized matrix units, proves its exact trace evaluation, and earns PSD from
rank-one cone tests. `MatrixClosurePrice` proves actual Schur Loewner convexity
for fixed native L and affine D, applies the conic theorem on the symmetric
budget space, and returns a nonzero PSD matrix certificate when the actual
derivative is negative in some PSD direction. Complementarity is a trace
pairing; full zero matrix slack is not asserted.

`MatrixClosurePriceExamples` proves an exact return of the actual one-by-one
Schur feasible set/value to the earlier scalar program and constructs its
actual matrix derivative and PSD price. An exact two-by-two control has nonzero
PSD price and slack with zero trace pairing.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_matrix_closure_price_statements.lean
lake env lean -DwarningAsError=true manifests/check_matrix_closure_price_axioms.lean
python3 ../scripts/de_matrix_closure_price_verify.py
```

Full build8114; all32 fresh statements/transitive closures checked. Cumulative985
uses exact immutable earlier953 plus fresh32, with proof/toolchain identity
checked; full cumulative command not rerun. See
`math/MATRIX_CLOSURE_PRICE_LEAN_2026-10-03.md` and its receipts. Paper, original
runtime and prior proofs/evidence unchanged. General nonsmooth Slater duality,
qualified split stationarity, matrix extended-objective reduction and physical
Lambda identification remain separate obligations.

## Extended-objective conic and matrix price (2026-10-03)

`ExtendedConeClosurePrice` defines the actual complete-lattice conic infimum
for the original EReal objective, earns finite-cost guards and exact infimum
equality on the effective domain, and transfers its actual finite-value Frechet
derivative. The constructed cone-positive price returns to every original
admissible point with complementarity and global extended Lagrangian minimization.
Actual extended primal/dual equality and finite certificate dual value are
proved. Competing complete-lattice duals safely retain minus infinity.

`ExtendedMatrixClosurePrice` uses actual singular-support Schur residuals,
earned Loewner convexity and symmetric budget topology to construct a nonzero
PSD trace price for a genuinely extended objective. No dual, complementarity,
energy-convexity field or full matrix activity is assumed.
`ExtendedMatrixClosurePriceExamples` proves an exact extended scalar return,
constructs the actual matrix derivative and returns primal/dual value1. Its
control proves that unrestricted toReal gives matrix value0 instead of1.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_extended_matrix_price_statements.lean
lake env lean -DwarningAsError=true manifests/check_extended_matrix_price_axioms.lean
python3 ../scripts/de_extended_matrix_price_verify.py
```

Full build8117; all18 fresh statements/transitive closures checked. Cumulative1003
uses exact immutable earlier985 plus fresh18 with proof/toolchain identity
checked; full cumulative command not rerun. See
`math/EXTENDED_MATRIX_PRICE_LEAN_2026-10-03.md` and its receipts. Paper, original
runtime and previous proof/evidence unchanged. Extended-objective matrix
reduction is now proved; general nonsmooth duality, qualified split stationarity
and physical Lambda identification remain separate obligations.

## Nonsmooth conic Slater and actual Schur matrix duality (2026-10-03)

`ConvexValueSupport` constructs support from strict-epigraph separation;
finite-dimensional convexity earns continuity. `NonsmoothConePrice` earns
convexity of the actual guarded value from approximate feasible costs, returns
local support globally by primal mixing, and proves cone positivity and
complementarity. Interior Slater slack and ordinary primal attainment earn
local nonempty/bounded-below costs by a midpoint lower bound.

`ExtendedNonsmoothConePrice` restores the price to the original EReal objective
and whole admissible domain with actual finite primal/dual equality.
`MatrixSlaterTopology` proves positive-definite slack is interior in the actual
symmetric PSD cone. `NonsmoothMatrixPrice` applies this to the original singular-
support Schur residual with fixed L and affine D. Strict decrease of the actual
value in a PSD direction earns a nonzero price. No value derivative, local-value
finiteness or dual is supplied to the Slater matrix theorem.
`NonsmoothPriceExamples` proves an actual value kink with a nonzero dual price,
and an original infinite-objective Schur matrix example using Slater alone.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_nonsmooth_price_statements.lean
lake env lean -DwarningAsError=true manifests/check_nonsmooth_price_axioms.lean
python3 ../scripts/de_nonsmooth_price_verify.py
```

Full build8123; all27 fresh statements/transitive closures checked. Cumulative1030
preserves exact earlier1003 plus fresh27; full cumulative command not rerun.
See `math/NONSMOOTH_PRICE_LEAN_2026-10-03.md`. Paper, original runtime and prior
proof/evidence unchanged. General nonsmooth Slater dual construction and its
original extended Schur matrix return are now proved. Qualified split stationarity,
physical identification and other parked original-claim issues remain separate.

## Constructed stationarity splitting and actual Schur smoothness (2026-10-03)

`ConvexSubgradient` gives supporting-functional definitions and proves exact
restriction/indicator/normal-cone and finite-real return. Convex mixing and actual
line derivatives remove a smooth summand and identify its support uniquely.
`ConvexSumSplit` constructs a split by actual open hypograph/epigraph separation;
finite-dimensional convexity earns continuity. Its extended version returns to
the whole original objective domain. Full ambient objective/constraint/normal
stationarity is proved for finite ambient convex objectives, permitting nonsmooth J.

`SchurStationarity` earns differentiability of actual fixed-native affine-probe
Schur energies from finite quadratic coordinates. The original nonsmooth Slater
price yields a full finite-objective matrix stationarity split, nonzero under
actual strict value decrease, and exact restricted-objective stationarity for
extended J. No constraint derivative or stationarity premise is supplied to the
Schur return. `StationarityExamples` supplies complete nonsmooth/Schur examples
and a convex infinite-objective boundary control with restricted zero support
but no ambient objective support or full normal split.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_stationarity_split_statements.lean
lake env lean -DwarningAsError=true manifests/check_stationarity_split_axioms.lean
python3 ../scripts/de_stationarity_split_verify.py
```

Full build8127; all26 fresh statements/transitive closures checked. Cumulative1056
preserves exact earlier1030 plus fresh26; full cumulative command not rerun. See
`math/STATIONARITY_SPLIT_LEAN_2026-10-03.md`. Paper, runtime and prior proof/evidence
unchanged. General relative-interior-qualified splitting of ambient extended J
from admissibility remains open; the broader paper is not yet complete.


## Relative-interior-qualified extended objective/normal splitting (2026-10-03)

`RelativeConvexContinuity` earns actual intrinsic-interior continuity and chart
cost bounds. `RelativeDifference` constructs the surjective difference map into
the sum of the actual domain directions; finite-dimensional openness earns
bounded-cost perturbation witnesses. `RelativeEqualitySupport` earns the actual
real infimum guards by midpoint mixing and applies the proved nonsmooth support
construction. `RelativeSumSplit` returns its support through an exact ambient
Hahn-Banach extension and proves the qualified objective/normal sum rule for
both the restriction and literal J+indicator. Original infinite-cost points are
included; finite-everywhere or full-dimensional assumptions are unnecessary.

`RelativeSchurStationarity` gives full original extended Schur stationarity with
an ambient objective support and admissibility normal, using actual earned trace
smoothness and the original Slater matrix price. Strict original value decrease
earns a nonzero price. `RelativeSplitExamples` computes a line-domain relative
interior, proves empty ambient interior and applies the construction to obtain
a forced nonzero ambient support and cancelling normal with zero premises.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_relative_split_statements.lean
lake env lean -DwarningAsError=true manifests/check_relative_split_axioms.lean
python3 ../scripts/de_relative_split_verify.py
```

Full build8133; all27 fresh statements/transitive closures checked. Cumulative1083
preserves exact earlier1056 plus fresh27; full cumulative command not rerun. See
`math/RELATIVE_SPLIT_LEAN_2026-10-03.md`. Paper/runtime/prior proof/evidence unchanged.
The general relative-interior-qualified extended objective/normal split is now
proved. Explicit matrix Jacobian/adjoint return, physical identification and
previously parked issues remain separate; the broader paper is still incomplete.


## Explicit fixed-native Schur derivative/adjoint (2026-10-03)

`MatrixDifferential` derives actual rectangular product calculus entry by entry
in the existing elementwise norm. `SchurDifferential` earns the original residual
Jacobian H R Z^T + Z R H^T, its symmetric range, actual fderiv identity and
trace-dual adjoint. General P uses P+P^T; PSD symmetry earns factor two. Affine
probes have their derivative earned, and arbitrary genuinely differentiable
probes have a conditional chain rule without finite-dimensional primal space.
Fixed matrix budgets contribute zero derivative. No primal inner product is
invented; the adjoint acts in the actual continuous dual through trace pairing.

`SchurAdjointStationarity` returns original extended qualified stationarity in
the literal traceAdjoint of fderiv actual_Xi form, including explicit evaluation
on every direction, complementarity and nonzero price under strict actual value
decrease. `SchurDifferentialExamples` computes the actual singular native
complement and a rectangular probe derivative, plus controls for a dropped
product-rule term and the invalid nonsymmetric factor-two shortcut.

```bash
lake build
lake env lean -DwarningAsError=true manifests/check_schur_differential_statements.lean
lake env lean -DwarningAsError=true manifests/check_schur_differential_axioms.lean
python3 ../scripts/de_schur_differential_verify.py
```

Full build8137; all28 fresh statements/closures checked. Cumulative1111 preserves
exact earlier1083 plus fresh28; full cumulative command not rerun. See
`math/SCHUR_DIFFERENTIAL_LEAN_2026-10-03.md`. Paper/runtime/prior proof/evidence fixed.
Explicit fixed-native affine-probe matrix Jacobian/adjoint return is proved.
Same-price scalar sensitivity/stationarity assembly, physical identification
and other original-target gaps remain; the goal is not complete.


## Canonical scalar sensitivity and qualified stationarity (2026-10-03)

`ScalarPriceStationarity` earns the full generic scalar Theorem S with the same
p=-V'(B)>0 supplying actual extended duality, derived activity and the qualified
objective/energy/normal split. Energy is a finite convex ambient extension and
may be nonsmooth. The actual common RI point, ordinary finite optimizer and
locally finite negative actual value derivative remain explicit. A separate
Slater/activity premise is unnecessary for this derivative-based construction.
The smooth specialization identifies the energy support with its actual
supplied derivative; the general endpoint supplies no energy derivative.
Every certificate price is identified as -V'(B), across different optimizers.

`ScalarSchurStationarity` earns the actual fixed-native affine Schur energy
derivative and the same-price literal matrix-adjoint stationarity with price
p*W. The energy constraint remains scalar. `ScalarStationarityExamples` returns
the original infinite-cost Schur example, proves every certificate price1, and
constructs full stationarity for energy(x,y)=x+abs(y), J=-x. Its actual value
is -B and differentiable, while the energy has no derivative at optimizer(0,0).

Full build8140; all19 new statements/closures freshly checked. Cumulative1130
is exact immutable1111 plus fresh19; full cumulative command not rerun. See
`math/SCALAR_STATIONARITY_LEAN_2026-10-03.md` and
`scripts/de_scalar_stationarity_verify.py`. Generic scalar Theorem S assembly is
closed. General matrix-map coverage, physical interpretation, moving native
calculus, primal attainment and broad original-target audit remain separate.


## General matrix-map Slater price and qualified stationarity (2026-10-03)

`GeneralMatrixPrice` constructs PSD trace-price certificates and original finite
extended strong duality for arbitrary Loewner-convex symmetric matrix maps.
PD Slater and ordinary finite optimizer earn the local finite value guards;
actual strict PSD-direction value decrease earns nonzero P. No primal topology
is needed for this price construction. Whole-budget trace representation is
proved, not just one optimizer pairing.

`ExtendedSmoothStationarity` removes a smooth finite summand using actual local
line derivatives and convex extended objective mixing, without requiring
summand convexity outside A. It earns the qualified ambient objective/normal
split from the actual common RI point. `GeneralMatrixStationarity` earns actual
trace-Lagrangian derivative and constructs full general matrix stationarity with
certificate/finite duality. Its smooth endpoint needs Loewner convexity on A
and actual matrix derivative at star. Literal fderiv follows actual
DifferentiableAt. The nonsmooth endpoint keeps a finite ambient Loewner-convex
extension explicit and earns a support of the actual scalar trace energy.

`GeneralMatrixExamples` earns a full nonzero-price construction for actual
Schur residual x^4 with nonlinear probe x^2, original infinite-cost objective,
actual optimizers/values1 and0, actual derivative, Slater and RI. Its entry is
formally not a quadratic polynomial. A matrix map x+abs(y) formally lacks a
derivative but receives nonsmooth stationarity. An off-A continuation control
refutes promoting restricted convexity to an ambient energy support.

Full build8144; all28 fresh statements/closures checked. Cumulative1158 preserves
immutable1130 plus fresh28; full cumulative command not rerun. See
`math/GENERAL_MATRIX_STATIONARITY_LEAN_2026-10-03.md` and
`scripts/de_general_matrix_verify.py`. Corrected general smooth matrix Theorem S
is mechanized. Nonsmooth extension requirements, actual derivative premises,
ordinary primal attainment and physical boundaries remain explicit.


## Full matrix sensitivity and same-price stationarity (2026-10-03)

`ConePriceSensitivity` identifies every earned budget certificate using the actual
locally finite EReal value derivative. Local finiteness is earned from Slater by
an exact original-value return; no finite budget dimension is needed for this
identification step. `MatrixPriceSensitivity` reconstructs Hermitian prices from
the whole symmetric trace dual and proves PSD certificate-price uniqueness across
possibly different optimizers. No optimizer or objective-support uniqueness follows.

`MatrixSensitivityStationarity` assembles actual full value sensitivity, PSD/nonzero
price, reconstructed matrix, qualified objective/normal stationarity, complementarity
and original strong duality with one price. Smooth Xi needs only Loewner convexity
on A and its actual derivative at star. The nonsmooth endpoint retains a finite
ambient Loewner-convex extension and earns actual trace-energy support. PD Slater
earns local value guards; they are not supplied to either final endpoint.

`MatrixSensitivityExamples` independently earns original extended Schur data and
canonical price1/full actual-adjoint stationarity. For Xi=[x+abs(y)], the actual
complete-lattice value is -coordinate(B) on the whole budget space, with actual
full derivative; nonsmooth stationarity returns price1 and dual0 despite no Xi
derivative. A nonzero antisymmetric matrix invisible to symmetric budgets and
distinct PSD prices equal on one direction delimit whole-price identification.

Full build8148; all26 fresh statements/standard-only closures checked. Cumulative1184
preserves exact immutable1158 plus fresh26; full cumulative command not rerun.
See `math/MATRIX_SENSITIVITY_LEAN_2026-10-03.md` and
`scripts/de_matrix_sensitivity_verify.py`. This strengthens the conditional matrix
theorem. Actual value differentiability and ordinary attainment remain premises;
physical identification, moving native calculus, broader original-target audit
and feasible outstanding toy constructions remain separate. The goal is incomplete.


## Actual first records and ratios on the robustness rectangle (2026-10-03)

`WindowRobustRecord` uses the original reified twelve-by-sixty-four population,
unchanged tags and growth IVP, exact real amplitude scaling and declared
rectangle d in[6/5,2], s in[1/3,3]. Actual scaled maxima attain witnesses; every
seed's first threshold is c times its original ANY-patch threshold, with
c=d/(delta0*s). Exact bounds100<T_first<3588 and T_first<T_aggregate earn
first-time applicability throughout each actual signed native window. Actual
first-collapse equivalence/minimality, positive times, zero/nonpositive matter
bounds and strict parameter ordering are proved. Original scaling returns exactly
to the earlier signed readout.

`WindowRobustRatio` bounds the actual native endpoint between the two extreme
corner roots, earning a common positive window. Ratios retain actual matter
density a^(-3); every admitted negative/nonpositive parameter has R<1/125,
every nonnegative admitted parameter has R<=8000*lambda, and all signed ratios
have one finite corner-root bound. Endpoint ratios exceed minimumEndpoint/1000
and are at most8000*maximumEndpoint. These are honest uniform positive/finite
bounds, not numerical order-unity certificates. Most strongly, one lambda>0
makes all twelve ratios positive and <epsilon simultaneously for every rectangle
point. Nonnegative ratios are strictly increasing with lambda. Exact matching
scaling factors preserve endpoints/times/ratios; a changed-knob control inside
the rectangle returns original times and ratios.

Full build8150; all39 fresh statements/standard-only closures checked.
Cumulative1223 preserves exact immutable1184 plus fresh39; full cumulative
command not rerun. See `math/ROBUST_RECORD_LEAN_2026-10-03.md` and
`scripts/de_robust_record_verify.py`. Floating resampling/rounding is not silently
identified with exact real coupling. Tighter numerical robustness-edge ratios,
first-time joint regularity, other sampled populations and broader original-target
coverage remain separate; the full goal is incomplete.


## Numerically certified full-rectangle actual edge ratios (2026-10-03)

`GrowthRescaledCertificate.native_scale_covariance` returns the original growth
function exactly under a->c*a, lambda->lambda/c^3, a0->a0/c. The initial D=1
and actual finite-start prefactor/term remain intact. For c in(1/5,4), rescaled
start is in[1/4000,1/200] and rescaled horizon in[5,100]. Three exact fixed
quadrature profiles earn lower growth>970*c at3/c^3 and scale5*c, lower
growth>897*c at(7/2)/c^3 and scale(8/3)*c, and upper horizon growth<960*c at
(7/2)/c^3. Their1925 cells and rational sums are checked by Lean's kernel;
generator uses Fraction/isqrt and detects false cells.

`WindowRobustEdge` returns these to the actual native boundary and original
ANY-patch first time across every d in[6/5,2],s in[1/3,3]. With c=d/(delta0*s),
actual endpoint u obeys3<u*c^3<7/2. Actual first time at the endpoint obeys
c/2<a_first<=(8/3)*c, so every seed has3/8<R<1792/27. All signed admitted
ratios satisfy0<=R<1792/27. These are explicit uniform numerical certificates,
replacing earlier unspecified-root bounds. They do not certify a sharp observed
value, typicality or physical Lambda. Earlier no-pinching remains fixed.

Full build8156; all28 fresh statements/standard-only closures checked.
Cumulative1251 preserves exact immutable1223 plus fresh28; full cumulative
command not rerun. See `math/ROBUST_EDGE_LEAN_2026-10-03.md` and
`scripts/de_robust_edge_verify.py`. Original paper/runtime/data/evidence fixed;
exact coupling is not identified with independently resampled or rounded arrays.
Other sampled population edge ratios, first-time joint regularity and the broader
original-target audit remain separate. The full goal is incomplete.


## Actual separately realized N32/N128 first-record numerical ratios (2026-10-03)

`WindowPatchCountFirstData` earns tight exact normalization scales c=T_aggregate/965
and actual first-ANY-patch thresholds in(450*c,897*c). Its kernel counterexample
shows the original500*c lower bound fails for at least one N32 seed. No population
inclusion or tag coupling is assumed. `WindowPatchCountRatio` returns actual
attained maxima to unique signed-window first times, ANY-patch collapse equivalence
and minimality. Actual endpoint equality and prior native finite-start quadrature
certificates earn3<u*c^3<7/2, N32 endpoint in(13/10,17/10) and N128 in(5,25/4).
Actual first-time bounds(9/20)*c<a<=(8/3)*c earn every seed's endpoint ratio
2187/8000<R<1792/27. Every signed admitted ratio satisfies0<=R<1792/27, with
nonpositive ratios<1/1000. One lambda>0 makes all24ratios<epsilon simultaneously.

Full build8158; all33 fresh statements/standard-only closures checked.
Cumulative1284 preserves exact immutable1251 plus fresh33; full cumulative
command not rerun. See `math/PATCH_RATIO_LEAN_2026-10-03.md` and
`scripts/de_patch_ratio_verify.py`. Fraction-only original-data report replay and
false-target controls pass. Historical grid numbers are not continuum roots;
sharp typicality, joint first-time regularity and broader original-target coverage
remain separate. No new downgrade; the full goal is incomplete.


## Actual first-record joint continuity and knob C1 (2026-10-03)

`GrowthFirstContinuity` constructs joint relative continuity of the unchanged
signed selector on its actual domain, including horizon equality. Strict final
slack earns ambient joint continuity; actual local root equations and positive
native velocity earn threshold derivative1/velocity and C1 on the open actual
threshold interval. The matter horizon-equality fallback is proved discontinuous
ambiently, so the guards are substantive.

`FirstPopulationContinuity` constructs a1-Lipschitz actual attained global
maximum; arbitrary continuous amplitudes/delta/lambda inputs give continuous
first-ANY-patch times under explicit original domain margins. Actual collapse
iff time<=a returns the construction. A two-patch maximizing switch yields an
actual nondifferentiable first time, while retaining positive legal amplitudes.
`WindowFirstRegularity` earns strict first-threshold slack from every original
N64 coupled-rectangle gate and both N32/N128 gates. Actual time/ratio are jointly
continuous in(d,s,lambda), first time is C1 in(d,s) at fixed lambda with exact
positive delta and negative amplitude partials, and endpoint time/ratio are
continuous. All original signed population readouts are continuous inlambda.

Full build8161; all38 fresh statements/standard-only closures checked.
Cumulative1322 preserves immutable1284 plus fresh38; full cumulative command
not rerun. See `math/FIRST_REGULARITY_LEAN_2026-10-03.md` and
`scripts/de_first_regularity_verify.py`. Joint C1 includinglambda, additional
population/knob sweeps and broad original-target completion remain separate.
No new supported-claim downgrade; full goal incomplete.


## Actual joint first-time C1 and signed implicit sensitivity (2026-10-03)

`GrowthJointContinuity` constructs actual joint primitive/growth/velocity/
sensitivity continuity from one positive root margin. `GrowthUnitDifferential`
earns the actual joint kernel derivative, a uniform compact-neighborhood norm
bound and every derivative-under-integral hypothesis; exact unit-interval
transport returns joint differentiation to the original finite-start primitive.
`GrowthJointDifferential` earns joint native growth differentiability before
partial derivatives identify its coefficients, then proves native C1.

`GrowthFirstDifferential` constructs the triangular derivative inverse and
uses actual nearby root equations and earned selector continuity to prove
joint first-time C1 onlambda>-1/A^3,1<T<G_lambda(A). The actual signed parameter
derivative is-sensitivity/nativeVelocity>0. No selector/inverse/derivative is
supplied as a premise. `WindowFirstDifferential` returns joint C1 to the entire
original N64 coupled rectangle in(d,s,lambda), C1 and exact positive sensitivity
to all original N32/N64/N128 signed first times, and joint C1 to actual endpoint
times and ratios in(d,s), including aggregate window endpoints. Every actual
ratio is C1 away fromlambda0 and is proved nondifferentiable atlambda0 because
of its absolute-value factor. Previous continuity and tied-max/horizon controls
remain fixed; arbitrary independent rank/max switches are not asserted smooth.

Full build8166; all61 fresh statements/standard-only closures checked.
Cumulative1383 preserves immutable1322 plus fresh61; full cumulative command
not rerun. See `math/FIRST_DIFFERENTIAL_LEAN_2026-10-03.md` and
`scripts/de_first_differential_verify.py`. Joint first-time C1/implicit signed
sensitivity obligation closed; combined additional-population/knob robustness
and broad original-target completion remain separate. Paper/runtime/data/old
proofs/evidence fixed; prior false/project-sized boundaries unchanged. Full goal
incomplete.


## Combined original population/knob robustness (2026-10-03)

`WindowPatchRobust` returns the actual separately realized N32/N128 populations
and fixed tags to the entire original rectangle d in[6/5,2], s in[1/3,3]. Actual
aggregate windows are(-1/8000,u]; first-ANY-patch times retain exact formation
and minimality. Actual endpoint order u32<u64<u128 and strict gate nesting hold
throughout. `WindowPatchRobustRegularity` earns joint first-time C1 in(d,s,lambda),
endpoint C1 in(d,s), exact derivative signs, and endpoint time/ratio C1. Ratios
are continuous, C1 away from0 and proved nondifferentiable at0.

The old rescaling domain(1/5,4) misses two actual combined corners, explicitly
proved as kernel controls. Three new whole-cell rational profiles certify1914
cells on the earned wider domain(1/6,5), retaining the original finite-start
initial scale, root term and prefactor. `WindowPatchRobustEdge` proves
5/2<u*c^3<7/2, normalized endpoint first time in(9/20,8/3], endpoint ratios
in(3645/16000,1792/27) and the same upper ratio bound across every signed gate.
One positive lambda makes all36 original N32/N64/N128 ratios arbitrarily small
simultaneously over the entire rectangle. Exact real rescaling is used; smooth
N dependence, freshly rounded NumPy identity and typicality are not claimed.

Full build8174; all81 fresh statements/standard-only closures checked.
Cumulative1464 preserves immutable1383 plus fresh81; full cumulative command
not rerun. See `math/COMBINED_ROBUSTNESS_LEAN_2026-10-03.md` and
`scripts/de_combined_robustness_verify.py`. Combined exact-toy robustness closed;
paper/runtime/data/old proofs fixed, prior stronger narrower bounds preserved.
Broad original-target completion remains open; prior false/project-sized
boundaries retained. Full goal incomplete.


## Smooth priors do not force actual upper-edge typicality (2026-10-03)

`WindowSmoothPrior` formalizes the previously identified failure of section7's
local-nonsingularity sufficiency on the ACTUAL growth toy. For any epsilon>0
and0<eta<1, one constructed exponential rate and positive prefix work for all
original N32/N64/N128 populations throughout the knob rectangle. Each density
is C-infinity, strictly positive and finite at zero, and normalized on its own
FULL positive window. Its exact prefix mass exceeds1-eta, while every actual
seed ratio on that prefix is<epsilon. Antiderivative, integrability, positive
normalization, common endpoint bound and actual gate/ratio returns are earned.

This is a normalized-density interval-mass certificate and actual low-ratio
event inclusion; no separate Mathlib probability object or abundance-weighted
pushforward is claimed. The signed negative sliver is outside this construction.
Regularity near zero alone cannot restore typicality. A declared prior family
or quantitative global density control and the actual pushforward are needed;
the contradicted numerical near-collapse remains false on its frozen support.

Full build8175; all10 fresh statements/standard-only closures checked.
Cumulative1474 preserves immutable1464 plus fresh10; full cumulative command
not rerun. See `math/SMOOTH_PRIOR_LEAN_2026-10-03.md` and
`scripts/de_smooth_prior_verify.py`. Paper/runtime/data/earlier proofs fixed.
This strengthens an earlier negative finding; full original goal incomplete.


## Original32-patch budget-dual mechanics and controls (2026-10-03)

`AllocationSampleData` reifies the original pinned generator's32 IEEE weights,
curvatures,10 budgets and3 offsets, with exact rational response certificates.
All frozen formatted fields match; historical CSV rounding is not claimed to
recover unrecorded historical bits. No optimizer/root-finding solver is rerun.
The coefficient generator is deterministic and its configured seed is unused.

`AllocationScreening` returns active-offset KKT laws to intrinsic selected
allocations and prices. `AllocationSample` proves0.46112<p<0.46113, actual
activity, all32 positive allocations, shared stationarity, unequal allocations,
global optimality/uniqueness and the actual derivative V'(B)=-p. Every offset
in[-1/4,1/4] has exact selected state invariance, price absorption and cost-value
shift, including original IEEE +/-0.2. All ten original sweep budgets classify:
first seven positive-price active, last three zero-price strictly slack.

`AllocationSampleControls` constructs32 true local singleton budget problems
with exact total B and unequal actual selected prices (first-pair gap>1/20).
The selected local/global states differ. Removing the budget with the same
linear coupling gives the unique unconstrained optimizer; strong support is
proved without a competitor mass guard. Its actual patch8 movement is>1/2
for both original IEEE shifts. No selected numerical-state premise is supplied.

Full build8179; all54 fresh statements/standard-only closures checked.
Cumulative1528 preserves immutable1474 plus fresh54; full cumulative command
not rerun. See `math/ALLOCATION_SAMPLE_LEAN_2026-10-03.md` and
`scripts/de_allocation_sample_verify.py`. Source bridge remains computational;
floating optimizer/finite-difference precision, Schur-budget identity and the
physical Lambda bridge are not inferred. Paper/runtime/frozen data/earlier
proofs fixed. No new downgrade of supported claims; full goal incomplete.


`GroundAlternating`, `GroundAlternatingRelaxation`, `GroundAlternatingOrbit`
construct the actual original eight-site ground response on positive alternating
fields under a constant background. Ground selection is earned from the full
eigen equation, positivity, symmetry and intrinsic uniqueness. Actual normalized
mixing is nonzero and preserves the slice at every iteration. Its earned contrast
derivative is1-m-m*k*b/8. At mixing1/2, -8<k*b<24 gives local actual-field
convergence to uniform; k*b<-8 or k*b>24 gives finite escape of every small
nonzero alternating perturbation from a fixed contrast neighborhood.

This is a scoped dynamical construction, not all-mode stability, nonexistence,
background blindness or certification of the frozen nonconstant-template
crossing. Full build8182; all65 fresh statements/standard-only closures checked.
Cumulative1593 preserves immutable1528 plus fresh65; full cumulative command
not rerun. See `math/GROUND_ALTERNATING_LEAN_2026-10-03.md` and
`scripts/de_ground_alternating_verify.py`. Paper/runtime/frozen data/earlier
proofs fixed; full original-target completion remains open.


`GroundBorder`, `GroundEquations`, `GroundSmooth`, `GroundSourceJacobian`,
`GroundNormalizedJacobian` derive the actual positive-ground and Step26 real
Jacobian for all backgrounds, including nonconstant ones. Actual ground simplicity
and normalization earn an invertible border. The implicit-function branch returns
to the existing continuous selector, proving C-infinity ground/energy regularity.
The selector derivative is constructed from that inverse, then composed with
unchanged quadratic sourcing. Actual normalization supplies P_u*((1-m)I+mJ),
and tangent fields at an actual fixed point return exactly to(1-m)h+mJh.
All-parameter positive fixed-point/Jacobian existence and zero-coupling controls
are also constructed. No derivative/inverse/gap premise is supplied.

The positive real representative is explicit; arbitrary signed/complex phase
rules and frozen complex initialization are not returned. Numerical branch/error
and spectral crossing certificates remain open, and no all-mode stability or
nonlinear branch uniqueness is inferred. Full build8187;51 fresh statements and
standard-only closures. Cumulative1644 preserves1593 immutable plus51 fresh;
full cumulative command not rerun. See `math/GROUND_JACOBIAN_LEAN_2026-10-03.md`
and `scripts/de_ground_jacobian_verify.py`. Paper and previous artifacts fixed;
full original-target completion remains open.

## Original-template root and spectral certificates

`GroundRootCertificate` derives the actual nonlinear eigen residual and derivative, returns positive roots to the ground selector, and proves a conditional a posteriori root criterion from explicit residual/derivative/positivity bounds. It also proves the full half-mixing derivative formula. Eleven fresh standard-only closures bring cumulative coverage to1655 (immutable1644 plus11); full build8188. Concrete exact Python interval certificates locate all30 original sampled positive roots (radius2^-32), certify28 stable half-mixing real tangent spectra and two unstable modes at coupling20/30. Coupling15 has radius<0.911617. These30 concrete bounds are not Lean kernel proof terms. Continuous branch identification, nonlinear basins and frozen complex trajectories remain open. See `../math/GROUND_INTERVAL_CERTIFICATES_2026-10-03.md` and `../scripts/de_ground_interval_verify.py`.

## Actual nonlinear local and zero-coupling global convergence

`GroundLocalDynamics` earns C-infinity normalization at actual unit fixed points, the full root/energy/bordered-Jacobian return, exact coordinate conjugacy and all-direction local attraction from actual derivative norm/row bounds. `GroundZeroCouplingOrbit` proves global convergence of the unchanged zero-coupling normalized map for every background and nonnegative unit initial field,0<m<=1, with explicit geometric distance bound; it also earns the all-coupling positive/unit invariant. The28 stable exact original sample certificates now return mathematically to local convergence, with Python root/basis/row inputs still not Lean instantiations. Full build8190;40 fresh standard-only closures; cumulative1695 preserves1655 immutable plus40 fresh. See `../math/GROUND_NONLINEAR_DYNAMICS_2026-10-03.md` and `../scripts/de_ground_dynamics_verify.py`.

## Original complex update and guarded local convergence (2026-10-03)

`GroundNativePhase`, `GroundNativeDerivative`, `GroundNativeIteration`,
`GroundNativeJacobian`, `GroundNativeLocal`, and `GroundNativeControls` retain
Step26's original exp(-i arg) phase rule and exact binary64 threshold. They
prove real-eigensolver sign return, actual full real derivative, locally earned
guards, all-parameter legal fixed points, and actual complex local attraction
from strict transformed block row bounds. The imaginary half-mixing block is
(I-u uᵀ)/2; its phase mode is zero and tangent modes are one half. Exact Python
certificates at all30 root boxes support28 full complex local-attraction returns.
Concrete sampled kernel instantiations remain incomplete. A unit pure-imaginary
ground input cancels at half mixing and fails the source normalization guard.
See `../math/GROUND_NATIVE_COMPLEX_2026-10-03.md`; no frozen-init basin or global
complex convergence is claimed.

## Actual nonlinear coupling branches and mode contacts (2026-10-03)

`GroundParameterEquations`, `GroundParameterBranch`, `GroundParameterTube`, and
`GroundParameterSpectrum` earn joint nonlinear regularity, partial/preconditioner
invertibility from a strict Newton defect, local actual branches and uniqueness,
uniform positive roots with C-infinity boundary germs, common-root seam identity,
and actual normalized-Jacobian continuity and minus-one modes by determinant IVT.
Exact Python replay supplies286 uniform tubes covering the original coupling
interval[0,30],287 common-root anchors and returns all12 original roots. Two
minus-one contacts are earned in(15.8,15.9) and(15.9,20). Concrete certificates
and the global finite-patch definition are not Lean-instantiated. No global root
uniqueness, transverse/first/unique crossing, nonlinear escape or frozen-init
basin is inferred. See `../math/GROUND_COUPLING_BRANCH_2026-10-03.md`.


The [finite coupling-branch assembly](../math/GROUND_FINITE_PATCH_2026-10-04.md) now constructs the global branch in
Lean from finite closed quantitative tubes and certified common-root overlaps.
Continuity and C-infinity seam germs are derived, then returned to the full
ground/energy selector, certified sample roots, legal native complex fixed points
and two distinct mode contacts. No global continuous branch is supplied.
The concrete286-tube cover and numerical sign/inequality proof terms remain
outside kernel instantiation; the preceding exact Python certificates are
preserved, not freshly replayed here.17 fresh standard-only theorem closures
bring cumulative coverage to1830 (immutable1813 plus17); full build8202.
No frozen-init basin or nonlinear runaway is inferred. Paper/runtime/data
unchanged; the overall original-paper goal remains incomplete.


The [first concrete kernel tube](../math/GROUND_KERNEL_TUBE_2026-10-04.md) now proves the actual original-background
positive ground branch for every real coupling in[0,15/128] inside Lean, using
the original radius1/256 ball. Signed rational interval arithmetic, exact
residual/derivative expression returns and the actual nine-coordinate product
sup operator norm earn the concrete bounds1/10 and3/1000. The arithmetic theorem
has no hypotheses and uses kernel reduction. Zero preconditioning and an
impossible residual budget are rejected by kernel proofs.40 fresh standard-only
closures bring cumulative coverage to1870; full build8207. Only one of286 tubes
is kernel-instantiated; the full cover/anchors/sample/sign proofs and frozen-init
basin remain open. Newton correction contraction is not native iteration
contraction. Paper/runtime/data unchanged; the full original goal is incomplete.


The [complete kernel coupling continuum](../math/GROUND_KERNEL_CONTINUATION_2026-10-04.md) now supplies all286 original uniform tubes and287 endpoint anchors
with concrete kernel arithmetic proofs, then derives their actual ball
containment, common-root seam identity and exact finite coverage of[0,30].
The resulting branch is C-infinity, strictly positive and unit normalized,
returns the full ground/energy selector, and consists of legal native complex
fixed points at the exact original tolerance. The branch theorem assumes only
coupling membership in[0,30]; no numerical certificate or global smooth branch
is supplied as a hypothesis.

589 fresh statements and standard-only closures bring cumulative coverage to2459
(immutable1870 plus589); full build8782. Thin sample-root identities, determinant
signs, all-interval stability, nonlinear escape and the frozen-init basin remain
separate kernel obligations. Newton contraction does not prove native convergence,
and κ15's prior local attraction still rules out the literalκ>=15 runaway reading.
Paper and frozen runtime/data are unchanged; the original-paper goal is incomplete.


The [native nonlinear escape construction](../math/GROUND_NATIVE_ESCAPE_2026-10-04.md) now earns the nonlinear bridge from an actual expanding real eigenmode
and an explicit derivative-norm gap to escape from arbitrarily close unit complex
inputs. C2 regularity supplies the quadratic remainder; finite tracking controls
all errors, and native phase/normalization guards hold through the escape.
The unchanged map's derivative and affine iteration return are derived. Combining
this analytical theorem with the preserved exact20/30 sample bounds establishes
mathematical local nonlinear instability there. Concrete spectral/sample kernel
instantiations remain pending; no closed numerical20/30 theorem is claimed here.

18 fresh statements and standard-only closures bring cumulative coverage to2477
(immutable2459 plus18); full build8783. Local instability does not prove the
frozen seed escapes or all orbits leave. The original-init basin, finite-budget
outcome and all-interval stability remain separate. κ15's certified local
attraction persists. Paper/runtime/data unchanged; original-paper goal incomplete.


The [kernel sample and derivative-entry construction](../math/GROUND_KERNEL_SAMPLES_2026-10-04.md) now instantiates all twelve original coupling-root boxes and two crossing
probes in the kernel and proves their full ground/energy identity with the actual
[0,30] branch. A new near-inverse border response estimate earns explicit column
errors without assuming a numerical inverse. Fourteen closed response certificates
then enclose every actual normalized half-mixing derivative entry, including source
feedback, the energy constraint and normalization projection. The concrete entry
theorem takes only finite sample/row/column indices.

57 fresh statements and standard-only closures bring cumulative coverage to2534
(immutable2477 plus57); full build8815. Zero border preconditioning and a deleted
positive response-error budget at20 are rejected by kernel proofs. Lawful zero-
coupling response budgets remain accepted. Coordinate inverses/norm tests and
determinant signs are the next kernel obligations; no new numerical stability or
mode-contact verdict is inferred from entry containment alone. Background-offset
samples, frozen-init basin and finite-step source outcomes remain separate.
Paper/runtime/data unchanged; the original-paper goal remains incomplete.


The 2026-10-04 coordinate packet now earns exact basis inverses and actual
real/imaginary/full derivative norms for all twelve original coupling samples
in the Lean kernel. The populated finite family proves actual native complex
local attraction at the ten samples through coupling 15, with all iterates active
and legal. Coupling15 has real norm below0.911617; couplings 20 and 30 have full norm
bounds 3/2 and 3 for the next escape construction. Kernel determinant signs and
expanding modes, the frozen initialization basin and the eighteen background
offset samples remain pending. See
[the coordinate mathematics note](../math/GROUND_KERNEL_COORDINATES_2026-10-04.md).


The 2026-10-04 spectral packet now proves seven actual shifted determinant
signs in the Lean kernel, two distinct minus-one contacts on the original branch,
and full unit expanding modes at couplings20 and30. These populate the nonlinear
bridge: arbitrarily close unit complex starts escape a fixed coordinate
neighborhood through finite active, legal native orbit segments. Concrete
returns have no supplied spectral or escape premises. The original phase bug
is retained. Frozen initialization basins, finite-step source outcomes and the
eighteen background-offset kernel instances remain pending. No first/unique/
simple/transverse contact, all-orbit escape or universal runaway claim is made.
See [the spectral mathematics note](../math/GROUND_KERNEL_SPECTRUM_2026-10-04.md).


The 2026-10-04 native reflection packet now returns the negative real branch
representative to legal native fixed points throughout[0,30], actual local
attraction at ten original coupling samples through15, and finite guarded escape
at20/30. Reflection is proved only on active orbit prefixes. A unit, legally
normalized inactive-phase example rejects unconditional reflection. A read-only
floating scout identifies the negative representative as the frozen seed's
apparent target at stable sampled couplings; it supplies no basin certificate.
The exact frozen-seed basin and18 offset kernel instances remain pending. See
[the signed-representative note](../math/GROUND_NATIVE_REFLECTION_2026-10-04.md).


The 2026-10-04 global native zero-coupling packet now proves convergence for
all real backgrounds and unit complex starts whose signed real ground overlap
exceeds the source threshold. The unchanged conjugate phase and half mixing are
retained, with geometric decay and active/legal execution at every step. Closed
seed arithmetic returns the original reified initialization at coupling0 to the
negative actual branch ground, with real overlap below-1/5 and no supplied basin
premise. Both initialization normalizations are represented. This is exact
mathematical model evidence; no60-step floating verdict or IEEE per-operation
emulation is claimed. Positive-coupling seed basins and18 offset kernel sample
instances remain pending. See [the zero-coupling seed note](../math/GROUND_NATIVE_ZERO_SEED_2026-10-04.md).

`GroundNativeZeroFinite` earns half-per-step squared-overlap-defect contraction
above real overlap1/2. `GroundOriginalSeedFinite` proves the original seed enters
this region after one update, using the whole certified root box and two exact
rational kernel comparisons. Its actual native zero-coupling squared Euclidean
distance is below(2e-9)^2 after60 updates and below(3e-9)^2 after59. The source
residual verdict and floating execution remain pending.

`GroundComplexEuclidean` provides the source Euclidean norm and two-alignment
gap estimates. `GroundComplexResidual` derives actual cycle operator budgets,
a quadratic Rayleigh-energy error and the eigen residual bound.
`GroundSourceDiagnostics` retains the four actual source diagnostic formulas,
including double phase alignment and the identical-expression sourcing comparison.
`GroundOriginalResiduals` earns all four original IEEE-threshold comparisons
in the exact mathematical zero-coupling original-seed orbit after60 updates.
A pure-imaginary actual native control distinguishes zero double gap from
single gap2 and remains illegal for the half update. Positive coupling and
IEEE per-operation returns are pending.


The exact original-seed native orbit at original coupling 0.3 now has a kernel
certified 16-update prefix, with active phase and legal normalization at inputs
0–15 and unit norm at states 0–16. Its endpoint is within 1e-5 in State sup-coordinate
norm of the negative actual branch ground. Uniform whole-potential-box Newton
certificates and both reciprocal-square-root guards are earned; the original
phase rule and both initialization normalizations are retained. Nearness does
not establish entry into the earlier unspecified local attraction radius. An
explicit quantitative basin and 60-update positive-coupling source tests remain
pending. See `../math/GROUND_NATIVE_PREFIX_2026-10-04.md`. The paper is unchanged; overall goal incomplete.

The original coupling 0.3 now has a kernel-certified explicit native basin:
coordinate radius 1/40000, whole-ball derivative bound 3/5 and reflected
sixteenth-iterate entry distance at most 1/48000. The exact original-seed orbit
converges to the negative actual branch ground, with all states unit and all
phase/normalization guards earned. The full sixteen-coordinate derivative and
near-inverse response error are retained. The original conjugated phase and
both initialization normalizations remain represented. Sixty-update source
diagnostics at 0.3, other positive-coupling seed basins, eighteen offset sample
instances and IEEE execution remain pending. See `../math/GROUND_NATIVE_BASIN_2026-10-04.md`. The paper is
unchanged; the overall goal remains incomplete.

All four exact mathematical source convergence tests now pass after60 updates
at original coupling0.3, with active/legal guards at every original iterate.
The actual sourced candidate has an earned distance bound; both source phase
alignments and the actual Rayleigh energy are retained. The State-to-Euclidean
norm bridge and sourced Hamiltonian budget are derived. This does not claim
IEEE execution, a first stopping index or independent sourcing consistency.
See `../math/GROUND_POSITIVE_SOURCE_RESIDUALS_2026-10-04.md`. Other seed basins and18 offset kernel instances remain pending;
the paper is unchanged and the overall goal remains incomplete.

All18 original background offsets at coupling0.3 now have kernel-certified
positive unit self-consistent ground/energy roots, local ball uniqueness and
legal actual native real fixed points. Whole background boxes cover both exact
uniform offsets and saved rounded input vectors. The offset-8 and+10 actual
fields differ by>3/10 at site0 and their source densities by>9/100, for both
models. Offset0 equals the original actual branch root. Local native stability
and frozen-seed60-step offset verdicts remain separate obligations; the Newton
rate is not a native contraction rate. See `../math/GROUND_OFFSETS_2026-10-04.md`. Paper/runtime unchanged;
overall goal incomplete.

All18 original background-offset roots now have actual native complex local
attraction at half mixing, for both signs and both exact/rounded input models.
The whole background-box derivative certificates earn distinct bordered
selector-response bounds, exact two-sided coordinate inverses, both native
real/imaginary blocks, and full16-coordinate operator norms below one. The
native convergence theorem preserves phase and normalization guards at every
nearby iterate. Radii are existential per background; frozen-seed entry and
sixty-update offset verdicts remain separate obligations. This adds162 fresh
standard-only declarations, cumulative3227, with a8932-job default build.
See `../math/GROUND_OFFSET_NATIVE_STABILITY_2026-10-04.md`. Paper and earlier mathematical evidence remain unchanged;
overall goal incomplete.

All18 original offset roots now have explicit native complex basins for both
signs, exact/rounded inputs and every background in their hulls. A common
coordinate radius1/400000 works across the finite family; the first17 also
admit1/40000. All sixteen input columns, cross blocks and whole-ball guards are
certified, with geometric distance bounds at every iterate. Frozen-seed entry
and sixty-update offset verdicts remain separate. This adds261 fresh
standard-only declarations, cumulative3488, with an8954-job default build.
See `../math/GROUND_OFFSET_EXPLICIT_BASINS_2026-10-04.md`. The paper is unchanged; overall goal incomplete.

## Original-seed infinite returns at rounded offsets (2026-10-04)

All eighteen saved rounded offset inputs now have closed Lean returns for the
actual original-seed infinite orbit, at original coupling 0.3, threshold 1e-10
and half mixing. Each orbit converges to the negative actual self-consistent
ground, with active phase, legal normalization and unit norm at every iterate.
421 populated step certificates enter the previously proved explicit basins
within 15–65 updates; actual coordinate errors then decay geometrically.
Every site's density converges, and the original-seed endpoint densities at
-8/+10 eventually remain separated by more than 9/100 at site 0.

This adds 956 fresh standard-only declarations, cumulative 4444, with a
9398-job default build. Both mathematical initialization normalizations and
the source phase convention are preserved. Exact uniform-offset seed returns,
whole input-hull seed returns, sixty-update verdicts and IEEE per-operation
execution remain separate. The paper is unchanged; the overall goal remains
incomplete. See `../math/GROUND_OFFSET_SEED_RETURNS_2026-10-04.md`.


All18 rounded-offset original-seed orbits now have exact mathematical
sixty-update source verdicts: fifteen pass the original four-test conjunction;
-5, -3 and +10 fail because the actual last-update residual exceeds the source
tolerance. All18 still converge eventually with all native guards/unit states.
The actual current sourced selector, actual Rayleigh energy and both diagnostic
phase calls are retained. This adds423 fresh standard-only declarations,
cumulative4867, with a9557-job default build. Exact uniform-offset seed returns,
whole input-hull seed returns, per-operation IEEE execution and first stopping
indices remain separate. See `../math/GROUND_OFFSET_SIXTY_VERDICTS_2026-10-04.md`.
The paper/runtime are unchanged; overall goal incomplete.
