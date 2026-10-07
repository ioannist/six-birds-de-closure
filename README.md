# Six Birds - Dark Energy as Closure

Three Stones v3 withdrew the finite-budget existence-boundary interpretation
and the generation-blindness theorem imported by the original paper. Neither
is restored by the results here. The original Boolean convergence readouts do
not determine the background control; that scoped result does not imply
intrinsic contingency of physical Lambda or prohibit additional selectors.
See [the dependency-withdrawal review](math/THREE_STONES_DEPENDENCY_WITHDRAWALS_2026-10-07.md).


This repository is the implementation workspace for the Six Birds dark-energy-as-closure program. The paper-support surface is the tracked code, tests, frozen result artifacts, Lean witnesses, and provenance manifests. Historical planning and agent-process workspaces are decommissioned and ignored for future additions; hashes needed by final artifacts are preserved in `results/provenance/decommissioned_plan_agent_sources.json`.

## Repository Map

- `sbt_cosmo/` is the installable Python package. It owns the background, growth, probe, Xi, audit, Hubble, inference, AOR, I/O, and plotting APIs.
- `configs/` contains tracked deterministic base, dataset, model, sampler, and prior skeletons.
- `data/manifests/` and `data/README.md` are tracked provenance records. Large payload directories are symlinked out to the NVMe data drive and gitignored.
- `experiments/E0_*` through `experiments/E8_*` are thin config-driven runners. They do not implement physics directly.
- `results/` is the committed reproduce-without-rerun surface for final tables, figures, and compact posterior summaries.
- `tests/` contains structural, registry, manifest, and future physics-gate tests.
- `lean/` is owned by the Lean track. The Python scaffold does not modify or depend on it.

## Reproduce Without Rerun

For completed experiments, reviewers verify claims from committed artifacts: per-experiment manifests, summaries, AOR ledgers, final tables, final figures, and compact posterior summaries under `results/<E#>/posteriors/`. Raw sampler chains and downloaded data payloads are reproducibility byproducts, not gate authorities.

## Current Packet Scope

Packet C0a creates the repository skeleton only. Physics, survey likelihoods, heavy cosmology backends, and experiment runs are deferred to C0b and later packets; placeholder APIs raise `NotImplementedError` until those packets implement them.

## Development Commands

The intended environment is the `sbt-de` micromamba environment on the NVMe data-drive. Source the committed helper so all future packets use the same root prefix, package cache, pip cache, and Python:

```bash
source scripts/env.sh
which python
# /mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin/python
python -m pip install -e .
pytest tests/test_imports_layering.py tests/test_xi_single_source.py tests/test_seeding.py tests/test_naming.py tests/test_registry.py
```

The full gold environment specification remains in `environment.yml`; the C0a core-resolved lock is `environment.core.lock.yml`, and the pip overlay lock is `requirements.lock`.

## Mathematical review status (October 2026)

The original paper is not fully substantiated: some value-blindness and measure
claims are contradicted or need narrower statements. The paper remains unchanged.
See [original-claim coverage](math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md),
[singular-support proofs](math/SINGULAR_ADEQUACY_PROOFS_2026-10-02.md),
[original allocation-price proofs](math/ALLOCATION_PRICE_PROOFS_2026-10-02.md),
[finite staging calibration](math/STAGING_RANK_PROOFS_2026-10-02.md),
[imported duality and composition review](math/IMPORTED_DUALITY_PROOFS_2026-10-02.md),
[adopted mediator strengthening and access-fork proofs](math/ACCESS_FORK_PROOFS_2026-10-02.md),
and [native fixed-point existence and solver-budget review](math/GROUND_STATE_PROOFS_2026-10-02.md)
for surviving claims, exact constructions and remaining boundaries.

The [2026-10-03 Lean construction](math/GROUND_EXISTENCE_LEAN_2026-10-03.md)
now proves self-consistent ground existence for every native eight-site
background and real coupling, with a constructed continuous positive selector,
lowest-eigenspace simplicity and a return to the complex model. It closes the
previous mechanization gap without proving iteration convergence or a physical
cosmological value.

The [growth-comparison construction](math/GROWTH_COMPARISON_LEAN_2026-10-03.md)
derives strict positivity, time/parameter ordering, uniqueness and the original
record-history threshold return from the exact growth IVP.
The [explicit IVP construction](math/GROWTH_EXISTENCE_LEAN_2026-10-03.md)
now supplies every live lambda, returns both equations and initial values to
scale factor, and proves parameter continuity. The
[growth-limit and window construction](math/GROWTH_WINDOW_LEAN_2026-10-03.md)
now proves the infinity limit, the unique positive threshold endpoint, and the
exact native record-history window. The
[population construction](math/WINDOW_POPULATION_LEAN_2026-10-03.md)
now checks all twelve realized populations, constructs their rank/count bridge,
and proves the original aggregate continuum window. The
[sensitivity construction](math/WINDOW_SENSITIVITY_LEAN_2026-10-03.md)
proves continuous endpoints, stability through ties, strict threshold/amplitude
ordering and an exact record window throughout the declared delta/scale
rectangle. The [growth-derivative construction](math/GROWTH_PARAMETER_LEAN_2026-10-03.md)
now proves strictly negative growth derivatives on the full live domain and
continuously differentiable endpoints, including both exact scaling derivatives
throughout that rectangle. The
[quadrature certificate](math/GROWTH_QUADRATURE_LEAN_2026-10-03.md) now proves
3 < positive endpoint < 4 for the original exact population, strengthening
the reported 2.33/5.31 witnesses. Finer numerical accuracy, floating solver
error and the physical identification remain separate obligations.

The [first-record construction](math/FIRST_RECORD_LEAN_2026-10-03.md) now returns
the actual earliest collapse of any original patch and its matter ratio. It
proves simultaneous arbitrarily small positive ratios while the aggregate gate
passes, strengthening the finite-grid no-pinching result. It also certifies
1/8 < R <= 24 for every original seed throughout 1 <= lambda <= 3, and
3/8 < R(3) <= 24, with lambda=3 above 75% of the positive endpoint. The [endpoint-ratio construction](math/ENDPOINT_RATIO_LEAN_2026-10-03.md) now
sharpens the endpoint bracket to 3 < lambda_plus < 3.4 and proves
0.375 < R(lambda_plus) < 53.125 for every original seed. The upper bound holds
throughout the entire nonnegative admitted window, with strict first-time and
ratio ordering. Other robustness populations and physical identification
remain separate obligations.

The [signed-record extension](math/SIGNED_RECORD_LEAN_2026-10-03.md) now
constructs actual earliest collapses throughout the entire admitted window
(-1/8000,lambda_plus], proves equality with the earlier nonnegative readout,
and retains its endpoint and no-pinching results. Every admitted negative
lambda has 0<R<1/8000 for each original seed; 0<=R<53.125 holds throughout
the full signed window. First time is strictly increasing across that domain,
and its zero-parameter value is exactly T_first/1000.

The [negative outside construction](math/NEGATIVE_ERASURE_LEAN_2026-10-03.md)
now certifies exactly 58 original seed-1100 patches collapsing before turnaround,
including both tags, and the same count before the turnaround buffer. The
declared toy erasure then leaves zero retained records. These are actual native
IVP histories; numerical solver error and physical crunch evolution remain
separate obligations.


The [patch-count construction](math/PATCH_COUNT_WINDOWS_LEAN_2026-10-03.md)
now certifies the original separately realized N=32 and N=128 populations.
Their actual continuum windows are strictly nested with the unchanged N=64
window: lambda_plus,32 < lambda_plus,64 < lambda_plus,128, with the same strict
negative cutoff. No population inclusion or retained-tag coupling is assumed.


The [infinite-time construction](math/ETERNAL_WINDOW_LEAN_2026-10-03.md) now
proves actual limiting growth, its continuity and strict parameter ordering,
and all-time record starvation for sufficiently large positive lambda. For
the original twelve seeds, finite formation with perpetual retention has the
exact window [0,u_infinity); its upper endpoint has only nine eventual both-tag
passes, while ten are required. Formation by a=20 with perpetual retention is
a distinct predicate with closed window [0,u_20]. The paper's unqualified
closed infinite-horizon endpoint requires this small correction; the paper
has not been edited.


The [horizon-limit extension](math/HORIZON_LIMIT_LEAN_2026-10-03.md) certifies
3<u_infinity<4 and convergence of the actual finite-horizon endpoints to it.
The actual N=32,64,128 populations now have strictly nested eternal windows,
with nine eventual seed passes at each excluded upper endpoint. The closed
interval [0,u_infinity] is proved to be the closure of the actual record-bearing
window; finite-time formation still excludes its upper endpoint.


The [eternal-edge ratio construction](math/ETERNAL_RATIO_LEAN_2026-10-03.md)
sharpens the infinite endpoint to 3<u_infinity<3.4 and constructs actual first
patch records for every original seed throughout 0<=lambda<=u_infinity.
Their first epochs lie in (0.5,2.5], with 0.375<R<53.125 at the infinite edge.
The eternal window still admits arbitrarily small positive ratios for all
seeds. First-patch formation at the endpoint does not supply the separate
required ten both-tag seed passes there.


The [global starvation certificate](math/GLOBAL_STARVATION_LEAN_2026-10-03.md)
sharpens the sufficient all-time cutoff from lambda>=10^9 to lambda>=32.
For the actual finite-start IVP, growth stays below 485 at every finite epoch,
while every original patch in all twelve-seed N=32,64,128 populations needs
more than 485 to collapse. Thus no patch ever collapses, and the original
both-tag record count is zero at every horizon. This is a sufficient cutoff,
with no optimal-cutoff or universal random-population claim.


The [allocation sensitivity construction](math/ALLOCATION_SENSITIVITY_LEAN_2026-10-03.md)
now derives the original carrier's cost derivative V'(B)=-price(B), with no
supplied differentiability premise. The actual value is C1 with Lipschitz
derivative on every positive budget, including patch active-set and active/slack
switches. An explicit exact-real central finite-difference error bound supports
the original two price readouts; floating solver/evaluation error remains
separate. Active budgets with zero derivative/price are retained as controls.


The [scalar convex closure-price construction](math/CONVEX_CLOSURE_PRICE_LEAN_2026-10-03.md)
now earns a positive price from the actual finite infimum value derivative,
proves global Lagrangian minimization and primal/dual value equality, and derives
constraint activity from strict sensitivity. Schur-energy convexity is proved
for affine dissolving probes with fixed native probes and PSD audit weight,
including singular native Gram blocks. A complete Schur example supplies its
own optimum, finite value and derivative; changing native probes has an exact
nonconvexity control. Extended-real split stationarity, matrix duality and
physical Lambda identification remain separate.

The [extended-objective construction](math/EXTENDED_CLOSURE_PRICE_LEAN_2026-10-03.md)
now proves the finite-domain reduction and preserves the actual extended-real
infimum, positive scalar price and global Lagrangian certificate. Its Schur
example includes genuine infinite objective values. An exact control shows
that omitting the domain restriction changes the value from one to zero.
Qualified split stationarity, matrix duality and the physical bridge remain open.

The [differentiable-value matrix construction](math/MATRIX_CLOSURE_PRICE_LEAN_2026-10-03.md)
now derives a nonzero PSD matrix price for actual symmetric Schur budgets,
with earned Loewner convexity, exact trace representation, complementarity,
global Lagrangian minimization and finite primal/dual equality. Its actual
matrix-budget example and nonzero-slack control are mechanized. General
nonsmooth Slater duality and qualified split stationarity remain separate.

The [extended-objective matrix construction](math/EXTENDED_MATRIX_PRICE_LEAN_2026-10-03.md)
now proves the conic finite-domain/infimum return and restores the matrix price
to every original admissible point, including infinite objective values. Its
actual extended primal/dual infima agree and are finite. A complete matrix
example and a bad-conversion control are mechanized; the differentiable-value
premise remains explicit.

The [nonsmooth Slater construction](math/NONSMOOTH_PRICE_LEAN_2026-10-03.md)
now constructs dual prices without a value derivative. Interior Slater slack
and ordinary finite primal attainment earn local finite costs; separation of
the actual value earns a cone-positive price. Positive-definite actual Schur
slack supplies a PSD matrix trace price for the original extended objective,
with complementarity, global Lagrangian minimization and finite primal/dual
equality. Strict actual value decrease earns a nonzero price. A genuine kink
example and an original extended Schur matrix example are mechanized.
Qualified split stationarity and the physical bridge remain separate.

The [constructed stationarity split](math/STATIONARITY_SPLIT_LEAN_2026-10-03.md)
now earns objective and finite continuous summand supports by separation. Actual
fixed-native affine-probe Schur energies are proved differentiable. Finite ambient
convex objectives receive a full objective/constraint/admissibility-normal split,
including nonzero PSD price under actual strict sensitivity. Extended objectives
receive exact restricted-objective stationarity. A boundary example proves that
restricted support cannot be relabeled as ambient support without a domain
qualification. The general relative-interior-qualified extended-objective split
remains to be constructed.


The [relative-interior-qualified construction](math/RELATIVE_SPLIT_LEAN_2026-10-03.md)
now earns the general ambient extended-objective/admissibility split, including
lower-dimensional domains. The exact sum rule is proved for both the restriction
and the literal J+indicator. It gives full original extended Schur stationarity
with actual trace derivative and a PSD price, nonzero under strict actual value
decrease. A zero-premise example has empty ambient domain interior and a forced
nonzero ambient objective support canceled by an admissibility normal. The
explicit matrix Jacobian/adjoint formula and physical bridge remain separate;
the broader paper is still incomplete.


The [explicit Schur derivative and adjoint](math/SCHUR_DIFFERENTIAL_LEAN_2026-10-03.md)
now computes the actual fixed-native matrix Jacobian and its trace-dual pullback.
Both product-rule terms are proved, and PSD symmetry earns the factor two.
Qualified original extended stationarity is returned in the literal D_Xi*P form
and an explicit equation for every primal direction. Singular native Gram blocks
and rectangular probes are retained, with actual controls for a missing term
and a nonsymmetric price. The physical bridge remains separate; the broader paper is incomplete.
The subsequent canonical scalar construction below closes the same-price assembly.


The [canonical scalar stationarity construction](math/SCALAR_STATIONARITY_LEAN_2026-10-03.md)
now proves the corrected generic scalar Theorem S with a single positive price:
actual value sensitivity, activity, strong duality, ambient objective/energy
subgradients and an admissibility normal. Nonsmooth finite convex energies are
retained. Its actual extended Schur specialization earns the derivative and
returns the literal matrix adjoint and every-direction formula. Scalar price
uniqueness is proved across certificates at potentially different optimizers.
A concrete nonsmooth energy has a differentiable actual value and full
stationarity despite no energy derivative at its optimizer. This closes the
same-price scalar assembly; physical identification and broad completion remain
separate.


The [general matrix-map construction](math/GENERAL_MATRIX_STATIONARITY_LEAN_2026-10-03.md)
now earns full qualified extended stationarity and original finite strong duality
for arbitrary Loewner-convex matrix maps. Smooth stationarity needs convexity on
A and actual differentiability at the optimizer. Strict actual PSD-direction
value decrease gives nonzero P. A nonsmooth endpoint keeps its finite ambient
extension explicit. The actual Schur example with nonlinear probe x^2 gives
residual x^4, beyond affine quadratic probes. Nonsmooth and off-A support controls
check the scope. General smooth matrix Theorem S is mechanized; physical
interpretation and broad original-target completion remain separate.


The [matrix sensitivity construction](math/MATRIX_SENSITIVITY_LEAN_2026-10-03.md)
identifies the entire symmetric PSD price as minus the actual full matrix-budget
value derivative. Slater earns local finite-value guards. The same nonzero price
supplies sensitivity, qualified stationarity and original strong duality;
uniqueness holds across certificates at different optimizers. Smooth and genuinely
nonsmooth examples return canonical price1. Controls show why a single directional
readout or an arbitrary nonsymmetric price does not suffice. The derivative and
ordinary optimizer remain hypotheses; broad original-target completion remains open.


The [robust first-record construction](math/ROBUST_RECORD_LEAN_2026-10-03.md)
returns actual first collapse and matter ratios to the whole declared coupled
threshold/amplitude rectangle and every signed admitted parameter. A single
positive parameter makes all twelve ratios arbitrarily small simultaneously
for every rectangle point. Endpoint ratios have uniform positive/finite bounds
in terms of the actual corner roots; these bounds do not certify a numerical
order-unity scale across the rectangle. Exact compensating knob changes preserve
the original readouts. The paper, runtime and previous proofs remain fixed.


The [certified robustness-edge construction](math/ROBUST_EDGE_LEAN_2026-10-03.md)
now gives explicit actual endpoint bounds3<u*c^3<7/2 and first-record ratios
3/8<R<1792/27 throughout the entire coupled threshold/amplitude rectangle,
for all twelve seeds. Exact scale covariance and three kernel-checked quadrature
profiles retain the original finite-start term/prefactor. Every signed admitted
ratio also has the explicit uniform upper bound1792/27. No sampled interpolation
or floating solver is used; physical identification and broad completion remain open.


The [patch-population ratio construction](math/PATCH_RATIO_LEAN_2026-10-03.md)
certifies actual N32 endpoint in(1.3,1.7) and N128 endpoint in(5,6.25), retaining
both separately realized original populations and the finite-start IVP. Every
seed's actual first-ANY-patch edge ratio is between2187/8000 and1792/27; all signed
admitted ratios have the same upper bound. One positive parameter makes all24
ratios arbitrarily small simultaneously. A kernel counterexample prevents an
incorrect transfer of the original N64 first-threshold lower bound. Broader
original-target completion remains open; paper/runtime/data remain fixed.


The [actual first-record regularity construction](math/FIRST_REGULARITY_LEAN_2026-10-03.md)
proves joint continuity of the signed first-time selector on its full admissible
domain and earns ambient continuity at every original admitted readout. Actual
first times are C1 in the coupled threshold/amplitude knobs at fixed lambda,
with positive threshold and negative amplitude sensitivities; endpoint times
and ratios are continuous. Arbitrary continuous finite amplitude changes retain
continuity through ties. Kernel controls show why horizon fallback and tied
maxima prevent broader unconditional smoothness claims. Paper/runtime/data fixed.


The [joint first-time calculus construction](math/FIRST_DIFFERENTIAL_LEAN_2026-10-03.md)
earns joint C1 including signed lambda for the actual first-record selector.
Its parameter derivative is minus actual growth sensitivity divided by native
velocity, hence positive. This returns to all original N32/N64/N128 times and
the entire N64 coupled rectangle; actual endpoint times and ratios are C1 in
the knobs. Ratios are C1 away from lambda=0 and are proved nondifferentiable
at zero because of abs(lambda). Original paper/runtime/data and earlier proofs
remain fixed. The broader original-target goal is still incomplete.


The [combined robustness construction](math/COMBINED_ROBUSTNESS_LEAN_2026-10-03.md)
extends the actual N32/N128 populations across the entire threshold/amplitude
rectangle, earning smooth endpoint movement, actual first-collapse C1 and
explicit signed-window ratio bounds. New exact quadrature certificates cover
the wider rescaling range missed by earlier estimates. One positive lambda
makes all36 original N32/N64/N128 ratios arbitrarily small simultaneously at
every rectangle point. Paper/runtime/data and earlier proofs remain fixed;
broader original-target completion remains open.


The [smooth-prior counterexample](math/SMOOTH_PRIOR_LEAN_2026-10-03.md)
returns the earlier nonsingularity objection to the actual growth toy. Smooth,
strictly positive densities on the full positive windows can assign arbitrarily
high mass to actual arbitrarily small ratios, uniformly across all three
original populations and the knob rectangle. Local regularity alone cannot
force upper-edge typicality. The broader original goal remains incomplete.


The [original allocation-carrier construction](math/ALLOCATION_SAMPLE_LEAN_2026-10-03.md)
returns the general theory to the pinned original32-patch inputs. It certifies
the rounded price0.4611, exact selected screening across an offset interval,
all original activity/slack cases and genuine local-budget/no-budget controls.
The no-budget response is proved the unique unconstrained optimizer. Floating
solver precision and historical bit recovery are separate; the paper remains
unchanged and the broader original goal remains incomplete.


The [actual alternating-sector iteration construction](math/GROUND_ALTERNATING_LEAN_2026-10-03.md)
proves local attraction and finite escape under the unchanged eight-site Step26
normalized ground iteration. At mixing1/2, the alternating sector is locally
attracting when -8<k*b<24 and repelling when k*b<-8 or k*b>24. Both background
and coupling affect this mechanism. The constant-background sector is explicit;
all-mode stability and the frozen nonconstant-background crossing remain open.


The [actual ground-Jacobian construction](math/GROUND_JACOBIAN_LEAN_2026-10-03.md)
proves C-infinity regularity of the existing ground selector at every real
potential and earns the actual Step26 source/normalized Jacobians for arbitrary
backgrounds, including nonconstant ones. Normalized tangent damping is derived,
and the original zero-coupling control returns exactly. Numerical branch and
spectral certificates remain open; no all-mode stability verdict is inferred.

The [original-template interval certificates](math/GROUND_INTERVAL_CERTIFICATES_2026-10-03.md) now verify isolated positive roots at all30 original sample arrays using exact integer interval arithmetic. At half mixing their real tangent spectra are stable at28 points, including coupling15, and unstable at20 and30. The analytic root criterion and full derivative return are proved in Lean; the concrete numerical certificates are Python-checked, not kernel instantiations. A continuously followed branch and the frozen complex run remain separate.

The [nonlinear ground-map return](math/GROUND_NONLINEAR_DYNAMICS_2026-10-03.md) now proves actual local convergence in all eight real directions from earned derivative row bounds, and direct global zero-coupling convergence for every background from nonnegative unit fields with0<m<=1. The28 stable original-sample certificates thereby earn mathematical local attraction using their exact Python inputs; concrete Lean instantiations and original complex basins remain separate.

The [original complex-update construction](math/GROUND_NATIVE_COMPLEX_2026-10-03.md)
retains the frozen phase-sign bug and proves its full sixteen-real-coordinate
derivative, legal fixed points for all backgrounds/couplings, and guarded
nonlinear local convergence. Exact computational imaginary-block bounds at
all30 original roots extend the28 stable sample returns to complex local
attraction, including coupling15; real instability at20/30 persists. Concrete
kernel certificate instantiations and the frozen initialization's basin remain
open. An explicit unit imaginary input cancels at half mixing, so global
complex convergence is not inferred.

The [original coupling-branch construction](math/GROUND_COUPLING_BRANCH_2026-10-03.md)
now certifies a connected positive ground branch throughout[0,30], through all12
original coupling roots. Uniform Newton tubes and common-root seams earn the
continuation; determinant signs give actual half-mixing minus-one modes in
(15.8,15.9) and(15.9,20). Lean proves the analytical construction and mode return;
concrete interval certificates and the final finite patch selection remain
outside kernel instantiation. This does not prove nonlinear runaway or restore
κ>=15 instability, since15 is locally attracting on this branch.


The [finite coupling-branch assembly](math/GROUND_FINITE_PATCH_2026-10-04.md) now constructs the global branch in
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


The [first concrete kernel tube](math/GROUND_KERNEL_TUBE_2026-10-04.md) now proves the actual original-background
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


The [complete kernel coupling continuum](math/GROUND_KERNEL_CONTINUATION_2026-10-04.md) now supplies all286 original uniform tubes and287 endpoint anchors
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


The [native nonlinear escape construction](math/GROUND_NATIVE_ESCAPE_2026-10-04.md) now earns the nonlinear bridge from an actual expanding real eigenmode
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


The [kernel sample and derivative-entry construction](math/GROUND_KERNEL_SAMPLES_2026-10-04.md) now instantiates all twelve original coupling-root boxes and two crossing
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
[the coordinate mathematics note](math/GROUND_KERNEL_COORDINATES_2026-10-04.md).


The 2026-10-04 spectral packet now proves seven actual shifted determinant
signs in the Lean kernel, two distinct minus-one contacts on the original branch,
and full unit expanding modes at couplings20 and30. These populate the nonlinear
bridge: arbitrarily close unit complex starts escape a fixed coordinate
neighborhood through finite active, legal native orbit segments. Concrete
returns have no supplied spectral or escape premises. The original phase bug
is retained. Frozen initialization basins, finite-step source outcomes and the
eighteen background-offset kernel instances remain pending. No first/unique/
simple/transverse contact, all-orbit escape or universal runaway claim is made.
See [the spectral mathematics note](math/GROUND_KERNEL_SPECTRUM_2026-10-04.md).


The 2026-10-04 native reflection packet now returns the negative real branch
representative to legal native fixed points throughout[0,30], actual local
attraction at ten original coupling samples through15, and finite guarded escape
at20/30. Reflection is proved only on active orbit prefixes. A unit, legally
normalized inactive-phase example rejects unconditional reflection. A read-only
floating scout identifies the negative representative as the frozen seed's
apparent target at stable sampled couplings; it supplies no basin certificate.
The exact frozen-seed basin and18 offset kernel instances remain pending. See
[the signed-representative note](math/GROUND_NATIVE_REFLECTION_2026-10-04.md).


The 2026-10-04 global native zero-coupling packet now proves convergence for
all real backgrounds and unit complex starts whose signed real ground overlap
exceeds the source threshold. The unchanged conjugate phase and half mixing are
retained, with geometric decay and active/legal execution at every step. Closed
seed arithmetic returns the original reified initialization at coupling0 to the
negative actual branch ground, with real overlap below-1/5 and no supplied basin
premise. Both initialization normalizations are represented. This is exact
mathematical model evidence; no60-step floating verdict or IEEE per-operation
emulation is claimed. Positive-coupling seed basins and18 offset kernel sample
instances remain pending. See [the zero-coupling seed note](math/GROUND_NATIVE_ZERO_SEED_2026-10-04.md).

The exact original-seed native zero-coupling orbit now has a kernel-earned
first-step entry into a faster contraction region and a full Euclidean distance
below2e-9 to the negative actual ground after60 updates (below3e-9 after59).
This does not yet certify all four source convergence residuals or IEEE execution.
See `math/GROUND_NATIVE_ZERO_FINITE_2026-10-04.md`.

All four exact mathematical source convergence tests now pass after60 updates
for the original seed at zero coupling, including the actual twice-aligned gap
and Rayleigh eigen residual. Both phase diagnostics and all native iterate guards
are earned. This does not certify IEEE execution or positive-coupling seed basins.
See `math/GROUND_SOURCE_RESIDUALS_2026-10-04.md`.


The exact original-seed native orbit at original coupling 0.3 now has a kernel
certified 16-update prefix, with active phase and legal normalization at inputs
0–15 and unit norm at states 0–16. Its endpoint is within 1e-5 in State sup-coordinate
norm of the negative actual branch ground. Uniform whole-potential-box Newton
certificates and both reciprocal-square-root guards are earned; the original
phase rule and both initialization normalizations are retained. Nearness does
not establish entry into the earlier unspecified local attraction radius. An
explicit quantitative basin and 60-update positive-coupling source tests remain
pending. See `math/GROUND_NATIVE_PREFIX_2026-10-04.md`. The paper is unchanged; overall goal incomplete.

The original coupling 0.3 now has a kernel-certified explicit native basin:
coordinate radius 1/40000, whole-ball derivative bound 3/5 and reflected
sixteenth-iterate entry distance at most 1/48000. The exact original-seed orbit
converges to the negative actual branch ground, with all states unit and all
phase/normalization guards earned. The full sixteen-coordinate derivative and
near-inverse response error are retained. The original conjugated phase and
both initialization normalizations remain represented. Sixty-update source
diagnostics at 0.3, other positive-coupling seed basins, eighteen offset sample
instances and IEEE execution remain pending. See `math/GROUND_NATIVE_BASIN_2026-10-04.md`. The paper is
unchanged; the overall goal remains incomplete.

All four exact mathematical source convergence tests now pass after60 updates
at original coupling0.3, with active/legal guards at every original iterate.
The actual sourced candidate has an earned distance bound; both source phase
alignments and the actual Rayleigh energy are retained. The State-to-Euclidean
norm bridge and sourced Hamiltonian budget are derived. This does not claim
IEEE execution, a first stopping index or independent sourcing consistency.
See `math/GROUND_POSITIVE_SOURCE_RESIDUALS_2026-10-04.md`. Other seed basins and18 offset kernel instances remain pending;
the paper is unchanged and the overall goal remains incomplete.

All18 original background offsets at coupling0.3 now have kernel-certified
positive unit self-consistent ground/energy roots, local ball uniqueness and
legal actual native real fixed points. Whole background boxes cover both exact
uniform offsets and saved rounded input vectors. The offset-8 and+10 actual
fields differ by>3/10 at site0 and their source densities by>9/100, for both
models. Offset0 equals the original actual branch root. Local native stability
and frozen-seed60-step offset verdicts remain separate obligations; the Newton
rate is not a native contraction rate. See `math/GROUND_OFFSETS_2026-10-04.md`. Paper/runtime unchanged;
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
See `math/GROUND_OFFSET_NATIVE_STABILITY_2026-10-04.md`. Paper and earlier mathematical evidence remain unchanged;
overall goal incomplete.

All18 original offset roots now have explicit native complex basins for both
signs, exact/rounded inputs and every background in their hulls. A common
coordinate radius1/400000 works across the finite family; the first17 also
admit1/40000. All sixteen input columns, cross blocks and whole-ball guards are
certified, with geometric distance bounds at every iterate. Frozen-seed entry
and sixty-update offset verdicts remain separate. This adds261 fresh
standard-only declarations, cumulative3488, with an8954-job default build.
See `math/GROUND_OFFSET_EXPLICIT_BASINS_2026-10-04.md`. The paper is unchanged; overall goal incomplete.

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
incomplete. See `math/GROUND_OFFSET_SEED_RETURNS_2026-10-04.md`.


All18 rounded-offset original-seed orbits now have exact mathematical
sixty-update source verdicts: fifteen pass the original four-test conjunction;
-5, -3 and +10 fail because the actual last-update residual exceeds the source
tolerance. All18 still converge eventually with all native guards/unit states.
The actual current sourced selector, actual Rayleigh energy and both diagnostic
phase calls are retained. This adds423 fresh standard-only declarations,
cumulative4867, with a9557-job default build. Exact uniform-offset seed returns,
whole input-hull seed returns, per-operation IEEE execution and first stopping
indices remain separate. See `math/GROUND_OFFSET_SIXTY_VERDICTS_2026-10-04.md`.
The paper/runtime are unchanged; overall goal incomplete.


## Original-input mathematical returns (2026-10-06)

Earlier review commits repaired statistical computations and audit semantics.
This native integration preserves those repairs and the original iteration
laws; the paper remains unedited throughout the review.

Dark energy remains the motivating inference problem. The results concern the
specified mathematical models and readouts; they do not derive physical dark
energy or transfer the model's interpretation to spacetime. The paper is
unchanged and still needs the agreed narrowing. See the
[interpretation scope](math/PHYSICAL_INTERPRETATION_SCOPE_2026-10-05.md).

The exact original twelve-coupling iteration now has a combined Lean theorem.
The ten sampled couplings through15 converge with legal normalization and unit
states at every update. Coupling15 fails the original four-test conjunction at
every update1..60, yet converges after certified basin entry by update178 and
eventually passes those tests. Couplings20 and30 approach genuine attracting
two-cycles; their states remain unit and bounded, while the declared site density
does not converge. The sixty-update diagnostic and infinite-time behavior
therefore distinguish different properties. These statements classify the
twelve supplied samples, not every intervening coupling or IEEE execution.

The eighteen original background controls have infinite limiting orbits at
coupling0.3; fifteen pass the sixty-update diagnostic. Neither Boolean readout
recovers all eighteen inputs. Certified seed returns also cover all backgrounds
in eighteen specified input boxes. This is not a whole continuous interval of
offsets, nor a universal impossibility of parameter identification from richer
observations. Guarded Option execution is proved separately; supplied unit
phase-related starts can split successful execution from normalization failure.

The adopted mediator theorem requires recovery of all four coordinates whenever
a deterministic mediator determines both declared readouts. It is an information
recovery result, with no lower bound of four literal storage fields or four
encoding dimensions. Optimization prices and growth/record windows retain their
explicit mathematical assumptions. They do not select a physically realized
cosmological parameter.

The registered integration adds1772 modules and20798 declarations to the
11776-declaration earlier cumulative audit. Its actual native build, all20798
statement queries and one full32574-query cumulative transitive-axiom command
pass with only `propext`, `Classical.choice` and `Quot.sound`. The preceding
whole-offset integration also passes its registered10003-job build,6909
statement/axiom checks,421-step replay and440-source regeneration. See
`results/native_registered_final_verification_2026-10-06` for the final native command
receipts; the preceding whole-offset results are in
`results/ground_offset_transport_2026-10-04/verification.json`. These are kernel checks and adversarial self-review, not independent
human review or a proof of the paper's unrevised physical claims.
