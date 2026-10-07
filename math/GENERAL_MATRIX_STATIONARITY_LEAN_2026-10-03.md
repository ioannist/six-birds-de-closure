# General matrix/Loewner price and qualified stationarity, 2026-10-03

Baseline: `2f88d23`. Review is adversarial self-review, not independent review.
Paper, runtime, external artifacts and all prior proof/evidence remain fixed.

This packet closes the general smooth matrix-map formulation in corrected LT1
`math/DERIVATION_LT1_2026-06-02.md`, section 2.3, beyond the earlier fixed-native
affine-probe application. It constructs the price, objective support, normal,
actual-derivative adjoint stationarity, complementarity and original extended
strong duality for an arbitrary Loewner-convex matrix map. No new downgrade to
the smooth structural theorem is needed. The nonsmooth analogue has an explicit
finite ambient extension hypothesis; convexity on A is not relabeled as ambient
convexity. Physical interpretation and broad paper completion remain separate.

## Exact original domain and budget

Xi maps the real primal space into the existing symmetric matrix subspace.
The budget B belongs to that same subspace, with its inherited existing finite
elementwise matrix norm. `GeneralMatrixPrice.LoewnerConvexOn A Xi` means precisely

```
a*Xi(x)+b*Xi(y)-Xi(a*x+b*y) is PSD,
x,y in A, a,b>=0, a+b=1.
```

The budget constraint is B-Xi(x) PSD. The objective remains the original EReal
J, including its infinite-cost points. Its restriction to A has a convex real
epigraph and no minus-infinity values. An ordinary finite optimum star is
supplied, along with x0 in A of finite cost and actual positive-definite slack
B-Xi(x0). The cone topology is on symmetric matrices, not on all matrices.

`GeneralMatrixPrice.matrix_price` uses the earlier constructed Slater local
finite costs and supporting price of the actual extended value. The actual
linear budget price is represented on the whole symmetric matrix space by
P, with PSD P earned from positivity on rank-one PSD directions. The explicitly
defined continuous price `tracePrice P` is H -> trace(P H). Its equality with
the constructed budget functional is proved on every original symmetric H.

The endpoint returns P PSD, an original extended conic DualCertificate using
that actual trace price, and equality/finiteness of the original complete-lattice
primal and dual infima. The certificate contains feasibility, complementarity,
and global extended Lagrangian minimization at every admissible x. Value
differentiability, local finite-value guards, a dual, or stationarity are not
supplied. Arbitrary nonlinear maps are permitted; no affine D is imposed.
The primal space needs no topology for this dual construction.

`matrix_price_nonzero` additionally uses actual strict value decrease under
a PSD budget increment. It returns P!=0. This retains a possible minus-infinity
competing value: a strictly cheaper candidate is obtained from the EReal
complete-lattice infimum, with no unguarded real conversion. Whole-matrix
activity does not follow from complementarity.

## Local smoothness and the qualified full split

`ExtendedSmoothStationarity.restricted_stationarity` earns restricted support
-k for original extended J from a finite smooth summand g, actual minimization
of J+g on A, and HasFDerivAt g k at star. Only objective convexity is needed;
g need not be convex away from star. It guards the finite-domain real return,
uses actual right-line derivatives and convex objective mixing, and returns
to all original admissible points, including top costs. No finite-dimensional
primal assumption is needed for this restricted support lemma.

Its qualified version uses the earlier actual common point of ri(dom J) and
ri(A) to earn an ambient J support q and normal eta with q+k+eta=0. The primal
ambient space is now finite-dimensional normed. No objective support, normal
or sum-rule field is supplied.

`GeneralMatrixStationarity.hasFDerivAt_trace_gap` derives the genuine scalar
trace-Lagrangian derivative by composing the actual matrix derivative Xi'
with trace pairing and subtracting the fixed budget. The derivative is
traceAdjoint Xi' P, the actual pullback into the primal continuous dual. No
primal inner product or Hilbert adjoint is invented.

The general smooth `matrix_stationarity` and its nonzero version construct
the Slater price, then apply the qualified split to that same certificate.
They require Loewner convexity only on A and actual matrix HasFDerivAt at star,
not a global convex extension or global differentiability. They return

```
P PSD [and P!=0 under strict actual budget-value decrease],
q in partial J(star), eta in N_A(star),
q+traceAdjoint(Xi') P+eta=0,
trace(P*(Xi(star)-B))=0,
original trace-price certificate and finite original primal/dual equality.
```

The actual matrix derivative is a legitimate input of this conditional general
theorem, as in LT1; the Lagrangian derivative, price, support, normal and final
stationarity are derived. The concrete Schur example below earns the matrix
derivative independently. `matrix_stationarity_fderiv` uses DifferentiableAt
of the actual Xi map first, then returns literal fderiv stationarity; it does
not rely on fderiv's nonsmooth zero fallback. Closedness and Slater RI membership
are unnecessary for these endpoints once ordinary attainment, finite PD Slater
and the separate common RI objective/admissibility qualification are present.

## Honest nonsmooth scope

`matrix_nonsmooth_stationarity` needs a finite ambient Loewner-convex extension
of Xi. The actual earned cone-positive certificate then makes trace(P Xi)
a finite ambient convex function. Finite-dimensional continuity and the actual
epigraph/hypograph separation earn its real subgradient k and restricted J
support -k; the common RI construction earns the ambient J/normal split.
The conclusion uses an actual support of trace(P Xi), not a fictitious matrix
derivative. No value or matrix differentiability premise is supplied.

The finite ambient extension is a sufficient condition for this nonsmooth
return, paralleling the corrected scalar theorem. The informal nonsmooth
remark in LT1 must be read with such an extension or an adequate sum-rule/domain
qualification. Loewner convexity only on A does not supply a global support
for an arbitrary off-A continuation. This is a scope precision for the
nonsmooth analogue, not a downgrade of the general smooth theorem proved here.

## Actual Schur/nonquadratic and nonsmooth instances

`GeneralMatrixExamples.quartic_actual_schur` proves Xi(x)=[x^4] equals the actual
repository residual for singular native L=0 and nonlinear dissolving probe
D(x)=[x^2]. Its PSD content also follows from the established actual residual
positivity. The matrix map's Loewner convexity follows from the pinned elementary
even-power convexity theorem. Its actual matrix derivative is 4*x^3 times
the scalar-to-matrix continuous linear map. It is not an affine-probe quadratic:
four exact evaluations refute every scalar polynomial of degree at most two
for its actual matrix entry. That control asserts exactly the entry statement;
it is not an unproved general classification of all Schur presentations.

The original extended objective (x-2)^2 on x>=0, infinity otherwise, is retained.
At budget[1] its actual optimizer is1 and its actual value is1. At budget[16]
its actual optimizer is2 and value0. Finite PD Slater at0 and common RI at1
are proved. The PSD increment[15] gives actual strict value decrease. The full
general endpoint constructs nonzero PSD P, separate original objective support
and normal, actual derivative-adjoint stationarity, original certificate and
dual value1. The final concrete statement has zero premises.

A second actual map [x+abs(y)] has no matrix derivative at optimizer(0,0), proved
by projecting its actual entry to the already refuted abs-line derivative.
Its finite ambient Loewner convexity, ordinary optimizer, finite PD Slater and
common RI point are independently proved. The full nonsmooth endpoint returns
an ambient support of its actual price-weighted trace energy and the qualified
stationarity split, with no derivative or final output premise. This map may
have negative values and is a general Loewner-map test, not an adequacy-PSD
residual. The quartic application above supplies the actual Schur instance.

Finally an off-A continuation is e(x)=x for x>=0 and -1 for x<0. Its one-by-one
matrix map is Loewner-convex on A=[0,infinity). Every positive scalar trace price
lacks an ambient energy support at x=1: comparisons at0 and2 force slope p,
and at-1/2 contradict the support. The control proves that restricted convexity
alone cannot be promoted to ambient support. It does not claim failure of the
smooth matrix theorem or of every nonsmooth theorem with a different qualified
extension. The final no-support statement has only the meaningful input p>0.

## Verification and next work

Full `lake build`: 8144 jobs. All 28 fresh exported theorem statements and
transitive axiom closures checked; only standard Lean axioms, no holes or
native_decide. Cumulative1158 is the exact immutable earlier1130 raw prefix
plus fresh28; the full cumulative command was not rerun. The verifier checks
source/toolchain identity, original-return statement coverage and protected
prior evidence. Receipts: `results/general_matrix_2026-10-03/`.

The corrected general smooth matrix/Loewner Theorem S is now mechanized, along
with a qualified nonsmooth extension and an actual nonlinear Schur instance.
The scalar Theorem S was assembled in the prior packet. The remaining scope
audit includes general matrix-price/value-derivative identification if needed
and other feasible original-target constructions. Physical Lambda, moving
native calculus, primal attainment and previously parked false/project-sized
claims remain separate. Broad paper completion is not asserted.
