# Nonsmooth conic Slater and actual Schur matrix duality, 2026-10-03

Baseline: `e40938d`. Paper, original runtime and prior proofs/evidence unchanged.
Review is adversarial self-review, not independent review.

This closes the nonsmooth Slater dual construction left separate by the earlier
value-derivative packets. Qualified splitting of objective, constraint and
admissibility subdifferentials remains a separate obligation. Primal attainment
is supplied as an ordinary finite optimum, not proved from compactness. No
physical identification follows from an optimization multiplier.

## Supporting functionals from the actual value

`ConvexValueSupport` separates an actual strict epigraph on an open convex
domain from its boundary point `(B,f(B))`. In a finite-dimensional real normed
budget space, convexity earns continuity by the pinned mathlib theorem. Local
continuity and openness make the strict epigraph open. Hahn-Banach separation
is an established import, not a supplied supporting functional. Evaluating the
strict separation at `(B,f(B)+1)` proves the vertical coefficient is positive.
A positive epsilon argument returns separation to the boundary epigraph; division
by the proved positive coefficient constructs a continuous linear d with

```
f(B)+d(T-B) <= f(T) for every T in the open convex domain.
```

The intermediate theorem also works in arbitrary normed budget spaces when
continuity is explicitly supplied. Neither version assumes differentiability.

`NonsmoothConePrice` uses the unchanged actual real conic cost set and guarded
infimum. Cone zero/addition/nonnegative-scaling laws, convex J on A, and conic
convexity of energy are explicit premises. Approximate feasible costs independently
earn convexity of this actual value on any convex budget domain where its cost
sets are nonempty and bounded below. This is not an assumed convex value field.

On a locally finite budget neighborhood, separation supplies d. Budget motion
in each positive cone direction, using the actual optimizer as a feasible
candidate, proves d is nonpositive on the cone. Mixing the optimizer with every
original x in A returns local support to a global primal inequality. Therefore
p=-d is cone-positive, and

```
p(energy(star)-B)=0,
J(star)<=J(x)+p(energy(x)-B) for every x in A.
```

The first equality follows from the global inequality at star and cone positivity
on its slack. It is not a premise, and does not assert the entire slack is zero.
The unchanged real certificate theorem then proves actual guarded primal/dual
infimum equality. A certificate also supports the actual value at every budget
with a nonempty cost set: V(B)-p(T-B)<=V(T). The lower bound earns boundedness
below there. Strict decrease earns positive p(T-B), hence nonzero p.

## Slater earns local finite costs

The derivative-free theorem can use explicit local finite-cost guards, or earn
them from an interior Slater point x0 in A. No relative-interior objective/domain
sum-rule hypothesis is needed for the combined global certificate proved here.

Let S=B-energy(x0) lie in the interior of the positive budget cone. Near B, both
T-energy(x0) and S+(B-T) are positive. The first condition supplies a finite
feasible cost at T. If x is feasible at T, conic convexity makes the midpoint of
x and x0 feasible at B, because

```
B-energy((x+x0)/2)
 = (T-energy(x))/2 + (S+B-T)/2
   + (energy(x)+energy(x0))/2-energy((x+x0)/2).
```

Convexity and ordinary optimality at B give the uniform lower bound
J(x)>=2J(star)-J(x0). Thus both actual real infimum guards hold locally; they
are not supplied to the Slater theorem. This construction needs topology and
finite dimension only for the budget space; the primal space is a real module.
No closedness/compactness or solver convergence conclusion is added.

## Extended objective and exact original return

`ExtendedNonsmoothConePrice` uses the actual original complete-lattice EReal
infimum, the original A, and the actual cone-feasibility relation. Its premises
are no minus-infinity objective on A, convex ordinary real epigraph, conic
convexity, ordinary finite primal attainment, and either actual finite value
near B or a finite interior Slater point. Earlier proved effective-domain
convexity and objective/optimizer reductions are imported. The finite local-value
route earns real-cost guards from actual EReal finiteness. The Slater route earns
these guards directly on the proved effective domain, without a local-value
premise.

Separation supplies the real certificate; the earlier proved domain return
restores it to every original admissible point, including plus-infinity objective
values. The finite price leaves those Lagrangian values plus infinity. The
original complete-lattice primal and dual values agree, and the dual value is
proved neither infinity. No toReal conversion over the unrestricted original
domain is used. Strict actual extended value decrease excludes zero price by an
actual cost witness below J(star). A competing value of minus infinity is handled
by complete-lattice semantics; no artificial real fallback is introduced.

## Actual Schur matrix budget and Slater topology

`MatrixSlaterTopology` proves that positive-definite slack lies in the interior
of the actual PSD cone on the bundled symmetric matrix space. A joint quadratic
form is continuous. Its strict positivity on the compact unit sphere supplies,
by the tube lemma, a neighborhood of symmetric matrices positive on the whole
sphere. Normalizing every nonzero vector returns this to PSD membership. The
zero vector and empty-index/zero-dimensional case are covered by the same proof.
The topology is the earlier elementwise norm on symmetric matrices. Positivity
is not falsely claimed to be open in the full matrix space.

`NonsmoothMatrixPrice` applies the extended conic Slater construction to exactly
Xi(x)=Support.residual L (D(x)), with fixed L and affine D. Prior exact blind-Gram
identities earn actual Loewner convexity, including singular native blocks.
Prior symmetrized matrix-unit and rank-one constructions earn the symmetric PSD
trace representative P. Positive-definite original slack at a finite x0, convex
real epigraph and ordinary finite optimizer now yield

```
P>=0,
trace(P*(Xi(star)-B))=0,
J(star)<=J(x)+trace(P*(Xi(x)-B)) for every original x in A,
actual extended trace-Lagrangian infimum=actual extended primal value,
that dual infimum is finite.
```

The theorem supplies no value derivative, local finiteness, dual, complementarity
or Loewner-convexity field. If the actual value decreases in a PSD direction,
P is proved nonzero. Prices need not be unique, and full matrix activity is not
claimed. Qualified separate subdifferential/normal-cone stationarity remains
outside this construction.

## Inhabitation and scope controls

`NonsmoothPriceExamples` constructs a genuinely nondifferentiable actual value:
J(x)=max(-x,-2x), energy(x)=x, A=R, cone=[0,infinity). Ordinary optimizer x=B
and actual V(B)=J(B) are proved at every real budget. At B=0 a strict Slater point
x0=-1 supplies the dual construction. Actual V(1)=-1<V(0)=0 earns a nonzero price
and actual primal/dual value0. The actual value at B=0 is proved not differentiable,
using |x|=2J(x)+3x and the pinned theorem for the absolute-value kink. This proves
the new route covers a case unavailable to the previous derivative theorem.

A second zero-premise theorem returns the original extended Schur matrix example:
actual one-by-one residual x^2, J=(x-2)^2 on x>=0 and plus infinity otherwise,
budget1 and optimizer1. The finite x0=0 supplies an actual positive-definite
slack. Feasible x=2 at relaxed budget4 gives strict actual value decrease. The
new nonsmooth matrix theorem supplies a nonzero PSD trace price with global
original-domain bound and actual dual value1. No derivative or local-value lemma
is used in that proof. The earlier full-matrix-activity and bad-toReal controls
remain unchanged.

## Verification

Full default `lake build`: 8123 jobs, success, warnings treated as errors.
All 27 new exported theorem statements and transitive axiom closures freshly
checked. Only propext, Classical.choice and Quot.sound occur; no sorry, local
axiom, admit or native_decide. The cumulative 1030 ordered closures preserve the
exact immutable earlier 1003 raw prefix and add the fresh 27-declaration suffix.
Earlier sources/toolchain and artifacts are checked by fingerprint and Git identity;
the full cumulative command was not rerun. The complete manifest remains executable.
The verifier records checkout and canonical Git hashes separately, preserving
historical CRLF artifacts. Original Python/RNG/solver suites were not rerun.

Receipts: `results/nonsmooth_price_2026-10-03/`; verification:
`scripts/de_nonsmooth_price_verify.py`; statement/axiom manifests:
`lean/manifests/check_nonsmooth_price_{statements,axioms}.lean`.

No new claim downgrade is required. General nonsmooth Slater duality and its
actual extended Schur matrix return are now mechanized. Qualified split KKT,
the physical bridge and the previously parked false/physical claims remain
separate; the full original paper is still not established as complete.
