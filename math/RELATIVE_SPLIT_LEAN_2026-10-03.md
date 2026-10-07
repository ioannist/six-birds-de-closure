# Relative-interior-qualified objective/normal splitting, 2026-10-03

Baseline: `2a63edc`. Review is adversarial self-review, not independent review.
Paper, original runtime, and previous proofs and evidence remain unchanged.

This packet constructs the general relative-interior-qualified split previously
left open. It returns that split to the original extended Schur problem. No
finite-everywhere objective, full-dimensional domain, supplied subgradient split,
value derivative, or local finite-value premise replaces the original target.
The broader paper remains incomplete; the physical Lambda bridge and other
previously parked issues are unaffected. No new claim downgrade is needed.

## Target and exact return

For a finite-dimensional real normed ambient space E, an extended objective J
with no minus-infinity values and convex real epigraph, a convex admissibility
set A, and an actual common point in ri(dom J) and ri(A), Lean proves

```
p in partial(J + indicator_A)(star)
  iff there exist q in partial J(star), n in N_A(star), q+n=p.
```

The supporting-functional definitions are the actual global original-objective
inequalities from `ConvexSubgradient`. Normal signs are n(x-star)<=0 on A.
The effective domain is exactly the set where the original J is not plus
infinity. Relative interior is mathlib's intrinsic interior in the actual
affine span. The qualification point need not be the optimizer.

Both the restriction version and the literal J+indicator version are proved.
Their equality is separately proved using the no-minus-infinity hypothesis;
the extended sum is not silently identified across ambiguous infinity arithmetic.
Closedness is unnecessary for this result. The original proper closed convex
objective assumptions therefore suffice, rather than being downgraded.

## Domain geometry and continuity

`RelativeConvexContinuity` proves that a real convex function on C is continuous
on ri(C). The pinned mathlib has a proof-wanted comment for this result, so it
is constructed here rather than treated as an established import. A point in C
provides an origin in its actual affine span S. The affine isometry from the
normed direction S.direction to S transports interior continuity of the pulled
back convex function. The inducing subtype topology returns continuity to ri(C).
The empty-domain case is handled separately.

At a relative-interior point x0, the actual chart u -> x0+u has a domain
neighborhood at zero. Convexity earns continuity at this origin, and hence the
upper bound f(x0+u)<=f(x0)+1 on a smaller neighborhood. None is a supplied field.

`RelativeDifference` uses P=(affineSpan C).direction,
Q=(affineSpan A).direction, and the actual budget space K=P+Q. The linear map

```
P x Q -> K, (u,v) -> u-v
```

is constructed and proved surjective by the submodule-sum representation.
The imported finite-dimensional module-topology open-map theorem makes it
open. Its image of the product of the two actual chart neighborhoods is a
neighborhood of zero in K. Thus, for every sufficiently small w in K, there
exist x in C and y in A with x-y=w and f(x)<=f(x0)+1. No ambient open-domain
assumption is used; K itself may be a proper subspace of E.

## Guarded equality value and separation

`RelativeEqualitySupport` works with the actual equality-perturbation feasible
costs and their real infimum. Its zero cone represents equality exactly. Given
an ordinary attained minimum at budget zero and bounded-cost witnesses near
zero, a witness at -w can be midpoint-mixed with every candidate at w. The
midpoint has zero budget; optimality and convexity give the uniform bound

```
f(candidate) >= 2*f(star)-M.
```

Together with the constructed feasible witnesses this earns nonempty and
bounded-below actual cost sets. The earlier proved nonsmooth cone-price
construction now applies: approximate costs earn value convexity, actual
strict-epigraph separation earns local support, and optimizer mixing returns
support globally. The equality cone imposes no price-sign restriction.

`RelativeSumSplit` applies this to the actual affine-span coordinate pair
domain. Every original x in C and y in A is explicitly represented, not only
nearby or full-dimensional points. Imported real Hahn-Banach extends the
constructed continuous functional on K to E with exact restriction. Global
pair support reads

```
f(star)+q(x-y)<=f(x), x in C, y in A.
```

Putting y=star gives objective support; putting x=star gives the normal -q.
For arbitrary restricted support p, subtract the actual linear functional p
from f. This preserves C and its qualification and reduces to ordinary
minimization. Adding p back gives q+n=p. The previously proved epigraph/domain
reduction supplies convexity of J.toReal on the exact effective domain.
Coercion restores support at every original point, including plus-infinity
objective values. Conversely, adding an ambient support and an admissibility
normal always gives a restricted support; this direction needs no qualification.

## Original Schur stationarity

`RelativeSchurStationarity` combines the earned split with the earlier original
extended Slater price and actual fixed-native affine-probe Schur smoothness.
The ambient epigraph restricts to A by an explicit convexity proof. For an
ordinary finite original optimizer, an actual finite-cost positive-definite
Slater slack, and the common relative-interior domain point, Lean constructs

```
P PSD, q in partial J(star), n in N_A(star),
q + fderiv(trace(P*(Xi(x)-B)))(star) + n = 0,
trace(P*(Xi(star)-B)) = 0.
```

The derivative is of the actual original scalar trace pairing, not a supplied
stationarity functional or an unguarded fderiv fallback: its differentiability
is proved by the earlier Schur module. Strict decrease of the original complete-
lattice value in a PSD budget direction also earns P!=0. If P=0, stationarity
would give restricted zero objective support, contradicting a cheaper actual
cost at the competing budget. This argument allows a competing value of minus
infinity and does not use an unguarded real conversion.

The explicit matrix Jacobian/adjoint formula remains a separate obligation.
Primal attainment is a hypothesis, as in the original theorem; it is not proved
here. The physical identification of this certificate with spacetime Lambda
also remains separate.

## Discriminating example and evidence

`RelativeSplitExamples` defines J(x,y)=x on the line y=0 and plus infinity off
that line, with A={(0,0)}. It proves no bottom values, convex epigraph, the exact
domain and relative interior, and empty ambient domain interior. Restricted
zero support is earned at the ordinary singleton optimum. The generic
qualified construction yields an ambient objective support q and a normal n
with q+n=0. Testing (-1,0) proves q!=0. The final construction has zero premises.
This tests a genuinely extended lower-dimensional domain and a normal needed
to cancel its objective support. The earlier -sqrt missing-qualification
counterexample is preserved unchanged.

Evidence: full `lake build` (8133 jobs), all 27 fresh exported theorem types and
transitive axiom closures, standard axioms only, no holes or native_decide.
Cumulative 1083 closures preserve the exact immutable earlier 1056 raw prefix
and append the fresh 27; the full cumulative command was not rerun. Source and
toolchain identity are checked by `scripts/de_relative_split_verify.py`.
Receipts are in `results/relative_split_2026-10-03/`, with fresh manifests in
`lean/manifests/check_relative_split_{statements,axioms}.lean`.
No Python suite, original solver, RNG, or empirical carrier was rerun.
