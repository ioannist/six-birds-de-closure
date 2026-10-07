# Constructed stationarity splitting and actual Schur smoothness, 2026-10-03

Baseline: `6e7db00`. Paper, original runtime and previous proofs/evidence unchanged.
Review is adversarial self-review, not independent review.

This packet earns a sum split when one summand is finite and continuous, connects
it to actual Schur smoothness, and proves full objective/constraint/normal-cone
stationarity for finite ambient convex objectives. It also proves the exact
restricted-objective stationarity for genuinely extended objectives. The general
relative-interior-qualified split between ambient extended J and admissibility
remains to be constructed; this packet does not replace that original target
with the finite-objective case. No new downgrade is required.

## Actual supporting-functional definitions

`ConvexSubgradient` defines ambient extended objective subgradients by a global
supporting inequality, with finite objective at star. `SubgradientOn A J` restricts
that inequality to A. It is proved exactly equivalent to an ambient subgradient
of the actual restriction x -> J(x) on A and plus infinity off A. It is not
identified with an ambient subgradient of J itself.

The actual admissibility indicator is zero on A and plus infinity off A. Its
subgradients are proved equivalent to the normal cone with sign convention
n(x-star)<=0 for every x in A. On the whole space the normal cone contains only
zero. Real supporting functionals are proved equivalent to the corresponding
extended-real subgradients after coercing a finite real objective. Zero restricted
support is equivalent to ordinary attained global minimization over A.

A smooth finite summand can be removed from a supporting inequality. Convexity
of J along each primal mix and the actual right line derivative of g prove

```
J(star)+g(star)+p(x-star)<=J(x)+g(x),
HasFDerivAt g k star
  => J(star)+(p-k)(x-star)<=J(x), for x in A.
```

The function being differentiated is actual p(t*(x-star))-g(star+t*(x-star));
its right upper support follows from the original total-support inequality and
objective convexity. This does not assume a split field. No convexity of the
smooth summand is needed for removal. Testing both ambient directions proves
that any supporting functional of a differentiable finite g equals its actual
derivative. This protects fderiv from use as an arbitrary fallback.

## Sum splitting by separation

`ConvexSumSplit` starts with an ordinary attained minimum of J+g on a convex
objective domain A. J is real convex on A; g is finite convex on the whole normed
ambient space and continuous. In finite dimensions continuity is earned from
global convexity. No subgradient, normal, support or sum-rule certificate is
supplied.

The actual disjoint convex sets are

```
s={(x,r): r<g(star)-g(x)},
t={(x,r): x in A, J(x)-J(star)<=r}.
```

Continuity makes s open. Ordinary total optimality makes the two sets disjoint.
Imported point-free open-set Hahn-Banach supplies a separating linear functional
l and level u. The actual star is in t at vertical coordinate zero, and each
negative vertical coordinate at star lies in s. These facts earn a positive
vertical coefficient c and prove u=l(star,0) by a positive-epsilon limit. The
normalized horizontal functional d is then constructed, with

```
J(star)-d(x-star)<=J(x) for every x in A,
g(star)+d(x-star)<=g(x) for every ambient x.
```

The extended-objective version imports the earlier proved effective-domain
convexity and real-objective return. It applies the real split on that exact
domain and restores the support to the entire original A, including infinite
objective points. It returns -d in the restricted objective subgradient and d
in the ambient finite summand subgradient. No unrestricted toReal conversion
or ambient objective/normal-cone identification is used.

For finite ambient convex J, apply the constructed split to indicator_A and
the finite continuous total J+g. This earns an admissibility normal -d and an
ambient total support d. Removing the actual smooth g earns objective support
q=d-k. Therefore

```
q in partial J(star), n in N_A(star), q+k+n=0.
```

Here the objective domain qualification is automatic because J is finite on the
whole space. Objective nonsmoothness is permitted. Convexity of A, ordinary
attainment, global convexity of J/g, and actual differentiability of g remain
explicit. No attainment or solver convergence is derived.

## Actual Schur constraint smoothness and stationarity

`SchurStationarity` uses exactly the previously constructed singular-support
Schur residual Xi(x)=Support.residual L (D(x)), with fixed native L and affine
D. The primal ambient space is now normed and finite-dimensional. Every finite
affine probe is proved differentiable by its continuous affine realization.
The exact blind-Gram residual identity expands the trace pairing as a finite
quadratic polynomial in actual probe coordinates. Lean proves differentiability
of the actual scalar Schur energy and trace budget gap at every point. PSD trace
energy convexity is earned by the prior actual Schur convexity theorem. No
constraint derivative premise is supplied to the final Schur theorem.

The prior nonsmooth Slater construction earns a PSD matrix price P from ordinary
finite primal attainment and an original positive-definite Slater slack. For a
finite ambient convex J, the constructed sum split returns actual ambient q and
admissibility normal n satisfying

```
q + fderiv(trace(P*(Xi(x)-B))) at star + n = 0,
trace(P*(Xi(star)-B))=0,
J(star)<=J(x)+trace(P*(Xi(x)-B)) for every x in A.
```

The actual constraint trace function is proved differentiable, so its fderiv is
its genuine derivative. This is the derivative of the exact scalar price pairing;
an explicit matrix-valued Jacobian/adjoint formula is not separately mechanized
in this packet. Prior actual primal/dual equality remains available. A separate
theorem keeps P nonzero when the original complete-lattice value decreases in a
PSD budget direction. Activity alone does not earn nonzero price.

For genuinely extended J, the same original Slater matrix price and constructed
sum split yield

```
-fderiv(trace(P*(Xi(x)-B))) at star in partial(restriction A J)(star).
```

This is the exact combined objective/admissibility stationarity. Splitting it
into an ambient extended objective subgradient and a separate normal remains
the relative-interior-qualified obligation. Whole matrix activity is not inferred
from complementarity. Singular native blocks are retained throughout.

## Inhabitation and missing-qualification control

`StationarityExamples` applies the generic finite-objective split to the actual
nonsmooth objective max(-x,-2x) and the independently constructed nonzero linear
budget price at zero. It earns an ambient objective subgradient q with q+price=0;
the actual normal of the full ambient space is proved zero. No differentiable
objective or stationarity is supplied.

A complete Schur example uses actual one-by-one residual x^2, ambient objective
(x-2)^2, original budget1 and optimizer1. The ordinary optimizer, positive-definite
slack at x0=0 and actual PSD-direction value decrease via x=2 at budget4 are proved
before applying the generic Schur stationarity theorem. The final zero-premise
statement returns nonzero PSD price, ambient objective subgradient, admissibility
normal, the actual trace-constraint derivative and complementarity.

The domain-qualification control is J(x)=-sqrt(x) for x>=0 and plus infinity
otherwise, with A={0} and star0. Lean proves no minus-infinity objective and
convex actual real epigraph. The actual restricted objective has zero supporting
functional at its constrained minimizer. Yet it has no finite ambient objective
subgradient at zero: testing any candidate slope at x=t^2, with
 t=1/(|p(1)|+1)>0, contradicts the proposed support because J(t^2)=-t.
Thus even an arbitrary admissibility normal cannot produce a full ambient split.
The standard relative-interior qualification fails here: ri(dom J)=(0,infinity)
and ri(A)={0}. The latter relative-interior computation is explanatory; the
mechanized false-target claim is no ambient support and no full split, together
with convex epigraph, no-bottom objective and actual restricted support.

This refutes dropping the domain qualification. It does not refute the original
qualified theorem. The distinction between restricted and ambient support is
substantive, not bookkeeping.

## Verification and remaining target

Full default lake build: 8127 jobs, success, warnings treated as errors. All26
new exported statements and transitive axiom closures freshly checked, using
only propext, Classical.choice and Quot.sound. No local axioms, holes, admits or
native_decide. Cumulative1056 preserves the exact immutable earlier1030 raw prefix
and adds fresh26. Earlier proof/evidence/toolchain identity is checked by the
verifier; the full cumulative command was not rerun. Checkout and canonical Git
hashes are recorded separately, preserving historical CRLF data. Original
Python/RNG/solver suites were not rerun.

Receipts: `results/stationarity_split_2026-10-03/`. Verifier:
`scripts/de_stationarity_split_verify.py`. New statement/axiom manifests:
`lean/manifests/check_stationarity_split_{statements,axioms}.lean`.

Next construction: earn the general relative-interior-qualified separation
between ambient extended J and the admissibility indicator, including lower-
dimensional intersecting domains. The pinned library has intrinsic-interior
infrastructure but no ready-made sum rule or relative-interior continuity theorem;
its latter continuity declaration is proof_wanted. A supplied split or assumed
relative-interior value support would leave the requested obligation unresolved.
The broader paper, physical identification and previously parked false/physical
boundaries remain incomplete; this packet makes no whole-goal completion claim.
