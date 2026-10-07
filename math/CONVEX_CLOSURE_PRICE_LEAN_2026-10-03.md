# Constructed scalar convex closure price and actual Schur return, 2026-10-03

Baseline: `85ef263`. The paper, original runtime, earlier proof modules and
evidence are unchanged. Review is adversarial self-review, not independent
review. This advances the section 4.1 scalar closure-price theorem beyond the
previous finite KKT/pairing witnesses. It makes no physical Lambda identification.

## Exact conditional scalar theorem

Let A be a convex admissible domain in a real module, and J and energy be
real-valued convex functions on A. Define the actual value

```
V(B) = inf {J(x) : x in A, energy(x)<=B}.
```

`ConvexClosurePrice.budgetValue` is this actual real infimum, not an arbitrary
supplied value record. Suppose an ordinary primal optimizer star exists at B.
On some open budget interval lo<B<hi suppose each feasible objective-cost set
is nonempty and bounded below. These are the explicit guards that make a real
infimum a finite value and prevent Lean's empty/unbounded infimum defaults
from being used as an optimization answer. Finally suppose that this actual
V has derivative d<0 at B, as in the original sensitivity hypothesis.

Then the new theorem **constructs** price=-d>0 and proves

```
energy(star)=B,
price*(energy(star)-B)=0,
J(star)<=J(x)+price*(energy(x)-B)  for every x in A.
```

Consequently star globally minimizes the Lagrangian on A, its Lagrangian
value is J(star), and the actual attained finite dual infimum equals V(B).
Any dual certificate for this optimizer agrees with -V'(B) when that actual
derivative exists. Nonnegative competing prices obey weak duality when their
Lagrangian image is bounded below; arbitrary unbounded infimum defaults are
not compared as finite dual values. The constructed dual's nonempty and
bounded-below guards are themselves derived from its attained global minimum.

No dual multiplier, value support law, value convexity, global Lagrangian
minimum or constraint activity is supplied in the construction theorem.
Activity follows from strict actual sensitivity, so the original separate
active-budget hypothesis is redundant in this finite-value setting. Neither
closedness, finite dimension nor Slater is needed in this direct argument once
ordinary optimum, local finite value and actual differentiability are supplied.
This does not assert that Slater alone supplies a finite differentiable value.

The generic theorem uses a real-valued objective on its admissible domain.
It does not mechanize all extended-real objective-domain reductions, separate
subdifferential sum rules or matrix/Loewner duality from the more general LT1
memo. Its certificate is global scalar Lagrangian minimization, which is the
correct combined-objective stationarity content; it does not silently split
subdifferentials without their domain qualifications. Those generalizations
remain separate obligations. The conditional scalar theorem and exact Schur
instances below are substantive improvements to original-target coverage.

## Derivation from primal mixing, not supplied duality

Fix any x in A and mix it with star using
`y(t)=(1-t)*star+t*x`, for 0<t<1. Convexity and feasibility give

```
energy(y(t)) <= B+t*(energy(x)-B),
J(y(t)) <= J(star)+t*(J(x)-J(star)).
```

The path budget tends to B as t tends to zero, so eventually it belongs to
the explicit finite-value interval. The actual infimum is no larger than
J(y(t)); primal optimality proves V(B)=J(star). Therefore

```
[V(B+t*(energy(x)-B))-V(B)]/t <= J(x)-J(star).
```

The derived path derivative is d*(energy(x)-B). Taking the right-hand slope
limit yields

```
J(star)+d*(energy(x)-B)<=J(x).
```

Substituting x=star, using energy(star)<=B and d<0, forces energy(star)=B.
Rearranging the same global bound constructs price=-d and its global
Lagrangian certificate. All admissible candidates are covered, not only a
local neighborhood of star. The time-like mixing parameter approaches zero
inside its positive domain; no nonexistent derivative of the optimizer is used.

The dual certificate then returns primal optimality and a true finite dual
infimum. Its supporting bound for any nonempty neighboring feasible-cost set
is `V(B)-price*(T-B)<=V(T)`. Hence `V(T)+price*T` has a local minimum at B;
its derivative vanishes, proving that any certificate price equals -d.
This downstream use of a certificate is separate from the construction of one.

## Actual Schur energy and earned convexity

`SchurClosurePrice` uses the already constructed singular-support residual

```
Xi(L,D) = D*D^T-D*L^T*(L*L^T)^dagger*L*D^T,
energy(D)=trace(W*Xi(L,D)).
```

The generalized Gram inverse is the previous `Adequacy.Support` spectral
construction, with its proved Penrose/range/projector properties. No new
pseudoinverse or PSD residual is assumed as a field. The proved Gram identity
is `Xi(L,D)=R*R^T`, where `R=D*(1-projector(L))` is the actual blind component.
For fixed native L and PSD weight W, this gives nonnegative energy.

For a+b=1 the exact weighted Gram identity is

```
G(aX+bY)=aG(X)+bG(Y)-a*b*G(X-Y),
G(R)=trace(W*R*R^T).
```

Nonnegative a,b and PSD W make the last term nonnegative. This independently
proves convexity of G and of the actual Schur energy in D. Precomposition with
an affine dissolving-probe map earns energy convexity on every convex closure
domain. Thus `positive_schur_price` applies the generic theorem with no supplied
energy-convexity field, including singular native Gram blocks. Its ordinary
primal optimum, actual finite value and actual negative derivative hypotheses
remain visible. Native probes and W are fixed; an arbitrary changing native
projection is not assumed convex.

For positive-definite native Gram blocks, the previously proved support inverse
identity returns this exact energy to the unchanged original
`ClosurePrice.schurEnergy`, and its scalar pairing to the unchanged original
`ClosurePrice.closureLagrangian`. The singular-support extension does not alter
the nonsingular convention. No allocation-sum budget is equated to Schur energy.

## Complete Schur instance and false-target control

`SchurClosurePriceExamples` supplies a one-dimensional actual Schur program:
L=0, W=1, D(x)=x, so energy(x)=x^2; J(x)=(x-2)^2. For 0<B<4, the optimizer
is sqrt(B), and the actual infimum is `(sqrt(B)-2)^2`. Every feasible-cost set
at B>0 is explicitly nonempty and bounded below. The value derivative at B=1
is constructed as -1 from that actual local formula. The theorem constructs
price1, the active optimizer x=1 and equality of primal/dual values. Slater is
explicitly witnessed by x=0, and the native Gram block is genuinely singular.
No optimum, finite value, derivative or certificate premise is supplied in the
final example theorem. Thus the conditional Schur class is inhabited in its
original matrix/probe domain.

An exact false-target control varies the native family affinely: L(x)=x while
D=1 and W=1 stay fixed. Energy at x=1 and x=-1 is zero, but at their midpoint
x=0 it is one. Lean proves this energy is not convex. Consequently affine
entries alone do not make jointly varying native/dissolving Schur data convex.
This preserves the explicit fixed-native restriction and the generic theorem's
energy-convexity hypothesis; it introduces no new paper downgrade, since the
paper's displayed energy uses a fixed native L and explicitly assumes convexity.

## Evidence and remaining scope

Full default build: 8107 jobs, with warnings treated as errors. All 34 new
statements and transitive axiom closures are freshly checked. The standard-only
cumulative audit has 929 ordered declarations: exact immutable earlier 895
prefix plus fresh34 suffix, with old proof/toolchain identity checked. The full
cumulative command was not rerun. Raw suffix, combined audit, statement and
adversarial self-review receipts are retained. Allowed axioms remain propext,
Classical.choice and Quot.sound; there are no proof holes or native_decide.

Run `python3 scripts/de_convex_closure_price_verify.py` from the repo root.
It checks statement domains, actual-infimum/strict-sensitivity inputs, earned
activity, concrete Schur returns and controls, prior artifact protections,
actual pinned Lean/mathlib proof bytes, and cumulative checkout/Git fingerprints.
From `lean/`, the fresh commands are `lake build`,
`lake env lean -DwarningAsError=true manifests/check_convex_closure_price_statements.lean`,
and `lake env lean -DwarningAsError=true manifests/check_convex_closure_price_axioms.lean`.
Refresh corresponding raw receipts when recomputing the packet. The optional
full audit is `lake env lean manifests/check_axioms.lean`. Evidence is in
`results/convex_closure_price_2026-10-03/`.

No original numerical carrier, empirical audit, RNG reification or Python test
suite was rerun. Physical Lambda identification, full extended-real split
stationarity and matrix/Loewner pricing remain outside this packet. The broader
original paper remains incomplete at its documented boundaries. This packet
constructs the scalar convex price and its actual Schur return, and strengthens
the activity claim without a new downgrade.
