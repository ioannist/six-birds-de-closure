# Constructed growth IVP and parameter continuity, 2026-10-03

Baseline: `887f12a`. This packet discharges the all-lambda solution premise in
the preceding comparison construction and proves parameter continuity. It also
returns the constructed solution to the implemented scale-factor equation.
The paper and frozen/runtime experiment code remain unchanged. Review is an
adversarial self-review with kernel checking, not an independent review.

## Original target and exact construction

For `a0>0`, `A>=a0`, and every `lambda>-1/A³`, construct functions D,p on
the entire original expanding interval `[a0,A]` satisfying

```
D(a0)=1, p(a0)=1/a0,
D_a=p,
p_a = [3/(2 a^5 H²)] D - [3/a - 3/(2 a^4 H²)] p,
H²=a^-3+lambda.
```

These are the equations and finite-start initial values in
`scripts/de_window_carrier.py:solve_growth`. The model is interpreted in exact
real arithmetic; the finite floating solver and its stopping rules are separate
computational artifacts.

In log scale `x=log(a/a0)`, set `c=lambda*a0³` and

```
h(x) = sqrt(exp(-3x)+c),
f(x) = 3 exp(-3x)/[2(exp(-3x)+c)],
I(x) = integral from 0 to x of exp(-2s)/h(s)^3 ds,
C = c+5/2,
D(x) = h(x) [1/h(0)+C I(x)],
v(x) = -f(x)D(x)+C exp(-2x)/h(x)^2.
```

`GrowthExistence` defines these functions using real square roots and the Bochner
interval integral. It proves the denominator is positive on the live interval,
the integrand is measurable and continuously integrable there, and the integral
has the indicated derivative at every point, **including both endpoints**.
The primitive is not an assumed antiderivative or an unpopulated proof record.

The derivative identities `h'=-fh`, `f'=2f²-3f` give `D'=v` and
`v'=fD+(f-2)v`. The algebraic identity
`C=h(0)²(1+f(0))` gives the actual initial values `D(0)=v(0)=1`.
The exact exponential identity

```
exp(-3x)+lambda*a0³
  = exp(-3x) [1+lambda*(a0 exp(x))³]
```

identifies f with the original log-scale coefficient. The horizon law from the
previous module supplies positivity for every live lambda; no sign or smallness
restriction on lambda is added. In particular negative live values and lambda
zero use the same construction.

`constructed_growthSolution` populates every field of the original IVP record
from these functions. `exists_growthSolution_of_horizon` derives all its inputs
from `a0>0`, `L>=0`, `a0 exp(L)=A` and `lambda>-1/A³`. There is no supplied
solution, positivity, monotonicity or continuity-in-parameter premise.

## Return to scale factor

`GrowthScaleReturn` defines

```
D_native(a) = D(log(a/a0)),
p_native(a) = v(log(a/a0))/a.
```

It proves `log(a/a0)` is in the full log interval when `a` is in `[a0,A]`,
and its derivative is `1/a`. The exact acceleration bridge and both chain-rule
calculations verify `D_native'=p_native` and the original p equation.
`exists_original_scale_solution` constructs the original-domain witness with
the native initial values. Neither existence nor its return is inferred from
the forward scale-to-log bridge alone.

The previous cone/comparison theorems now apply to constructed solutions. Their
conclusions are no longer merely conditional on an externally supplied IVP:
`native_positive` derives strict growth/derivative positivity throughout the
native interval. The log IVP uniqueness theorem identifies the constructed
solution with any other exact log IVP solution; the lambda-zero endpoint agrees
with `exp(L)=A/a0` by the separately constructed matter solution.

## Parameter continuity without changing the model

For a fixed live c and `L>=0`, put `epsilon=(exp(-3L)+c)/2>0`.
Replace the squared-root denominator **in a proof device only** by
`max(exp(-3x)+d,epsilon)`. This makes its integrand jointly continuous for all
real d,x. The established parametric interval-integral theorem gives continuity
of the resulting integral in d.

Whenever `d>c-epsilon` and `x` is in `[0,L]`,
`exp(-3x)+d>=epsilon`. Thus the regularized integrand agrees exactly with the
original one throughout the integration interval on an open neighborhood of c.
The integral equality is proved by congruence; continuity transfers to the
original primitive. The constructed solution, differential equations and
experiment code are never replaced by a clipped version.

Continuous multiplication, division by positive h and this integral theorem
give continuity of both D(L) and v(L) in c. Composing `c=lambda*a0³` supplies
`finalGrowth_continuousAt` at every live lambda. Applying the strict comparison
theorem to the explicitly constructed solutions proves
`finalGrowth_strictAntiOn`; the native-domain endpoint theorems conclude

```
lambda ↦ D_native(A) is continuous at every lambda>-1/A³;
it is strictly decreasing on that interval when A>a0.
```

These statements have no supplied family of solutions and no monotone-growth
premise. The zero-length horizon remains admissible for construction and
continuity, but strict parameter ordering requires `A>a0`.

## Adversarial self-review and exact remaining gap

The return checks the implemented acceleration coefficients, both derivatives
and both initial values. It does not substitute the cosmological growing-mode
solution initialized at a=0 for the actual finite-a0 IVP. Negative live lambdas
are included. The strict turnaround cutoff is never crossed; no uniform
denominator bound is asserted at the cutoff. The primitive's derivative is
proved with actual integrability and measurability, not assigned as a field.

Endpoint `HasDerivAt` hypotheses in the preceding module are now populated by
the explicit globally defined functions. Although division, square root and
integral have total Lean values outside the live interval, the solution and
parameter theorems are scoped to the region where denominators are positive.
No result uses those outside values to extend the physical expanding branch.
The continuity regularization is locally identical on the entire integration
interval and does not weaken the target.

All-lambda existence, positivity, strict comparison and continuity are now
locally mechanized. Differentiability in lambda and the strict sensitivity
derivative remain written mathematics. The positive-infinity limit
`3/2-exp(-2L)/2`, finite ranked-seed aggregation, and the unique positive upper
endpoint still need local Lean assembly. Consequently this packet does not
claim a complete local continuum-window certificate or interval-certified
numerical edge location. The original physical identification and contradicted
tag/prior claims remain outside its scope.

The next substantive construction is the infinity limit. The matrix/Grönwall
estimate in `ORIGINAL_CLAIM_COVERAGE_2026-10-02.md` remains valid, but the new
comparison theorem gives a shorter route with a better bound. For lambda>=0,
comparison with the matter solution gives `D(x),v(x)<=exp(x)<=exp(L)`.
Also `f(x)<=3/[2(1+lambda*a0³)]` for x>=0. Against the limiting solution
`Dinf=3/2-exp(-2x)/2`, `vinf=exp(-2x)`, the differences obey

```
deltaD'=deltaV,
deltaV'=-2deltaV+q,
0<=q=f(D+v)<=epsilon=3 exp(L)/(1+lambda*a0³),
deltaD(0)=deltaV(0)=0.
```

The cone lemma gives nonnegative differences. Comparing `exp(2x)deltaV` with
`epsilon*(exp(2x)-1)/2` gives `deltaV<=epsilon/2`; integrating the growth
inequality gives the mathematical bound

```
0 <= G(lambda)-[3/2-exp(-2L)/2]
  <= (3/2) exp(L) L/(1+lambda*a0³).
```

For a0>0 this tends to zero as lambda tends to positive infinity. This sharper
estimate is a written derivation for the next Lean packet, not already a local
declaration. It uses constructed solutions and exact ODE comparisons, with no
assumed asymptotic growth law. Continuous strict decrease can then land at the
unique threshold endpoint through the intermediate value theorem.

## Verification

Both new default-build modules compile with warnings as errors. They contain
36 new theorems: 27 in `GrowthExistence` and 9 in `GrowthScaleReturn`.
The full default build and expanded 444-declaration transitive audit are recorded
in `results/growth_existence_2026-10-03/` and
`lean/manifests/axiom_audit_growth_existence_2026-10-03.txt`. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Elaborated endpoint statements
are separately recorded. No Python runtime change, new native run or numerical
error certificate is claimed. Prior receipts remain historical evidence.
