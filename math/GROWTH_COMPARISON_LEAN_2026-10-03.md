# Exact growth-IVP comparison and record-history return, 2026-10-03

Baseline: `4fb7986`. This is constructive mathematics and adversarial self-review
with Lean kernel checking. The paper, native algorithm and frozen outputs are
unchanged. No independent reviewer or fresh numerical integration is claimed.

## Target and return to the original equation

The original `scripts/de_window_carrier.py:solve_growth` integrates

```
H²(a) = a^-3 + λ,
D_a = p,
p_a = [3/(2 a^5 H²)] D - [3/a - 3/(2 a^4 H²)] p,
D(a0)=1, p(a0)=1/a0.
```

Put `a=a0 exp(x)`, `v=a p`, and `L=log(A/a0)`. The exact transformed IVP is

```
D_x = v,
v_x = fλ(x) D + (fλ(x)-2) v,
fλ(x) = 3/[2(1+λ (a0 exp(x))³)],
D(0)=v(0)=1.
```

`GrowthComparison.scale_acceleration_bridge` proves the rational identity with
the original `WindowRecords.hubbleSquared`; `log_growth_derivative` and
`log_velocity_derivative` prove the actual chain-rule bridge. This is the original
growth carrier, not an alternative monotone gate. The declared continuous
threshold-equality and turnaround-erasure conventions remain as before; no
contracting branch or elapsed-time crunch is constructed.

`Live a0 λ L` means positivity of `1+λ a(x)³` on the whole closed interval.
`live_of_horizon` derives it from `a0>0`, `a0 exp(L)=A` and `λ>-1/A³`.
`scale_log_horizon` supplies the endpoint identity for positive `a0,A`.
Coefficient continuity and a finite upper bound are **constructed** on this
compact interval, including negative live lambdas arbitrarily close to the
cutoff. No uniform bound across the cutoff is claimed.

## The substantive cone and comparison proof

For any forced system

```
D'=v, v'=fD+(f-2)v+q,  0<=f<=K, q>=0,
```

define `E=(min(D,0))²+(min(v,0))²`. The squared negative part is differentiable
even at zero, with derivative `2 min(y,0)`. The zero case is proved by gluing
the square on the nonpositive half-line and the zero function on the nonnegative
half-line. Four sign cases and the square `(D-v)²>=0` give

```
E' <= 4(K+1) E.
```

Mathlib's scalar Grönwall inequality gives `E<=0` from `E(0)=0`. Since `E>=0`,
both coordinates remain nonnegative. This argument does not assume the signs
of the evolving solution. With strictly positive initial coordinates,
`D'=v>=0` and `(exp(2x)v)'=exp(2x)[f(D+v)+q]>=0` imply strict positivity of
both coordinates throughout the closed interval.

If initial coordinates are zero and `q>0`, the weighted velocity has strictly
positive derivative. It is strictly positive at every `x>0`; integrating
`D'=v` gives strict positivity of D as well. These are proved for every such
system, not only the desired growth family.

For `λ1<λ2`, the coefficient satisfies `f1>f2` on the live interval. The
difference of two original solutions satisfies the forced system with

```
q=(f1-f2)(D2+v2)>0, D_difference(0)=v_difference(0)=0.
```

Positivity of the second solution is already derived. Applying strict forcing
therefore proves `Dλ1(x)>Dλ2(x)` and `vλ1(x)>vλ2(x)` for every `x>0`.
Applying the nonnegative-cone lemma to both signed differences at equal lambda
also proves uniqueness of IVP solutions. `matter_solution` constructs the
lambda-zero control `D=v=exp(x)` for the original initial data.

## Original record-history return

For every fixed nonnegative patch amplitude, collapse anywhere on `[0,L]`
is equivalent to `amplitude*D(L)>=threshold`, because growth in time is now
derived from the ODE. For positive attained maxima `m0,m1` among the fixed
false/true-tag populations, `record_history_iff_threshold` returns this to

```
both tags have collapsed by the horizon
    iff D(L) >= max(threshold/m0, threshold/m1).
```

The maxima and fixed tags remain explicit finite-population inputs, as in
`WindowRecords`. `record_gate_parameter_downward` proves downward closure in
lambda within the live branch. It supplies neither a coupling between independently
reseeded populations nor invariance under changes in the tag distribution.

## Exact mechanization boundary and self-review

The module has 28 theorems. `GrowthSolution` contains continuity, the two exact
differential equations and the original initial values. It contains **no**
positivity, comparison, uniqueness, parameter sensitivity or threshold result.
The substantive theorems derive these conclusions for any functions satisfying
the IVP. This is conditional on actual IVP solutions, not a local all-lambda
existence declaration. The earlier mathematical existence proof remains valid;
this packet does not mislabel a supplied solution as its construction.

The derivative hypotheses are `HasDerivAt` on the closed interval, including
endpoints. A live coefficient is smooth on an open neighborhood of the compact
interval, so the classical IVP has such a local extension. Supplying that
extension for every live lambda remains part of the next Lean construction.
The theorem is not about the integrator's discrete samples or rounded arithmetic.

Strict parameter comparison requires `a0>0` and positive elapsed log scale.
At `x=0`, all growth/velocity initial values agree; the theorem does not claim
a strict inequality there. The zero-length interval is allowed in positivity,
uniqueness and history equivalence. The negative live cutoff is strict; no
statement crosses the singular turnaround endpoint. Off-diagonal cooperativity
is proved from the coefficient, not inferred from a generic ODE name. The
cone estimate accepts arbitrary signed evolving coordinates, which is essential
for its application to solution differences.

Full local mechanization of global solution existence, continuous/differentiable
dependence on lambda, the positive-infinity limit, ranked-seed aggregation and
the unique upper endpoint is still pending. This packet improves support for
the original two-sided toy window without proving its complete continuum
certificate in Lean or any physical cosmological statement.

## Next construction: an explicit quadrature for the exact IVP

A direct construction can avoid a general-purpose global ODE existence library.
Let `c=λ a0³`, `h(x)=sqrt(exp(-3x)+c)`, and on the live interval define

```
I(x) = integral from 0 to x of exp(-2s)/h(s)^3 ds,
C = c + 5/2,
D(x) = h(x) [1/h(0) + C I(x)],
v(x) = -fλ(x) D(x) + C exp(-2x)/h(x)^2.
```

This is a mathematical construction, not yet a Lean declaration. Its denominator
is positive throughout the interval and on a neighborhood of it. Ordinary
finite-interval integration therefore defines smooth functions. Direct
differentiation gives `h'=-f h`, `I'=exp(-2x)/h³` and
`f'=2f²-3f`. Thus `D'=v`; differentiating the stated v and substituting these
identities gives `v'=fD+(f-2)v`. Also `h(0)²=1+c`, `I(0)=0`, and
`C=h(0)²(1+f(0))`, so `D(0)=v(0)=1`. This supplies every live lambda, including
zero and negative values, and the comparison theorem then applies directly.
The formula is regular at lambda zero; no growing-mode initial condition is
silently substituted for the actual finite-a0 initial condition.

The next executable step is to formalize positivity of h, these derivative
identities and the integral fundamental theorem, then construct `GrowthSolution`
from the displayed D,v. Parameter continuity can subsequently be obtained from
continuous finite-interval integration on compact live parameter neighborhoods.

## Verification

The default Lean build passes. The expanded transitive audit checks all 408
declarations, including all 28 new theorems, allowing only `propext`,
`Classical.choice` and `Quot.sound`. The fresh raw receipt is
`lean/manifests/axiom_audit_growth_comparison_2026-10-03.txt`; elaborated endpoint
statements and source hashes are in `results/growth_comparison_2026-10-03/`.
No runtime algorithm was changed or numerical error certificate added.
Earlier dated receipts remain historical evidence.
