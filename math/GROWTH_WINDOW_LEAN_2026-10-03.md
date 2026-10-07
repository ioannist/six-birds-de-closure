# Quantitative growth limit and exact native record window, 2026-10-03

Baseline: `5e3a0d6`. This packet closes the positive-infinity limit and unique
threshold-endpoint obligations left by the explicit growth-IVP construction.
It returns the window to the original scale-factor collapse history. The paper,
frozen source and runtime experiment code remain unchanged. Review is an
adversarial self-review with kernel checking, not an independent review.

## Target and original domain

Keep the implemented finite-start IVP, with `a0>0`, `A>a0`,
`L=log(A/a0)` and live `lambda>-1/A³`. Its constructed log-scale solution has

```
D'=v, v'=f D+(f-2)v, D(0)=v(0)=1,
f=3/[2(1+lambda*(a0 exp(x))³)], G(lambda)=D(L).
```

`GrowthExistence` supplies actual functions for every live lambda and proves
their equations, initial data, parameter continuity and strict parameter
ordering. `GrowthScaleReturn` verifies both native derivatives and initial
values. This packet uses those established proofs; it does not introduce a
new solution family or supply the desired properties as hypotheses.

The exact new target is: if `Ginf<T<G(0)`, there is a unique positive `upper`
with `G(upper)=T`, and the live threshold gate is precisely

```
lambda > -1/A³ and lambda <= upper.
```

The native record version uses nonnegative fixed amplitudes and fixed tag bits,
with positive attained maxima m0,m1, and sets
`T=max(delta/m0,delta/m1)`. These are explicit realization premises, not a claim
that every population or tag distribution satisfies them.

## Quantitative limit derived from the ODE

The limiting finite-start solution is explicitly defined:

```
freeV(x)=exp(-2x), freeD(x)=3/2-exp(-2x)/2.
```

Lean proves its derivatives and both initial values. It is the free system
`freeD'=freeV`, `freeV'=-2freeV`, with the same initial data as the original
IVP. It is not the cosmological growing mode initialized at a=0.

For lambda>=0, comparison with the exact matter solution gives
`D(x),v(x)<=exp(x)<=exp(L)` on `[0,L]`. The zero-lambda case is handled by
IVP uniqueness and the separately proved matter solution; the zero-time case
uses the actual initial data. For positive lambda and time the previously
proved strict comparison supplies the upper bounds.

Since `a0 exp(x)>=a0`, positivity and ordinary denominator ordering give

```
0 < f(x) <= 3/[2(1+lambda*a0³)].
```

Let `d=D-freeD`, `w=v-freeV`, and `q=f(D+v)`. Their exact derivative equations
and initial values are derived by subtraction:

```
d'=w, w'=-2w+q, d(0)=w(0)=0,
0<=q<=epsilon=3 exp(L)/(1+lambda*a0³).
```

`forced_free_bound` is a generic scalar estimate for this system. The earlier
cone theorem, applied with cooperative coefficient zero, derives d,w>=0.
The integrating factor `W=exp(2x)w` has derivative `exp(2x)q`. Comparing W
with `B=epsilon*(exp(2x)-1)/2`, whose derivative is `epsilon*exp(2x)`, gives
`W<=B` from their equal zero initial values. Thus `w<=epsilon/2`. A second
derivative fence compares d with `epsilon*x/2` and proves
`0<=d(x)<=epsilon*x/2`. Continuity and derivative hypotheses for both fences
are verified; no integral of an unproved inequality or supplied positivity
field is used.

Applying the estimate to the constructed IVP at x=L gives

```
0 <= G(lambda)-[3/2-exp(-2L)/2]
  <= [(3/2) exp(L) L]/[1+lambda*a0³].
```

This improves the coarse matrix-exponential estimate in the previous written
argument. Because a0>0, the denominator tends to positive infinity. The
right-hand side tends to zero. The squeeze theorem proves, with a genuine
`Tendsto` declaration,

```
G(lambda) -> 3/2-exp(-2L)/2 as lambda -> +infinity.
```

The total definitions outside the live region play no role: all quantitative
bounds use lambda>=0, and the limit proof uses that region eventually. L=0
is allowed for the bound and limit, giving constant endpoint growth 1; strict
ordering and the positive endpoint construction require L>0.

## Constructed endpoint and exact boundary conventions

The proved limit and `Ginf<T` give a finite b>0 with G(b)<T. The proved
parameter continuity holds on the entire interval `[0,b]`, and
`T<G(0)=exp(L)`. The intermediate value theorem therefore constructs
`upper` in `[0,b]` with `G(upper)=T`. The strict inequality at zero shows
upper>0. Strict parameter decrease proves uniqueness among all positive
roots; this is not a bisection output or an assumed threshold witness.

`live_iff_horizon` proves both directions of

```
Live(a0,lambda,L) iff lambda>-1/A³,
```

using `a0 exp(L)=A`. The reverse direction was previously available; the new
forward direction evaluates the actual positive denominator at L.
Strict decrease then proves

```
Live(a0,lambda,L) and T<=G(lambda)
  iff -1/A³<lambda<=upper.
```

Threshold equality is included. Turnaround equality is excluded. Negative
live values are covered by the same strict-order theorem, rather than by a
separate guessed continuation. The native theorem substitutes
`L=log(A/a0)`, proves L>0 and `exp(L)=A/a0`, and returns this window to
`nativeGrowth(a0,lambda,A)`.

## Return to the full original record history

For nonnegative amplitude, `native_ever_collapse_iff_final` proves

```
(exists a in [a0,A], delta<=amplitude*D_native(a))
  iff delta<=amplitude*D_native(A).
```

The forward direction uses the established time monotonicity, the proved
log-scale interval membership and nonnegative amplitude. The reverse uses A
itself. This handles the full continuous scale-factor interval, including both
endpoints, without replacing history by sampled integrator steps.

For fixed tags and positive attained maxima, the existing two-tag predicate
lemma then proves history is record-bearing iff
`max(delta/m0,delta/m1)<=D_native(A)`. The tag inequality supplies distinct
patch witnesses; merely having two collapses is not substituted for having
both tags. `exists_unique_native_record_window` composes this return with the
constructed endpoint theorem. Its result is the exact record window
`(-A^-3,upper]` for the same realization and threshold.

## Adversarial self-review and remaining coverage

The limit uses the actual finite-start IVP. Denominator positivity is derived,
the matter control solves the exact initial-value problem, and both free
initial values are checked. The forced comparison starts at zero differences,
and its forcing bound comes from proved signs and matter bounds. No uniform
bound at the negative cutoff is claimed. The endpoint construction uses a
proved `Tendsto`, not an assumed asymptotic law; its uniqueness uses the
constructed family's strict decrease. Native history covers the original
scale interval and both tag values, not only a scalar summary with no return.

The theorem requires the two strict threshold inequalities. It does not assert
an upper endpoint for a homogeneous null, absent tag, zero tagged maximum,
or an arbitrary threshold. It does not identify erasure at turnaround with an
integrated physical crunch. The model's live-gate convention is the declared
persistence test; no singular-branch evolution is constructed.

The general threshold window and single-realization native record window are
now locally mechanized. The next concrete construction is the twelve-seed
aggregate: construct finite tagged maxima, derive the k-th threshold/count
identity with ties handled correctly, and reify the original populations and
k=10. The existing exact Python receipt constructs the twelve thresholds and
checks their rank, but that receipt is not a Lean proof of this aggregation.
The numeric rational threshold already has a Lean arithmetic bound, but it
is not silently assigned to the population by this packet.

Parameter differentiability and the corresponding smooth sensitivity remain
written mathematics. Neither the floating edge location nor the order-unity
coincidence ratio receives a rigorous integration error certificate here.
The physical identification and previously contradicted universal tag/prior
claims remain outside this construction. No whole-paper completion is claimed.

## Verification

Both new modules are default-build roots and compile with warnings as errors.
They add 17 theorems: 10 in `GrowthLimit` and 7 in `GrowthWindow`.
The full default build passes (8064 jobs). A fresh transitive audit covers all
461 registered declarations, allowing only `propext`, `Classical.choice` and
`Quot.sound`. Exported limit/window statements are independently elaborated in
a separate statement-check file (this is coverage checking, not independent
mathematical review).

Receipts and source hashes are in `results/growth_window_2026-10-03/`, with the
raw audit in `lean/manifests/axiom_audit_growth_window_2026-10-03.txt`.
Older receipts remain historical evidence. No Python runtime changed, so no
fresh Python solver run or numerical verification is claimed. Paper and frozen
source remain unchanged from the initial checkpoint.
