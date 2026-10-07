# Infinite-time growth and actual perpetual-record windows, 2026-10-03

Baseline: `da0a53b`. The paper and all earlier proof/evidence packets are
unchanged. This packet constructs the time limit of the actual original
finite-start growth IVP, returns it to the original twelve-seed population,
and corrects the endpoint semantics. Review is adversarial self-review.

## Exact target and result

Original section 5 claims sufficiently large positive parameters prevent
records ever forming, and that the eternal-persistence limit has a one-sided
closed window `[0,lambda_plus]`. Formation and persistence both use the same
finite horizon in the original predicate. Allowing formation at any finite
horizon, while demanding retention at every horizon, yields instead

```
[0,u_infinity),   0 < u_20 < u_infinity,
D_infinity(u_infinity) = T_aggregate.
```

This is an endpoint correction, not loss of a positive window or its boundedness.
The upper endpoint is excluded because growth approaches its limit strictly
from below and never reaches that value at a finite epoch. Exactly nine of the
original twelve seeds can eventually form both tag records at that endpoint;
ten are required. Allowing a collapse at infinite time would change the
record rule. The original finite-horizon window remains unchanged.

A second, distinct predicate keeps formation by `a=20` and demands perpetual
retention thereafter. Its window is exactly `[0,u_20]`, including the original
finite-horizon upper endpoint. This legitimately preserves closedness if that
formation deadline is intended, but it is not the original predicate with its
common formation/persistence horizon sent to infinity. Both predicates and
the distinction are now mechanized; the paper is left for its later phase.

For the actual unchanged twelve-by-sixty-four population, every patch stays
below collapse at every finite `a>=1/1000` whenever `lambda>=10^9`. This coarse
sufficient cutoff establishes the all-time starvation claim. It is not a
sharp edge estimate or a claim that the historical outside point 5.31 forms
no records.

## Constructed limit and bounds

Use the existing verified coordinates `x=log(a/a0)` and `c=lambda*a0^3`.
The original initial data are `D(a0)=1`, `D'(a0)=1/a0`. For `c>0`,

```
r_c(x) = sqrt(exp(-3x)+c),
f_c(x) = exp(-2x)/r_c(x)^3,
J_infinity(c) = integral_(0,infinity) f_c(x) dx,
G_infinity(c) = sqrt(c) * [1/r_c(0) + (c+5/2)*J_infinity(c)],
D_infinity(a0,lambda) = G_infinity(lambda*a0^3).
```

`GrowthInfinite` proves the improper integral integrable using the majorant
`exp(-2x)/sqrt(c)^3`, whose integral is `1/(2*sqrt(c)^3)`. It proves convergence
of the finite interval integral, of the square-root factor, and hence of the
actual constructed growth. Native scale convergence follows from
`log(a/a0)->infinity`; no asymptotic solution or growth law is supplied.

The established cooperative IVP comparison gives strict increase in time.
Consequently, for every finite `a>=a0` and `lambda>0`,

```
D(a0,lambda,a) < D_infinity(a0,lambda)
             < 3/2 + 5/[4*lambda*a0^3].
```

The second strict inequality retains the original finite-start homogeneous
term: `sqrt(c)/sqrt(1+c)<1`. Passing the already proved finite-time comparison
with free growth through the time limit gives `3/2<=G_infinity(c)`. These two
bounds squeeze `G_infinity(c)->3/2` as `c->infinity`, and likewise the native
limiting growth as `lambda->infinity` for every `a0>0`.

The total definitions at nonpositive parameters are not treated as valid
positive-branch limiting growth: every such theorem requires positive `c` or
positive `a0,lambda`. The guarded endpoint selector is only used with its
positive-domain and `T>3/2` guard discharged.

## Continuity, strict ordering, and endpoint construction

For continuity at `c>0`, nearby parameters `d>c/2` share the integrable tail
majorant `exp(-2x)/sqrt(c/2)^3`. Pointwise parameter continuity and dominated
convergence prove continuity of `J_infinity` and `G_infinity`.

A limit of strictly ordered finite growth values alone would not prove strict
ordering of limiting growth. Instead the actual IVP velocity comparison gives
`v(c1,x)>v(c2,x)` for `0<c1<c2`, `x>0`. Thus the growth gap is increasing, is
already positive at `x=1`, and remains at least that positive gap in the limit.
This proves strict antitonicity of the limiting growth, with no strict ordering
premise assumed.

For every `a0>0,T>3/2`, `GrowthEternalWindow` constructs a unique positive
limiting-growth root. For the low side, choose `A=a0*(T+1)` and use the already
proved finite-horizon root; its finite growth equals T and its limiting growth
is strictly greater. The parameter-infinity limit supplies a high side below
T. Dominated-convergence continuity and the IVT give a root; strict ordering
gives uniqueness. This covers every such threshold, not just the sampled one.

Convergence plus strict finite-time growth proves exactly

```
exists finite a>=a0 with T<=D(a0,lambda,a)
  iff T<D_infinity(a0,lambda)       (lambda>0).
```

At zero parameter, the original exact matter solution `D=a/a0` supplies every
finite threshold. Algebraic perpetual horizon admissibility is
`forall A>=a0, -1/A^3<lambda`, proved equivalent to `lambda>=0` by its actual
cutoff limit. This is the declared expanding-horizon/erasure convention, not an
integration of a contracting branch or a physical finite proper-time crunch.

## Return to the original records and a false-endpoint control

`WindowEternalRecords` imports the unchanged original amplitudes, tags,
attained positive tagged maxima and exact ten-pass rank certificate. It applies
the existing actual native-history/aggregate return at arbitrary finite A;
it does not assume that the previously fixed-A=20 equivalence holds at a
variable horizon. The aggregate threshold remains

```
T_aggregate = 971912828383572000768 / 1012057850670495125.
```

An individual seed can eventually form both tag records exactly when its seed
threshold is strictly below limiting growth. At the new root, the unchanged
strict-below rank certificate gives nine such seeds. This is a mathematical
false-target control for closing the upper endpoint, rather than a renamed
predicate or an asserted limiting count.

For global starvation, the analytic bound gives `D<3` when `lambda*a0^3>=1`.
A small kernel computation verifies `3*max(m_false,m_true)<delta` for each
original seed. The earlier kernel-checked attained maxima then bound every
original patch. Thus no patch reaches delta at any finite epoch for
`lambda>=10^9`. No new population, RNG, numerical ODE solve, or assumed global
growth bound is used.

## Verification and remaining scope

The fresh default build passes 8093 jobs with warnings treated as errors.
The current ordered transitive audit covers 798 declarations, including all
47 new theorems, with only `propext`, `Classical.choice` and `Quot.sound`.
All 47 exported statements are separately checked. Exact manifests, build,
raw audit, source/toolchain fingerprints and gate verification are retained in
`results/eternal_window_2026-10-03/verification.json` and the named receipts.
No Python test suite, RNG reification or original solver rerun is claimed.
The computational provenance of the unchanged realized inputs retains its
previous scope.

The physical Lambda identification, unchanged Step26/54 background-dependence
problem, false existential coupling boundary, contradicted measure claims,
and unrestricted tag irrelevance/run-only wording remain unresolved or parked
as previously recorded. This packet does not establish completion of the
original paper. Finer infinite-endpoint brackets and analogous eternal returns
for the other already reified patch-count populations are possible subsequent
estimates. The current original finite-horizon theorem, signed first times,
edge ratios, negative outside witness, and robustness proofs remain unchanged.


Recompute the packet verification after the build and raw audits with
`python3 scripts/de_eternal_window_verify.py` from the repository root. The
verifier checks exact ordered axiom closures, every exported new statement,
original input margins/ranks with rational arithmetic, unchanged prior proof
and evidence artifacts, pinned mathlib sources and cumulative byte fingerprints.
It uses no numerical solver or RNG; its result is evidence for the stated
packet, not a completion certificate for the paper.
