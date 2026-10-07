# Original first records throughout the signed window, 2026-10-03

The exact original twelve-seed toy now has a constructed first-collapse time
and matter ratio throughout its entire admitted signed window,
(-1/8000,lambda_plus]. The new live-domain construction agrees with the earlier
positive-domain construction wherever that readout was certified. For every
original seed and admitted negative lambda,

```
0 < a_first,j(lambda) < 897/1000,
0 < R_j(lambda) < 1/8000.
```

For every admitted real lambda, including zero and the positive endpoint,

```
0 <= R_j(lambda) < 425/8 = 53.125.
```

At the positive endpoint, the earlier 3/8<R_j<425/8 bound is retained. At zero,
a_first,j(0)=T_first,j/1000 and R_j(0)=0. Simultaneously arbitrarily small
positive ratios while the aggregate gate passes are also returned to the
signed readout. The paper, original runtime, reified population and frozen
external source are unchanged.

## Extending the construction, not using a fallback as a record time

The earlier `GrowthFirstRecord.firstTime` was deliberately scoped to nonnegative
lambda and returned its default a0 outside that domain. Applying that default
to an admitted negative lambda would not represent a first-collapse readout.
The earlier positive proofs are unchanged; the new `GrowthFirstRecordLive`
constructs the root on the full expanding interval instead.

For a0>0, A>=a0 and lambda>-(1/A^3), the same exact native IVP is live throughout
[a0,A]. The already constructed solution supplies D(a0)=1, continuity, strict
positivity and strict increase in a. If 1<T<=D(lambda,A), IVT and injectivity
construct the unique a in [a0,A] with D(lambda,a)=T. This is the new first-time
function's certified domain; its own default is excluded by its specification
premises. No first time, monotonicity or reachable-root witness is supplied as
a theorem hypothesis beyond the general API's explicit threshold condition.

`firstTime_eq_nonnegative` proves equality with the older first-time function
by uniqueness of the actual root. The equality is derived, not declared as an
interface assumption or achieved by silently changing the old definition.

For each original seed, the unchanged all-patch maximum is attained and
positive, and its exact first threshold T_first,j lies in (500,897). The
original aggregate gate is precisely

```
lambda > -1/8000 and D_native(lambda,20)>=T*,  960<T*<961.
```

Consequently every original seed's first root is reachable whenever the gate
passes, even though the both-tag gate only requires ten seed passes. All root
premises are discharged from this original gate and the already checked data.
The gate is also proved equivalent to membership in (-1/8000,lambda_plus].

`WindowSignedRecord.time_iff_any_collapse` proves at every a in [1/1000,20]
that an original patch has reached delta iff the new first time is at most a.
`time_is_first_collapse` exports attainment and absence of earlier collapse.
The original first readout concerns any patch, not the epoch at which both
tag values have appeared. The matter ratio is exactly abs(lambda)*a_first^3,
equivalently abs(lambda)/(a_first^3)^-1, with first time strictly positive on
the entire signed admitted domain.

## Nonpositive comparison and the negative ratio bound

The finite-start matter solution is exactly D_0(a)=a/a0. This identity is
returned from the actual zero-parameter IVP, including its original initial
velocity, rather than a growing-mode approximation.

For a0<a<=A and a live nonpositive lambda, the earlier strict parameter
antitonicity implies D_0(a)<=D_lambda(a). At a=a0 both equal 1. The cutoff for
the shorter horizon a is derived from a<=A and positive a; it is not assumed
that negative lambda is automatically live. Therefore at the constructed root,

```
a_first/a0 <= D_lambda(a_first)=T,
a_first <= a0*T.
```

For the original population a0=1/1000 and T_first,j<897, this gives first
collapse before 897/1000. Its time is positive, hence a_first^3<=1. The signed
window's strict negative cutoff gives abs(lambda)<1/8000 whenever lambda<=0.
Multiplication returns R_j<=abs(lambda)<1/8000. For lambda<0, both factors are
strictly positive, so the ratio is also positive. At lambda=0 the unique
matter root is exactly a0*T and the ratio is zero.

For nonnegative admitted lambda, uniqueness identifies the new time and ratio
with the earlier certified functions. The positive-window upper bound 425/8
then returns unchanged. Combining the branches proves the uniform full signed
window bound with no new quadrature tables or floating calculations.

## Ordering and the endpoint/no-pinching return

For any two admitted lambdas lambda1<lambda2, the first time is strictly
increasing. At the second root, positivity puts it after a0 and before A.
The full-horizon cutoff implies both parameters are live at that shorter
horizon. Strict parameter antitonicity makes the first history strictly above
T there, and strict time monotonicity puts its own root strictly earlier.
This proof covers both negative parameters and comparisons across zero.
No claim of ratio monotonicity over the entire signed domain is made: the
absolute value introduces a distinct dependence on the negative branch.

At the actual positive endpoint, equality with the earlier readout proves
3/8<R_j(lambda_plus)<425/8 for all twelve seeds. The prior no-pinching witness
is positive and passes the original aggregate gate, so the same equality
returns, for every epsilon>0, a single lambda>0 with all twelve signed-readout
ratios in (0,epsilon). The witness does not substitute the zero case for the
strictly positive parameter assertion.

## Adversarial self-review

- The live parameter domain, initial data and history are the original exact
native IVP. The cutoff is strict; a root at the singular turnaround horizon
is not admitted.
- Root construction requires actual reachability. In the original return that
premise is derived for every seed from its checked threshold and the actual
aggregate gate, not from a supplied first-record field.
- The old positive definition is not treated as a correct negative readout.
The new extension is constructed independently and is proved equal on the
certified overlap, with both defaults excluded there.
- Matter comparison is used in the correct reversed direction for nonpositive
lambda: D_lambda>=a/a0 bounds first time above, whereas D_lambda<=a/a0 was
used to bound positive-branch first time below.
- All divisions use positive a0 or positive constructed time. The native
parameter comparison at an interior root has a derived shorter-horizon
cutoff. Equality at the first threshold is included in collapse equivalence.
- The signed first-time ordering is proved, but no signed ratio ordering or
unproved differentiability is inferred from it.
- The full ratio bound is for the original population in declared native units.
It does not certify SciPy interpolation/error, the finite-grid statistics,
a probability measure or a physical Lambda/crunch theory. The original toy
still erases at declared turnaround; the word crunch is not upgraded to an
integrated physical evolution.
- This was adversarial self-review without an independent reviewer.

## Evidence and remaining original scope

The default build passes 8084 jobs. The fresh 694-declaration standard-only
axiom audit includes all 31 new theorems (10 general live-domain, 21 original
signed return). All 31 statements are separately exported and checked. See
`results/signed_record_2026-10-03/verification.json` and
`lean/manifests/axiom_audit_signed_record_2026-10-03.txt`. Previous evidence
packets, including exact quadrature certificates, are retained unchanged.
There are no new numerical certificates in this pure Lean extension.

Next constructions include an actual early-record witness before the outside
negative toy erasure, and the original separately sampled patch-count
robustness populations. The present first-time theorem assumes the declared
gate and therefore does not itself return records formed in an excluded
history before erasure. The previously proved coupled delta/amplitude-scale
endpoint rectangle is unchanged. Known false original claims and physical
identification retain their earlier boundaries; the broader goal is incomplete.
