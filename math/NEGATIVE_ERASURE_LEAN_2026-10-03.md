# Original negative outside witness: 58 collapses before toy erasure

The original seed-1100 negative outside witness now has a constructed collapse
history for the exact native IVP. Exactly 58 of its unchanged 64 patches collapse
before turnaround, and both tag values are present. The same count and tags hold
before the original turnaround buffer. The declared erasure policy then gives
zero retained records and failure of the final record-bearing predicate.

This restores the original reported 58-to-zero example at the mathematical
carrier level. It does not integrate physical evolution through a big crunch or
prove the numerical integrator's error bound. The paper is unchanged.

## Original inputs and precise return

The population is imported from unchanged `WindowSampleData`: the exact binary
fractions of the original NumPy-realized amplitudes and the original Boolean
tags. Seed 1100 is row zero. As in the earlier native continuum certificates,
`a0=1/1000`, `delta=843/500`, the horizon is 20, and initial values are
`D(a0)=1`, `D'(a0)=1/a0`. These are the declared exact decimal mathematical
model scalars; floating evaluation of the initialization is not formalized.

The negative parameter is the exact binary value from the original full-precision
`coincidence_readout.json`, printed there as `-0.00027000000000000006`, namely

```
lambda = -1245155224975395 / 4611686018427387904.
```

The C2 CSV rounds this to `-0.00027`; its parsed float differs by one binary
step. The theorem uses the full-precision value rather than substituting the
rounded row. `de_negative_erasure_check.py` checks this identity with Python Fraction,
replays the previously captured population, and compares the frozen C2 witness
row's count and tags. This provenance replay runs neither RNG nor solver.
Its rational count/gap statements are independently checked in Lean's kernel.
No reported CSV count is a premise of the history theorem.

`preCollapsed i` means that there is an actual scale `a` in `[a0,t)` where
`delta <= amplitude_i * D_native(lambda,a)`. `stoppedCollapsed i` uses
`[a0,min(20,t*(1-1/100000000))]`, the exact mathematical counterpart of the
original buffer rule. Neither definition replaces a collapse history with a
supplied count, a positive-domain fallback, or a final value at the singularity.

## Upper bound on the entire expanding branch

For `c=lambda*a0^3`, write the existing exact solution as

```
r(x) = sqrt(exp(-3*x)+c),
I(x) = integral from 0 to x of exp(-2*u)/r(u)^3 du,
alpha = c+5/2,
D(x) = r(x)*(1/r(0)+alpha*I(x)).
```

On a live interval, the derivative of
`B(x)=(2/3)*exp(x)/r(x)-I(x)` is `(2/3)*exp(x)/r(x)>0`.
Consequently

```
I(x) <= (2/3)*(exp(x)/r(x)-1/r(0)),
D(x) <= (2/3)*alpha*exp(x) + (1-(2/3)*alpha)*r(x)/r(0).
```

For `-1<c<=0`, `3/2<alpha<=5/2`, so the second summand is strictly
negative and `D(x)<(5/3)*exp(x)`. Returning to native scale gives

```
D_native(lambda,a) < 5*a/(3*a0)
```

for every live nonpositive parameter and `a>=a0`. This is a generic bound
proved from the actual finite-start quadrature; no near-turnaround numerical
integration, limit interchange, or growing-mode normalization is used.

## Lower bound from a constructed subsolution

Put `s=-lambda*a0^3>=0`. The live coefficient of the original log IVP is
`f(x)=3/(2*(1-s*exp(3*x)))`. Construct

```
G(x) = exp(x) + (s/6)*(exp(4*x)-exp(x)*(1+3*x)),
V(x) = exp(x) + (s/6)*(4*exp(4*x)-exp(x)*(4+3*x)),
A(x) = exp(x) + (s/6)*(16*exp(4*x)-exp(x)*(7+3*x)).
```

Direct differentiation gives `G'=V`, `V'=A`, with `G(0)=V(0)=1`.
Convexity of exp gives `G,V>=exp(x)` for `x>=0`. Live denominator positivity
and `s>=0` give `f-3/2 >= (3/2)*s*exp(3*x) >= 0`. The exact matter residual is

```
A-(3/2)*G+(1/2)*V = (s/4)*(11*exp(4*x)-5*exp(x)).
```

Thus the actual residual `q=f*G+(f-2)*V-A` is nonnegative: its first product
is at least `3*s*exp(4*x)`, leaving at least
`(s/4)*exp(4*x)+(5*s/4)*exp(x)`. The differences between the actual solution
and this candidate solve the earlier cooperative system with this derived
forcing, zero initial differences and a coefficient bounded on each live
compact interval. The already proved cone theorem therefore gives `D>=G`.
No subsolution inequality or sign is supplied as a hypothesis of the return.

At `a=15`, `exp(log(a/a0))=15000` and
`exp(4*log(15000))=15000^4`. Even the coarse proved estimate
`log(15000)<=14999` suffices to establish `D_native(lambda,15)>17000`.
The cutoff at 15 is discharged by exact rational arithmetic.

## Turnaround, count gap and history

IVT constructs a unique cubic root `t` in `[77/5,31/2]`. Rational endpoint
inequalities make both bounds strict. Its cube is `-1/lambda`, hence
`1/t^3+lambda=0`; positive scales below it satisfy the strict live cutoff.
In particular `15.4<t<15.5<20`, the buffer lies strictly between 15 and t,
and the original full-horizon aggregate gate excludes this parameter.

The generic upper bound implies `D_native(lambda,a)<26000` for every
`a` in `[a0,t)`. The unchanged population has an exact gap:

```
card {i : delta <= amplitude_i*17000} = 58,
(delta <= amplitude_i*17000) iff (delta <= amplitude_i*26000), for every i.
```

These statements and explicit opposite-tag witnesses at indices 54 and 58
are checked with `decide +kernel`, using the imported original amplitudes.
Any pre-turnaround collapse implies the 26000 inequality, hence the 17000
inequality by the gap. Conversely that inequality implies collapse at the
actual interior scale 15 by the proved lower bound. This establishes the
history equivalence and exactly 58 collapses; it also establishes both tags.
The same interior witness lies before the buffer, proving the stopped history
is identical to the pre-turnaround history.

## Declared erasure, without a physical interpretation

The original runtime declares records persistent exactly when turnaround is
not at or before the horizon. Its mathematical retained predicate is therefore
`stoppedCollapsed i AND 20<t`. Since `t<20`, every retained predicate is false,
the final count is zero, and final record-bearing fails. Pre-erasure
record-bearing has been independently constructed from the actual histories.
The erasure law remains visible as a definition of the toy policy; it is not
claimed to follow from growth dynamics or to describe a physical crunch.

The frozen CSV reports `distinct_tags_final=1` even when `record_count_final=0`.
The original expression clips the pre-erasure tag count to at most one when
final distinguishability is false. It is a bookkeeping indicator, not the
cardinality of the final retained tag set. No theorem here identifies that
historical column with an actual retained-set cardinality. The original runtime
and frozen CSV are unchanged.

## Adversarial self-review and evidence

The review is an adversarial self-review, not an independent review. It checked
that the lower forcing is derived, the upper estimate includes the finite-start
term, the full expanding interval excludes its singular endpoint, and the
count return uses the exact original population. All multiplication directions
use nonnegative amplitudes. All count premises are kernel-derived. The cubic
root and the witness at 15 are constructed, and erasure is explicitly scoped
to the original stipulated policy. Exact decimal initialization and threshold
scalars remain distinguished from floating solver total correctness.

The four new modules export 34 theorems. The default build passes 8088 jobs;
the current 728-declaration transitive axiom audit permits only propext,
Classical.choice and Quot.sound. All 34 statements are separately checked.
The replay passes, and changing the requested count to 59 or enlarging the gap
to 27000 is rejected. Receipts are in `results/negative_erasure_2026-10-03/`;
`verification.json` records protected paths and cumulative source fingerprints.

Separately sampled patch-count robustness populations, fine numerical edge and
first-time accuracy, floating solver errors, and physical Lambda/record bridges
remain outside this construction. Earlier identified false unrestricted claims
and project-sized physical obligations are unchanged. The overall goal remains
active.

## Next construction: actual patch-count populations

A fresh read-only scouting calculation with pinned NumPy 1.26.4 realizes the
original N=32 and N=128 populations using the same source draw order. It also
replays N=64 and checks its threshold against the unchanged captured JSON.
The tenth (80%-gate) seed thresholds are exactly

```
N=32: 971912828383572000768 / 776048084276875375,
N=64: 971912828383572000768 / 1012057850670495125,
N=128: 161985471397262000128 / 201471766463730375.
```

They are approximately 1252.387, 960.333 and 804.011, respectively, and their
exact rational ordering has been checked computationally. These additional
population values are not yet reified or kernel-certified, and are not premises
of this packet's 58-count theorem. Reifying their amplitudes, tags, maxima and
ranks is the next step. The existing native-window and endpoint-antitonicity
laws can then prove the original three continuum windows and their actual
endpoint ordering without an assumed ordering or another ODE construction.

For each N and seed, the source draws N normal samples first and then N tag
uniforms. Changing N shifts the tag draws: none of the twelve seeds preserves
all common-prefix tags between N=64 and either new N. Therefore the return must
use the actual separately realized populations and their checked thresholds;
a theorem for adding patches while retaining old tags would be a different
coupling. This calculation runs no growth solver and asserts no universal
monotonicity for arbitrary reseeded populations.
