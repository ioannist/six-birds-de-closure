# Quantitative tails, horizon limits and eternal robustness, 2026-10-03

Baseline: `c7e89b3`. The original paper, inputs, runtime, earlier proof modules
and evidence packets are unchanged. Review is adversarial self-review.

## Exact original return

The original N=64 limiting endpoint now has a certified bracket
`3 < u_infinity < 4`. Actual positive finite-horizon endpoints increase strictly
with formation horizon and converge to this constructed endpoint. The horizon
20 value is proved equal to the unchanged previously certified finite endpoint.
For each sufficiently long finite horizon A, the original twelve-seed gate
has the exact window `(-1/A^3,u(A)]` for every real lambda.

The eternal-record returns now also cover the actual separately realized
N=32 and N=128 populations. Their windows are `[0,u_infinity,N)`, with

```
0 < u_infinity,32 < u_infinity,64 < u_infinity,128.
```

The gate inclusions are strict, with witnesses at the smaller window's excluded
endpoint. Every limiting endpoint has exactly nine eventual both-tag seed
passes; ten are required. Each eternal endpoint strictly exceeds its own
original finite-horizon endpoint. Keeping formation by a=20 instead gives the
distinct closed perpetual-retention window `[0,u_20,N]`.

All three actual populations have all-time positive-branch record starvation:
for lambda>=10^9, no patch reaches collapse at any finite a>=1/1000. The bound
is deliberately coarse and does not claim to be a sharp starvation edge.
No amplitudes/tags, population inclusion or random coupling are supplied anew.

## Quantitative tail from the actual IVP

`GrowthInfiniteTail` derives, for c>0 and x>=0,

```
v_c(x) <= (c+5/2)*exp(-2*x)/c,
0 < G_infinity(c)-G_c(x) <= (c+5/2)*exp(-2*x)/(2*c).
```

The existing constructed IVP and positivity make the negative `-rate*growth`
term in the explicit velocity nonpositive. The remaining denominator
`root(c,x)^2=exp(-3*x)+c` is at least c. This derives the velocity estimate;
no decay or tail law is assumed. The function
`G_c(x)+(c+5/2)*exp(-2*x)/(2*c)` is antitone by its actual derivative. Passing
the proved growth/time limit through that inequality gives the tail bound.
The strict lower bound is the already verified strict finite-time/limit order.

Returning x=log(A/a0), c=lambda*a0^3 gives exactly

```
D_infinity(a0,lambda)-D(a0,lambda,A)
 <= [lambda*a0^2+5/(2*a0)]/[2*lambda*A^2]
```

for a0>0, lambda>0, A>=a0. In particular at a0=1/1000, lambda=4, A=20,
combining this bound with the unchanged certified `D(4,20)<936` gives
`D_infinity(4)<937<T_aggregate`. Strict limiting parameter order then gives
`u_infinity<4`; the earlier finite endpoint lower bound and its strict order
below the infinite endpoint give `3<u_infinity`. No new quadrature, solver or
floating approximation is used.

## Actual endpoint convergence and guards

`GrowthHorizonLimit.finiteEndpoint a0 T A` is the already verified finite-root
selector evaluated at log(A/a0). For a0>0, T>3/2 and A>a0*T, all its guards are
proved: A>a0, positive logarithmic horizon, freeGrowth<T, and T<A/a0. The
selector's default branch is therefore excluded on the entire eventual domain.
Its value is positive, solves the actual native IVP threshold equation, and
is strictly below the constructed infinite root.

Strict horizon ordering follows from the actual finite-time growth comparison.
For convergence, use the order characterization of real convergence. Every
positive lo below the infinite root has limiting growth strictly above T;
actual time convergence eventually gives D(lo,A)>T, and finite-horizon strict
parameter comparison then gives lo<u(A). Nonpositive lower tests follow from
u(A)>0. Upper tests follow from u(A)<u_infinity. This proves the endpoint
limit itself rather than only defining a compatible limiting formula. No
unjustified exchange of moving-parameter/time limits or uniformity is used.

`WindowEternalBounds` returns these statements to the unchanged original rank
threshold and actual record-history gate at every such finite horizon. It
also proves equality of the selected A=20 root with the old certified root.

## Closed limiting envelope versus actual finite formation

The previous packet proved the actual eventual finite-formation and perpetual
retention window `[0,u_infinity)`. This packet additionally proves its closure
is `[0,u_infinity]`. Together with actual finite-endpoint convergence, this
makes a closed limiting envelope precise. It does not turn endpoint equality
into an actual record: the unchanged count of nine eventual seed passes at
u_infinity still fails the required ten. Thus the paper's closed interval can
be retained as a qualified closure/envelope statement, or its actual record
window uses an open upper endpoint. Those meanings cannot be interchanged.
The paper remains untouched for its later editing phase.

## Actual robustness populations

`WindowEternalPatchCounts` applies the original actual history/maxima/rank return
at arbitrary finite A. It constructs positive infinite roots from the generic
IVP theorem and derives strict endpoint ordering from the exact unchanged
threshold ordering `T128<T64<T32`. Each seed's eventual both-tag record is
equivalent to its seed threshold being strictly below limiting growth. The
kernel-certified strict rank then proves nine eventual passes at each upper
endpoint. A small new kernel check of the existing tagged maxima supplies the
margin `3*max(m_false,m_true)<delta` for all seeds of both robustness populations;
the analytic global bound proves no original patch ever collapses above the
same coarse cutoff. Exact rational checks replay these margins/ranks from the
unchanged receipts without re-running the RNG or solver.

The populations are not nested: changing N shifts the original tag draws.
The proved order concerns these actual three realizations, not arbitrary
reseeding or a derivative in discrete N. The finite-horizon sensitivity and
ratio theorems retain their existing scope.

## Evidence scope

The full default build passes 8097 jobs with warnings treated as errors.
All 32 new exported statements are separately checked. All 32 new transitive
axiom closures are freshly inspected, allowing only `propext`, `Classical.choice`
and `Quot.sound`. The current cumulative audit has 830 ordered declarations:
the exact immutable previously audited 798-declaration prefix plus the fresh
32-declaration suffix. Verification checks prefix byte identity, manifest
identity and unchanged prior proof sources/toolchain. This is a cumulative
audit, not a claim that the full 830-declaration command was rerun in this packet.
The new raw suffix and combined receipt are both retained. The full manifest
can still be re-audited with `lake env lean manifests/check_axioms.lean`.

Receipts, adversarial self-review, exact rank/margin controls and cumulative
checkout/canonical-Git byte fingerprints are in `results/horizon_limit_2026-10-03/`.
Recompute the new audit with `lean/manifests/check_horizon_limit_axioms.lean`,
the statement checks with `lean/manifests/check_horizon_limit_statements.lean`,
and packet verification with `python3 scripts/de_horizon_limit_verify.py`.
No Python test-suite, numerical growth solver or reification rerun is claimed.

The original paper is still not substantially backed or complete in full.
Physical Lambda identification, the original background-dependent dynamics,
false unrestricted coupling-boundary/tag-irrelevance/run-only wording and
contradicted measure conclusions retain their previously documented boundaries.
A possible next quantitative construction would sharpen global starvation or
prove first-record ratios at the actual infinite endpoint with an explicitly
constructed finite first time. That readout must not reuse a selector outside
its previously verified finite-horizon guard.
