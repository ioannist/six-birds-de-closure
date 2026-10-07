# Explicit numerical robustness-edge ratios, 2026-10-03

Baseline: `42f228c`. Adversarial self-review, not independent review. Paper,
original runtime, reified inputs and previous proofs/evidence remain fixed.

## Original target and attained statement

The original paper section5/appendixA reports population/threshold/amplitude
robustness and a bounded coincidence-ratio scale near the positive record-window
edge. The preceding packet returned first records/ratios across the entire exact
coupled rectangle but gave only corner-root constants. This packet replaces them
with explicit numerical bounds on actual original native endpoints and readouts.
For every declared rectangle point and every one of the original twelve seeds,

```
d in[6/5,2], s in[1/3,3], delta0=843/500,
c=d/(delta0*s), u=actual native positive record-window endpoint,
3<u*c^3<7/2,
c/2<a_first(u)<=(8/3)*c,
3/8<R_first(u)<1792/27 (approximately66.37).
```

Every signed admitted ratio has0<=R<1792/27. These are explicit uniform
certificates for the continuum rectangle, not sampled interpolation. The broad
finite bracket is not a sharp inferred cosmological value or a typicality theorem.
The paper's honest no-pinching remains unchanged and holds uniformly by the prior
packet. No new downgrade is needed.

## Exact covariance, rather than a different asymptotic model

Unfolding the original native function gives the exact identity

```
D_{a0,lambda/c^3}(c*A)=D_{a0/c,lambda}(A), c!=0.
```

Both dimensionless parameter lambda*a0^3 and actual log(A/a0) are equal after
this change. The original initial value D=1 is retained; no multiplicative
change in D is smuggled in. The left side always has original a0=1/1000 in the
application. The earlier rectangle inequalities earn1/5<c<4, hence rescaled
start y=a0/c belongs to[1/4000,1/200], and the original horizon20 becomes20/c
in[5,100].

The actual native quadrature remains

```
D_{y,Lambda}(A)=sqrt(A^(-3)+Lambda)*
  (sqrt(y^(-3)+Lambda)^(-1)+(Lambda*y^2+5/(2*y))*I_Lambda(y,A)).
```

Finite-start bounds are earned uniformly:

```
2500*c<=prefactor(Lambda,y) for Lambda>=0,
prefactor(7/2,y)<=(2500+1/1000)*c,
initialTerm(7/2,y)<=c/500.
```

The initial term is bounded in the upper estimate and retained as nonnegative
in the lower estimates; it is not removed by redefining the model. The
parameter-dependent Lambda*y^2 term remains in both prefactor bounds.

## Three kernel-certified profiles

The new generator uses Python Fraction and integer isqrt only. Each entire
cell is bounded by the already proved unimodal integrand inequalities. Rational
endpoint/square inequalities and sums are checked with decide+kernel. Invalid
lower/upper first-cell mutations are rejected. Default mode replays exact bytes.
The three profiles are:

| Lambda | Interval | Direction and integral bound | Cells |
|---|---|---|---|
|3|[1/200,5]|I>=224/1000|619|
|7/2|[1/200,8/3]|I>=1909/10000|522|
|7/2|[1/4000,100]|I<=2035/10000|784|

Actual positive-integrand interval monotonicity transfers them to variable start
y and horizon20/c. Rational square-root bounds1734/1000,1884/1000 and1874/1000
then earn the actual original-growth inequalities

```
D_{a0,3/c^3}(5*c)>970*c,
D_{a0,(7/2)/c^3}((8/3)*c)>897*c,
D_{a0,(7/2)/c^3}(20)<960*c.
```

No quadrature approximation is identified with the integral. Each inequality
passes from rational whole-cell certificates to the actual analytic integral,
then exact native quadrature/covariance returns to the original IVP.

## Endpoint and first-time return

The original reified aggregate threshold is in(960,970), proved exactly, so its
scaled threshold is in(960*c,970*c). Actual growth at5*c is below or equal to
horizon growth because5*c<=20. The two actual horizon comparisons and genuine
strict antitone lambda dependence yield

```
3/c^3<u<(7/2)/c^3.
```

No endpoint-bracket premise is supplied. Original ANY-patch first thresholds
are c times their original values in(500,897). Nonnegative matter comparison
earns a_first>c/2. At the actual u, genuine lambda comparison with(7/2)/c^3
and the prefix certificate earn growth above every first threshold at(8/3)*c.
This scale lies inside the original interval, so the actual first-time threshold
equivalence yields a_first<=(8/3)*c. This is first collapse of ANY patch, the
original runtime readout, not the later two-tag formation epoch.

Actual R=abs(u)*a_first^3 combines these independent earned bounds. u>0 gives
3/8<R< (7/2)*(8/3)^3=1792/27. The existing strict nonnegative ratio ordering
returns the upper bound to every nonnegative admitted lambda; the earlier
negative bound R<1/125 covers the rest of the actual signed window.

## Verification and remaining scope

Six new default roots add28 theorems. Full lake build8156 jobs passes;
all28 statement/transitive axiom checks exit0, standard Lean axioms only,
no holes/native_decide. Cumulative1251 retains exact immutable earlier1223 raw
prefix plus fresh28; full cumulative command not rerun. Exact generator replay,
false-cell controls, source/toolchain and prior evidence checked by verifier.
Receipts: `results/robust_edge_2026-10-03/`.

The explicit numerical ratio obligation for the entire exact coupled rectangle
is now discharged at the stated constants. Original floating-array multiplication,
new sampling, separately realized N32/N128 ratio estimates, first-time joint
regularity and sharp numerical typicality remain distinct. Physical Lambda,
moving native calculus, ordinary optimization attainment and prior false or
project-sized claims are unaffected. The broader user goal is not complete.
