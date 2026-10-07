# Actual joint first-time C1 and signed implicit sensitivity, 2026-10-03

Baseline: `29acb05`. Adversarial self-review, not independent review. The paper,
runtime, reified populations/tags, prior proofs and prior receipts remain fixed.

## Target and exact return

Original section 5 reports smoothly moving record-window edges under threshold
and amplitude changes. Earlier constructions earned actual aggregate endpoint
C1, actual first-time joint continuity and C1 in the coupled knobs at fixed
lambda. This packet closes joint first-time C1 including the signed parameter,
with an actual implicit sensitivity rather than supplied differentiation data.

For a0>0, A>=a0, the unchanged selector
`GrowthFirstRecordLive.firstTime a0 A T lambda` is jointly C1 on the open domain

```
lambda > -1/A^3,  1 < T < nativeGrowth(a0,lambda,A).
```

Its joint derivative at its actual selected scale a is

```
da = (dT - S dLambda)/V,
S = finalSensitivity(a0,log(a/a0),lambda),
V = nativeDerivative(a0,lambda,a).
```

Actual strict interior formation earns S<0 and V>0, so
`partial_lambda firstTime = -S/V > 0`. The original finite-start initial data
and IVP are retained. No continuity, derivative, inverse, domination bound or
implicit-function applicability premise is supplied for the actual selector.

## The joint calculus is constructed

`GrowthJointContinuity` first earns one positive root margin over all nearby
moving integration intervals for the original primitive and parameter
primitive. A globally continuous clipped integrand agrees with the actual
integrand everywhere on each interval in this neighborhood. Parametric
integration then gives joint primitive continuity, actual growth/velocity/
sensitivity continuity, and their native log-chart returns. The clipping is
a proof device; it does not redefine the original function or IVP.

`GrowthUnitDifferential` proves the exact change of variables

```
primitive(c,x) = x * integral[0,1] integrand(c,x*t) dt.
```

The actual unit kernel's joint derivative is explicitly constructed. With
y=x*t, R=sqrt(exp(-3*y)+c), its coefficients are

```
partial_c = -3 exp(-2*y)/(2 R^5),
partial_x = t*(-2 exp(-2*y)/R^3 + 9 exp(-2*y) exp(-3*y)/(2 R^5)).
```

For x>=0 and a positive root at (c,x), choose a later live L>x. One compact
rectangle around (c,x), together with t in[0,1], has a uniform positive root
margin. This includes x=0: negative nearby x still satisfies x*t<=L. The
clipped derivative is globally continuous; compactness bounds its operator
norm, and the margin identifies it with the actual derivative on the whole
rectangle. Measurability, original base integrability, the uniform norm bound
and every nearby actual kernel derivative are earned before applying Mathlib's
derivative-under-integral theorem. Exact transport and multiplication by x
then give the actual primitive's joint Frechet derivative.

`GrowthJointDifferential` constructs joint growth differentiability from this
primitive, the actual positive root and original finite-start factors. Only
after joint differentiability has been earned do coordinate restrictions and
uniqueness identify its derivative with
`growthParameter dc + velocity dx`. The generic identification helper requires
already-established joint differentiability explicitly; separate partial
derivatives are not treated as enough. Composition with the differentiable
native log chart earns joint native growth differentiation; original native
partial derivatives identify it as `S dLambda + V da`. Joint continuity of
these actual fields gives native C1 on the open live/scale region.

## The selector's inverse is earned

`GrowthFirstDifferential` uses the actual map

```
F(lambda,a) = (nativeGrowth(a0,lambda,a),lambda),
g(T,lambda) = (lambda,firstTime(a0,A,T,lambda)).
```

The actual derivative of F is `(S dLambda + V da,dLambda)`. Positive native
velocity earns V!=0. An explicit continuous linear inverse is constructed and
both inverse identities are proved; its action is `(dLambda,(dT-S dLambda)/V)`.
The actual strict selector guards earn a neighborhood of admissible roots.
Their original growth equations prove F(g(q))=q there. Earlier constructed
joint selector continuity, actual joint growth differentiation, and this
earned local identity meet the inverse theorem's hypotheses. The inverse
theorem then yields the actual selector derivative. Joint continuity of
actual sensitivity/velocity composed with the actual selector gives a
continuous derivative field and hence joint C1 on the earned open domain.

The strict final slack is substantive. The prior matter-case control proves
the unchanged fallback selector is not ambient continuous at horizon equality.
No ambient C1 assertion at that boundary is made.

## Original populations, coupled knobs and ratio control

`WindowFirstDifferential` returns the construction to all original signed
N64 readouts and both separately realized N32/N128 populations. Every admitted
first time is C1 in lambda and has the exact positive derivative -S/V. Actual
gate membership already earned first-threshold strict final slack, including
the positive aggregate endpoint. No new endpoint guard is supplied.

For the entire original N64 coupled rectangle d in[6/5,2], s in[1/3,3], actual
first time is jointly C1 in(d,s,lambda) at every admitted point. Actual positive
aggregate endpoint composed with this joint theorem gives joint C1 endpoint
first times and endpoint ratios in(d,s). The original ratio
`R=abs(lambda)*firstTime^3` is jointly C1 away from lambda=0.

The zero boundary is now proved explicitly: for any differentiable positive
time f at zero, differentiability of abs(lambda)*f(lambda)^3 would, by division
by the nonzero smooth factor, imply differentiability of abs at zero. This
contradicts the established absolute-value theorem. All original N32/N64/N128
ratios, and all N64 coupled-rectangle ratios, are therefore nondifferentiable
at lambda=0. Their existing continuity remains valid. This makes the earlier
absolute-value smoothness restriction explicit; it does not weaken the proved
positive-endpoint or knob claims. Prior tied-maximum controls remain fixed;
arbitrary independent amplitude switches are not relabeled C1.

## Verification and remaining scope

Five new roots add61theorems. Full `lake build` passes8166jobs, with warnings
as errors. All61 statements and fresh transitive axiom closures are checked.
Cumulative1383 preserves the exact immutable1322-declaration raw prefix plus
fresh61; the full cumulative command was not rerun. No holes, native_decide or
nonstandard axioms occur in the fresh closures. Pinned Lean/mathlib and all
protected prior source/evidence hashes are checked by
`scripts/de_first_differential_verify.py`. Receipts are in
`results/first_differential_2026-10-03/`.

The actual joint first-time C1 and signed implicit-sensitivity obligation is
closed. Combined additional-population/knob robustness and the broader original
target audit remain. Sharp typicality, floating solver identity, physical
Lambda identification and previously false/project-sized claims are not
established by this packet. The full user goal remains incomplete.
