# Actual first-record continuity and knob differentiability, 2026-10-03

Baseline: `999d7ae`. Adversarial self-review, not independent review. Paper,
runtime, reified inputs and earlier proof/evidence remain fixed.

## Target and exact coverage

Original section5 reports continuous/smooth robustness under threshold and
amplitude changes. Actual aggregate endpoints were already C1 for the original
exact coupled rectangle; numerical actual first-record edge ratios were certified.
This packet constructs regularity of the actual first-ANY-patch selector itself,
rather than supplying continuity or an inverse as a theorem hypothesis.

For fixed a0>0 and horizon A>=a0, the actual signed selector
`GrowthFirstRecordLive.firstTime a0 A T lambda` is jointly continuous within

```
D={(T,lambda): -1/A^3<lambda, 1<T, T<=nativeGrowth(a0,lambda,A)}.
```

This includes horizon equality T=G_lambda(A). If T<G_lambda(A), D contains a
neighborhood of (T,lambda), so the unchanged selector is jointly ambient
continuous there. At fixed lambda it is C1 on1<T<G_lambda(A), with actual
threshold derivative

```
partial_T firstTime = 1/nativeDerivative(a0,lambda,firstTime) > 0.
```

There is no supplied selector continuity, derivative or local inverse. This
packet does not assert joint C1 in lambda and threshold, nor a lambda derivative.

## Earned local roots and continuity

`GrowthFirstContinuity.Domain` is the actual selector's admissibility domain.
Previous existence/uniqueness and positivity/strict scale monotonicity establish
that selected times lie in[a0,A] and solve original native growth=T.

To show joint relative continuity, use the order-topology criterion. For any
b<the actual selected time, if b<a0 the interval bound already gives eventual
b<all nearby selected times. Otherwise b belongs to[a0,A] and strict growth
ordering givesG_lambda(b)<T. Actual native parameter differentiability at this
fixed b earns continuity in lambda, soG_lambda'(b)<T' persists. All nearby points
within D have actual roots; their original growth equality and strict scale
ordering yieldb<firstTime(T',lambda'). The upper test is symmetric: ifA<b the
interval bound suffices; otherwiseT<G_lambda(b) persists and yieldsfirstTime<b.
This argument handles horizon equality without an interior-root assumption.

With strict final slack, actual fixed-horizon parameter continuity and the two
strict guards earn D in the ambient neighborhood. Relative continuity then
becomes ambient continuity. Strict final slack also earns actual time in(a0,A).

At fixed lambda, the existing actual native scale derivative is positive. Nearby
thresholds lie in(1,G_lambda(A)), so actual root equations establish the local
left-inverse identityG_lambda(firstTime(d))=d. Mathlib's one-dimensional inverse
lemma returns the reciprocal velocity derivative. Existing native velocity
continuity composed with earned selector continuity makes this derivative
continuous and yields C1 on the open actual threshold interval.

## Finite population and original returns

`FirstPopulationContinuity.maximum` constructs the true attained maximum over
all finite patches. It instantiates the existing tag-maximum constructor with a
constant auxiliary label only to compute an untagged maximum; original tags are
not changed. The maximum is1-Lipschitz in the actual finite amplitude vector.
Thus delta/maximum is continuous at each nonzero maximum, including ties. Under
actual positive maximum, live lambda, threshold>1 and strict final slack, composing
with the earned generic selector gives first-time continuity for arbitrary
continuous amplitude, threshold and lambda inputs. The ANY-patch collapse iff
time<=a theorem returns this constructed function to actual first collapse.
These are explicit generic applicability hypotheses, not conclusions hidden as
recognition inputs. No fixed maximizing index is assumed.

`WindowFirstRegularity` earns strict first-threshold slack from actual gates for
the original N64 exact rescaling rectangle and both separately sampled N32/N128
populations. Every first threshold is strictly below the independently certified
aggregate threshold, while gate membership bounds aggregate by actual horizon
growth. Thus the selector's ambient continuity applies even at the positive
aggregate window endpoint; there is no horizon-equality fallback issue there.

For the entire coupled rectangle and every signed admitted lambda, actual time
and R=abs(lambda)*time^3 are jointly continuous in(d,s,lambda). R is continuous
also atlambda0; differentiability ofabs there is not claimed. At fixed lambda,
actual first time is jointly C1 in(d,s). The chain rule earns exact partials,

```
partial_d time = Tfirst_original/(delta0*s) * 1/nativeVelocity > 0,
partial_s time = -(d*delta0*Tfirst_original)/(delta0*s)^2 * 1/nativeVelocity < 0.
```

Existing actual C1 aggregate endpoint composed with joint time/ratio continuity
gives continuous actual endpoint first times and ratios throughout the rectangle.
For all original N64 and independently sampled N32/N128 seeds, actual signed
first times and ratios are continuous inlambda at every admitted parameter.
The original functions, finite-start IVP, gate and ANY-patch readout remain fixed.

## Controls and boundaries

The actual fallback selector is not ambient continuous at horizon equality in
the matter case: withlambda0,T=A/a0 it returnsA, but immediately higher thresholds
fall outside the domain and returna0. The right-hand filter limit isa0, proving
discontinuity whenA>a0. Relative continuity on D remains valid. No general
ambient theorem at equality is smuggled in.

For two patches with amplitudes1+t and1-t, the actual global maximum is1+abs(t).
It is continuous but not differentiable at0. With original a0=1/1000,horizon20,
lambda0 and declared threshold500, actual first time for|t|<1 is
(1/2)/(1+abs(t)). Both amplitudes are positive in this neighborhood and actual
first thresholds are attainable. This actual first time is not differentiable
at0: a differentiable time with nonzero value would reconstruct a differentiable
maximum through(1/2)/time, contradicting the maximum control. The threshold500
is a generic control parameter, not the original rectangle's collapse threshold.
The original common positive rescaling does not switch maximizing patches, and
its C1 result is retained. Arbitrary finite-input continuity is not relabeled C1.

## Verification and remaining work

Three new roots add38theorems. Full lake build8161jobs passes; all38 exported
statements/transitive closures pass with standard Lean axioms only, no holes or
native_decide. Cumulative1322 preserves exact immutable1284 raw prefix plus
fresh38; the full cumulative command was not rerun. Prior source/evidence and
pinned Lean/mathlib identity checked by`de_first_regularity_verify.py`. New
boundary/tie/actual-readout controls are proved in Lean, not sampled tests.
Receipts are in`results/first_regularity_2026-10-03/`.

Joint first-time continuity and actual knob C1/derivative-sign obligations are
closed. Joint C1 includinglambda and its implicit derivative, combined additional
population-and-knob sweeps, sharp typicality and broader original-target audit
remain separate. No new downgrade of the supported original coupled-knob claims.
Previous physical/project-sized and false-claim boundaries remain unchanged.
The full user goal is not complete.
