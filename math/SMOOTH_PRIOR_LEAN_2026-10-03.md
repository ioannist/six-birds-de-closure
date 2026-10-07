# Smooth full-support priors and actual small-ratio records, 2026-10-03

Baseline: `cb12a5d`. Adversarial self-review, not independent review. The paper,
runtime, populations, data, previous proofs and previous receipts are unchanged.

## Original target and obstruction

Section 7 identifies nonsingularity of the prior near zero as the sole property
needed for upper-edge typicality. The earlier review already gave a smooth
exponential counterexample on[0,1]. This construction now returns that objection
to every actual original population and the entire coupled knob rectangle.
It does not change the declared flat/log measure classes or their corrected
computational results to make their collapse criterion pass.

For a positive rate k and actual positive endpoint U, define

```
raw(k,t) = k exp(-k*t),
density(k,U,t) = k exp(-k*t)/(1-exp(-k*U)).
```

This density is C-infinity as a real function, strictly positive everywhere,
finite and positive at zero, and normalized on the FULL positive window[0,U].
It is not an atom, a density singular at zero, or a density restricted to a
small subwindow. The actual normalization is earned, not assumed:

```
integral[0,U] density(k,U,t) dt = 1,
integral[0,a] density(k,U,t) dt
  = (1-exp(-k*a))/(1-exp(-k*U)).
```

The raw integral follows from the actual antiderivative-exp(-k*t), with its
derivative and interval integrability proved. The normalizer is positive
because k,U>0. Continuous smooth numerator divided by a fixed real constant
gives C-infinity; positivity additionally uses the earned normalizer guard.

## Actual uniform construction

Let Umin be the unchanged N32 endpoint at(d,s)=(2,1/3). The preceding packet
proves it positive and below every actual N32/N64/N128 endpoint throughout
d in[6/5,2], s in[1/3,3]. For ANY epsilon>0 and 0<eta<1, construct

```
a = min(Umin,epsilon/16000)>0,
k = log(2/eta)/a>0.
```

Then exp(-k*a)=eta/2. At every actual endpoint U>=a, the actual prefix mass
is greater than1-eta. The same k and a work for every population and every
rectangle point; only the earned normalization changes with its actual U.

Every lambda in[0,a] belongs to every actual gate. The preceding actual
finite-horizon bound gives R<=8000lambda<=epsilon/2<epsilon for ALL twelve
seeds of each population. Consequently the prefix carrying mass>1-eta consists
entirely of admitted actual small-ratio records, simultaneously over all36
seed readouts and all knob points. No derivative, root, time bound, window,
normalization or low-ratio region is supplied as a premise of the final theorem.

`actual_all_windows_smooth_small_ratio` exports these quantifiers and exact
integrals. The result is an interval-mass certificate for a normalized positive
density and an inclusion in the actual low-ratio event. It does not separately
construct a Mathlib probability-measure object or a record-weighted pushforward.
Any seed law supported on the original twelve seeds preserves the pointwise
prefix inclusion; no claim about a particular abundance weight is inferred.

This proves that even smooth full-support priors can make arbitrarily small
ratios overwhelmingly likely on the positive windows. Local nonsingularity
alone cannot force upper-edge typicality. Repair requires a specified prior
family or quantitative global density control, followed by the actual record
pushforward. Such conditions do not by themselves restore the contradicted
original numerical near-collapse. The signed negative sliver is outside this
positive-prior construction, and no physical prior is inferred.

## Evidence and remaining scope

One new root adds10 theorems. Full `lake build` passes8175 jobs with warnings
as errors. All10 statements and transitive standard-only axiom closures are
freshly checked. Cumulative1474 preserves the exact immutable1464-declaration
prefix and appends10 fresh closures; the full cumulative command was not rerun.
The verifier checks actual statement scope, integral normalization, original
functions, pinned Lean/mathlib, and protected prior source/evidence hashes.
Receipts are in `results/smooth_prior_2026-10-03/`.

This strengthens an already established negative finding and introduces no new
downgrade of supported claims. Section 7's local-regularity sufficiency is false
and this restoration route stops here. The actual toy windows and all earlier
conditional duality results remain proved. Unchanged-dynamics blindness,
unrestricted value impossibility and the physical Lambda bridge remain the
broader main-claim boundaries recorded in the coverage note. Full goal incomplete.
