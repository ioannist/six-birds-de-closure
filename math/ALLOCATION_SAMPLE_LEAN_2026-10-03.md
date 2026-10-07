# Original 32-patch allocation carrier and controls, 2026-10-03

Baseline: `5b18121`. Adversarial self-review, not independent review. The paper,
original runtime, frozen results, previous proofs and previous receipts are
unchanged. This packet returns the general allocation mathematics to section
4.2's original coefficient generator and budget construction.

## Inputs and source bridge

`de_allocation_sample_certificate.py` calls the unchanged original
`make_patch_params(DualConfig())` in the pinned NumPy 1.26.4 environment. It
reifies all 32 IEEE weights, curvatures, ten budget values and three original
offsets as exact rationals. It calls only the original closed-form unconstrained
response and budget arithmetic; no optimizer or root-finding solver is rerun.
Every reported coefficient, budget and offset formats exactly as the frozen
CSV field. Hex representations, rational values, original source hashes and
historical CSV hashes are recorded in `cells.json`.

The source bridge is computational. Historical CSVs round to twelve digits;
their matching formatted fields do not prove bit identity with an unrecorded
historical machine state. The Lean endpoint is exact mathematics on the current
pinned reproduction of the original generator's IEEE inputs, rather than a
proof of transcendental floating arithmetic or historical root-finding error.
This distinction is retained in the verifier. The exact carrier mechanics and
the rounded price claim are certified; machine-precision residual/error values
reported by the original solver remain computational evidence.

The coefficients are fixed trigonometric arrays. The configured seed is unused
by this generator, and no random coefficient draw is inferred. Their exact
reified bounds are 0.7<w_i<1.6 and 0.2<c_i<0.41. The original active budget is
the exact reification of22.244493749688203, not a silently substituted exact
fraction of the real unconstrained optimum. The original IEEE offsets +/-0.2
are slightly larger in absolute value than the exact decimal1/5. The certified
screening interval[-1/4,1/4] contains them both, and control comparisons explicitly
use their actual rational values.

## Exact response and selected-price construction

The unchanged original objective is

```
U_s(x) = sum_i[w_i log(1+x_i)-c_i*x_i^2/2+s*x_i],
x_i>=0, sum_i x_i<=B.
```

`AllocationScreening.demand_margin_bounds` proves an actual response bound from
rational trial marginals. Strict antitonicity of the original marginal and the
original demand stationarity/complementarity prove both sides, including the
zero branch. No numerical response is assumed. The generator uses rational
binary search for trial intervals of width1e-6, on five fixed price profiles:
0,0.46112,0.46113,0.2,-0.2. Lean kernel checks all160 endpoint marginal
inequalities, parameter bounds, sums, sweep classifications and control gaps.
A deliberately false response cell is rejected by exact replay.

At price0.46112 the certified total response exceeds the original budget, and
at0.46113 it lies below it. Actual antitonic response and selected KKT feasibility
prove the intrinsic selected price is above the lower trial price. Its positivity
earns budget activity. Complementarity plus the upper response bound then earns
the upper price inequality:

```
0.46112 < selectedPrice(0) < 0.46113.
```

This supports the paper's rounded0.4611. No optimizer, root, activity, selected
price, stationarity or sensitivity is supplied as a premise of this concrete
result. All32 selected allocations are positive because the certified price is
below every actual weight. Hence every patch's actual marginal equals the
single selected price. The exact first two coefficient orders give strictly
unequal selected allocations. Actual KKT support returns global optimality and
uniqueness against every feasible alternative, with the original quadratic
loss penalty. The previously constructed value derivative returns to these
inputs for every positive budget and every offset: V_s'(B)=-selectedPrice_s(B).
At the original active budget it is strictly negative.

## Screening and actual controls

`selected_offset_screened` returns the previous active-offset KKT law to the
unchanged SELECTED allocation and price, using intrinsic uniqueness at B>0.
At the actual original budget, the earned price bound guarantees p+s>0 for
every s in[-1/4,1/4]. Consequently

```
x_s=x_0, p_s=p_0+s, mass(x_s)=B,
V_s(B)=V_0(B)-s*B.
```

Every shifted patch is positive and obeys the same shifted price. The original
three IEEE offset cases return exactly to these identities. This is screening
within the original sum-budget problem, not a Schur-budget equivalence or a
physical vacuum-energy theorem.

The local-budget control uses B/32 for each unchanged patch objective. Exact
rational marginals there are all positive, and the second local price exceeds
the first by more than1/20. A genuine singleton KKT problem is constructed for
each patch; uniqueness identifies its actual selected allocation as B/32 and
its actual selected price as that marginal. The total local allocation is
exactly B. Its allocation differs from the original heterogeneous global
allocation, and the actual first two local selected prices are unequal. This
changes the constraint, rather than adding unequal price labels to a record.

The source-coupled control removes the sum constraint and retains the SAME
linear offset in the objective. The constructed response is proved the unique unconstrained global optimizer.
Its zero-price KKT support applies to every nonnegative competitor without a
mass guard, and the price term vanishes. The unchanged exact response is
demand(w_i,c_i,s,0)=demand(w_i,c_i,0,-s). Certified rational responses at +/-1/5
prove that patch8 moves by more than1/2 in either direction from its unshifted
unconstrained response. Actual offset monotonicity extends the bound to the
original IEEE +/-0.2. Thus the screening/control contrast is proved for the
actual coefficient generator, without a selected numerical state premise.
The reported sharper0.56--0.67 maxima are not relabeled kernel certificates.

All ten original sweep budgets are retained exactly. Their first seven lie
below the certified real unconstrained mass and have a positive price and
binding budget. The last three lie strictly above it and have zero price and
strict slack. No universal active-implies-positive statement is inferred;
the earlier active-zero-price counterexample remains unchanged.

## Verification and original-target boundary

Four new roots add54 theorems. Full `lake build` passes8179 jobs with warnings
as errors. All54 statements and transitive standard-only axiom closures are
freshly checked. Cumulative1528 preserves the exact immutable1474-declaration
prefix and appends54 fresh closures; the full cumulative command was not rerun.
Pinned Lean/mathlib, byte replay, source bridges, exact exported domains and
protected previous source/evidence hashes are checked by
`scripts/de_allocation_sample_verify.py`. Receipts are in
`results/allocation_sample_2026-10-03/`.

This strengthens the original finite-carrier form and must-flip controls, with
no new downgrade of supported mathematical claims. Floating optimizer residuals
and finite-difference precision are not certified here. The physical Lambda
bridge, unchanged-dynamics blindness and contradicted measure conclusions remain
separate. The original paper is unchanged and the full user goal is incomplete.
