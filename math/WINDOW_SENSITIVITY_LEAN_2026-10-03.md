# Constructed endpoint and population sensitivity, 2026-10-03

Baseline: `98dda95`. This packet mechanizes continuity and directional ordering
of the actual record-window endpoint, including changes in maximizing patches
and seed rank. It also proves an exact record window throughout the original
collapse-threshold/amplitude-scale rectangle. Paper, original Python runtime,
reified data and frozen source remain unchanged. Review is an adversarial
self-review with kernel checking, not an independent mathematical review.

## Target and result

The earlier packets construct the exact finite-start growth IVP and prove
continuity and strict decrease of endpoint growth G(lambda), its infinity limit,
and a unique positive threshold root for `Ginf<T<G(0)`. They prove the original
fixed twelve-seed aggregate record window and reify its threshold T0.

This packet constructs the *endpoint function* E(T), proves it continuous on
that full open threshold interval, and proves it strictly decreasing. It
constructs the finite tagged-maximum and k-th-rank functions and proves each
is globally 1-Lipschitz in the finite maximum metric. Continuous input
amplitudes and collapse thresholds therefore give continuous aggregate
thresholds and endpoints, subject to the actual denominator and endpoint
applicability conditions. No fixed maximizing patch or strict seed ordering
is required for continuity.

For the original realization with a positive common real amplitude multiplier
s, fixed tags, and a positive collapse threshold d, the exact aggregate
threshold is

```
T(d,s)=T0*d/(delta0*s), delta0=843/500,
T0=971912828383572000768/1012057850670495125.
```

Every point of `d in [6/5,2]`, `s in [1/3,3]` is proved admissible. Its exact
native record gate is `(-1/8000,E(d,s)]`, with threshold equality included.
E is continuous on the entire rectangle, strictly decreases with d, and
strictly increases with s. Thus this covers the intermediate parameter values
as well as the declared robustness-sweep points for these two knobs.

Continuity and strict ordering do not establish differentiability or a
nonzero derivative. Smooth sensitivity remains a separate construction; this
packet does not relabel these results as a smoothness theorem.

## Constructed rank and quantitative stability

`GrowthRankSensitivity.rankThreshold` selects the rank supplied by the earlier
finite construction when `0<k<=number of seeds`, and has fallback zero outside
that domain. Its specification includes attainment by an actual seed value,
fewer than k values strictly below it, at least k values at or below it, and

```
k<=passingCount(thresholds,x) iff rankThreshold(thresholds,k)<=x.
```

A uniform one-sided bound `g_j<=f_j+epsilon` makes every passing seed at
`rank(f)` pass under g at `rank(f)+epsilon`. The rank specification therefore
gives `rank(g)<=rank(f)+epsilon`. Applying this in both directions yields

```
if every |f_j-g_j|<=epsilon,
then |rank(f)-rank(g)|<=epsilon.
```

This is promoted to a `LipschitzWith 1` theorem for the finite maximum metric
and then to continuity. Tied seeds remain distinct in the passing counts;
changing their order introduces no discontinuity. Pointwise monotonicity and
positive homogeneity are proved by the same count semantics. The rank function
is identified with any correct strict-below/weak-at-threshold certificate,
so selecting it by classical choice introduces no ambiguity in its value.

## Actual threshold-to-endpoint map

`GrowthEndpointSensitivity.endpoint` selects the already constructed unique
positive root whenever a0,L are positive and `Ginf<T<exp(L)`. Its specification
proves both positivity and `G(E(T))=T`. The fallback value outside that domain
is not used to assert a physical or mathematical window there.

Strict decrease of G gives strict decrease of E. To prove ordinary
`ContinuousAt`, use the open admissible threshold interval as a neighborhood.
For any a<E(T), if a<0 then nearby positive endpoints are above a. Otherwise
strict growth-parameter ordering gives `G(a)>T`, and all sufficiently nearby
d<G(a) have E(d)>a. Similarly, for b>E(T), `G(b)<T`, and all sufficiently
nearby d>G(b) have E(d)<b. The order-topology limit criterion proves continuity
with both inequalities. No continuity of an assumed inverse or sensitivity
field is supplied as a premise; the nearby roots come from the earlier actual
IVP/IVT construction.

The module also proves positive-edge ordering in the growth horizon. For
`0<L1<L2` and the same threshold admissible for both, let lambda=E_L1(T)>0.
The constructed growth family is the same function on both horizons. Its
proved strict increase in time gives `G_L2(lambda)>T`; strict decrease in
lambda at L2 then gives `E_L1(T)<E_L2(T)`. This changes the positive edge in
the opposite direction to the already proved tightening of the negative
persistence cutoff. No continuity in a discrete patch count is inferred.

## Population functions and native applicability

`GrowthPopulationSensitivity.tagMaximumValue` takes the maximum constructed
on the actual finite set of patches carrying the chosen fixed tag. Its
specification supplies an attaining patch and all same-tag bounds. A positive
patch proves that maximum positive. It equals any supplied correct attained
maximum, including the original reified maxima.

If a tag set is empty, the total function uses zero; its continuity is then
constant. This is not used to make an absent tag pass. Native record theorems
require positive patches of both tags, and continuity of the division readout
requires nonzero maxima at the point under consideration.

For nonempty fixed tag sets, uniform one-sided amplitude perturbation bounds
the maximum perturbation by applying the bound to an attaining patch. The
empty-set case is checked separately. Two-sided bounds again give a global
1-Lipschitz theorem. These maps are continuous even when the maximizing patch
changes.

The actual seed and aggregate functions are

```
m_jb(amplitudes) = constructed tagged maximum,
t_j(amplitudes,delta)=max(delta/m_j0,delta/m_j1),
T(amplitudes,delta,k)=rankThreshold(t,k),
E_population=E(T).
```

Finite-function continuity, division by the stated nonzero maxima, continuous
max, the rank Lipschitz theorem and the constructed endpoint continuity are
composed explicitly. The parameter space may be any topological space;
a0,L and the tags stay fixed. Ranking and maximizing-patch switches are allowed.
The endpoint theorem requires its aggregate threshold to be admissible at the
point. Because that interval is open, the local return is valid without a
fixed-rank assumption.

`populationEndpoint_native_window` proves the constructed boundary function
is the actual native aggregate-record boundary. It derives positive attained
maxima from positive tagged patch witnesses, obtains its rank certificate
from the constructed rank, and applies the existing native aggregate theorem.
Unique-root identification returns the witness endpoint to the same endpoint
function used in the continuity theorem. Nonnegative amplitudes and the exact
threshold applicability conditions are visible here. There is no merely
continuous surrogate with no return to record histories.

## Return to the original realization and robustness rectangle

`WindowSensitivity` identifies the newly constructed tagged maxima with the
kernel-checked original maxima and the constructed rank with original T0.
A positive common amplitude multiplier scales the actual maxima by s and every
seed threshold by its reciprocal. A positive multiplier of delta scales every
seed threshold by that multiplier. Rank positive homogeneity therefore gives
`T(d,s)=T0*d/(delta0*s)` exactly, including any ties.

The exact original arithmetic gives `900<T0<1000`. Together with
`d in [6/5,2]`, `s in [1/3,3]`, and `delta0=843/500`, simple positive-denominator
bounds prove

```
3/2<T(d,s)<20000.
```

Since `Ginf<3/2` at `L=log(20000)` and `G(0)=20000`, both endpoint inequalities
hold everywhere in the rectangle. The original positive tagged patches remain
positive after rescaling, and all amplitudes remain nonnegative. The native
window theorem therefore returns an exact record gate for every rectangle
point, with no extra supplied rank, maximum, solution or threshold-bound
hypothesis.

Continuity is proved jointly in (d,s), including all rectangle boundaries,
by composing the rational scaling function with E. A larger d gives a larger
threshold and hence a strictly smaller endpoint. A larger s gives a strictly
smaller threshold and hence a strictly larger endpoint. These signs use strict
ordering, not a sampled monotonicity test or an assumed derivative.

The coupling is exact real rescaling of the same reified amplitudes and tags.
The original runtime multiplies newly generated floating arrays by a changed
heterogeneity scalar, so rounding may differ from exact real rescaling. No
identity of those arrays or equality of floating verdicts arbitrarily near an
edge is claimed. Likewise, changing N can move the RNG draw boundary and tags;
separately reseeded N=32/128 populations are not silently treated as nested or
as points of a continuous N parameter.

## Adversarial self-review and remaining work

Choice functions are populated by established finite maxima, finite ranks and
unique positive roots. Their specifications are proved before composition.
The stability constants use the actual finite maximum metric, and rank ties
retain multiplicity. Empty tag sets and inadmissible ranks have harmless total
fallbacks but are excluded from record applicability. Division requires the
actual nonzero maximum; positive-tag construction supplies it in the native
window. The original model coefficients and finite-start data are unchanged.

The population continuity map keeps tags and horizon fixed. Its native return
has the actual nonnegative-amplitude and positive-tag premises. The original
rectangle specialization discharges them, as well as all threshold inequalities,
from the reified realization. The horizon ordering theorem uses the same
constructed growth function and requires the threshold admissible at both
horizons; it does not assert persistence on a contracting branch.

Continuity through ties is stronger coverage than a fixed-ranking argument,
but it permits corners. Smoothness and the strict nonzero growth derivative
still need mechanization. The concrete next construction is parameter
differentiability of the actual quadrature and a return of its sensitivity to
the inhomogeneous variational ODE. The already proved strict-forcing comparison
can then prove `G'(lambda)<0`; a local inverse-derivative theorem can return
smooth endpoint sensitivity where the active finite maxima/rank are fixed.

Numerical edge accuracy, the order-unity coincidence ratio, the physical Lambda
identification and the previously contradicted universal tag/prior claims are
not repaired by this packet. Whole-paper completion remains unproved.

## Verification

Four new default-build modules add 40 theorems: 8 rank, 6 endpoint,
13 population and 13 original-realization sensitivity. The full default build
passes 8071 jobs with warnings as errors. The fresh transitive audit covers all
524 registered declarations, permitting only `propext`, `Classical.choice` and
`Quot.sound`. Seventeen exported statements are separately elaborated for
exact hypotheses and conclusion coverage. No holes or `native_decide` are used.

Receipts and fingerprints are in `results/window_sensitivity_2026-10-03/`,
with the raw audit in
`lean/manifests/axiom_audit_window_sensitivity_2026-10-03.txt`. Original runtime,
reified inputs, paper and frozen source are unchanged, so no fresh growth solve,
Python test suite or reification run is claimed. The earlier provenance receipts
remain historical evidence. Review is self-review, not independent review.
