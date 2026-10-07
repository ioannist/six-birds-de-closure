# Original twelve-seed continuum window, 2026-10-03

Baseline: `2d8be19`. This packet closes the finite-population/rank obligation
left by the growth-limit and native-window construction. The paper and original
runtime/frozen sources remain unchanged. Review is an adversarial self-review
with kernel checks and a separate computational provenance check, not an
independent mathematical review.

## Original target and result

Use the original seeds 1100 through 1111, each with 64 patches. Each seed has
its fixed sampled nonnegative amplitudes and Boolean tags. The exact model uses
the declared decimal constants `a0=1/1000`, `A=20`, `delta=1.686=843/500`.
A seed passes when the full continuous native growth history collapses at least
one patch of each tag, with persistence to the horizon. The aggregate requires
at least 80% of twelve seeds, equivalently ten passes.

`WindowSample.exists_unique_realized_window` proves, with no hypotheses:

```
there is a unique upper>0 such that
  D_native(a0,upper,A)=T*,
  and for every real lambda,
    realizedGate(lambda) iff -1/8000<lambda<=upper,

T* = 971912828383572000768 / 1012057850670495125
   = 960.33327318164... .
```

The scalar threshold is tied to all twelve populations by checked maxima,
threshold formulas and exact rank counts; it is not assigned to the gate as an
assumption. `realizedGate` expands to the original persistence cutoff and the
count of seed histories containing both tag values. The ODE functions and their
qualitative properties come from the earlier explicit IVP construction.

This is a continuum theorem for the exact declared model with the realized
inputs reified as exact rationals. The deterministic NumPy-to-input bridge is
reproducibly checked outside Lean. It is not a formalization of NumPy's RNG,
the probability law of random populations, or the floating growth integrator.
The runtime also checks an `integration_sane` diagnostic. Exact live-IVP
existence and regularity establish the mathematical integration admissibility
used here; they do not prove that SciPy returns a successful diagnostic at every
live real lambda. The theorem is not a total-correctness claim about that solver.

## Finite maxima and rank construction

`GrowthPopulation.finite_attained_maximum` takes a nonempty finite patch set,
forms its finite image of amplitudes, and takes the attained maximum there.
It returns both an original patch attaining the value and every patch bound.
`exists_positive_tagMaximum` applies this to the patches of a fixed tag;
a positive patch of that tag establishes nonemptiness and positive maximum.
Thus finite maxima are constructible in the actual carrier, rather than an
unpopulated recognition record.

For a threshold family t_j, define

```
C(x)=number of seeds j with t_j<=x.
```

`passingCount_mono` derives monotonicity by subset inclusion. If the number
strictly below T is less than k and C(T)>=k, then

```
C(x)>=k iff T<=x.
```

For x<T, every passing threshold at x lies strictly below T, so fewer than k
can pass. For x>=T, seed-count monotonicity supplies at least k. This proof
retains all seed multiplicities, including tied thresholds.

`exists_count_threshold` constructs such a T whenever
`0<k<=number of seeds`. Take the finite set of threshold values whose passing
count is at least k; it is nonempty because the finite family maximum passes
all seeds. Choose its least member T. If at least k seed thresholds were
strictly below T, the attained maximum B of those thresholds would satisfy
B<T and C(B)>=k, contradicting minimality. Therefore T has exactly the rank
certificate required by the count equivalence. Removing duplicate *candidate
values* never removes duplicate *seeds* from C.

`native_record_count_eq` applies the already proved original scale-factor
history/threshold equivalence to every seed. On the live branch it identifies
the count of actual continuous record histories with C(D_native(A)), using
`t_j=max(delta/m_j0,delta/m_j1)`. The generic aggregate/window theorems combine
this identity, the rank certificate and the constructed ODE endpoint. Their
population, maxima and rank inputs are explicit. The concrete theorem below
discharges them.

## Exact input realization and kernel certificates

`scripts/de_window_reification.py` uses the unchanged original defaults,
original seed list, original draw order and NumPy 1.26.4. It records every
IEEE amplitude as its exact rational value and every tag as a Bool. It also
records the maximizing patch indices, 24 tagged maxima, twelve exact thresholds,
and aggregate T*. The full realization is in
`results/window_population_2026-10-03/population.json` and the generated Lean
module `WindowSampleData.lean`.

The model scalars a0,A,delta use their declared exact decimal values. The
sampled amplitude values include the original floating multiplication by the
heterogeneity scale and are reified *after* that multiplication. Thus they are
not silently replaced by decimal approximations or a newly sampled population.
The exact model's threshold-equality theorem is not a claim that floating
rounding gives the same verdict arbitrarily close to an endpoint.

Four generated theorems use `decide +kernel`, with no `native_decide`:

- all 768 amplitudes are nonnegative; each tagged maximum is positive, attained
  at the supplied patch with the correct tag, and bounds every patch of that tag;
- every seed threshold is exactly the maximum of its two collapse ratios;
- exactly nine thresholds are strictly below T*, and exactly ten are at or below;
- `3/2<T*<20000`.

These are checked closed rational computations, not asserted certificate
fields. `WindowSample.sampled_maxima` transfers the rational inequalities and
attainment identities to the real-valued carrier. The exact rational-to-real
cast preserves order, maxima and division. The transferred certificates then
populate the original `TagMaximum` records.

`seed_fraction_iff` proves for any natural passing count that
`4/5<=passing/12` iff `10<=passing`. `realized_gate_iff_seed_fraction` ties the
actual gate definition to that percentage readout. Independently, the
reification tool checks all thirteen possible passing counts against the
original NumPy mean and floating 0.8 comparison; they select the same ten-pass
cutoff. This finite computational bridge does not assert a general floating
arithmetic theorem.

## Computational provenance checked separately

The generator's default command regenerates expected bytes in memory and
compares the complete JSON and Lean artifacts byte for byte. Regeneration is
explicitly available with `--write`. It checks every exact seed threshold and
the aggregate threshold against the earlier original-claim receipt.

`scripts/de_window_reification_check.py` does not call the generator's sampling
routine. It calls the original `run_seed` and captures its local amplitude/tag
arrays at return. Collapse lookup is temporarily disabled and dummy growth is
supplied solely to reach this return, so no ODE solve occurs. The captured arrays
match all 768 reified values and tags. Deliberately altered amplitude/tag inputs
are detected. The checker restores the profiling hook even on failure.

The capture stub's record verdict is not used: it is only a way to inspect the
unchanged original sampler. Kernel proofs establish the model's record/window
claims. Neither the sampler capture nor old floating-run comparisons certify
integration error. Source fingerprints and the generated Lean fingerprint are
recorded with the population.

## Endpoint landing and self-review

The kernel rank certificate and general rank/count theorem establish the
aggregate threshold without assuming sortedness, a permutation or a kth-rank
readout. Both distinct tag values are required in every passing seed. The
histories range over the entire original scale interval `[a0,A]`, and are
returned to final growth using proved time monotonicity.

The exact arithmetic gives `T*>3/2>Ginf` and `T*<20000=G(0)`. These discharge
both strict endpoint inequalities. The earlier continuum theorem constructs the
unique positive endpoint from the actual ODE's continuity, strict ordering and
proved infinity limit. The native cutoff is exactly `-1/20³=-1/8000`.
Threshold equality is included; turnaround equality is excluded. There is no
assumed limiting law, threshold endpoint, family of solutions, positivity,
monotone growth or aggregate-equivalence field.

The final theorem has no hypotheses because all finite population and endpoint
inputs have been discharged for the explicit realization. This does not remove
the realization itself from the statement: its values are the module's concrete
input definitions, with the computational provenance boundary just described.
Generic positivity/maxima results make no claim about populations missing a
positive patch of either tag. The rank construction excludes k=0 and k exceeding
the population size, as required. Ties are handled through strict-below and
weak-at-threshold counts.

The original fixed-population aggregate continuum-window obligation is now
complete in Lean. Numerical edge brackets and the order-unity coincidence ratio
remain native computational observations, without a rigorous integration-error
certificate. Parameter differentiability and smooth sensitivity remain written
mathematics; continuous strict ordering is already mechanized. Erasure is the
declared turnaround rule, not an integrated contracting/crunch solution. This
packet does not restore the contradicted universal tag/prior assertions or
provide a physical cosmological-constant identification. Whole-paper completion
remains unproved.

## Verification and next constructive work

The full default build passes 8067 jobs with warnings as errors. The three new
modules add 23 theorems: 8 population constructions, 4 rational certificates,
and 11 real sample/window theorems. A fresh transitive audit covers all 484
registered declarations and permits only `propext`, `Classical.choice` and
`Quot.sound`. Twelve exported statements are separately elaborated for exact
quantifier/input coverage. Both provenance check tools pass.

Receipts and fingerprints are in `results/window_population_2026-10-03/`,
with the raw audit in
`lean/manifests/axiom_audit_window_population_2026-10-03.txt`. The broad Python
test suite and growth solver were not rerun: original runtime code is unchanged,
and the fresh checks target the new reification bridge and formal mathematics.
Prior receipts remain historical evidence. The paper and frozen source remain
unchanged from the initial checkpoint.

The next feasible construction is endpoint/threshold sensitivity and its
population-parameter return, followed by a rigorous numerical bracket if needed
for the reported edge location. A physical Lambda identification remains a
separate spacetime-theory project rather than an omitted scalar lemma.
