# Original patch-count robustness windows, 2026-10-03

The original separately realized N=32 and N=128 populations now have
kernel-certified input maxima and aggregate ranks and constructed continuum
record windows. Together with the unchanged N=64 construction, the actual
positive endpoints obey

```
0 < lambda_plus,32 < lambda_plus,64 < lambda_plus,128.
```

All three windows have the same strict negative cutoff -1/8000 and include
their own positive endpoint. Their admitted sets are strictly nested. This
supports the ordering observed in the original patch-count robustness control
without assuming that reseeding a different N retains existing tags or creates
a nested record population. The paper and original runtime are unchanged.

## Original realized inputs

The source `control_c4` changes the `n_patches` configuration to 32, 64 and 128
while retaining the other base parameters. For each seed 1100 through 1111,
`run_seed` draws N normals to form the amplitudes, and then N uniforms to form
the tags. The new `de_patch_count_reification.py` follows this draw order with
pinned NumPy 1.26.4 and captures each amplitude as its exact binary rational.
It first replays all amplitudes, tags, maxima and thresholds of the unchanged
N=64 captured JSON and requires exact equality. It then records the N=32 and
N=128 populations in `results/patch_count_2026-10-03/populations.json`.

The declared exact mathematical model scalars remain a0=1/1000,
delta=843/500 and a_max=20, with the original initial data D(a0)=1,
D'(a0)=1/a0. The 80%-of-twelve-seeds gate requires at least ten seed passes;
its real-fraction equivalence is the previously proved original theorem.
NumPy's probability law and floating growth-integrator total correctness are
not formalized. No growth solver is run by this construction.

`WindowPatchCountData` uses a finite two-element variant: false denotes N=32,
true denotes N=128, and the patch index type is `Fin (patchCount variant)`.
The data include all 1,920 amplitudes and tags, the 48 attained tagged maxima,
the 24 seed thresholds and their two aggregate thresholds. No N=64 input or
previous realization is edited or substituted.

For each variant and seed, `decide +kernel` checks amplitude nonnegativity,
strictly positive tagged maxima, their actual attaining indices/tags, and all
patchwise upper bounds. It also checks the exact seed threshold
`max(delta/m_false,delta/m_true)`. For each aggregate threshold it checks
exactly nine seed thresholds strictly below and ten at or below it. Equality
is included in collapse and in the aggregate gate.

The exact tenth seed thresholds are

| N | Exact aggregate threshold | Approximate value |
|---|---|---|
| 32 | 971912828383572000768 / 776048084276875375 | 1252.3873817550934 |
| 64 | 971912828383572000768 / 1012057850670495125 | 960.33327318164 |
| 128 | 161985471397262000128 / 201471766463730375 | 804.0107764996599 |

The new kernel certificates prove 1252<T32<1253, 804<T128<805, the admissibility
bounds 3/2<T<20000, and the strict ordering T128<T64<T32. The N=64 fraction
is the unchanged earlier certified value. The new Python replay rejects false
rank certificates obtained by doubling either threshold or substituting the
N=64 threshold for either of the new populations. Default generator mode
checks both generated Lean and JSON bytes exactly; no RNG theorem is inferred
from this computational provenance check.

## Returning maxima and ranks to actual collapse histories

`WindowPatchCounts.sampled_maxima` transports the rational certificates to
real amplitudes and the previously proved `TagMaximum` interface. Their
attainment and signs are constructed by the data certificates. They are not
unresolved assumptions of the original-population return.

For a live parameter, the original native IVP is continuous, positive and
strictly increasing in scale. Consequently a patch collapses somewhere in
[a0,20] iff its final contrast exceeds or equals delta. Both tag values appear
iff growth reaches the maximum of their two positive collapse thresholds.
The finite rank theorem then identifies ten seed passes with growth reaching
the exact aggregate threshold.

The exported `realized_gate_iff_seed_fraction` and
`realized_gate_iff_threshold` establish, for each new population,

```
realizedGate_N(lambda)
  iff lambda > -1/8000 AND at least 80% of the twelve seeds have both tags,
  iff lambda > -1/8000 AND D_native(lambda,20) >= T_N.
```

The record-bearing predicate in these statements quantifies over actual
continuous native histories of the realized patches. It is not a surrogate
scalar gate whose connection to original records is assumed.

## Constructed continuum endpoints and ordering

For fixed horizon 20, the earlier proved zero-parameter endpoint growth is
20000 and the parameter-infinity limit is less than 3/2. Every new T lies
strictly between these limits. The previously proved continuity and strict
parameter antitonicity of the actual IVP therefore construct a unique positive
root D_native(lambda_plus,N,20)=T_N by IVT. The full live-domain comparison
returns the exact window

```
realizedGate_N(lambda) iff -1/8000 < lambda <= lambda_plus,N,
```

for every real lambda. The root is chosen from a proved unique existence
statement; there is no fallback masquerading as a certified endpoint.
`upper_spec` exposes its positive sign, root equality and complete window.

The same actual growth function is used by all three populations. Its strict
parameter antitonicity reverses the kernel-proved threshold ordering, giving
lambda_plus,32 < the unchanged original N=64 endpoint < lambda_plus,128.
`gate_inclusions` returns the ordering to the actual three record gates for
every real lambda. `strict_gate_witnesses` constructs strictness: the original
N=64 endpoint passes its own gate but fails N=32, and the actual N=128 endpoint
passes N=128 but fails N=64. Both witnesses meet the strict live cutoff.
`zero_passes` and `cutoff_fails` give explicit boundary controls for both new
populations.

## Adversarial self-review and limits

This is adversarial self-review, not independent mathematical review. It checked
that the source draw order, exact realized binary amplitudes, original seeds
and tag bits are retained; that the 80% gate means ten rather than nine passes;
and that both-tag maxima and aggregate ranks are separately kernel-certified.
It checked the actual-history return, strict negative cutoff, closed positive
endpoint, derived admissible threshold range and default-free root choice.
The endpoint ordering is obtained from the same growth IVP and actual threshold
ordering, rather than supplied as a theorem premise.

Changing N shifts the subsequent tag draws. The actual seeded populations do
not retain all old tag bits in the common prefix. The proof assumes no
population inclusion and makes no universal monotonicity claim for arbitrary
reseeded populations. N is discrete: strict ordering of these three original
populations does not establish a derivative in N or behavior at every other
patch count. The earlier C1 delta/common-scale results for fixed tagged
populations retain their scope.

The historical C4 CSV reports coarse inside/outside brackets. The new result
constructs and orders the actual continuum endpoints; it does not certify the
numerical integrator, upgrade each reported inside point into an exact edge,
or supply a physical Lambda or erasure bridge. Finer numeric brackets and
first-time ratio bounds for the additional populations are separate estimates.

## Evidence and next work

The default Lean build passes 8090 jobs. The current transitive audit contains
751 declarations, including all 23 new theorems, and permits only propext,
Classical.choice and Quot.sound. All 23 exported statements are separately
checked. Reification byte replay, exact N=64 baseline replay and false rank
controls pass. Receipts and cumulative byte fingerprints are in
`results/patch_count_2026-10-03/verification.json`; Git's canonical bytes and
checkout bytes are distinguished when historical CSV line endings differ.
Previous proof modules, notes and receipts, the paper, original Python runtime,
and frozen external source are unchanged.

Next, examine the original eternal-persistence limit with its formation-deadline
semantics made explicit. The finite-horizon results proved here do not establish
an infinite-horizon endpoint or justify carrying threshold equality through a
limit of actual first-collapse histories. No conclusion about that claim is
inferred merely from the existing finite-horizon window.

The same infinite-time construction should test the paper's positive-branch
wording that sufficiently large parameters prevent records ever forming,
rather than merely preventing them by the finite declared horizon. This is
a separate return from the finite-horizon starvation examples; it will require
a derived global growth bound and actual finite-epoch attainment analysis.
