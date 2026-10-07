# Original all-time starvation at a modest cutoff, 2026-10-03

Baseline: `52cfe0e`. The paper, original runtime, all three original realized
populations, and earlier proof/evidence packets are unchanged. This is an
adversarial self-review, with no independent reviewer.

## Exact result and original return

For the actual constructed finite-start native growth IVP, with a0=1/1000,

```
D_infinity(a0,32) < 485,
D(a0,lambda,a) < 485  for every lambda>=32 and every finite a>=a0.
```

Every patch in each of the original twelve-seed N=32,64,128 populations has
nonnegative amplitude and satisfies `485*amplitude < delta_c=843/500`.
Consequently no patch ever reaches collapse at any finite epoch for lambda>=32.
The original both-tag record histories are empty, and their twelve-seed passing
counts equal zero at every horizon. This substantially sharpens the existing
sufficient cutoff lambda>=10^9 without changing the model or any population.
It does not identify the smallest starvation parameter.

`WindowGlobalStarvation.no_original_patch_ever` and
`no_robustness_patch_ever` quantify over all original seeds and patches and
exclude any finite a>=a0 with `delta_c<=amplitude*D`. The later record/count
returns use the original `GrowthPopulation.nativeRecord` histories, amplitudes
and tags, rather than an auxiliary gate substituted for them. The counts are
zero even if a supplied horizon is below a0, when the histories are empty.

## Exact certificate and infinite-time bridge

`WindowStarvationData` has 64 native cells on [1/1000,4]. The grid includes the
exact peak at a=1/4, since `2*32*(1/4)^3=1`. The previously derived unimodal
whole-cell bounds apply, using increasing right endpoints, decreasing left
endpoints, or the global peak across a turning point. All rational inequalities,
endpoints and the sum bound are checked by Lean's kernel with `decide +kernel`.
No floating quadrature or solver answer supplies a proof premise.

The upper cell sum is exactly `136242057/4000000000`, and the integral obeys

```
J_32(1/1000,4) <= 341/10000.
```

`GrowthStarvationCertified` returns this through the actual native quadrature,
retaining its homogeneous finite-start term. It bounds the final root by 566/100
and the initial inverse root by 1/30000. With
`alpha=32*(1/1000)^2+5/(2*(1/1000))`, the resulting finite bound is

```
(566/100)*(1/30000+alpha*341/10000)
    = 22617899758259/46875000000 < 9651/20.
```

The already derived actual IVP tail at a=4 is

```
D_infinity(a0,32)-D(a0,32,4)
    <= alpha/(2*32*4^2) = 78125001/32000000 < 49/20.
```

Adding these gives `D_infinity(a0,32)<485`. The actual infinite-growth
parameter antitonicity extends the bound to all lambda>=32; strict finite-time
growth below its time limit then gives the global finite-epoch bound. Finite
quadrature alone does not certify the infinite limit; this derived tail is the
necessary bridge. Time infinity is distinct from parameter infinity.

The generic no-collapse and no-record theorems expose the amplitude positivity
and margin as hypotheses. The actual population instances earn both inputs:
the previous attained tagged-maxima proofs bound every patch, and new small
kernel computations check `485*max(tagged_maxima)<delta_c` for all 36 population
and seed instances. No random-population bound is inferred. The N=32 and N=128
populations remain their original separate realizations, with no assumed
amplitude or tag coupling.

## Review and evidence

The exact generator `scripts/de_global_starvation_certificate.py` uses only
`Fraction` and integer `isqrt`, with outward rational square-root enclosures.
Default mode replays the certificate bytes. A zero upper cell and a lowered
sum target 34/1000 are rejected. The latter rejects this particular cell-sum
certificate, not every possible integral bound at that target.

The verifier independently checks all 64 cells, the sum, root and tail
arithmetic, and all 2688 original patch amplitudes from the unchanged exact
population receipts. The minimum any-patch growth thresholds are approximately
616.956 (N=32), 511.578 (N=64), and 497.139 (N=128), all strictly above 485;
these decimals illustrate the exact rational margins rather than supply them.

The full default build passes 8103 jobs with warnings treated as errors. All
19 new statements and transitive axiom closures are freshly checked, permitting
only `propext`, `Classical.choice` and `Quot.sound`. The cumulative audit has
874 ordered declarations: an exact immutable previously audited 855 prefix and
fresh 19 suffix, with old proof/toolchain identity checked. The entire cumulative
command was not rerun in this packet. Both raw suffix and combined receipt are
retained. Verification also checks the actual pinned Lean binary version,
mathlib revision/direct proof bytes, prior artifact identity, and cumulative
checkout/canonical Git fingerprints.

Recompute from the Lean directory with `lake build`,
`lake env lean manifests/check_global_starvation_statements.lean`, and
`lake env lean manifests/check_global_starvation_axioms.lean`; preserve their
corresponding raw receipts if recomputing the complete packet. From the repo
root, run `python3 scripts/de_global_starvation_certificate.py` and
`python3 scripts/de_global_starvation_verify.py`. The latter requires the
saved build, statement, axiom and self-review receipts. The full optional audit
is still `lake env lean manifests/check_axioms.lean`.

The receipts are in `results/global_starvation_2026-10-03/`. No fresh original
solver, RNG reification or Python test-suite run is claimed. The scope is the
declared growth toy and original finite populations; no physical Lambda bridge,
crunch dynamics, measure or typicality result follows. The broader paper remains
incomplete at the previously documented boundaries. This packet strengthens a
correct original starvation claim and introduces no new downgrade.
