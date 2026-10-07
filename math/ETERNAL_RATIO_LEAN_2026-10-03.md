# Actual first records and ratios at the infinite endpoint, 2026-10-03

Baseline: `b4d57fc`. The paper, original runtime and inputs, earlier proof
modules and evidence packets are unchanged. Review is adversarial self-review.

## Exact original readout and results

For the unchanged original twelve-by-sixty-four population, the same original
first-any-patch time and ratio functions now have a proved enlarged domain
`0<=lambda<=u_infinity`, including the limiting parameter itself. No selector
is evaluated on an unproved fallback branch. The new results are

```
3 < u_infinity < 17/5,
1/2 < a_first(j,lambda) <= 5/2,
R(j,lambda) = abs(lambda)*a_first(j,lambda)^3,
0 <= R(j,lambda) < 425/8.
```

The time and ratio are strictly increasing in lambda on this closed domain.
Throughout `3<=lambda<=u_infinity`, including the actual limiting endpoint,

```
3/8 < R(j,lambda) < 425/8
```

for every original seed j. Thus the finite-horizon upper-edge ratio bounds
also hold at the actual infinite edge, using real first times of original
patches. These are explicit bounded ratios, not a claim that the historical
sampled maximum 17.4 is a certified continuum supremum.

For every epsilon>0 there is a positive lambda in the actual eternal record
window such that every original seed has `0<R<epsilon`. This strengthens the
paper's no-pinching negative to the actual infinite window. It does not imply
anything about a probability measure or typicality.

The endpoint's first patch and the aggregate both-tag criterion are distinct.
At u_infinity each seed still forms a first patch record at a finite time;
only nine seeds eventually form both tags, whereas ten are required. The
upper endpoint remains excluded from the actual eternal record-bearing window.
No claim of aggregate admissibility at that endpoint is introduced here.

## A sharper exact certificate

The previous 704-cell upper bound at lambda=17/5 was too loose to carry the
existing tail estimate below the original aggregate threshold. This packet
refines just the native cells below a=1 by splitting them at rational midpoints,
giving 1024 cells over [1/1000,20]. The unchanged mathematically derived
unimodal integrand bounds are used: increasing endpoint, decreasing endpoint,
or exact global peak across the turning point.

`scripts/de_eternal_ratio_certificate.py` uses only `Fraction` and integer
`isqrt`; it generates upper enclosures, rational arrays and a receipt. The
kernel checks every cell, endpoints and the actual sum bound

```
J_(17/5)(1/1000,20) <= 4159/20000.
```

The computed upper cell sum is exactly `9981036619/48000000000`, below that
certificate. A zeroed upper cell and the lowered sum target 207/1000 are
rejected by the exact validator. The latter rejects this certificate target;
it is not by itself an impossibility theorem for every other quadrature.
No floating quadrature, solver output or sampled bound is used in these proofs.
A numerical quadrature was used only to scout the refinement, not as evidence
for any exported theorem.

`WindowEternalRatioCertified` returns the whole-cell certificate through the
original finite-start native quadrature, keeping its initial term. Rational
root/prefactor bounds give `D(17/5,20)<959`. The already derived actual IVP tail
then gives `D_infinity(17/5)<960<T_aggregate`. Strict limiting parameter
ordering proves `u_infinity<17/5`; its already certified lower bound is 3.

## Actual finite first-time construction and global earliest return

The existing prefix theorem gives `D(17/5,5/2)>901`, while the unchanged exact
per-seed first thresholds satisfy `500<T_first(j)<897`. For every lambda in
[0,u_infinity], parameter comparison gives growth at a=5/2 at least as large
as the certified prefix growth. Time comparison gives the same threshold
reachability by a=20. These facts discharge all guards of the original
`WindowFirstRecord.time` selector: positive a0, nonnegative lambda, first
threshold above one, and actual attainment by its finite construction horizon.
The total selector's fallback value is never a valid witness in this return.

The resulting time satisfies the actual IVP threshold equation. For any finite
a>=a0, the first-any-patch criterion is exactly `a_first<=a`. The proof places
a and the selected first time inside the common live horizon `max(20,a)`, then
uses actual strict time ordering and the unchanged attained amplitude maximum.
Thus earliestness is proved at every finite epoch, not only below twenty.
The maximum over all patches is used regardless of tags, matching the original
runtime first-record readout.

The matter comparison gives `a_first>=a0*T_first>1/2`; the prefix reachability
gives `a_first<=5/2`. At zero, the exact matter solution gives
`a_first=T_first/1000`, and the ratio is zero. Parameter comparison proves
strict first-time ordering; positivity of the times then gives strict ratio
ordering. The upper bound is `R<=125*lambda/8<425/8`, and the lower near-edge
bound follows from lambda>=3 and a_first>1/2.

For the no-pinching construction choose
`lambda=min(u_infinity/2,epsilon/32)`. This is positive and below the actual
eternal endpoint, so the original aggregate gate holds. The derived linear
ratio bound gives every seed R<epsilon, with positive R. Neither record-bearing
nor a small ratio is assumed as a field of a supplied witness.

## Evidence and scope

The full default build passes 8100 jobs with warnings treated as errors.
All 25 new statements and transitive axiom closures are freshly checked.
The cumulative audit has 855 ordered declarations: the exact immutable
previously audited 830-declaration prefix plus the new 25-declaration suffix.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Prior
proof/toolchain byte identity and the full manifest prefix are checked. This
is a cumulative audit; the entire 855-declaration command was not rerun.
The fresh raw suffix and combined receipt are both retained.

Exact certificate byte replay, false certificate controls, independent rational
cell/sum checks, prior-artifact protections, adversarial self-review and
cumulative checkout/canonical-Git fingerprints are retained in
`results/eternal_ratio_2026-10-03/verification.json` and its receipts. Recompute
with `python3 scripts/de_eternal_ratio_certificate.py`, the new axiom/statement
manifests, and `python3 scripts/de_eternal_ratio_verify.py`. No original growth
solver, RNG reification or Python test-suite rerun is claimed.

These results concern the original toy and N=64 first-record readout. They do
not identify physical Lambda, integrate a physical crunch, certify floating
ODE errors or provide a typicality measure. Ratio bounds for other robustness
populations are separate estimates. The original paper remains incomplete
overall at the earlier documented physical, background and measure boundaries.
