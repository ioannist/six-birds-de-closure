# Staging calibration: finite rank law and original-verdict return

Baseline: `ecce4b3`. The paper and frozen B2 artifacts remain unchanged. This is
a documented mathematical review amendment for subsequent runs, with a separate
recomputation on the original outputs. It is not a retroactive preregistration.
Review is adversarial self-review by one reviewer.

## Original target and newly exposed obligation

The original staging statistic is

```
S = max_split |m_split-m_joint| /
    sqrt(sigma_split^2+sigma_joint^2+0.05^2).
```

The original null threshold was NumPy's interpolated empirical 95th percentile
of **20** mock scores. One of those same 20 scores exceeded it, yielding the
reported empirical rate 0.05. That is a rate on the calibration sample. It is
not a theorem that a fresh null observation exceeds the threshold with
probability <=0.05, even if the scores are exchangeable. The distinction
matters to the paper's wording about calibrated false-alarm control.

The repair uses a conservative finite rank rule. Its statistical guarantee
requires exchangeability of the observed and mock scores under their complete
design/fitting procedure. The original procedure takes its physical anchor
from a fit to the observed data, and simulates mocks at that fitted anchor.
This does **not** establish the exchangeability premise for the actual
composite cosmological null. The repair supplies a valid conditional law,
preserves the finite firing, and leaves that applicability boundary visible.

## Independent finite law, including ties

For N scores s_i, define the inclusive upper rank

```
r_i = #{j : s_j >= s_i}.
T_k = {i : r_i <= k}.
```

For every score vector, including ties, `#T_k<=k`. If T_k is nonempty,
choose a least-scoring member i. Every member of T_k has score >=s_i,
so T_k is contained in i's upper set, whose cardinality is r_i<=k. The
empty case is immediate. This is proved in `StagingAudit.tail_card_le`.

Uniformly selecting an audited index gives a rejection fraction at most k/N.
For a probability law invariant under index permutations, each index's
rejection probability is equal. Taking expectations of the deterministic
counting inequality therefore gives, for a predetermined future index,

```
P(r_future<=k) = E[#T_k]/N <= k/N.
```

The general finite-law probabilistic step is also mechanized: nonnegative
weights of total mass one, arbitrary score arrays at each outcome, and equal
index marginal rank masses imply the same bound. `sum_rankMass_le` first
derives the summed mass bound from the deterministic law;
`balanced_rankMass_bound` then divides by N. Equal marginal rank masses
are an **explicit hypothesis**, not an assertion about real-data fitting.
For general measurable exchangeable scores the expectation argument above is
the mathematical return; a continuous probability-space construction is not
claimed as local Lean coverage.

## Exact algorithmic return

Given n null scores and a future score s, compute

```
p_rank = [1 + #{null scores >= s}]/(n+1).
```

Reject when p_rank<=alpha. Equivalently, let
`k_null=ceil((n+1)*(1-alpha))`; reject **strictly above** the k_null-th
sorted null score. If k_null>n, use an infinite cutoff and make no rejection.
Inclusive ranks preserve conservativeness at ties. In the augmented vector,
rejection implies an upper rank at most `n+1-k_null<=alpha*(n+1)`.
The count law supplies the conditional level bound.

`sbt_cosmo/audits/calibration.py` implements this rule using exact Fraction
arithmetic for the rank index. Exact alpha is serialized as a fraction as
well as a display float: rounding 1/3 before a ceiling could otherwise
change a boundary rank. The independent CSV validator rederives the ceiling,
cutoff, and protocol metadata without importing the helper.

For n=20 and alpha=1/20, k_null=20, so the cutoff is the **largest** null
score. The conditional bound is 1/21<1/20. The finite rank/count proof and
these inequalities are mechanized. Too few mocks cannot support this nominal
level by a nontrivial deterministic rank rejection; the helper reports the
infinite-cutoff case explicitly rather than interpolating a spurious level.

## A genuine failure control for the old interpolation

Take 21 distinct scores 0,...,20, assign them uniformly to the 21 indices,
and reserve the last index as the future observation. This is exchangeable.
Conditional on its omitted value i, the other 20 scores are the null sample.
The interpolated empirical p95 is 0.95 times its 19th score plus 0.05 times
its 20th score:

```
i<19: cutoff=19+1/20,
i=19: cutoff=18+2/20,
i=20: cutoff=18+1/20.
```

Values 19 and 20 exceed their respective cutoffs. Thus the old method rejects
with probability 2/21>1/20. The finite-rank rule rejects only value 20,
with probability 1/21. Lean constructs the legacy cutoff table, proves
its rejection set is exactly {19,20}, and verifies its rate. Python
independently constructs and sorts all 21 actual omitted arrays, checks the
interpolation bridge, and computes both rejection counts. The counterexample
tests the actual percentile operation, not an assumed false-alarm rate.

## Return to the frozen B2 computation

The original null maximum is 8.878869923235262, compared with the legacy
interpolated cutoff 8.327825973219865. Recomputing S from the raw split m and
uncertainty columns gives 9.629761049875103. The real observation still exceeds
the stronger cutoff. Its descriptive upper-rank fraction is 1/21. This is
**not** asserted to be a valid real-data p-value without exchangeability.

Under the stronger cutoff, the empirical SN injection rate at epsilon=0.20
is 17/20=0.85, and the BAO rate at epsilon=0.10 is 20/20=1. The first
grid amplitudes reaching the declared empirical 0.8 gate remain exactly
0.20 and 0.10. These measured rates do not certify population power >=0.8;
there are only 20 injection realizations at each amplitude. The real firing
and both detection-grid values survive the repair. Repeated empirical-null
training exceedance is now zero; it is not reported as a population rate.

Both future calibration builders now export the versioned finite-rank rule,
its exact alpha, and the conditional scope. Historical artifacts lacking the
method field are validated using their original empirical-quantile protocol.
Their values are not silently replaced. The validator now recomputes S and its driving split from
raw split parameters and rejects forged score, component and localization
fields; it previously read the repeated maximum without deriving it.

## Common shifts do not imply zero rejection probability

At fixed uncertainties, a common translation of split and joint estimates
cancels exactly in every statistic component. The Lean component law proves
this, with a positive-denominator guard and a concrete shifted witness that
still exceeds a threshold. Taking a finite maximum preserves the identity.
If a random estimator genuinely shifts all estimates together with unchanged
uncertainties, its rejection probability remains its null rejection
probability; it is not forced to zero. In the noiseless equal-estimate case,
the score is zero. Neither statement proves that the actual nonlinear fit
has unchanged uncertainties or is exactly translation-equivariant under
every data-space injection. The paper's assertion of zero TPR at every
amplitude "by construction" therefore needs narrower wording. The useful
design conclusion survives: coherent common shifts do not create systematic
split disagreement, whereas localized alternatives can.

## Review and remaining applicability

The adversarial pass checks ties, too-few-mock resolution, exact alpha
serialization, exchangeability, data-dependent anchors, empirical versus
population rates, and score reconstruction. Exhaustive small-vector tests
verify the actual algorithm's rejection counts for multiple levels and ties.
Builder tests ensure both production paths use the repaired cutoff, and the
independent validator checks both old and versioned protocols.

An exact real-data composite-null level guarantee would require independently
justified nuisance handling, such as an appropriate nuisance-pivotal statistic
or a certified conservative composite-null calibration. Plug-in parametric
mocks, even with an additional refit, do not automatically give an exact
finite-sample guarantee. That is a separate statistical applicability task.
The present result retains the original finite mock-audit grade and original
finite firing; it does not assign causal closure evidence or derive Lambda.

The receipt is `results/staging_rank_2026-10-02/receipt.json`. Build, axiom
audit, full Python tests and source hashes are recorded beside it. This packet
strengthens one surviving empirical leg; it does not complete the original
paper's contradicted background/value/measure claims.
