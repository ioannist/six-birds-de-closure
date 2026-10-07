# Mathematical review, 2026-10-01

The mathematical and computational support has been reviewed and repaired.
The paper has **not** been edited. Initial checkpoint: `6a71e6c`.
This is a self-review by one reviewer, including a separate adversarial pass;
agreement between two implementations is not independent human review.

This report records the review baseline committed as `2a8a33a`. Subsequent
user-requested constructions are recorded separately in
[`RESTORATION_CONSTRUCTIONS_2026-10-01.md`](RESTORATION_CONSTRUCTIONS_2026-10-01.md).
Its new carrier theorems do not retrospectively change the frozen verdicts.

Further original-carrier window and CPL-chart proofs, and the current
completion judgment, are in
[`ORIGINAL_CLAIM_COVERAGE_2026-10-02.md`](ORIGINAL_CLAIM_COVERAGE_2026-10-02.md).
The coverage table below remains the 2026-10-01 review baseline.

The strongest justified result is a collection of exact structural theorems,
explicitly scoped analytic/finite witnesses, and conditional finite numerical
audits. It does not establish a physical identification of Lambda with a
budget multiplier, unrestricted impossibility of in-layer value selection,
or coincidence typicality from smoothness of an otherwise unspecified prior.

## Claim coverage and material decisions

| Target | Strongest supported statement | Remaining boundary |
|---|---|---|
| Closure-price form | Convex-dual price under stated domain/CQ/sensitivity hypotheses; exact Lean witnesses and offset lemmas | General convex duality is a mathematical argument, not a local Lean theorem. No stress-energy/Friedmann bridge. |
| Background value | Fifteen distinct offsets pass the frozen Step54 audit; that predicate does not force one offset | The actual dynamics depend on the background. No theorem excludes selectors using additional accessible content. |
| Record window | A finite toy predicate gives a two-sided sampled window under the declared growth and erasure rules | Negative erasure is at turnaround, not an integrated big crunch at a fixed elapsed time. No physical transfer or continuum certification. |
| Measure/typicality | Conditional distributions under five specified priors, now computed on joint lambda/seed support | No tested class collapses in the base or robustness variants; non-singularity near zero alone is insufficient. |
| Empirical audit | The committed window and empirical-audit verdicts rederive from their frozen inputs | Compressed likelihood, finite mock calibration, and supplied nuisance assumptions remain explicit. No causal attribution to closure. |
| Phantom readout | One positive analytic density gives the finite readout samples and a unique phantom threshold for z>-1 | The independently supplied decay generator is a toy certificate. No physical dynamics, ghost absence, or arbitrary-rewrite P-adeq theorem. |

The material gaps in background blindness and near-collapse were raised during
the review. Work proceeded on the scoped mathematical repairs and receipts.
These boundaries must be reflected in the later paper-editing phase; no title
or main paper theorem has been silently rewritten here.

## 1. P-adeq used the wrong matrix order

Original location: `lean/SbtCosmo/Adequacy/Reconciliation.lean`,
`PAdeqRealization` and `p_adeq_iff_xi_psd`.
The original realization asserted `symC C R = U* Xi U` and tested ordinary PSD
of `symC C R`. The mathematical P-adeq condition is positivity in the C metric:

```
<x,Sx>_C = x^T C S x >= 0,  S = sym_C(R).
```

Thus the matrix to test is **C S**. For example, let
`C=diag(2,1)` and `R=[[1/2,1/2],[1,2]]`. Then `CR=[[1,1],[1,2]]` is positive
definite and R is C-self-adjoint. R is not Euclidean symmetric, so it is not
Euclidean PSD in Mathlib's Hermitian-matrix sense. This is a substantive
coordinate mismatch, not a failed kernel proof of the old conditional theorem.

Repair: carry `C.PosDef` and `C * symC C R = U* Xi U`, retain invertibility
of U, and prove the corrected positivity equivalence. The added
`cInner_symC_eq_energy` and `p_adeq_quadratic_nonneg` connect the exported
matrix result to the stated quadratic form. An invertible congruence is
sufficient; the theorem does not claim U is an isometry or construct it for
an arbitrary empirical rewrite.

The ordinary Schur PSD theorem was already correct under native positive
definiteness and joint PSD. The new `joint_gram_psd` proves joint PSD from
stacked TL/TD Gram data, removing that supplied hypothesis from
`projection_identity_packaged_psd`.

The algebraic projection identity uses Mathlib's total ordinary matrix inverse
and remains valid as algebra without a rank premise. Calling its packaged
`nativeProjector` an orthogonal projector requires the native positive-definite
hypothesis. It is not the Moore-Penrose projector on singular native support.
The corpus projection/optimal residual/exact-adequacy arguments were inspected
in `../six-birds-papers/Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex`.
They do not turn the local easy implication chain into a locally mechanized
full singular-support equivalence.

The Python `XiCosmo.evaluate` function is a signed scalar low-rank ansatz. It
does not construct a Schur matrix. A verified coordinate-to-matrix map is
required before any PSD theorem can be transferred to that empirical ansatz;
the shared name alone supplies no such bridge.

The zero-rewrite selection corollary also needs a tie rule: zero complexity
at zero does not exclude a nonzero repair with zero complexity. The math note
now requires positive complexity away from zero or an explicit zero-preferring
tie-break to claim that a selector returns zero. Availability of a zero repair
does not require that extra assumption.

## 2. Fiber counts counted duplicate list entries

Original location: `lean/SbtCosmo/LocalGlobal.lean`, `GluingRecord`.
Completeness of a list does not imply absence of duplicates. With one global
state listed twice, the old classifier reported ambiguity despite a unique
global lift. Its theorem about list counts was valid, but the advertised
cardinality semantics were wrong.

Repair: require `globals.Nodup`, update the toy instance, and prove
`fiberCard_eq_one_iff_unique_global`. The existing four statuses now have
their intended finite semantics. The SN/BAO toy remains an abstract restriction
map; compatibility was stipulated and no survey gluing theorem was proved.

## 3. Phantom samples were independent of the supplied density

Original T5 stored rho samples 84,72,92 but arbitrary w+1 samples -1,1,2.
It explicitly disclosed the absence of an analytic readout identity. This
limited its coverage despite the correct finite crossing proof.

Repair: preserve the rho samples and set w+1 to `-1/9, 1/27, 9/23`.
The analytic density

```
rho(z) = 287/4 + 16 (z-7/8)^2
w(z) = -1 + (1+z) rho'(z)/(3 rho(z))
```

has exactly these density/readout samples at z=0,1,2. The new analytic module
proves positivity, the derivative, the threshold identity, and
`w(z)<-1 iff z<7/8` on z>-1, together with consistency of the original T5 samples.
There is still one adjacent sign change and a phantom sample; its value is
now -10/9 rather than the previous unrelated -2.

The Python stability helper's docstring falsely advertised P-adeq. It now
describes the actual sampled density and spectral diagnostics. Its supplied
squared-gradient c_eff2 proxy is not a Schur positivity or ghost certificate.
Eigenvalues with nonpositive real parts certify absence of exponential growing
modes; a zero-real-part Jordan block can still give polynomial growth.

## 4. Holonomy witnesses did not require a loop

The old general existential statements permitted any route list, including
an open path. Their concrete witnesses happened to be closed.
`IsClosedLoop` now requires matching first/last endpoints with at least one
bridge, and both existential holonomy theorems carry it. These are finite
transport-loop witnesses, not a measurement of the empirical Hubble tension.
The current and predictive maps are explicit toy abstractions, not a derivation
of all future sufficient statistics of the empirical routes.

T1 idempotence, T2 separating route defects, and T7 Option-status well-formedness
were correct as represented. T7 assumes its classifier discipline and does
not prove that a status resolves a nonzero physical residual.

## 5. Closure-price qualification and offset domain

`math/DERIVATION_LT1_2026-06-02.md` used an extended-real objective but wrote
Slater without requiring finite objective cost at the strict-feasibility point.
It also split subdifferentials without giving the required domain sum rule.
The theorem now gives sufficient relative-interior/domain qualifications and
a finite ambient convex energy extension. The value function is differentiable
in a finite neighborhood. Without a sum rule, use stationarity for the combined
Lagrangian-plus-indicator function. The matrix version needs Loewner convexity,
strict PSD Slater slack, and differentiability to use its displayed derivative.
The positive-price conclusion under strict sensitivity is preserved.

`scripts/de_dual_carrier.py` tested activity against the unshifted optimum.
For a sufficiently negative linear offset, a formerly binding budget becomes
slack, and the old Brent bracket could fail. Activity is now based on the
shifted unconstrained optimizer, with a separate zero-budget KKT witness and
input validation. The positive root is rationalized to avoid cancellation.

Screening by a rebased multiplier is conditional: the rebased price must
remain nonnegative and the budget must still bind. The new Lean
`active_kkt_linear_offset` makes those conditions explicit. On a fixed
equality-budget face the utility ordering is unchanged by adding cB, as
proved separately. This toy adds `c sum(x_i)` to utility, not a literal constant
to the objective; a literal constant would leave both the optimizer and its
price unchanged. No physical vacuum-energy screening follows without a bridge.

Fresh corrected sweep: max KKT residual about 1.11e-12; max price versus
finite-difference value derivative error about 3.56e-11. These are numerical
checks, not rigorous interval error bounds.

## 6. Step54 is nonselection by a finite audit, not exact blindness

The cited F50 theorem was inspected in the vendored Foundations IV source.
It classifies a descended background as constant or nonconstant on a declared
moduli quotient, and identifies a stipulated singleton vacuum criterion.
It does not prohibit every selector or every proof in a layer.

Step54's actual Step26 dynamics use

```
T00_i = gradientEnergy_i + b_i |psi_i|^2
V_i   = b_i + kappa T00_i.
V_i(b+c)-V_i(b) = c (1 + kappa |psi_i|^2).
```

For nonuniform density and nonzero kappa,c, this is not a scalar identity
shift. The source's own `structural_note_rows` explicitly says there is no
full background-independence theorem. The new Lean module proves the sitewise
identity and its non-scalar consequence. A numerical source check confirms
nonconstant potential increments and distinct converged states at offsets
0 and 0.1, with both runs passing the same declared convergence predicate.

The safe exact conclusion is: **if two admitted candidates have different
readouts, admissibility does not force a single readout**. The new Lean
`two_admitted_values_not_forced` proves precisely that conditional statement.
The separate `same_record_different_value_no_factor` requires equal full
declared access records; passing the same Boolean audit is not a substitute
for that premise. Neither lemma forbids an additional selector.

The rederivation now labels nonselection at finite-sweep strength and checks
finite nonnegative residuals, matching comparison case sets, duplicate keys,
and parameter values. The counts remain 15/18 and the kappa pass/fail split
remains unchanged. A failed 60-step convergence test is not proof that the
parameter lacks any fixed point or is inadmissible for all algorithms.
The accepted offsets are not even a contiguous sampled interval: -8 passes
while -5 and -3 fail. Thus “bounded moduli” is a finite classification label,
not a proved connected or globally bounded continuum parameter region.

## 7. Correct measure pushforward and changed verdicts

Original locations: `scripts/de_measure_probe.py` and its validator.
The old calculation pushed forward per-lambda seed medians. Record weights
were unconditional mean counts times the RS pass fraction. In general,
`E[N] P(RS) != E[N 1_RS]`, and weighting a median is not weighting the
distribution of record-bearing seeds. The validator repeated the same error.
Interpolating atom locations against cumulative atom masses also invented a
continuous quantile distribution without specifying it.

Repair: for each admitted lambda quadrature node, assign every RS-passing seed
its node mass divided by the number of seeds, times its own declared record
weight. Push forward those individual readouts and use the left inverse of
the weighted empirical CDF. Zero-weight atoms are ignored. The distribution
remains a finite quadrature approximation, with the declared positive cutoff
and zero-lambda log-R exclusion; it is not a continuum error certificate.

Corrected base values:

| Class | P(top decade) | 90% log10 R width | Median epoch ratio | Collapses |
|---|---:|---:|---:|---|
| M1 | 0.3311 | 1.8211 | 1.3556 | no |
| M2 | 0.0405 | 4.9558 | 8.7147 | no |
| M3 | 0.1938 | 2.2187 | 1.7076 | no |
| M4 | 0.1938 | 2.2187 | 1.7076 | no |
| M5 | 0.0086 | 4.4167 | 13.7976 | no |

All five classes are also noncollapsing in all three frozen robustness
variants. M3 and M4 coincide because, on every RS-passing seed,
`f_coll=N_rec/n_patches`, with n_patches fixed within the variant. This
proportionality gives exactly the same normalized measure. Historical
preregistrations, raw samples, and old verdict tables have been preserved;
corrected receipts are separate under `results/math_review_2026-10-01/`.

Linear priors still give much smaller median epoch ratios than log priors,
and record weights still broaden the linear-class distribution. The previous
near-collapse/robustness-flip finding is not supported after correcting the
pushforward. The top threshold is the maximum supported seed R, so it is
also sensitive to rare supported seeds; it has not been redefined to improve
the verdict.

The assertion “non-singular near zero implies most mass near the upper edge”
is false for an arbitrary prior. On [0,1], the smooth positive density
proportional to exp(-lambda/0.01) gives mass about 4.54e-5 to [0.1,1].
Regularity near zero alone does not determine its mass elsewhere. Quantitative
global density bounds or a specified prior family would be needed, followed
by the actual record pushforward. No theorem rules out a carrier-native
measure merely because no preferred one was constructed.

## 8. Numerical boundaries and reproducibility

`chi2_distance` treated scalar/diagonal covariance entries as standard
deviations, giving residual²/variance² instead of residual²/variance. It now
agrees with the full covariance form and validates positive covariance.
`kl_distance` silently discarded atoms with p>0,q=0. It now returns infinity
for that support mismatch and rejects invalid mass inputs.

The window integrator returned “sane” when turnaround preceded the initial
grid, although its presumed expanding initial conditions did not exist.
That case now fails. Seed generators are materialized once so that every
lambda receives the declared seeds. A window search without records at zero
now fails explicitly instead of looping indefinitely. The historical field
`crunch_before_tmax` is documented as a turnaround/erasure rule at a_max;
the actual negative boundary comes from H²=a^-3+lambda and that toy rule.

An initial full Python test run found six E0 fitted-scalar differences from
the historical receipt, at roughly 1e-9 to 5e-6 absolute scale. They remain
far inside every scientific gate. The revised replay check compares two
fresh same-environment runs strictly, including exact array values; only
named floating optimizer outputs use 1e-6 relative tolerance against the
historical receipt. Generated inputs, other values, and all gate decisions
retain strict checks. Portable bitwise identity of L-BFGS-B fit results is
not claimed. Historical outputs were not regenerated to hide the difference.

The R0 predictive audit also had an identifiability error. Leaving out a
saturated route, or the sole route in a category, leaves its contrast
unidentified. A Moore-Penrose coefficient fit chooses a representative but
does not supply a proper predictive prior for that missing direction.
`loo_pointwise_conditional` now checks estimability and refuses such a score.
Model tables report `null` and `unidentified_without_prior`; an unavailable
score cannot pass the ELPD rule. Plug-in pseudoinverse scores remain labeled
diagnostics rather than gate authorities. All three non-null designs in the
actual six-route R0 audit have this leave-one-out limitation.

Family holdout scoring now uses the full conditional predictive covariance,
including test/train cross covariance and correlations between held-out
routes, rather than adding marginal log densities as though independent.
The existing fallback of an unseen category to the training reference is
still a **declared prediction rule**, not a learned law for an unseen family.
Choosing the best oracle on a held-out family is an oracle diagnostic, not
validation of a single preselected predictive model. Score standard-error and
effective-N rules remain declared heuristics, not exact frequentist coverage
theorems for correlated routes. The corrected R0 power verdict remains false.
Analytic tests check the correlated intercept formula and the joint family
Gaussian density against independent closed-form calculations.

## 9. Proof versus execution and historical research memos

The “emergent means unprovable/run-only” prefaces were not valid mathematics.
A fixed proof system can represent changing object-level packages and verify
a finite deterministic execution. Non-factorization through a smaller record
does not imply unprovability in a stronger formal theory or construction by
running unspecified rules. A shortcut lower bound needs a declared resource
model, and an undecidability claim needs its actual quantifiers and reduction.

The Avenue C/D, topological, criticality, transmutation, and LT3 prefaces now
state those limits. The LT3 counterexample still correctly refutes determination
of its stated cap by its six Boolean channels: the two presentations have
different definable-predicate counts. That cap is not necessarily an attained
run length or a canonical physical endpoint. The historical magnitude result
has a review notice; its author/process interpretation is not used as a proof.
These repairs preserve the conditional physics/scale analyses and do not turn
their literature estimates into universal no-go theorems. This review does
not certify a nonlinear GR magnitude construction or every cited phenomenological
estimate in those historical exploratory memos.

LT2's bridge inventory is also scoped as an unresolved construction, rather
than a proof of universal underdetermination. The absence of a specified
lapse/evolution law does not itself construct the equal-input, unequal-output
witnesses required for a non-factorization theorem.

## 10. Verification and adversarial self-review

Lean v4.28.0 and the locked mathlib revision were used. Fresh full builds
passed (3152 build jobs), and the final Python suite passed all 97 tests.
`lean/manifests/check_axioms.lean` checks all 56 local theorem declarations;
the current raw axiom closures are in `axiom_audit_2026-10-01.txt`.
No `sorry`, `sorryAx`, custom axioms, or native-decide trust extension is allowed.
Ordinary Lean foundations `propext`, `Classical.choice`, `Quot.sound` are
disclosed. Supplied realization/CQ/stability witnesses are hypotheses, not
additional proved physical content.

The commands, results, and test-source hashes are recorded in
[`verification.json`](../results/math_review_2026-10-01/verification.json).

The final self-review checks duplicate-free fiber semantics, metric rather
than Euclidean order, closed-loop witnesses, analytic readout consistency,
shifted-budget slack, covariance dimensions and positivity, support-mismatch
KL, joint measure conditioning, zero-mass quantiles, and the distinction
between exact lemmas and floating sweep evidence. The corrected measure
tables agree with a separately coded row-level calculation. Fresh window and
empirical-audit verdicts agree with the frozen records. These checks establish
the represented results and their declared limits; they do not certify the
broader paper claims listed in the opening table.

## 11. Options for strengthening the results

For a background non-factorization theorem, first declare exactly what the
selector may access and construct two candidates with the **same full access
record** and different background values. The new factorization lemma then
applies. Alternatively, construct dynamics invariant under background shifts
and prove that invariance, including the stress-energy feedback term. Removing
that term changes the carrier and would require a new experiment; the present
Step26 dynamics cannot support the asserted scalar-shift argument.

For a typicality theorem, specify a prior family with quantitative global
bounds and derive a bound for the joint record-bearing pushforward. Smoothness
alone cannot suffice, as the explicit exponential-prior counterexample shows.
The current five measures support a comparison of declared measures, with
linear-prior median epochs nearer unity than log-prior medians. Restoring the
old collapse finding would require new justified mathematical input or a new
carrier, rather than a different quantile convention or post hoc threshold.

Identifying a closure price with physical Lambda needs an explicit map from
the constrained state space and ledger to a gravitational field equation,
with conserved stress-energy and the correct dimensions and sign. This is
additional research. The conditional convex-dual theorem and its formalized
examples remain valid without that identification.
