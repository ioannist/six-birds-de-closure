# 3. Method

## 3.1 Three instruments

**Theorems about declared models.** Claims about the *form* of a term, about exact windows and about what a readout
determines are theorems. Each is stated with its hypotheses. Most are mechanized in Lean 4; Appendix C lists the modules
and the verification record. A theorem is only as relevant as its model, so each model is specified in full
(Appendix A).

**Computations on finite-dimensional models.** Claims about behavior that is not yet proved, or about sampled quantities
such as medians over seeds, come from running the models. Each model declares its state space, dynamics, swept
parameter, grid, seeds and the predicate under test before the sweep. The record rule of Section 5 tests collapse,
distinguishability and retention; it does not stipulate a target interval of $\lambda$. No observed cosmological value
($\Omega_\Lambda$, $H_0$, $10^{-123}$) appears in any model specification, predicate or threshold, and model quantities are
reported in model units. The four models are the allocation model (Section 4), the record-window model (Section 5), the
self-consistent lattice model (Section 6) and the measure probe built on the record-window model (Section 7).

**Audits of public data.** Claims about the observed universe are confined to Section 8. They are statistical audits of
DESI DR2 BAO, Pantheon+ supernovae and compressed Planck distance priors. The staging audit of Section 8.3 is calibrated
twice: on mock $\Lambda$CDM realizations through the same pipeline, to set its threshold, and on injected alternatives,
to measure whether it can detect anything. The model comparison and the chart comparison are not calibrated in this way,
the route residuals inherit the staging audit's calibration, and the growth diagnostics have their own injection
controls.

## 3.2 Controls

The computed claims come with designated controls, alternatives on which the verdict is expected to change. A control
that fails to change the verdict shows that the test has no demonstrated sensitivity to that alternative. The main
controls are:

| claim (section) | control and outcome |
|---|---|
| one price over heterogeneous allocations (4) | per-patch budgets of the same total give unequal prices |
| for an originally binding budget, a common linear term $s\,x_i$ leaves the optimizer unchanged provided the shifted price $p+s\ge0$ (4) | without the global budget the same term moves the allocation; one patch moves by more than $1/2$ |
| the price is positive while the budget strictly binds (4) | budgets above the unconstrained total give price zero |
| records need structure (5) | with zero initial amplitudes no patch collapses at any $\lambda$, including $\lambda=0$ |
| records need both tag values (5) | constant tags fail the both-tag requirement even when patches collapse; in an independent-patch model the tag probability changes the probability of holding both tags |
| the limit readout carries information (6) | across the twelve sampled couplings, ten orbits converge and two approach two-cycles |
| the staging audit can detect a split (8) | probe-localized injections are detected in at least 80% of mocks at the largest tested amplitudes |
| the growth audit can detect a residual (8) | in the nonlinear model configurations a finite injected signal is detected; in the linear configurations the injection adds effectively no signal |

The measure criterion of Section 7 has no positive control: no declared prior meets it, and Section 7.3 proves that on
the base grid no reweighting of the grid values that keeps every value in the support can meet it.

## 3.3 Verification and reproduction

The original model and geometry-audit verdicts have build scripts, independently written validators that re-derive the
verdicts from the raw output tables, and unit tests (Appendix C); additional computations have their own documented
checks. Statements labelled as Lean theorems were checked in a full registered build of the Lean development, followed by
registered declaration and type queries and transitive axiom checks confirming that the proofs use only the standard
axioms (Appendix C); that each declaration states what the paper says it states is a matter of review. Statements argued on paper, and exact certificates computed outside Lean, are labelled as
such where they occur. Agreement between two implementations, or between a proof and a computation, is a consistency
check; it is not an independent human review.

The geometry audits do not depend on a Boltzmann solver: a compressed, scipy-based background pipeline is the only
path they use. A pinned recipe recomputes the audit verdicts and repeats a reduced end-to-end fit within a declared
tolerance (Appendix C).

## 3.4 Pre-registration and amendments

The real-data battery was pre-registered before its audit tables were generated. The registration fixed the models,
splits, statistics and thresholds, and used data products and $\Lambda$CDM and $w_0w_a$ fits that already existed from an
earlier stage of the program; the registration therefore guards the audit computations, not first contact with the data.
Two amendments were made during execution and are logged in the registration record. First, the rewrite model was
refitted through the same likelihood as the baselines after a first fit on a reduced data vector proved not comparable;
that first fit is not reported as a result. Second, the staging audit's original class of injected alternatives, a
rewrite applied coherently to all probes, was never detected, and was replaced by alternatives applied to one probe at a
time (Section 8.3). A later mathematical review replaced the staging audit's interpolated percentile threshold with a
conservative rank rule; this is a documented amendment, not a retroactive registration, and it does not change the
verdict. Throughout, fitted amplitudes are in-sample parameters and are never reported as predictions.
