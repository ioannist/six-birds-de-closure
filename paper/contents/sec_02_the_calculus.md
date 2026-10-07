# 2. The Six Birds vocabulary

This section introduces only the parts of the Six Birds closure calculus that the paper uses. Fuller accounts are in
[@TsiokosSixBirds2026] and [@TsiokosFoundations2026].

## 2.1 Theories as closure packages

The calculus describes theories by how they compress and complete a system. A **closure package** consists of a **lens**
$f$, a deterministic coarse-graining that keeps some features of a substrate and discards the rest; a **completion** $E$,
which fills in what the lens discarded whenever the description is used and is idempotent on its declared domain
($E^2=E$); and **audits**, functionals that test whether the package stays consistent in use. The standard cosmological
model can be read in these terms: the FLRW lens keeps a few homogeneous degrees of freedom, the homogeneous completion
fills in the rest, and consistency tests between probes act as audits. We use this reading as a guide for building
models, not as a theorem about cosmology.

The program organizes the moves a package can make into six primitive roles, $P_1$ to $P_6$. The Foundations series
argues that these six are canonical under its composability and bounded-access assumptions [@TsiokosFoundations2026];
that argument is not repeated or relied on here. The roles that appear in this paper are:

| role | meaning | where it appears |
|----|--------------------|----------------------------------------------|
| $P_1$ | operator rewrite | a correction term added to the macro law, such as the rewrite family $\Delta_H(z)$ (Section 8) |
| $P_2$ | constraints and gating | admissibility rules: budgets, collapse thresholds, convergence tests (Sections 4–6) |
| $P_3$ | protocols and route structure | the order in which completions are applied, and probe routes in the data (Sections 6, 8) |
| $P_4$ | staging and refinement | redshift bins, probe splits, finite iteration budgets (Sections 6, 8) |
| $P_5$ | packaging | the quotient into macro-objects: patches, records, the homogeneous background |
| $P_6$ | accounting | budgets and ledgers, whose multipliers are the shadow prices of Section 4 |

## 2.2 Readouts and determination

Many results in this paper answer the question *does this record determine that quantity?* Let $r:Z\to Y$ be a readout
on a nonempty set $Z$ of admissible configurations and $q:Z\to Q$ a quantity of interest. We say that $r$ **determines**
$q$ if $q=\phi\circ r$ for some function $\phi:Y\to Q$, that is, if configurations with equal readouts always have equal
values of $q$. If two admissible configurations have the same readout but different values of $q$, no decoder, however
complicated, can recover $q$ from $r$. This is the factorization test of the calculus. It is a statement about the
readout, not about all possible observations: a richer readout may determine $q$.

A second test asks whether two completions commute, $E_1E_2=E_2E_1$. A nonzero commutator means that the order in which
two fill-in rules are applied matters. Section 6.5 applies both tests to a pair of coarse descriptions.

## 2.3 Budgets and shadow prices

The calculus records a conserved or budgeted quantity at one level as a **price** at the level above. If a description
minimizes a cost $J$ subject to a budget $e(x)\le B$, then under convexity and regularity conditions (Section 4.1) the
multiplier of the budget is the rate at which the optimal cost $V(B)$ falls as the budget is relaxed, $p=-V'(B)$. Inverse
temperature as the multiplier of a mean-energy constraint in entropy maximization, and prices in resource allocation,
are familiar examples. What such a construction fixes is the *existence* and
the *form* of the multiplier: one number per binding global constraint, zero when the constraint is slack. Its numerical
value depends on the budget level and on the objective. Section 4 states the precise theorem used here.

In the Six Birds corpus this reading was also applied to holographic min-cut duality [@RyuTakayanagi2006;
@FreedmanHeadrick2017]. The precise finite relation, which we use only as a comparison, is stated in Section 4.4.

## 2.4 Evidence types and provenance

We report every result with its evidence type:

- **Theorem [Lean]**: a mathematical statement about a declared model whose proof is checked by the Lean 4 kernel with
  mathlib [@deMoura2021; @mathlib2020], using only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
  Statements that rely on an argument not yet mechanized are labelled as such.
- **Exact computation**: a computation in rational or interval arithmetic outside Lean, with its inputs recorded.
- **Floating computation**: an ordinary numerical computation. Its reported precision is not a rigorous error bound.
- **Audit**: a pre-registered statistical test on public data, with its calibration and any amendments disclosed.

Results computed in this paper's repository are called **local**. Results taken from other Six Birds papers are called
**imported**; they motivate the models and are never used as local proofs. One imported computation, the background
sweep behind Section 6, was copied into the repository with a hash manifest, re-run, and re-derived by independent code;
its rows are therefore local results, and Section 6 gives their mathematical analysis. Several cross-paper connections drawn elsewhere in the Six Birds corpus are not used, because their current source does
not establish them as theorems: a blindness of the calculus to the Standard Model's generation count, an exclusion of
proton decay and monopoles by record stability, and a null prediction for tabletop tests of gravitationally induced
entanglement, which that source derives only for an assumed perfect-record channel.
