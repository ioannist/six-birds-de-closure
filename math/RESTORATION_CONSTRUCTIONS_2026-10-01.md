# Additional constructions for the claim restoration

Baseline: `2a8a33a`, after the mathematical review. The paper and historical
experimental artifacts are untouched. This is mathematical construction and
adversarial self-review by one reviewer, not independent human review.

Later original-carrier window/chart results and the current completion
judgment are in
[`ORIGINAL_CLAIM_COVERAGE_2026-10-02.md`](ORIGINAL_CLAIM_COVERAGE_2026-10-02.md).

## Outcome and target coverage

| Target | Construction/result | Status |
|---|---|---|
| Exact background blindness beyond a finite audit | Global nonlinear ledger; compensated force; full relative gauge quotient; all finite projected-gradient histories | Constructed and mechanized for the new finite carrier. |
| Retain the original Step26 local dynamics rather than deleting its feedback | Norm and density-ledger tangent projection of its original kinetic/sourcing force | Constructed; exact pointwise projection theorem, mathematical global-flow argument, and numerical history checks. The update law changes. |
| Universal impossibility of an absolute selector | No absolute-price recovery or shift-equivariant selector from the maximal invariant record | Proved for the declared gauge quotient. Constant gauge choices exist. No claim about unrestricted selectors or physical Lambda. |
| Restore the frozen base near-collapse by changing only the lambda prior | Exact sharp conditional-mixture bound 8/11 < 4/5; record-weighted bound 57/80 | Impossible on the frozen full-support samples. This route is paused. |
| Physical gravitational identification and magnitude | Would need a conservation-compatible spacetime action/equations and dimensional bridge | Parked: substantial separate research, not supplied by these constructions. |

The constructive restoration is an **additional global-ledger carrier**, not a
reinterpretation of the old Step54 pass set as an exact blindness theorem.
It provides the missing equal-full-record witnesses. It does not restore the
old measure numbers, the bounded 15/18 classification in this new carrier, or
the assertion that emergence makes quantities unprovable. A fixed formal
theory can verify these finite executions.

## 1. Derive the missing ledger from the actual feedback

Write rho_i=|psi_i|². At a fixed field, Step26's local potential is

```
V_i(b) = b_i + kappa * (gradientEnergy_i + b_i rho_i).
V_i(b+c) - V_i(b) = c (1 + kappa rho_i).
```

The term proportional to rho_i is the obstruction to scalar-shift blindness.
The ledger term with precisely this derivative is

```
q_kappa(rho) = rho + kappa/2 * rho²,
Q_kappa(psi) = sum_i q_kappa(|psi_i|²).
```

The derivative of q is 1+kappa*rho. The derivative of Q with respect to the
complex conjugate field is `(1+kappa*rho_i) psi_i`; in real coordinates its
gradient is twice that vector. Thus the background-shift force is exactly a
normal to a fixed-Q surface. Among quadratic terms a*rho+b*rho² the required
derivative forces a=1 and b=kappa/2: this ledger was determined by the
obstruction, not fitted to a desired Lambda or a measure verdict.

Fixing Q=B is **additional mathematical content**. It is a legitimate global
budget but is not a consequence of the original Step26 code or a proved
physical conservation law. For kappa>=0 and rho>=0, q>=rho; positive level
sets are bounded. The extension must be described as such.

If mu is the equality-ledger price, the compensated potential is

```
V_i^closed(b,mu) = V_i(b) - mu (1+kappa*rho_i)
                 = (b_i-mu)(1+kappa*rho_i) + kappa*gradientEnergy_i.
```

It is exactly unchanged under `(b_i,mu) -> (b_i+c,mu+c)`, for every field,
not only uniform density or a converged sample. A single scalar mu handles
the site-dependent feedback because it multiplies the correct ledger normal.
Using only the original normalization ledger cannot remove the rho-dependent
part. At the initial field below, its remaining squared norm is
`c²*kappa²*35/11664`, strictly positive when c*kappa is nonzero.

## 2. A genuine, globally optimal finite equality-budget realization

Put x_i=q_kappa(rho_i), kappa>=0. This is a bijection of nonnegative densities
with nonnegative ledger amounts, with stable inverse

```
rho_i = 2*x_i / (1+sqrt(1+2*kappa*x_i)).
```

On the simplex x_i>=0, sum x_i=B>0, maximize

```
U_b(x) = sum_i [w_i log(1+x_i) - c_i*x_i²/2 + b_i*x_i],
w_i>0, c_i>0.
```

The feasible simplex is nonempty and compact. U is continuous and strictly
concave: its diagonal Hessian entries are `-w_i/(1+x_i)²-c_i<0`.
Hence a unique maximizer exists. A common background shift adds exactly cB
to every feasible objective value. The whole optimizer, not just its KKT
equations, is unchanged. This order argument is mechanized generically in
`objective_order_on_ledger` and `optimizer_shift_iff`.

The equality multiplier solves the scalar decreasing allocation equation
sum_i x_i(mu-b_i)=B, where each positive coordinate satisfies

```
w_i/(1+x_i) - c_i*x_i + b_i = mu.
```

At zero coordinates the left side is <=mu. The strictly concave problem
makes these conditions sufficient. The scalar root has a finite explicit
bracket in the implementation, including cases with zero coordinates and
negative mu. Under b+c the multiplier is mu+c, so all densities remain the
same. This realizes the background coefficient in density coordinates:
the derivative of the background contribution is b_i*(1+kappa*rho_i).
The remaining utility is new; it is not asserted to equal Step26's full
kinetic/stress functional.

Here b is an auxiliary utility coupling; equality of its derivative coefficient
does not identify maximization of this utility with Step26 energy minimization.
The constrained field-flow construction below retains the original force
itself and does not rely on that auxiliary utility interpretation.

Equality multipliers may have either sign. Absolute positivity of mu is not
invariant under this additive gauge. For an inequality budget, full screening
continues only while the budget binds and the rebased multiplier is
nonnegative. The earlier `active_kkt_linear_offset` records that limitation.
We do not use equality-ledger invariance to overwrite the inequality theorem.

### Actual iterative histories, not only a chosen final optimizer

Use projected gradient ascent in x:

```
x_(t+1) = Proj_simplex(x_t + eta * grad U_b(x_t)).
```

For every vector v, simplex projection is unchanged by adding a common scalar
to v; its water level shifts by that scalar. The projection characterization
`x_i=max(v_i-tau,0), sum x_i=B` gives this directly. Its state is unique.
The Lean proof of uniqueness sums the coordinate inequality

```
(max(v-t,0)-max(v-u,0))²
  <= (u-t)*(max(v-t,0)-max(v-u,0));
```

the right side sums to zero for equal budgets. Consequently every lawful
projected-gradient update, and every finite history from the same initial
state, is identical at b and b+c. The projection water levels divided by eta
rebase by c. `full_projected_histories` proves the state-history conclusion
without presupposing an invariant update.

For the implemented rate eta=1/max_i(w_i+c_i), let m=min_i c_i>0. On
nonnegative coordinates the unprojected update has diagonal derivatives in
[0,1-eta*m], so it is a contraction by 1-eta*m. Simplex projection is
nonexpansive: its variational inequalities give
`||P(v)-P(w)||² <= <v-w,P(v)-P(w)>`, followed by Cauchy-Schwarz.
The unique KKT optimizer is a fixed point. Thus
`||x_t-x_*|| <= (1-eta*m)^t ||x_0-x_*||`, a quantitative convergence return.
This general estimate is not locally mechanized. The receipt compares
300 iterations against the separately solved scalar-root optimizer. Agreement
is about 7e-16 in ledger coordinates. Removing the global budget moves the
state under the same shift, by norm about 4.29 in the declared density readout.

## 3. Project the original Step26 force onto the new ledger

There is also an extension retaining the original local kinetic and sourcing
force, rather than replacing it with the concave allocation utility. Let

```
F_b(psi) = (K + diag(V_b[psi])) psi.
rho_i = |psi_i|²,  N(psi)=sum rho_i,  I(psi)=sum rho_i².
```

Keep the original normalization N=1 and add Q_kappa=1+kappa*I/2 fixed.
For kappa>0 this is equivalent to fixing I=r. As real vectors in R^(2n),
the constraint normals span psi and rho*psi. Let A contain these columns
and let P=Id-A(A^T A)^(-1)A^T be the tangent projection. Then

```
F_(b+c) = F_b + c*(psi+kappa*rho*psi),
P F_(b+c) = P F_b,
dpsi/dt = -P F_b(psi).
```

Both N and I are conserved by the exact ODE. We have not assumed that F is
the gradient of an energy, so we make no claim of energy descent or global
convergence. This changes the old damped lowest-eigenvector update into a
constrained flow; the original kinetic operator and local source force are
retained.

### Realizability, regularity, and all-time blindness

Choose n=8 and rho_i=i/36 for i=1,...,8, with arbitrary declared phases.
Then N=1 and r=I=17/108. This r differs from 1/m for every integer m=1,...,8.
The constraint-normal Gram matrix on N=1 is

```
[[1, r], [r, sum rho_i³]],
det = sum rho_i³ - r² = sum rho_i*(rho_i-r)².
```

If det=0, every nonzero rho_i equals r. With m nonzero coordinates this
forces mr=1, contrary to the choice of r. Therefore the normals are
independent everywhere on the compact level set N=1,I=r. The projection is
smooth on a neighborhood of this regular level set; F is polynomial in real
field coordinates, so the vector field is locally Lipschitz. Tangency keeps
solutions on the compact level set. Local existence and uniqueness and
compact continuation give a unique global flow for each finite b. Since its
vector field is exactly the same for b and b+c on the level set, the whole
continuous-time field history is the same. This is an ordinary mathematical
ODE argument; the global manifold/continuation theorem is not locally Lean
mechanized. The exact pointwise annihilation is mechanized by
`projected_feedback_blind` and applies separately to real and imaginary
coordinates.

Write the normal force as epsilon*psi+mu*(1+kappa*rho)*psi. Its coefficients
are unique on this level set. Under a background shift, mu becomes mu+c and
epsilon is unchanged. The relative background, compensated potential,
normalized field, conserved ledgers, and all corresponding histories are
unchanged. The flow's price may vary with time; its spatial scalar character
and shift covariance do not prove a spacetime-constant physical Lambda.
The numerical receipt integrates to time 20: field-history
differences are about 2e-14 or less, price-rebase errors about 1.4e-12,
and conserved-ledger drift about 1.1e-11. These are floating checks, without
rigorous integration error bounds. The final tangent-force norm is about
1.17e-4: this run is **not** a 1e-8 convergence certificate.

The same projection still sees changes to kappa and to an inhomogeneous
background: at the initial field, kappa=0.3 versus 0.4 changes the tangent
force by norm about 0.00217, and adding 1 at a single site changes it by
about 0.152. This discriminates the specific common-shift gauge direction.
It is not a derivation of an admissibility boundary or a selected kappa.
The optional sibling-source check directly compares the local force formula
against the original Step26 implementation; its update law is not reused.

## 4. Construct the full-record split pair and apply descent

Fix all structural data and let a presentation be `(state,b,mu)`, where state
may contain the full invariant current and predictive history. Define

```
record(state,b,mu) = (state, (b_i-mu)_i).
shift_c(state,b,mu) = (state, b+c, mu+c).
```

Equal records are **exactly** these gauge orbits, as proved by
`record_eq_iff_shift`. This quotient is maximal for the declared simultaneous
additive gauge: it retains the full state and every relative background
coordinate. It is not an arbitrary Boolean convergence bit or a deletion of
a gauge-invariant physical observable. The constructions above supply lawful
shifted realizations and prove their invariant histories agree.

For any presentation p, p and shift_1(p) therefore have the same full record
and absolute prices differing by 1. The descent criterion (Foundations IV,
F50's first clause, with its proof inspected) implies that absolute price
cannot be recovered as a function of this record. The new Lean theorem
`absolute_price_not_descend` constructs this split pair explicitly. Moreover,
no selector from the quotient can be shift-equivariant as an absolute-value
law: invariance of its input would require f(record)=f(record)+1.
`no_equivariant_absolute_selector` proves that stronger naturality obstruction.

A selector choosing mu=0 as a gauge convention exists. A policy selecting one
background for extra reasons also exists. The theorem says such choices
cannot be recovered as an equivariant absolute value from this invariant
layer. It does not say that every possible selector is logically impossible.
It excludes arbitrary functions of the entire declared invariant record,
not only a tested search routine or finite-time convergence criterion.

The formalization also constructs an explicit admitted pair, not merely an
unrestricted ambient pair: kappa=2, densities (1/2,1), ledger amounts (3/4,2),
budget 11/4, utility weights (63/16,9), curvatures (1,1), background (0,1/2),
and price 3/2 satisfy the concrete allocation KKT conditions. Shifting the
background by 1 gives price 5/2 and the same heterogeneous density. Both prices
are positive. `realized_admitted_prices_not_descend` excludes recovery on the
nonnegative-density KKT-admitted domain itself. The strict-concavity argument
above makes these genuine optimizer witnesses; its general sufficiency proof
is mathematical rather than locally mechanized.

Likewise no normalized probability measure on the absolute-price line can be
invariant under **all** translations. Every half-open interval [k,k+1) would
have the same mass a. If a>0, sufficiently many disjoint intervals have mass
greater than 1; if a=0, their countable union R has mass zero. Thus an absolute
prior needs symmetry-breaking content. This short measure argument is not
locally mechanized. A bounded interval, a distinguished origin, or a declared
metric/prior is additional content; it can support a probability measure.

This is a restored exact toy blindness result on a stated formed quotient.
The physically gravitating cosmological constant is not thereby shown to be
an additive gauge coordinate. Establishing that identification remains the
separate gravitational bridge obligation.

## 5. Exact obstruction to restoring the frozen base measure

Retain all base RS-admitted lambda nodes, the equal seed distribution, and
the original maximum R. From the frozen decimal CSV, the maximum is exactly
642599004699/100000000000. Test top-decade membership by `10*R>=Rmax` in
rational arithmetic, avoiding log rounding. The 44 nodes give the following
(top-seed count, admitted-seed count) pairs, in increasing lambda order:

```
(0,12) repeated forty times; (2,12); (4,12); (7,12); (8,11).
```

Every conditional probability is <=8/11. Any nonnegative reweighting of
whole lambda nodes produces a convex mixture of these conditional
probabilities, so its top-decade probability is <=8/11<4/5. Strictly positive
priors keep every seed supported, hence keep the original maximum and band.
The 80% gate is impossible, independently of the 90%-width gate. The bound
is sharp on this fixed band; concentration on the last node attains it.

With the declared within-seed record weights, the corresponding sharp bound
is 57/80 for both N_rec and f_coll. Their equality is expected from the fixed
patch-count proportionality. The receipt derives those bounds separately.
Only the equal-seed 44-count instance and the general weighted-ratio bound
are locally mechanized. Their external-data premise is checked exactly by
the receipt script. The ODE-generated decimal observations remain numerical
inputs, not exact continuum solutions.

This rules out restoring the old base near-collapse by merely supplying a
more concentrated strictly positive lambda prior. It also demonstrates that
within-lambda seed/record variability matters for this observable. Smoothness
near zero cannot be the only load-bearing input of a general theorem.

The bound is **not** claimed after changing the support and recomputing Rmax,
selecting particular seeds, changing the record observable, altering the
carrier, or taking a continuum/refined-grid limit. The robustness variants
have sharp conditional bounds 1, 10/11, and 11/12 without record weighting;
this particular obstruction does not exclude a new prior there. It does not
restore the original declared M1 results there either. Any new successful
prior would need its own independent rationale rather than tuning to this
gate.

The frozen-base restoration route is therefore paused on a proved finite
obstruction, rather than being left as an indefinitely difficult search.

## 6. Verification, dependencies, and adversarial self-review

The exact ledger, objective-order, force-compensation, simplex-projection,
full finite-history, quotient, and prior-bound lemmas are in
`lean/SbtCosmo/Derivation/GaugeClosure.lean` and `PriorObstruction.lean`.
No physical bridge, ODE convergence assumption, vacuum selector, or preferred
prior is hidden in a constructor. Supplied feasible/projection records are
visible hypotheses where existence is not locally formalized. The compact
strictly concave simplex construction and the regular compact field level
set establish realizability mathematically; numerical instances check the
implemented constructions.

Recompute from the repository root with the sbt-de Python:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python scripts/de_restoration_constructions.py --check-sibling
```

Receipts and source hashes are in
[`results/restoration_2026-10-01/`](../results/restoration_2026-10-01/README.md).
Full builds, tests, and axiom closures are recorded there and under
`lean/manifests/`. The old review receipts remain historical baseline evidence.
Final verification: full Lean build passes (3154 jobs), all 107 Python tests
pass, and all 85 local theorem declarations have fresh axiom audits within
`propext`, `Classical.choice`, and `Quot.sound`, with no proof holes.

The adversarial pass checks that (1) the new ledger is explicitly added,
(2) equality-price signs are not silently treated as inequality KKT signs,
(3) absolute gauge origins are not called physical observables, (4) the record
is a full gauge quotient rather than an audit bit, (5) projected sourcing is
not falsely called gradient descent or a converged old Step26 run, (6) the
global-flow argument avoids all singular normal levels, (7) the numerical
prior obstruction concerns frozen decimals and a fixed band, and (8) support
changes and extra seed selectors are not excluded by that obstruction.

The continuum gravitational bridge and the original unrestricted “no value-law
exists” wording remain parked. The former requires substantive new physics;
the latter needs an explicit notion of lawful selector. The gauge-equivariant
formulation above is one mathematically valid replacement with constructed
premises, not a universal impossibility theorem obtained from a finite sweep.
