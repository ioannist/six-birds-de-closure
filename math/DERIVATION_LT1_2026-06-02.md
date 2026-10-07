# WP-DERIV-LT1 Memo: Magnitude Pre-Mortem, Structural Dual Certificate, and Physics Bridge Obligation

Review correction (2026-10-01): the general dual statement below now makes
the objective-domain and subdifferential constraint qualifications explicit.
The price conclusion is preserved. Neither it nor a carrier run is an
impossibility theorem for proofs of an emergent quantity.

Status: LT1 math memo. No empirical data work. No Lean theorem added in this
packet. The Lean target is specified below; full mechanization is a follow-up.

Governing inputs read first:

- `plan/DERIVATION_DARK_ENERGY_AS_CLOSURE.md` v2.
- `plan/EXTERNAL_RULING_DERIVATION_PLAN_2026-06-02.md`.
- Existing reconciliation receipts:
  `math/xi_cosmo_schur_reconciliation.md` and
  `lean/SbtCosmo/Adequacy/Reconciliation.lean`.

## 0. Gate Verdict

The structural route survives only as a closure-price formalism. It does not
yet derive dark energy.

Magnitude pre-mortem:

- Direct Buchert/kinematical-backreaction reading: fails M1 by about five
  orders of magnitude if the closure price is just ordinary `Q_D`.
- Fitting/light-cone reading: can mimic acceleration only through an
  order-`0.1` distance-redshift distortion, not through a theorem supplied by
  Schur duality. This is a possible apparent-geometry bridge, but currently
  nonunique and must be fixed before comparison.
- Clock/calibration/timescape-like reading: can be order unity only with large
  lapse/volume-fraction effects. That is not ruled out by the pre-mortem, but
  it is a separate physics bridge, close to timescape unless SBT adds new
  fixed F4/F18 constraints.

Recommended LT1 outcome: **C**, bridge failure/nonuniqueness, with a sharp
conditional **B** if the only admitted bridge is ordinary Buchert `Q_D`. Outcome
**A** is not supported. Outcome **D** is not forced: Claim S is a valid
finite-dimensional convex-dual certificate theorem under the stated
nondegeneracy hypotheses, but it is structural only.

## 1. Deliverable 0: Magnitude Pre-Mortem

Target magnitude. The spine is `Omega_Lambda ~= 0.68`, so a candidate effective
closure density must reach at least

```text
M1:  Omega_eff = O(0.1--1),
```

not merely a positive sign. A mechanism that gives `10^-5 rho_crit` is not a
dark-energy mechanism.

### 1.1 Buchert / kinematical backreaction `Q_D`

Buchert's scalar averaged equations can be written schematically as

```text
3 H_D^2 = 8 pi G <rho>_D - (1/2)(<R>_D + Q_D),
3 a_D''/a_D = -4 pi G <rho>_D + Q_D,
```

ignoring a fundamental Lambda term. In this chart the kinematical
backreaction scale enters as `Q_D/H_D^2`; equivalently an effective density
or acceleration contribution is order

```text
Omega_Q ~ Q_D / H_0^2
```

up to constants and sign conventions. To mimic `Omega_Lambda ~= 0.68`, the
required scale is

```text
|Q_D| / H_0^2 = O(1).
```

The governing reviewer ruling records the standard perturbative/Rasanen-type
wall as

```text
|Q_D| / H_0^2 <= O(10^-5)
```

for the ordinary kinematical backreaction reading. Therefore:

```text
predicted Omega_eff ~ 10^-5, not O(0.1--1).
```

Verdict:

| level | reachable? | reason |
|---|---:|---|
| M0 sign | maybe | sign depends on the domain and convention |
| M1 scale | no | misses by about five orders of magnitude |
| M2 precision | no | cannot approach `0.68` without an amplifier |

Conclusion. If `lambda_closure` maps to ordinary `Q_D`, then SBT has renamed
standard kinematical backreaction and inherits the `10^-5` wall. This is
outcome **B** if a Buchert bridge exists but no larger non-`Q_D` term is found.

### 1.2 Fitting / light-cone interpretation

Here the closure price does not enter as a stress-energy source. It enters as
an inferred geometry effect: a mismatch between the true lumpy light-cone
observables and the smooth FLRW model used to interpret them.

The observable is roughly a luminosity-distance distortion:

```text
D_L^obs(z) = D_L^FLRW,no-DE(z) (1 + delta_D(z)).
```

A magnitude residual is

```text
delta_mu(z) = 5 log10(1 + delta_D(z)).
```

To mimic the difference between a matter-only smooth model and a
`Omega_Lambda ~= 0.68` flat model over the supernova range, the needed
fractional distance distortion is not perturbative:

```text
delta_D(z) = O(0.1--0.3)       for z ~ 0.5--1,
delta_mu(z) = O(0.2--0.6) mag.
```

Therefore a light-cone bridge can reach M1 only if it supplies a coherent
order-`0.1` distance-redshift bias with a fixed redshift shape. A Schur
residual or KKT multiplier alone does not determine such a bias. If the map is
chosen after looking at the desired `D_L(z)` curve, it is a fitted
normalization and violates the no-amplifier rule.

Verdict:

| level | reachable? | reason |
|---|---:|---|
| M0 sign | conditionally | apparent acceleration can arise from distance bias |
| M1 scale | conditionally | requires `O(0.1)` coherent `D_L` bias, not `10^-5` |
| M2 precision | not yet | needs a fixed light-cone map predicting the curve |

Conclusion. This route is not killed by the `Q_D` wall, but it is currently
outcome **C**: the bridge from `lambda` or `Xi_C` to `D_L(z)` is undefined or
nonunique. It is also not a stress-energy derivation unless a separate
covariant effective source is constructed.

### 1.3 Clock / calibration / timescape-like interpretation

Here the effective acceleration comes from lapse, clock, and regional volume
fraction effects rather than a small local stress-energy perturbation.
Schematically, a wall observer's inferred Hubble and distance variables depend
on a lapse factor `gamma` between a volume-average time and the observer's
clock:

```text
dt_bar = gamma d tau_wall.
```

An order-unity apparent dark-energy term requires order-`0.1--1` changes in
the clock/volume sector, not `10^-5` metric-potential corrections:

```text
Delta H / H = O(0.1),
Delta tau / tau_H = O(0.1),
void/volume fraction effects = O(0.5--1).
```

In physical terms, this means differential aging at the tens-of-percent level
over a Hubble time and an onset tied to nonlinear structure/void domination
around low redshift. That is the qualitative timescape mechanism. The SBT
layer would be new only if it adds fixed, falsifiable lawful-obstruction
constraints: for example, a predeclared F4/F18 route-gluing or lawhood-descent
condition that predicts which clock/calibration quotients objectivize and
which remain holonomy-like.

Verdict:

| level | reachable? | reason |
|---|---:|---|
| M0 sign | conditionally | lapse/volume effects can mimic acceleration |
| M1 scale | conditionally | requires large clock/volume effects |
| M2 precision | not yet | needs fixed lapse/volume evolution and onset |

Conclusion. This is not ruled out by the pre-mortem, but it is not derived by
Claim S. Without a fixed bridge it is outcome **C**. If the bridge is just
timescape with SBT labels, novelty depends on additional testable F4/F18
constraints, not on the existence of a Schur dual.

### 1.4 Gate Decision

The gate does not say "all routes are `10^-5`." It says:

1. A direct `Q_D` stress-energy reading fails as observed dark energy.
2. The only routes with plausible M1 scale are not supplied by convex duality
   or Schur algebra; they require a separate fitting/light-cone or clock
   physics bridge.
3. Therefore the derivation route must not proceed as "dark energy derived."
   The honest status after LT1 is **C** unless and until Claim P is supplied;
   if Claim P collapses to ordinary `Q_D`, the status is **B**.

## 2. Deliverable 1: Claim S, Structural Dual-Certificate Theorem

### 2.1 Setup

Let `X` be a finite-dimensional real vector space of admissible closure
coordinates `Delta`. Let `A subset X` be nonempty, closed, and convex. Let

```text
J : A -> R union {+infty}
```

be a proper closed convex repair/complexity objective.

For each `Delta in A`, let `D_Delta` be the dissolving family after applying
the declared closure coordinate. The Schur adequacy residual is

```text
Xi(Delta) = Xi_C(D_Delta | L)
          = K_DD(Delta) - K_DL(Delta) K_LL^dagger K_LD(Delta).
```

The existing reconciliation result fixes the interpretation: `Xi` is the
theorem-grade leftover content. It is not the rewrite and not a stress-energy
term.

Let `W >= 0` be a fixed audit weight and define the scalar Schur energy

```text
e(Delta) = <W, Xi(Delta)> = tr(W Xi(Delta)).
```

Assume `e` is convex on `A`. This is a hypothesis of the structural theorem;
it is automatic only for declared affine/quadratic residual models with a
fixed positive audit pairing. The budgeted closure value is

```text
V(Omega) = inf { J(Delta) : Delta in A, e(Delta) <= Omega }.
```

The matrix/Loewner version replaces `e(Delta) <= Omega` by
`Xi(Delta) <=_L Omega` and uses a PSD matrix dual certificate `Lambda >= 0`
with pairing `<Lambda, Xi(Delta)-Omega>`.

### 2.2 Theorem S, scalar budget form

The following statement is true and is the correct structural Claim S.

Theorem S. Fix a budget `Omega`. Suppose:

1. `A` is nonempty, closed, convex and finite-dimensional.
2. `J` is a proper closed convex extended-real function on `X`, with
   `ri(dom J) intersect ri(A)` nonempty. Its restriction to `A` is the objective.
3. `e(Delta)=tr(W Xi_C(D_Delta|L))` has a finite convex extension to `X`.
   In finite dimensions this extension is continuous. This is a sufficient
   regularity condition for the displayed split stationarity formula.
4. The optimum `Delta_*` exists.
5. The adequacy constraint is active:

   ```text
   e(Delta_*) = Omega.
   ```

6. A constraint qualification holds, for example Slater:

   ```text
   exists Delta_0 in ri(A) intersect ri(dom J),
       J(Delta_0) < +infty and e(Delta_0) < Omega.
   ```

7. The value function is finite on a neighborhood of `Omega`, differentiable
   at `Omega`, and strictly
   budget-sensitive there:

   ```text
   V'(Omega) < 0.
   ```

Then there is a nonzero scalar dual closure certificate `lambda > 0` such
that

```text
0 in partial J(Delta_*) + lambda partial e(Delta_*) + N_A(Delta_*),
lambda (e(Delta_*) - Omega) = 0,
lambda = - V'(Omega) > 0.
```

Equivalently, the Lagrangian is

```text
Lagr(Delta,lambda;Omega)
  = J(Delta) + lambda ( tr(W Xi_C(D_Delta|L)) - Omega ),
```

so `lambda` is explicitly the marginal price of one unit of allowed Schur
residual energy. This is the only conclusion: a structural dual certificate
exists in the closure optimization problem.

### 2.3 Matrix/Loewner version

For a matrix budget `Omega_mat`, use

```text
Xi_C(D_Delta|L) <=_L Omega_mat.
```

Under the analogous finite-dimensional convexity and Slater hypotheses, KKT
gives a PSD matrix certificate `Lambda >= 0` with

```text
0 in partial J(Delta_*) + D_Xi(Delta_*)^* Lambda + N_A(Delta_*),
<Lambda, Xi_C(D_Delta_*|L) - Omega_mat> = 0,
Lagr(Delta,Lambda;Omega_mat)
  = J(Delta) + <Lambda, Xi_C(D_Delta|L) - Omega_mat>.
```

Nonzero `Lambda` requires strict matrix-budget sensitivity: the value function
must decrease in at least one PSD budget direction. Complementarity plus
activity alone does not imply `Lambda != 0`.

Here convexity means **Loewner-convexity** of the matrix-valued map `Xi`,
Slater means `Omega_mat - Xi(Delta_0)` is positive definite at a point in
the relative-interior objective domain, and the displayed `D_Xi` requires
`Xi` differentiable there and at the optimizer. For a nonsmooth map use
the subdifferential of `Delta -> <Lambda, Xi(Delta)>` instead of `D_Xi`.
Without the sum-rule qualification, stationarity is expressed safely as
`0 in partial(J + lambda*e + indicator_A)(Delta_*)`, not as an assumed
equality of separate subdifferentials.

### 2.4 Proof

Proof, scalar form.

1. The Schur object in `e(Delta)` is the existing adequacy residual. The
   validated T3 receipt proves positivity in the positive-definite finite
   block case, and the paper/corpus proof supplies the legal-quotient
   projection identity in the general support case. This identifies the
   audit content being priced.
2. By finite-dimensional convex programming and Slater's condition, strong
   duality and KKT hold. Therefore there exists `lambda >= 0` satisfying
   stationarity, feasibility, and complementarity.
3. Sensitivity of convex value functions gives

   ```text
   -lambda in partial V(Omega).
   ```

   If `V` is differentiable at `Omega`, this becomes

   ```text
   lambda = -V'(Omega).
   ```

4. Strict budget sensitivity is precisely `V'(Omega)<0`, hence
   `lambda>0`.

This proves Claim S under the stated hypotheses. It proves no Friedmann
source, no pressure, no equation of state, and no dark-energy magnitude.

### 2.5 Refutation of the overstrong theorem

The theorem "active constraint implies nonzero multiplier" is false, even with
a simple constraint qualification.

Counterexample. Minimize

```text
f(x) = x^2
```

subject to

```text
x <= 0.
```

The optimum is `x_*=0`, and the constraint is active. Slater holds, since
`x=-1` is strictly feasible. KKT stationarity is

```text
2x_* + lambda = 0,
```

so `lambda=0`. The value is locally insensitive to relaxing the upper bound:
for constraints `x <= Omega` with `Omega >= 0`, the unconstrained minimizer
`x=0` remains feasible and the value stays `0`.

Therefore activity plus constraint qualification is not enough. Strict
budget-sensitivity or an equivalent nondegenerate tradeoff condition is
minimal for a positive certificate.

### 2.6 Relation to `Xi_C`

The relation to `Xi_C` is through the Lagrangian pairing:

```text
lambda tr(W Xi_C(D_Delta|L))
```

in the scalar case, or

```text
<Lambda, Xi_C(D_Delta|L)>
```

in the Loewner case. Thus the dual certificate prices the forced Schur
leftover content. It does not convert that leftover content into energy
density. That conversion is Claim P.

## 3. Lean Target

No Lean implementation is added in this packet. The appropriate staged Lean
work is:

1. `SbtCosmo.Derivation.ClosurePrice.active_not_implies_positive_multiplier`
   - mathlib-free or light-mathlib finite witness.
   - Statement: the one-dimensional problem `min x^2` subject to `x <= 0`
     has active constraint and KKT multiplier `0`.
   - Purpose: mechanically blocks the overstrong "active implies nonzero"
     theorem.

2. `SbtCosmo.Derivation.ClosurePrice.scalar_quadratic_budget_certificate`
   - finite one-dimensional positive witness.
   - Example: minimize `(x-a)^2` subject to `x <= Omega`, with `Omega<a`.
     The optimizer is `x=Omega`, the constraint is active, and the KKT
     multiplier is `lambda=2(a-Omega)>0`.
   - Purpose: verifies the strict-sensitivity/nondegenerate case.

3. `SbtCosmo.Derivation.ClosurePrice.schur_energy_budget_lagrangian`
   - imports `SbtCosmo.Adequacy.Reconciliation`.
   - Defines the finite scalar Schur energy

     ```text
     e(Delta) = tr(W adequacyResidual KLL KLD(Delta) KDD(Delta)).
     ```

   - States the Lagrangian pairing with `lambda`.

4. General KKT/sensitivity theorem
   - paper proof in this memo for LT1.
   - Lean mechanization requires a deliberate convex-analysis layer:
     finite-dimensional convex sets, Slater/CQ, normal cones, subgradients,
     value-function sensitivity. This should be a separate packet if needed.

No Lean theorem should state that the closure certificate is a dark-energy
term. Any Lean theorem here can certify only the structural dual certificate
or the counterexample to overclaiming.

## 4. Deliverable 2: Claim P Physics-Bridge Obligation

Claim P is the missing physics theorem. It must be stated before any
derivation claim.

A valid bridge is a map

```text
B :
  (spacetime/averaging domain, L, D, C, Omega,
   Delta_*, Xi_C(D_Delta_*|L), lambda or Lambda)
    -> T_eff_ab
```

or, after symmetry reduction,

```text
B :
  (...) -> (rho_eff(t), p_eff(t)).
```

It must satisfy all five conditions.

### P1. Covariant and domain-explicit

The bridge must specify:

- the spacetime domain or averaging foliation;
- gauge/observer dependence;
- whether it is a Buchert spatial average, light-cone fit, clock/lapse map,
  or another construction;
- units for `lambda`, `Lambda`, and `Xi_C`;
- how legal quotient directions are removed.

Without this, `lambda` is only a dual variable in an audit optimization.

### P2. Averaged constraint equations

The output must enter the averaged Friedmann constraints. For a reduced FLRW
chart, it must give equations of the form

```text
3 H_eff^2 = 8 pi G (rho_m,eff + rho_eff) - 3 k_eff/a_eff^2,
3 a_eff''/a_eff = -4 pi G (rho_m,eff + rho_eff + 3 p_eff),
```

or the exact Buchert/light-cone/clock analogue with every extra term named.

### P3. Bianchi / conservation consistency

The bridge must obey a conservation law:

```text
nabla^a T_eff_ab = 0
```

or state a precise exchange law with the averaged matter sector. In
symmetry-reduced form:

```text
rho_eff' + 3 H_eff (rho_eff + p_eff) = source/exchange,
```

with the source fixed before comparison.

### P4. Predictions

The bridge must predict, without fitting to dark-energy data:

```text
Omega_eff,
w_eff(z) = p_eff/rho_eff,
onset timing.
```

The staged requirements are:

```text
M0: sign and acceleration behavior,
M1: Omega_eff = O(0.1--1),
M2: Omega_eff ~= 0.68 plus onset and w(z) shape.
```

### P5. No Omega_Lambda normalization

The scale must come from declared physical inputs: averaging domain, density
contrast, lapse/volume fractions, light-cone map, audit covariance units, or
other predeclared quantities. It must not contain:

- a free multiplier chosen to hit `Omega_Lambda`;
- a hidden normalization in `C`, `Omega`, `W`, or `B`;
- a post-hoc chart map selected because it reproduces `w(z)`.

### Why Schur/KKT does not supply `B`

Schur and convex duality provide:

```text
Xi_C(D|L) >= 0,
lambda or Lambda prices the budgeted residual constraint.
```

They do not provide:

- tensor indices;
- covariance under spacetime diffeomorphisms;
- pressure;
- a continuity equation;
- an averaged curvature/backreaction split;
- a light-cone distance map;
- a clock/lapse model;
- a numerical energy-density scale in units of `rho_crit`.

Therefore Claim S cannot imply Claim P. The required extra input is
cosmological averaging/light-cone/clock physics plus a predeclared map from
the Schur residual coordinates into those physical variables.

## 5. LT1 Bottom Line

Claim S is a valid structural target under CQ plus strict budget-sensitivity:
a nonzero dual closure certificate exists and is explicitly paired with the
Schur residual. The overstrong active-constraint theorem is false and must not
be used.

The magnitude pre-mortem blocks any current claim of dark-energy derivation.
If the bridge is ordinary Buchert `Q_D`, the magnitude is too small: outcome
**B**. If the bridge is light-cone or clock/timescape-like, the magnitude can
be order unity only after a separate, fixed, non-normalized physics bridge is
specified: current outcome **C**. Only after Claim P is constructed and reaches
at least M1 can the derivation route move toward outcome **A**.
