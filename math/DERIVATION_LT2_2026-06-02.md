# WP-DERIV-LT2 Memo: Bounded Clock/F4 Bridge Pre-Mortem and LT1 Lean Capstone

Review correction (2026-10-01): this memo records a missing specified bridge,
not a proved universal impossibility or a uniqueness classification of all
physical models. The inventory in section 6 is not a formal non-factorization
proof: such a proof would require equal declared input records and unequal
bridge outputs. References to the only available route mean only the routes
examined in this bounded investigation. The historical Lean receipts below
are superseded for current verification by the dated mathematical review.

Status: LT2 bounded bridge pre-mortem plus Lean capstone report.

Governing inputs read first:

- `plan/EXTERNAL_RULING_DERIVATION_LT1_2026-06-02.md`.
- `plan/DERIVATION_DARK_ENERGY_AS_CLOSURE.md` v2, especially sections 7.5
  and 7.6.
- `math/DERIVATION_LT1_2026-06-02.md`.

## 0. Verdict

Output option: **(2) refutation / no fixed bridge presently specifiable.**

No no-amplifier SBT map

```text
B_clock :
  (Xi_C, lambda, D_wall/void, fixed early-time matching)
    -> (gamma(t), f_v(t), H_dressed(t), D_L(z))
```

is presently determined by F4 local-global obstruction plus F18 lawhood
descent. The only currently `O(1)`-capable route is a timescape-class
clock/lapse/volume model with additional physical closure relations. SBT can
state objectivity, descent, and no-overread tests for such a bridge, but it
does not select the bridge or its magnitude from `Xi_C`/`lambda`.

Outcome: **C** as the primary verdict: Claim S is structural and the clock
bridge is undefined/nonunique. Conditional **B** remains if the bridge is
forced back to ordinary Buchert `Q_D`. Outcome **A** is not supported. Outcome
**D** is not forced because the structural theorem and Lean capstone are
valid.

Banking statement: Six Birds does not derive the observed dark-energy
magnitude through any **established** bridge. This does not prove that no
possible future clock/light-cone bridge exists.

## 1. Target Bridge and Required Inputs

A positive LT2 bridge would have to output:

```text
gamma(t)      lapse, dt_bar = gamma d tau_wall
f_v(t)        void/volume fraction
H_dressed(t)  wall-observer dressed expansion
D_L(z)        dressed distance-redshift relation
```

from allowed inputs only:

```text
Xi_C, lambda, wall/void domain partition and curvature bookkeeping,
matter density, conservation equations, early-time matching,
observed/simulated void fraction with uncertainty,
fixed O_F4, fixed F18 lawhood criterion.
```

Forbidden inputs:

```text
gamma_0 or f_v(t) tuned to SN/Omega_Lambda,
obstruction weights selected after seeing D_L(z),
an arbitrary multiplier converting lambda into rho_crit units,
any post-hoc chart map.
```

The problem is dimensional and dynamical. `Xi_C` is an audit residual and
`lambda` is a scalar or matrix dual price in an optimization problem. Neither
has, by itself, the tensor/clock units, lapse evolution equation, or
wall/void conservation closure required to compute `gamma(t)` or `f_v(t)`.

## 2. LT2-A: F4 Gluing Extremality

Candidate form:

```text
(gamma, f_v) = argmin O_F4(gamma, f_v)
```

with fixed density/curvature bookkeeping, conservation, fixed early-time
boundary, and no SN fit.

A plausible symbolic functional would have to look like

```text
O_F4(gamma,f_v)
  = obstruction_to_gluing(
      SN_chart(gamma,f_v),
      BAO_chart(gamma,f_v),
      CMB_acoustic_chart(gamma,f_v),
      local_clock_chart(gamma,f_v))
    + conservation_penalty(gamma,f_v)
    + early_time_matching_penalty(gamma,f_v).
```

This does not yet define a no-amplifier bridge. To be determinate, the
functional needs:

1. chart maps from `(gamma,f_v)` to SN/BAO/CMB/local-clock observables;
2. norms and relative weights between chart residuals;
3. a conservation law for the wall/void sectors;
4. a lapse evolution equation or closure condition;
5. units connecting `Xi_C`/`lambda` to the clock variables.

If the chart maps and weights are chosen to reproduce the distance curve, the
construction is a fit. If the weights are arbitrary, the construction has a
hidden amplifier. If the lapse law is supplied from timescape physics, the
construction is timescape-class physics plus an SBT consistency audit, not an
SBT derivation.

Conclusion for LT2-A. The extremal `gamma(f_v)` does not follow from the
currently declared F4 obstruction alone. It must be supplied by an additional
physical lapse/volume closure relation. LT2-A fails as a positive bridge.

## 3. LT2-B: F18 Lawhood Descent

Candidate claim:

```text
Exactly one clock bridge descends through the access quotient across
SN / BAO / CMB-acoustic / local-clock charts.
```

This is not presently true as a specified theorem. F18 can reject a
chart-specific rule that fits SN only and fails to transport to BAO/CMB/clock
charts. But F18 does not currently select a unique bridge because many
inequivalent models can be made chart-stable once their physical maps are
declared:

- standard FLRW plus an effective dark component;
- timescape-class lapse/volume models;
- light-cone fitting models;
- calibration/clock reinterpretations;
- modified-gravity or effective-fluid charts.

The access quotient and transport law have not been specified tightly enough
to make uniqueness a theorem. In particular, no declared quotient forces one
specific lapse relation `gamma(f_v)`, one `f_v(t)` evolution, or one dressed
distance formula.

Conclusion for LT2-B. F18 supplies a descent/transport obligation and can
rule out SN-only fitting, but it does not presently select exactly one clock
bridge. LT2-B fails as a positive bridge.

## 4. LT2-C: Objectivity / No-Overread

Candidate criterion:

```text
wall/void time variables become objective only if they form a common quotient
across the relevant charts.
```

This is a valid SBT discipline. It gives a negative classification when the
clock variables do not descend to a common quotient:

```text
objectivity not earned.
```

But this criterion is not a bridge to dark-energy magnitude. It tells us when
not to overread a chart-dependent lapse as an objective cosmological source.
It does not compute `gamma(t)`, `f_v(t)`, `Omega_eff`, or `w(z)`.

Conclusion for LT2-C. The objectivity criterion is useful, but its positive
output is not a clock bridge. Its honest result here is "objectivity not yet
earned," hence no dark-energy derivation.

## 5. Five Pre-Registered Gates

| gate | status | reason |
|---|---|---|
| 1. No free `Omega_Lambda` normalizer | **Fail for any positive bridge currently specifiable** | Avoiding a normalizer leaves `O_F4` without weights/units/lapse law; adding them currently requires timescape physics or post-hoc chart weights. |
| 2. Predict `Omega_eff = O(0.1--1)` before fitting | **Fail** | O(1) scale can be asserted by timescape-like lapse/volume input, but is not predicted from `Xi_C`/`lambda`/F4/F18 alone. |
| 3. Onset `z lesssim 1` not by hand | **Fail/undetermined** | Nonlinear void growth can motivate low-redshift onset, but the current SBT data do not derive `f_v(t)` or onset from the Schur residual. |
| 4. Chart consistency | **Fail** | No fixed bridge currently predicts SN plus at least two of BAO, CMB acoustic scale, local-H0 reinterpretation, growth-boundary, or clock/age observable. |
| 5. Distinguish from timescape | **Fail** | No SBT-only prediction is presently specified: no fixed `O_F4 -> gamma(f_v)`, no no-free-parameter `f_v(t) <-> Xi_C`, no chart-descent theorem ruling out a class of timescape choices. |

Overall gate result: **fail**. The derivation route should bank at outcome
**C/B**, not proceed to a dark-energy derivation claim.

## 6. Bridge Inventory and Unresolved Construction

Assume a positive no-amplifier `B_clock` is presently specifiable from the
declared inputs. Then it must determine `gamma(t)` and `f_v(t)` without using
SN acceleration, `Omega_Lambda`, or post-hoc chart weights.

But the declared structural inputs have the following content:

1. `Xi_C` is a Schur adequacy residual: a PSD audit leftover between native
   and dissolving probe families.
2. `lambda` is a KKT/dual sensitivity certificate pricing a scalar or Loewner
   residual budget.
3. F4 classifies local-global gluing statuses.
4. F18 requires lawhood descent through an access quotient.

None of these supplies:

- a wall/void Einstein or Buchert evolution system;
- a lapse evolution law;
- a volume-fraction growth law;
- a dressed distance-redshift formula;
- a units-preserving map from audit energy to `rho_crit`;
- relative chart weights for SN/BAO/CMB/local-clock extremization.

Therefore this memo has not specified the map from those inputs. A formal
underdetermination theorem would additionally need two realizations with the
same declared inputs and different outputs; that construction is not given
here. The routes examined would need an additional physical
timescape/light-cone/averaging model. If that model is added, SBT can audit
its objectivity and descent, but the `O(1)` scale comes from the added physics,
not from F4/F18 or the Schur dual certificate.

Thus no fixed SBT clock bridge is specified here. The O(1) route examined
reduces to a timescape-class bridge plus SBT consistency criteria.

## 7. What Would Be Needed to Reopen Outcome A

Future work would need all of the following before any derivation claim:

1. a fixed functional `O_F4` with dimensioned terms and predeclared chart
   weights;
2. a physical relation from `Xi_C` or `lambda` to wall/void curvature,
   density, lapse, or volume variables;
3. a conservation/Bianchi-compatible wall/void evolution system;
4. a derived `gamma(f_v)` and `f_v(t)`, not fitted to SN;
5. predictions for `Omega_eff`, `w(z)`, onset, and at least two non-SN chart
   checks;
6. at least one prediction that rules out or restricts a timescape choice.

Until then, the banked result is a structural closure-price theorem plus an
honest bridge/magnitude boundary.

## 8. LT1 Lean Capstone Status

Files added/changed:

- `lean/SbtCosmo/Derivation/ClosurePrice.lean`
- `lean/lakefile.lean`
- `lean/README.md`
- `lean/manifests/coverage_table.md`
- `lean/manifests/trust_base.txt`

Mechanized structural receipts:

- `SbtCosmo.Derivation.ClosurePrice.active_zero_multiplier_counterexample_optimizer`
  proves `x=0` minimizes `x^2` over `x<=0`.
- `SbtCosmo.Derivation.ClosurePrice.active_not_implies_positive_multiplier`
  proves an active KKT witness with multiplier `0`, blocking
  active-implies-positive overclaiming.
- `SbtCosmo.Derivation.ClosurePrice.strict_sensitivity_positive_optimizer`
  proves `x=Omega` minimizes `(x-a)^2` over `x<=Omega` when `Omega<a`.
- `SbtCosmo.Derivation.ClosurePrice.strict_sensitivity_positive_kkt`
  proves the positive multiplier `lambda=2*(a-Omega)>0` for that strict case.
- `SbtCosmo.Derivation.ClosurePrice.schurEnergy` defines `tr(W Xi_C)` using
  the validated adequacy residual.
- `SbtCosmo.Derivation.ClosurePrice.closureLagrangian` defines
  `J + lambda*(tr(W Xi_C)-Omega)`.
- `SbtCosmo.Derivation.ClosurePrice.closure_lagrangian_pairing`
  exposes that structural Lagrangian pairing definitionally.

Build command:

```bash
cd lean && lake build SbtCosmoDerivation
```

Build result:

```text
✔ [3139/3140] Built SbtCosmo.Derivation.ClosurePrice (4.1s)
Build completed successfully (3140 jobs).
```

Full project build:

```bash
cd lean && lake build
```

Full build result:

```text
Build completed successfully (3150 jobs).
```

Lean honesty disclosure:

- No theorem states or implies that the structural certificate is dark energy.
- No `sorry`, `admit`, `axiom`, `opaque`, `constant`, or `native_decide` was
  introduced.
- New theorem axiom closures are recorded in `lean/manifests/trust_base.txt`;
  each is within `{propext, Classical.choice, Quot.sound}`.
