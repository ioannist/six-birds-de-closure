import SbtCosmo.Adequacy.Reconciliation
import Mathlib.Tactic

/-!
LT1/LT2 structural closure-price capstone.

This module mechanizes only the finite structural witnesses from the LT1 memo:
an active constraint can have zero multiplier, a strict-sensitivity quadratic
witness has a positive multiplier, and a scalar Lagrangian can pair a dual
certificate with the validated Schur adequacy residual. It proves no
Friedmann-source, clock-bridge, or dark-energy claim.
-/

open Matrix
open scoped Matrix

namespace SbtCosmo.Derivation.ClosurePrice

noncomputable section

variable {n m : Type*}

/-- One-dimensional KKT conditions for a single inequality constraint.

The arguments are the objective gradient at the candidate point, the
constraint gradient, the constraint value `g(x)`, and the multiplier.
-/
structure KKT1D (objectiveGradient constraintGradient constraintValue lambda : ℝ) : Prop where
  dual_nonnegative : 0 ≤ lambda
  stationarity : objectiveGradient + lambda * constraintGradient = 0
  complementarity : lambda * constraintValue = 0
  feasibility : constraintValue ≤ 0

/-- A scalar inequality constraint is active when its value is zero. -/
def ActiveConstraint (constraintValue : ℝ) : Prop :=
  constraintValue = 0

/-- In the problem `min x^2` subject to `x ≤ 0`, `x=0` is an optimizer.

This is included to make the zero-multiplier witness a genuine optimization
example, not just an isolated KKT tuple.
-/
theorem active_zero_multiplier_counterexample_optimizer
    {x : ℝ} (_hx : x ≤ 0) :
    (0 : ℝ)^2 ≤ x^2 := by
  simpa using sq_nonneg x

/-- Active constraint plus KKT does not force a positive multiplier.

For `min x^2` subject to `x ≤ 0` at `x=0`, the constraint is active and the
KKT multiplier `lambda=0` satisfies stationarity and complementarity.
-/
theorem active_not_implies_positive_multiplier :
    ActiveConstraint (0 : ℝ) ∧ KKT1D 0 1 0 0 ∧ ¬ (0 < (0 : ℝ)) := by
  constructor
  · rfl
  constructor
  · constructor <;> norm_num
  · norm_num

/-- For `Omega<a`, `x=Omega` minimizes `(x-a)^2` over the half-line `x≤Omega`. -/
theorem strict_sensitivity_positive_optimizer
    {a Omega x : ℝ} (hOmega_a : Omega < a) (hx : x ≤ Omega) :
    (Omega - a)^2 ≤ (x - a)^2 := by
  nlinarith [sq_nonneg (x - Omega), hOmega_a, hx]

/-- Strict-sensitivity quadratic witness: active constraint and positive multiplier.

For `min (x-a)^2` subject to `x≤Omega`, with `Omega<a`, the candidate
`x=Omega` has KKT multiplier `lambda = 2*(a-Omega) > 0`.
-/
theorem strict_sensitivity_positive_kkt
    {a Omega : ℝ} (hOmega_a : Omega < a) :
    KKT1D (2 * (Omega - a)) 1 (Omega - Omega) (2 * (a - Omega)) ∧
      0 < 2 * (a - Omega) := by
  constructor
  · constructor
    · linarith
    · ring
    · ring
    · norm_num
  · linarith

/-- A linear utility offset rebases the price only while the budget remains
active and the rebased dual remains nonnegative. This is not invariance under
an arbitrary additive constant in a physical stress-energy source. -/
theorem active_kkt_linear_offset {gradient value lambda offset : ℝ}
    (h : KKT1D gradient 1 value lambda) (hactive : value = 0)
    (hrebase : 0 ≤ lambda + offset) :
    KKT1D (gradient - offset) 1 value (lambda + offset) := by
  constructor
  · exact hrebase
  · have hs := h.stationarity
    linarith
  · rw [hactive]
    ring
  · exact h.feasibility

/-- On a fixed equality-budget face, the offset is the same additive constant
for every candidate, so utility order is unchanged. -/
theorem equality_budget_offset_order_iff (ux uy budget offset : ℝ) :
    ux + offset * budget ≤ uy + offset * budget ↔ ux ≤ uy := by
  constructor <;> intro h <;> linarith

/-- Scalar Schur energy `tr(W Xi_C)` using the validated T3 adequacy residual. -/
def schurEnergy [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (W : Matrix m m ℝ) (KLL : Matrix n n ℝ) (KLD : Matrix n m ℝ)
    (KDD : Matrix m m ℝ) : ℝ :=
  Matrix.trace (W * SbtCosmo.Adequacy.Reconciliation.adequacyResidual KLL KLD KDD)

/-- Structural Lagrangian pairing a scalar certificate with Schur energy.

`J` is a scalar objective value at the candidate, `lambda` is the structural
dual certificate, and `Omega` is the scalar adequacy budget. This definition
does not assign physical units or an effective stress-energy interpretation.
-/
def closureLagrangian [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J lambda Omega : ℝ) (W : Matrix m m ℝ) (KLL : Matrix n n ℝ)
    (KLD : Matrix n m ℝ) (KDD : Matrix m m ℝ) : ℝ :=
  J + lambda * (schurEnergy W KLL KLD KDD - Omega)

/-- The capstone Lagrangian is exactly the `lambda * tr(W Xi_C)` structural pairing. -/
theorem closure_lagrangian_pairing
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J lambda Omega : ℝ) (W : Matrix m m ℝ) (KLL : Matrix n n ℝ)
    (KLD : Matrix n m ℝ) (KDD : Matrix m m ℝ) :
    closureLagrangian J lambda Omega W KLL KLD KDD =
      J + lambda *
        (Matrix.trace
          (W * SbtCosmo.Adequacy.Reconciliation.adequacyResidual KLL KLD KDD) -
            Omega) := by
  rfl

end

end SbtCosmo.Derivation.ClosurePrice
