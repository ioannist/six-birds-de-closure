import SbtCosmo.Derivation.GroundRationalInterval
import SbtCosmo.Derivation.GroundPointCoordinates

/-! A rational expression model returned to the actual sourced nine equations,
their already earned derivative, and the actual Newton defect. The enclosure
soundness theorem proves real bounds from computable rational comparisons. -/
namespace SbtCosmo.Derivation.GroundResidualEnclosure
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundRootCertificate GroundRationalInterval
open GroundPointCoordinates
open scoped BigOperators

inductive Variable where
  | background : Fin 8 → Variable
  | coupling : Variable
  | state : Fin 9 → Variable
  deriving DecidableEq

abbrev Expression := Expr Variable
instance : Add Expression := ⟨Expr.add⟩
instance : Neg Expression := ⟨Expr.neg⟩
instance : Sub Expression := ⟨fun a b => a + -b⟩
instance : Mul Expression := ⟨Expr.mul⟩
instance (n : ℕ) : OfNat Expression n := ⟨Expr.const n⟩

def valuation (b : Field) (κ : ℝ) (x : Point) : Variable → ℝ
  | .background i => b i
  | .coupling => κ
  | .state j => coord x j

def uExpr (i : Fin 8) : Expression := .var (.state i.castSucc)
def energyExpr : Expression := .var (.state (Fin.last 8))
def gradExpr (i : Fin 8) : Expression :=
  (uExpr (next i) - uExpr (prev i)) * .const (1/2)
def sourceExpr (i : Fin 8) : Expression :=
  .var (.background i) + .var .coupling *
    (gradExpr i * gradExpr i + .var (.background i) * uExpr i * uExpr i)

def residualExpr : Fin 9 → Expression := Fin.lastCases
  ((Expr.sum (fun i : Fin 8 => uExpr i * uExpr i) - 1) * .const (1/2))
  (fun i => (1 + sourceExpr i - energyExpr) * uExpr i -
    (uExpr (prev i) + uExpr (next i)) * .const (1/2))

def basisField (j : Fin 9) (i : Fin 8) : ℚ := if i.castSucc = j then 1 else 0
def basisEnergy (j : Fin 9) : ℚ := if Fin.last 8 = j then 1 else 0
def sourceColumnExpr (i : Fin 8) (j : Fin 9) : Expression :=
  2 * .var .coupling *
    (gradExpr i * .const ((basisField j (next i) - basisField j (prev i))/2) +
     .var (.background i) * uExpr i * .const (basisField j i))

def derivativeExpr (j : Fin 9) : Fin 9 → Expression := Fin.lastCases
  (Expr.sum (fun i : Fin 8 => uExpr i * .const (basisField j i)))
  (fun i => sourceColumnExpr i j * uExpr i +
    (1 + sourceExpr i - energyExpr) * .const (basisField j i) -
    .const ((basisField j (prev i) + basisField j (next i))/2) -
    .const (basisEnergy j) * uExpr i)

theorem eval_uExpr (b : Field) (κ : ℝ) (x : Point) (i : Fin 8) :
    (uExpr i).eval (valuation b κ x) = x.1 i := by
  simp only [uExpr, Expr.eval, valuation, coord, Fin.lastCases_castSucc]

theorem eval_energyExpr (b : Field) (κ : ℝ) (x : Point) :
    energyExpr.eval (valuation b κ x) = x.2 := by
  simp only [energyExpr, Expr.eval, valuation, coord, Fin.lastCases_last]

theorem eval_gradExpr (b : Field) (κ : ℝ) (x : Point) (i : Fin 8) :
    (gradExpr i).eval (valuation b κ x) = GroundState.gradient x.1 i := by
  simp [gradExpr, Expr.eval, eval_uExpr, GroundState.gradient]
  ring

theorem eval_sourceExpr (b : Field) (κ : ℝ) (x : Point) (i : Fin 8) :
    (sourceExpr i).eval (valuation b κ x) = sourcePotential b κ x.1 i := by
  simp only [sourceExpr, Expr.eval, valuation, eval_uExpr, eval_gradExpr,
    sourcePotential, BackgroundSelection.potential]
  ring

theorem residualExpr_return (b : Field) (κ : ℝ) (x : Point) (j : Fin 9) :
    (residualExpr j).eval (valuation b κ x) = coord (residual b κ x) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [residualExpr, coord, Fin.lastCases_last]
    simp [Expr.eval, Expr.eval_sum, eval_uExpr, GroundRootCertificate.residual,
      GroundEquations.equations, normSq, pow_two]
    ring
  · simp only [residualExpr, coord, Fin.lastCases_castSucc]
    simp [Expr.eval, eval_uExpr, eval_sourceExpr, eval_energyExpr, GroundRootCertificate.residual,
      GroundEquations.equations, shifted, hamiltonian]
    ring

theorem basisField_return (j : Fin 9) (i : Fin 8) :
    (basisField j i : ℝ) = (column j).1 i := by
  by_cases h : i.castSucc = j <;> simp [basisField, column, fromCoord, Pi.single_apply, h]

theorem basisEnergy_return (j : Fin 9) : (basisEnergy j : ℝ) = (column j).2 := by
  by_cases h : (8 : Fin 9) = j <;> simp [basisEnergy, column, fromCoord, Pi.single_apply, h]

theorem derivativeExpr_return (b : Field) (κ : ℝ) (x : Point) (j i : Fin 9) :
    (derivativeExpr j i).eval (valuation b κ x) = coord (residualDerivative b κ x (column j)) i := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [derivativeExpr, coord, Fin.lastCases_last]
    simp [Expr.eval_sum, Expr.eval, eval_uExpr, basisField_return, residualDerivative_apply, dot]
  · simp only [derivativeExpr, coord, Fin.lastCases_castSucc]
    simp [sourceColumnExpr, Expr.eval, valuation, eval_uExpr, eval_gradExpr,
      eval_sourceExpr, eval_energyExpr, basisField_return, basisEnergy_return,
      residualDerivative_apply, GroundSourceJacobian.sourceDerivative_apply,
      shifted, hamiltonian, GroundState.gradient]
    ring

def preconditioner (C : Matrix (Fin 9) (Fin 9) ℚ) : Point →L[ℝ] Point :=
  matrixMap (fun i j => (C i j : ℝ))

def correctedResidualExpr (C : Matrix (Fin 9) (Fin 9) ℚ) (i : Fin 9) : Expression :=
  Expr.sum (fun j => .const (C i j) * residualExpr j)

def defectExpr (C : Matrix (Fin 9) (Fin 9) ℚ) (i j : Fin 9) : Expression :=
  .const (if i = j then 1 else 0) - Expr.sum (fun a => .const (C i a) * derivativeExpr j a)

theorem correctedResidualExpr_return (C : Matrix (Fin 9) (Fin 9) ℚ)
    (b : Field) (κ : ℝ) (x : Point) (i : Fin 9) :
    (correctedResidualExpr C i).eval (valuation b κ x) =
      coord (preconditioner C (residual b κ x)) i := by
  simp [correctedResidualExpr, Expr.eval_sum, Expr.eval, residualExpr_return,
    preconditioner, matrixMap_apply]

theorem defectExpr_return (C : Matrix (Fin 9) (Fin 9) ℚ)
    (b : Field) (κ : ℝ) (x : Point) (i j : Fin 9) :
    (defectExpr C i j).eval (valuation b κ x) =
      coord (correctionDerivative b κ (preconditioner C) x (column j)) i := by
  change (defectExpr C i j).eval (valuation b κ x) =
    coord (column j - matrixMap (fun i j => (C i j : ℝ)) (residualDerivative b κ x (column j))) i
  rw [coord_sub, coord_column, matrixMap_apply]
  by_cases hij : i = j <;>
    simp [defectExpr, Expr.eval_sum, Expr.eval, derivativeExpr_return, hij, sub_eq_add_neg]

theorem defect_norm_bound (C : Matrix (Fin 9) (Fin 9) ℚ) (B : Variable → Interval)
    (b : Field) (κ : ℝ) (x : Point) {q : ℚ} (hq : 0 ≤ q)
    (hB : ∀ v, (B v).Contains (valuation b κ x v))
    (hrows : ∀ i, (∑ j, ((defectExpr C i j).enclose B).bound) ≤ q) :
    ‖correctionDerivative b κ (preconditioner C) x‖ ≤ (q : ℝ) := by
  apply operator_norm_le_rows _ (by exact_mod_cast hq)
  intro i
  calc
    (∑ j, |coord (correctionDerivative b κ (preconditioner C) x (column j)) i|) ≤
        ∑ j, (((defectExpr C i j).enclose B).bound : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← defectExpr_return]
      exact Interval.abs_le_bound ((defectExpr C i j).enclose_sound hB)
    _ ≤ q := by exact_mod_cast hrows i

theorem corrected_residual_norm_bound (C : Matrix (Fin 9) (Fin 9) ℚ) (B : Variable → Interval)
    (b : Field) (κ : ℝ) (x : Point) {y : ℚ} (hy : 0 ≤ y)
    (hB : ∀ v, (B v).Contains (valuation b κ x v))
    (hbound : ∀ i, ((correctedResidualExpr C i).enclose B).bound ≤ y) :
    ‖preconditioner C (residual b κ x)‖ ≤ (y : ℝ) := by
  apply norm_le_coordinates (by exact_mod_cast hy)
  intro i
  rw [← correctedResidualExpr_return]
  exact (Interval.abs_le_bound ((correctedResidualExpr C i).enclose_sound hB)).trans
    (by exact_mod_cast hbound i)

end
end SbtCosmo.Derivation.GroundResidualEnclosure
