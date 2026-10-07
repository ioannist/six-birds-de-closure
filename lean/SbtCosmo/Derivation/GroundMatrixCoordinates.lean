import SbtCosmo.Derivation.GroundOriginalResponses

/-! Exact rational coordinate bases and interval row bounds for actual linear
maps. Inverse identities are arithmetic obligations, rather than an assumed
change of coordinates or an externally supplied derivative matrix. -/
namespace SbtCosmo.Derivation.GroundMatrixCoordinates
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundRationalInterval
open scoped BigOperators

abbrev QMatrix := Matrix (Fin 8) (Fin 8) ℚ
abbrev RMatrix := Matrix (Fin 8) (Fin 8) ℝ

def realMatrix (A : QMatrix) : RMatrix := fun i j => (A i j : ℝ)

structure InverseArithmetic (S P : QMatrix) : Prop where
  left : P * S = 1
  right : S * P = 1

theorem realMatrix_mul (A B : QMatrix) :
    realMatrix (A * B) = realMatrix A * realMatrix B := by
  ext i j
  simp [realMatrix, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul]

theorem realMatrix_one : realMatrix 1 = 1 := by
  ext i j
  by_cases h : i = j <;> simp [realMatrix, Matrix.one_apply, h]

def basis {S P : QMatrix} (h : InverseArithmetic S P) : Field ≃L[ℝ] Field :=
  (Matrix.toLin'OfInv
    (show realMatrix P * realMatrix S = 1 by rw [← realMatrix_mul, h.left, realMatrix_one])
    (show realMatrix S * realMatrix P = 1 by rw [← realMatrix_mul, h.right, realMatrix_one])).toContinuousLinearEquiv

theorem basis_apply {S P : QMatrix} (h : InverseArithmetic S P) (x : Field) (i : Fin 8) :
    basis h x i = ∑ j, (S i j : ℝ) * x j := by
  rfl

theorem basis_symm_apply {S P : QMatrix} (h : InverseArithmetic S P) (x : Field) (i : Fin 8) :
    (basis h).symm x i = ∑ j, (P i j : ℝ) * x j := by
  rfl

def entries (L : Field →L[ℝ] Field) : RMatrix :=
  fun i j => L (GroundLocalDynamics.column j) i

def conjugate (T : Field ≃L[ℝ] Field) (L : Field →L[ℝ] Field) : Field →L[ℝ] Field :=
  T.symm.toContinuousLinearMap.comp (L.comp T.toContinuousLinearMap)

theorem conjugate_entries {S P : QMatrix} (h : InverseArithmetic S P)
    (L : Field →L[ℝ] Field) (i j : Fin 8) :
    entries (conjugate (basis h) L) i j =
      ∑ a, ∑ b, (P i a : ℝ) * entries L a b * (S b j : ℝ) := by
  change (basis h).symm (L (basis h (GroundLocalDynamics.column j))) i = _
  rw [basis_symm_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [GroundLocalDynamics.linear_action_entries, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [basis_apply, GroundLocalDynamics.column, Pi.single_apply]
  simp [entries, GroundLocalDynamics.column, mul_assoc]

def transformExpr (S P : QMatrix) (i j : Fin 8) : Expr (Fin 8 × Fin 8) :=
  Expr.sum (fun a => Expr.sum (fun b =>
    .mul (.mul (.const (P i a)) (.var (a,b))) (.const (S b j))))

def transformed (S P : QMatrix) (B : Matrix (Fin 8) (Fin 8) Interval)
    (i j : Fin 8) : Interval := (transformExpr S P i j).enclose (fun k => B k.1 k.2)

theorem transformExpr_return {S P : QMatrix} (h : InverseArithmetic S P)
    (L : Field →L[ℝ] Field) (i j : Fin 8) :
    (transformExpr S P i j).eval (fun k => entries L k.1 k.2) =
      entries (conjugate (basis h) L) i j := by
  rw [conjugate_entries]
  simp only [transformExpr, Expr.eval_sum, Expr.eval]

theorem transformed_sound {S P : QMatrix} (h : InverseArithmetic S P)
    (L : Field →L[ℝ] Field) (B : Matrix (Fin 8) (Fin 8) Interval)
    (hB : ∀ a b, (B a b).Contains (entries L a b)) (i j : Fin 8) :
    (transformed S P B i j).Contains (entries (conjugate (basis h) L) i j) := by
  rw [← transformExpr_return h L i j]
  exact Expr.enclose_sound _ (fun k => hB k.1 k.2)

structure RowArithmetic (S P : QMatrix) (B : Matrix (Fin 8) (Fin 8) Interval) (q : ℚ) : Prop where
  nonneg : 0 ≤ q
  rows : ∀ i, (∑ j, (transformed S P B i j).bound) ≤ q

theorem conjugate_rows {S P : QMatrix} (h : InverseArithmetic S P)
    (L : Field →L[ℝ] Field) (B : Matrix (Fin 8) (Fin 8) Interval) {q : ℚ}
    (hq : RowArithmetic S P B q) (hB : ∀ a b, (B a b).Contains (entries L a b)) (i : Fin 8) :
    (∑ j, |entries (conjugate (basis h) L) i j|) ≤ (q : ℝ) := by
  calc
    _ ≤ ∑ j, ((transformed S P B i j).bound : ℝ) :=
      Finset.sum_le_sum (fun j _ => Interval.abs_le_bound (transformed_sound h L B hB i j))
    _ ≤ (q : ℝ) := by exact_mod_cast hq.rows i

theorem conjugate_norm {S P : QMatrix} (h : InverseArithmetic S P)
    (L : Field →L[ℝ] Field) (B : Matrix (Fin 8) (Fin 8) Interval) {q : ℚ}
    (hq : RowArithmetic S P B q) (hB : ∀ a b, (B a b).Contains (entries L a b)) :
    ‖conjugate (basis h) L‖ ≤ (q : ℝ) :=
  GroundLocalDynamics.operator_norm_le_rows _ (by exact_mod_cast hq.nonneg)
    (conjugate_rows h L B hq hB)

def imaginaryExpr (i j : Fin 8) : GroundResidualEnclosure.Expression :=
  .mul (.const (1/2)) (.add (.const (if i = j then 1 else 0))
    (.neg (.mul (GroundResidualEnclosure.uExpr i) (GroundResidualEnclosure.uExpr j))))

def imaginaryIntervals (β : Fin 8 → ℚ) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    (i j : Fin 8) : Interval :=
  (imaginaryExpr i j).enclose (GroundKernelTube.box β a a z r)

theorem imaginaryExpr_return (b : Field) (κ : ℝ) (x : GroundBorder.Point) (i j : Fin 8) :
    (imaginaryExpr i j).eval (GroundResidualEnclosure.valuation b κ x) =
      entries (GroundNativeJacobian.imaginaryDerivative (1/2) x.1) i j := by
  rw [entries, GroundNativeJacobian.imaginaryDerivative_apply]
  by_cases hij : i = j <;>
    simp [imaginaryExpr, Expr.eval, GroundResidualEnclosure.eval_uExpr,
      GroundLocalDynamics.column, Pi.single_apply, GroundBorder.dot, hij]
  all_goals ring

theorem imaginaryIntervals_sound (β : Fin 8 → ℚ) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    {x : GroundBorder.Point}
    (hx : x ∈ Metric.closedBall (GroundKernelTube.center z) (r : ℝ)) (i j : Fin 8) :
    (imaginaryIntervals β a z r i j).Contains
      (entries (GroundNativeJacobian.imaginaryDerivative (1/2) x.1) i j) := by
  rw [← imaginaryExpr_return (GroundKernelTube.background β) (a : ℝ) x i j]
  exact Expr.enclose_sound _ (GroundKernelTube.box_sound β a a z r ⟨le_rfl, le_rfl⟩ hx)

end
end SbtCosmo.Derivation.GroundMatrixCoordinates
