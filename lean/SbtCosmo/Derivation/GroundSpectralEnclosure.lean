import SbtCosmo.Derivation.GroundDeterminantDefect
import SbtCosmo.Derivation.GroundTriangularArithmetic

/-! Exact entry-box tests return to determinant signs of actual real operators.
The preconditioner and its triangular factors are data with checked obligations. -/
namespace SbtCosmo.Derivation.GroundSpectralEnclosure
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundMatrixCoordinates GroundRationalInterval GroundDeterminantDefect
open scoped BigOperators

abbrev Box := Matrix (Fin 8) (Fin 8) Interval

def shifted (B : Box) (ell : ℚ) (i j : Fin 8) : Interval :=
  (B i j).add (Interval.point (-ell * (if i = j then 1 else 0)))

theorem shifted_sound (B : Box) (L : Field →L[ℝ] Field) (ell : ℚ)
    (hB : ∀ i j, (B i j).Contains (entries L i j)) (i j : Fin 8) :
    (shifted B ell i j).Contains ((entries L - (ell : ℝ) • (1 : RMatrix)) i j) := by
  have h := Interval.add_sound (hB i j)
    (Interval.point_sound (-ell * (if i = j then 1 else 0)))
  by_cases hij : i = j <;>
    simpa [shifted, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij] using h

def defectExpr (C : QMatrix) (i j : Fin 8) : Expr (Fin 8 × Fin 8) :=
  .add (.const (if i = j then 1 else 0))
    (.neg (Expr.sum (fun k => .mul (.const (C i k)) (.var (k,j)))))

def defects (C : QMatrix) (B : Box) (i j : Fin 8) : Interval :=
  (defectExpr C i j).enclose (fun k => B k.1 k.2)

theorem defectExpr_return (C : QMatrix) (A : RMatrix) (i j : Fin 8) :
    (defectExpr C i j).eval (fun k => A k.1 k.2) = (1 - realMatrix C * A) i j := by
  by_cases hij : i = j <;>
    simp [defectExpr, Expr.eval, Expr.eval_sum, Matrix.sub_apply,
      Matrix.mul_apply, realMatrix, hij, sub_eq_add_neg]

structure Arithmetic (C : QMatrix) (B : Box) (q : ℚ) : Prop where
  nonneg : 0 ≤ q
  lt_one : q < 1
  rows : ∀ i, (∑ j, (defects C B i j).bound) ≤ q

theorem defect_norm {C : QMatrix} {B : Box} {q : ℚ}
    (h : Arithmetic C B q) (A : RMatrix) (hB : ∀ i j, (B i j).Contains (A i j)) :
    ‖fieldMap (1 - realMatrix C * A)‖ ≤ (q : ℝ) := by
  apply GroundLocalDynamics.operator_norm_le_rows _ (by exact_mod_cast h.nonneg)
  intro i
  have he := fieldMap_entries (1 - realMatrix C * A)
  calc
    _ = ∑ j, |(1 - realMatrix C * A) i j| := by
      change (∑ j, |entries (fieldMap (1 - realMatrix C * A)) i j|) = _
      rw [he]
    _ ≤ ∑ j, ((defects C B i j).bound : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hc := Expr.enclose_sound (defectExpr C i j) (fun k => hB k.1 k.2)
      rw [defectExpr_return] at hc
      exact Interval.abs_le_bound hc
    _ ≤ (q : ℝ) := by exact_mod_cast h.rows i

theorem determinant_product {C : QMatrix} {B : Box} {q : ℚ}
    (h : Arithmetic C B q) (A : RMatrix) (hB : ∀ i j, (B i j).Contains (A i j)) :
    0 < (realMatrix C).det * A.det :=
  preconditioned_det_product _ _ ((defect_norm h A hB).trans_lt (by exact_mod_cast h.lt_one))

theorem product_sign_return {s a b : ℝ} (hc : 0 < s * a) (hp : 0 < a * b) : 0 < s * b := by
  rcases mul_pos_iff.mp hc with ⟨hs, ha⟩ | ⟨hs, ha⟩ <;>
    rcases mul_pos_iff.mp hp with ⟨ha', hb⟩ | ⟨ha', hb⟩
  · exact mul_pos hs hb
  · linarith
  · linarith
  · exact mul_pos_of_neg_of_neg hs hb

theorem actual_shifted_sign {C : QMatrix} {B : Box} {q ell : ℚ} {s : ℤ}
    (h : Arithmetic C (shifted B ell) q) (L : Field →L[ℝ] Field)
    (hB : ∀ i j, (B i j).Contains (entries L i j))
    (hc : 0 < (s : ℝ) * (realMatrix C).det) :
    0 < (s : ℝ) * (entries L - (ell : ℝ) • (1 : RMatrix)).det :=
  product_sign_return hc (determinant_product h _ (shifted_sound B L ell hB))
end
end SbtCosmo.Derivation.GroundSpectralEnclosure
