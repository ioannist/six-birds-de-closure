import SbtCosmo.Derivation.GroundNativeLocal

/-! Full sixteen-real-coordinate row bounds for the State product sup norm.
Both off-diagonal real/imaginary blocks contribute to every row. -/
namespace SbtCosmo.Derivation.GroundStateRows
noncomputable section
set_option maxHeartbeats 3000000
open GroundState GroundNativePhase
open scoped BigOperators

def leftField (L : State →L[ℝ] State) : Field →L[ℝ] State := L.comp (ContinuousLinearMap.inl ℝ Field Field)
def rightField (L : State →L[ℝ] State) : Field →L[ℝ] State := L.comp (ContinuousLinearMap.inr ℝ Field Field)

theorem real_action_entries (L : State →L[ℝ] State) (x : State) (i : Fin 8) :
    (L x).1 i = ∑ j, (L (GroundLocalDynamics.column j, 0)).1 i * x.1 j +
      ∑ j, (L (0, GroundLocalDynamics.column j)).1 i * x.2 j := by
  have hR := GroundLocalDynamics.linear_action_entries
    ((ContinuousLinearMap.fst ℝ Field Field).comp (leftField L)) x.1 i
  have hI := GroundLocalDynamics.linear_action_entries
    ((ContinuousLinearMap.fst ℝ Field Field).comp (rightField L)) x.2 i
  change (L (x.1, 0)).1 i = ∑ j, (L (GroundLocalDynamics.column j, 0)).1 i * x.1 j at hR
  change (L (0, x.2)).1 i = ∑ j, (L (0, GroundLocalDynamics.column j)).1 i * x.2 j at hI
  rw [← hR, ← hI]
  change (L x).1 i = (L (x.1, 0)+L (0, x.2)).1 i
  rw [← map_add]
  simp

theorem imag_action_entries (L : State →L[ℝ] State) (x : State) (i : Fin 8) :
    (L x).2 i = ∑ j, (L (GroundLocalDynamics.column j, 0)).2 i * x.1 j +
      ∑ j, (L (0, GroundLocalDynamics.column j)).2 i * x.2 j := by
  have hR := GroundLocalDynamics.linear_action_entries
    ((ContinuousLinearMap.snd ℝ Field Field).comp (leftField L)) x.1 i
  have hI := GroundLocalDynamics.linear_action_entries
    ((ContinuousLinearMap.snd ℝ Field Field).comp (rightField L)) x.2 i
  change (L (x.1, 0)).2 i = ∑ j, (L (GroundLocalDynamics.column j, 0)).2 i * x.1 j at hR
  change (L (0, x.2)).2 i = ∑ j, (L (0, GroundLocalDynamics.column j)).2 i * x.2 j at hI
  rw [← hR, ← hI]
  change (L x).2 i = (L (x.1, 0)+L (0, x.2)).2 i
  rw [← map_add]
  simp

theorem scalar_row_bound (A B : Fin 8 → ℝ) (x : State) {q : ℝ}
    (hr : (∑ j, (|A j|+|B j|)) ≤ q) :
    |(∑ j, A j*x.1 j)+(∑ j, B j*x.2 j)| ≤ q*‖x‖ := by
  have hR (j : Fin 8) : |x.1 j| ≤ ‖x‖ := by
    have hp : |x.1 j| ≤ ‖x.1‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.1 j
    exact hp.trans (by rw [Prod.norm_def]; exact le_max_left _ _)
  have hI (j : Fin 8) : |x.2 j| ≤ ‖x‖ := by
    have hp : |x.2 j| ≤ ‖x.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.2 j
    exact hp.trans (by rw [Prod.norm_def]; exact le_max_right _ _)
  rw [← Finset.sum_add_distrib]
  calc
    |∑ j, (A j*x.1 j+B j*x.2 j)| ≤ ∑ j, |A j*x.1 j+B j*x.2 j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (|A j|+|B j|)*‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        |A j*x.1 j+B j*x.2 j| ≤ |A j*x.1 j|+|B j*x.2 j| := abs_add_le _ _
        _ ≤ |A j| *‖x‖+|B j| *‖x‖ := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hR j) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hI j) (abs_nonneg _))
        _ = (|A j|+|B j|)*‖x‖ := by ring
    _ = (∑ j, (|A j|+|B j|))*‖x‖ := by rw [Finset.sum_mul]
    _ ≤ q*‖x‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg x)

theorem operator_norm_le_rows (L : State →L[ℝ] State) {q : ℝ} (hq : 0 ≤ q)
    (hR : ∀ i, (∑ j, (|(L (GroundLocalDynamics.column j, 0)).1 i|+
      |(L (0, GroundLocalDynamics.column j)).1 i|)) ≤ q)
    (hI : ∀ i, (∑ j, (|(L (GroundLocalDynamics.column j, 0)).2 i|+
      |(L (0, GroundLocalDynamics.column j)).2 i|)) ≤ q) : ‖L‖ ≤ q := by
  apply L.opNorm_le_bound hq
  intro x
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg x))).mpr
    intro i
    rw [Real.norm_eq_abs, real_action_entries]
    exact scalar_row_bound _ _ x (hR i)
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg x))).mpr
    intro i
    rw [Real.norm_eq_abs, imag_action_entries]
    exact scalar_row_bound _ _ x (hI i)

theorem field_operator_norm_le_rows (L : State →L[ℝ] Field) {q : ℝ} (hq : 0 ≤ q)
    (hR : ∀ i, (∑ j, (|L (GroundLocalDynamics.column j, 0) i|+
      |L (0, GroundLocalDynamics.column j) i|)) ≤ q) : ‖L‖ ≤ q := by
  apply L.opNorm_le_bound hq
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg x))).mpr
  intro i
  have he := real_action_entries (L.prod (0 : State →L[ℝ] Field)) x i
  change L x i = ∑ j, L (GroundLocalDynamics.column j, 0) i*x.1 j +
    ∑ j, L (0, GroundLocalDynamics.column j) i*x.2 j at he
  rw [Real.norm_eq_abs, he]
  exact scalar_row_bound _ _ x (hR i)


end
end SbtCosmo.Derivation.GroundStateRows
