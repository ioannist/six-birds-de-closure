import SbtCosmo.Derivation.GroundMatrixCoordinates
namespace SbtCosmo.Derivation.GroundDeterminantDefect
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundMatrixCoordinates
open scoped BigOperators

theorem small_norm_det_ne_zero (L : Field →L[ℝ] Field) (hn : ‖L‖ < 1) :
    (1 - entries L).det ≠ 0 := by
  intro hd
  obtain ⟨h, hh, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have he : h - L h = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hk
    convert hk using 1
    congr 1
    funext i
    rw [GroundLocalDynamics.linear_action_entries]
    rfl
  have hfix : h = L h := sub_eq_zero.mp he
  have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hb := L.le_opNorm h
  rw [← hfix] at hb
  nlinarith

theorem entries_smul (t : ℝ) (L : Field →L[ℝ] Field) : entries (t • L) = t • entries L := by
  ext i j
  rfl

theorem small_norm_det_positive (L : Field →L[ℝ] Field) (hn : ‖L‖ < 1) :
    0 < (1 - entries L).det := by
  let f : ℝ → ℝ := fun t => (1 - t • entries L).det
  have hc : Continuous f := (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  have h0 : f 0 = 1 := by simp [f]
  have h1 : f 1 = (1 - entries L).det := by simp [f]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht
    have hl : ‖t • L‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc
        t * ‖L‖ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg L)
        _ < 1 := by simpa using hn
    simpa only [f, entries_smul] using small_norm_det_ne_zero (t • L) hl
  by_contra hp
  have hm : f 1 < 0 := by
    have hh : f 1 ≠ 0 := hne 1 ⟨by norm_num, le_rfl⟩
    rw [h1] at hh
    rw [h1]
    exact lt_of_le_of_ne (le_of_not_gt hp) hh
  have hz : (0 : ℝ) ∈ f '' Set.Icc 0 1 :=
    intermediate_value_Icc' (by norm_num) hc.continuousOn ⟨hm.le, by rw [h0]; norm_num⟩
  obtain ⟨t, ht, he⟩ := hz
  exact hne t ht he
def fieldMap (A : RMatrix) : Field →L[ℝ] Field := (Matrix.toLin' A).toContinuousLinearMap

theorem fieldMap_entries (A : RMatrix) : entries (fieldMap A) = A := by
  ext i j
  change (A.mulVec (GroundLocalDynamics.column j)) i = A i j
  simp [Matrix.mulVec, dotProduct, GroundLocalDynamics.column, Pi.single_apply]

theorem preconditioned_det_product (C B : RMatrix)
    (h : ‖fieldMap (1 - C * B)‖ < 1) : 0 < C.det * B.det := by
  have hp := small_norm_det_positive (fieldMap (1 - C * B)) h
  simpa only [fieldMap_entries, sub_sub_cancel, Matrix.det_mul] using hp

end
end SbtCosmo.Derivation.GroundDeterminantDefect
