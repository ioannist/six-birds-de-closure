import SbtCosmo.Derivation.GroundNativeEscape
import SbtCosmo.Derivation.GroundMatrixCoordinates
namespace SbtCosmo.Derivation.GroundRealModeNormalize
noncomputable section
set_option maxHeartbeats 1000000
open GroundState GroundNativeLocal

theorem real_mode_full_unit (S R : Field ≃L[ℝ] Field) (b u : Field) (κ m ℓ : ℝ)
    {h : Field} (hh : h ≠ 0)
    (he : GroundNormalizedJacobian.normalizedJacobian b κ m u h = ℓ • h) :
    ∃ v : GroundNativePhase.State, ‖v‖ = 1 ∧ coordinateDerivative (S.prodCongr R) b κ m u v = ℓ • v := by
  let w : GroundNativePhase.State := (S.symm h, 0)
  have hw : w ≠ 0 := by
    intro hn
    have hz : S.symm h = 0 := congrArg Prod.fst hn
    have hh' : h = 0 := by simpa using congrArg S hz
    exact hh hh'
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hew : coordinateDerivative (S.prodCongr R) b κ m u w = ℓ • w := by
    rw [coordinateDerivative_blocks]
    apply Prod.ext
    · change S.symm (GroundNormalizedJacobian.normalizedJacobian b κ m u (S (S.symm h))) = ℓ • S.symm h
      simp [he]
    · simp [w]
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  · rw [map_smul, hew, smul_smul, smul_smul, mul_comm]
theorem determinant_zero_eigenmode {L : Field →L[ℝ] Field} {ℓ : ℝ}
    (hd : (GroundMatrixCoordinates.entries L - ℓ • (1 : GroundMatrixCoordinates.RMatrix)).det = 0) :
    ∃ h : Field, h ≠ 0 ∧ L h = ℓ • h := by
  obtain ⟨h, hn, hh⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨h, hn, ?_⟩
  have he : L h - ℓ • h = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hh
    convert hh using 1
    congr 1
    funext i
    rw [GroundLocalDynamics.linear_action_entries]
    rfl
  exact sub_eq_zero.mp he
theorem bracket_full_mode (S R : Field ≃L[ℝ] Field) (b u : Field) (κ m a c : ℝ)
    (hac : a < c)
    (hs : (GroundMatrixCoordinates.entries (GroundNormalizedJacobian.normalizedJacobian b κ m u) -
      a • (1 : GroundMatrixCoordinates.RMatrix)).det *
      (GroundMatrixCoordinates.entries (GroundNormalizedJacobian.normalizedJacobian b κ m u) -
      c • (1 : GroundMatrixCoordinates.RMatrix)).det < 0) :
    ∃ ell ∈ Set.Ioo a c, ∃ v : GroundNativePhase.State, ‖v‖ = 1 ∧
      coordinateDerivative (S.prodCongr R) b κ m u v = ell • v := by
  let f : ℝ → ℝ := fun t => (GroundMatrixCoordinates.entries
    (GroundNormalizedJacobian.normalizedJacobian b κ m u) - t • (1 : GroundMatrixCoordinates.RMatrix)).det
  have hc : Continuous f := (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  obtain ⟨ell, hell, hd⟩ := GroundParameterSpectrum.strict_sign_crossing hac hc.continuousOn hs
  obtain ⟨h, hh, he⟩ := determinant_zero_eigenmode hd
  obtain ⟨v, hv, heigen⟩ := real_mode_full_unit S R b u κ m ell hh he
  exact ⟨ell, hell, v, hv, heigen⟩
end
end SbtCosmo.Derivation.GroundRealModeNormalize
