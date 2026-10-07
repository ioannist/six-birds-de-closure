import SbtCosmo.Derivation.GroundNativeReflection

/-! A unit, legally normalized inactive-phase input rejects unconditional
reflection of the unchanged native update. The active guard is substantive. -/
namespace SbtCosmo.Derivation.GroundReflectionControls
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeReflection
open scoped BigOperators

def fallbackField : Field := fun i => if i.val < 4 then uniform i else -uniform i
def fallbackReference : ComplexField := realEmbed fallbackField

theorem fallback_reference_unit : complexNormSq fallbackReference = 1 := by
  apply GroundState.realEmbed_normalized
  have he : normSq fallbackField = normSq uniform := by
    unfold normSq
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < 4 <;> simp [fallbackField, hi]
  exact he.trans uniform_normalized

theorem fallback_overlap_zero : overlap (realEmbed uniform) fallbackReference = 0 := by
  norm_num [overlap, fallbackReference, fallbackField, realEmbed, uniform, Fin.sum_univ_succ]

theorem zero_native_candidate_uniform (z : ComplexField) : nativeCandidate 0 0 z = realEmbed uniform := by
  have hv : complexSourcePotential 0 0 z = 0 := by
    funext i
    simp [complexSourcePotential, BackgroundSelection.potential]
  rw [nativeCandidate, hv]
  congr 1
  exact positive_ground_unique (positiveGround_spec 0).2 (uniform_ground 0)
    (positiveGround_spec 0).1 uniform_positive

theorem fallback_native_outputs :
    nativeUpdate 0 0 0 1 fallbackReference = realEmbed uniform ∧
    nativeUpdate 0 0 0 1 (-fallbackReference) = realEmbed uniform := by
  have hp : nativeMixed 0 0 0 1 fallbackReference = realEmbed uniform := by
    simp [nativeMixed, zero_native_candidate_uniform, nativePhase, fallback_overlap_zero]
  have hn : nativeMixed 0 0 0 1 (-fallbackReference) = realEmbed uniform := by
    simp [nativeMixed, zero_native_candidate_uniform, nativePhase, overlap_neg_right, fallback_overlap_zero]
  have hnorm : complexNormalize (realEmbed uniform) = realEmbed uniform := by
    funext i
    simp [complexNormalize, GroundState.realEmbed_normalized uniform_normalized]
  constructor
  · rw [nativeUpdate, hp, hnorm]
  · rw [nativeUpdate, hn, hnorm]

theorem fallback_legal_inactive :
    NativeLegal 0 0 0 1 fallbackReference ∧ ¬ ActivePhase 0 0 0 fallbackReference := by
  constructor
  · have hp : nativeMixed 0 0 0 1 fallbackReference = realEmbed uniform := by
      simp [nativeMixed, zero_native_candidate_uniform, nativePhase, fallback_overlap_zero]
    simp [NativeLegal, hp, GroundState.realEmbed_normalized uniform_normalized]
  · simp [ActivePhase, zero_native_candidate_uniform, fallback_overlap_zero]

theorem unconditional_unit_reflection_rejected :
    ¬ (∀ z : ComplexField, complexNormSq z = 1 → NativeLegal 0 0 0 1 z →
      nativeUpdate 0 0 0 1 (-z) = -nativeUpdate 0 0 0 1 z) := by
  intro h
  have he := h fallbackReference fallback_reference_unit fallback_legal_inactive.1
  rw [fallback_native_outputs.1, fallback_native_outputs.2] at he
  have hv := congrFun he 0
  have hr := congrArg Complex.re hv
  have hp := uniform_positive 0
  simp only [Pi.neg_apply, realEmbed, Complex.neg_re, Complex.ofReal_re] at hr
  linarith

end
end SbtCosmo.Derivation.GroundReflectionControls
