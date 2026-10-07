import SbtCosmo.Derivation.GroundOriginalResiduals
import SbtCosmo.Derivation.GroundReflectionControls

/-! An actual phase diagnostic control: double alignment can return zero while
single alignment has gap2. This input is illegal for the native half update. -/
namespace SbtCosmo.Derivation.GroundSourceDiagnosticControls
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean GroundComplexResidual
open GroundSourceDiagnostics GroundSourceJacobian

def g : ComplexField := realEmbed uniform
def z : ComplexField := Complex.I • g

theorem imaginary_unit : complexNormSq z = 1 := by
  have hg : l2 g = 1 := l2_unit (realEmbed_normalized uniform_normalized)
  rw [← l2_sq, z, l2_smul, Complex.norm_I, hg]; norm_num

theorem first_alignment {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    nativePhase τ g z = -z := by
  have he : overlap g z = Complex.I := by
    rw [z, overlap_smul_right, overlap_self]
    have hn : complexNormSq g = 1 := realEmbed_normalized uniform_normalized
    rw [hn]; simp
  have ho : τ < ‖overlap g z‖ := by rw [he, Complex.norm_I]; exact hτ1
  rw [nativePhase_ratio hτ0 ho, he, Complex.norm_I]
  funext i
  simp [z]

theorem second_alignment {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    nativePhase τ (nativePhase τ g z) z = z := by
  rw [first_alignment hτ0 hτ1]
  have he : overlap (-z) z = -1 := by rw [overlap_neg_left, overlap_self, imaginary_unit]; simp
  have ho : τ < ‖overlap (-z) z‖ := by rw [he]; simpa using hτ1
  rw [nativePhase_ratio hτ0 ho, he]
  funext i
  simp

theorem actual_double_gap_control {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    finalFixedGap τ 0 0 z = 0 ∧ l2 (nativePhase τ (nativeCandidate 0 0 z) z-z) = 2 := by
  have hc : nativeCandidate 0 0 z = g := GroundReflectionControls.zero_native_candidate_uniform z
  constructor
  · rw [finalFixedGap, hc, second_alignment hτ0 hτ1]
    simp [l2]
  · rw [hc, first_alignment hτ0 hτ1]
    have he : -z-z = (-2 : ℂ) • z := by funext i; simp; ring
    rw [he, l2_smul, l2_unit imaginary_unit]
    norm_num

theorem imaginary_half_update_illegal {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ActivePhase τ 0 0 z ∧ ¬ NativeLegal τ 0 0 (1/2) z := by
  have hf : groundMap 0 0 uniform = uniform := by
    rw [GroundNormalizedJacobian.zero_coupling_groundMap]
    exact positive_ground_unique (positiveGround_spec 0).2 (uniform_ground 0)
      (positiveGround_spec 0).1 uniform_positive
  have h := GroundNativeControls.native_half_imaginary_illegal uniform_normalized hf hτ0 hτ1
  have he : z = pack (0, uniform) := by
    funext i; apply Complex.ext <;> simp [z, g, pack, realEmbed]
  rw [he]; exact ⟨h.2.1, h.2.2.2⟩

end
end SbtCosmo.Derivation.GroundSourceDiagnosticControls
