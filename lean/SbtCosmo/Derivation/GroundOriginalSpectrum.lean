import SbtCosmo.Derivation.GroundOriginalCoordinates
import SbtCosmo.Derivation.GroundRealModeNormalize
import SbtCosmo.Derivation.GroundSpectralTests.Test000
import SbtCosmo.Derivation.GroundSpectralTests.Test001
import SbtCosmo.Derivation.GroundSpectralTests.Test002
import SbtCosmo.Derivation.GroundSpectralTests.Test003
import SbtCosmo.Derivation.GroundSpectralTests.Test004
import SbtCosmo.Derivation.GroundSpectralTests.Test005
import SbtCosmo.Derivation.GroundSpectralTests.Test006

/-! Closed determinant signs, two branch contacts, and expanding native modes.
All numeric obligations are populated by kernel-checked integer/interval tests. -/
namespace SbtCosmo.Derivation.GroundOriginalSpectrum
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundKernelTube GroundOriginalFirstTube GroundOriginalSamples
open GroundMatrixCoordinates GroundSpectralEnclosure GroundTriangularArithmetic
open GroundNativeLocal GroundOriginalCoordinates GroundNativeIteration

structure Certificate where
  sample : Fin 14
  ell : ℚ
  sign : ℤ
  CI : ZMatrix
  LI : ZMatrix
  UI : ZMatrix
  dc : ℤ
  dl : ℤ
  du : ℤ
  B : Box
  factor_arithmetic : GroundTriangularArithmetic.Arithmetic CI LI UI dc dl du sign
  box_return : B = GroundOriginalResponses.enclosures sample
  defect_arithmetic : GroundSpectralEnclosure.Arithmetic (scaled CI dc) (shifted B ell) (1/1000)

def tests : Fin 7 → Certificate :=
  Fin.cases ⟨12, GroundSpectralTests.Test000.ell, GroundSpectralTests.Test000.sign, GroundSpectralTests.Test000.CI, GroundSpectralTests.Test000.LI, GroundSpectralTests.Test000.UI, GroundSpectralTests.Test000.dc, GroundSpectralTests.Test000.dl, GroundSpectralTests.Test000.du, GroundSpectralTests.Test000.B, GroundSpectralTests.Test000.factor_arithmetic, GroundSpectralTests.Test000.box_return, GroundSpectralTests.Test000.defect_arithmetic⟩ (
  Fin.cases ⟨13, GroundSpectralTests.Test001.ell, GroundSpectralTests.Test001.sign, GroundSpectralTests.Test001.CI, GroundSpectralTests.Test001.LI, GroundSpectralTests.Test001.UI, GroundSpectralTests.Test001.dc, GroundSpectralTests.Test001.dl, GroundSpectralTests.Test001.du, GroundSpectralTests.Test001.B, GroundSpectralTests.Test001.factor_arithmetic, GroundSpectralTests.Test001.box_return, GroundSpectralTests.Test001.defect_arithmetic⟩ (
  Fin.cases ⟨10, GroundSpectralTests.Test002.ell, GroundSpectralTests.Test002.sign, GroundSpectralTests.Test002.CI, GroundSpectralTests.Test002.LI, GroundSpectralTests.Test002.UI, GroundSpectralTests.Test002.dc, GroundSpectralTests.Test002.dl, GroundSpectralTests.Test002.du, GroundSpectralTests.Test002.B, GroundSpectralTests.Test002.factor_arithmetic, GroundSpectralTests.Test002.box_return, GroundSpectralTests.Test002.defect_arithmetic⟩ (
  Fin.cases ⟨10, GroundSpectralTests.Test003.ell, GroundSpectralTests.Test003.sign, GroundSpectralTests.Test003.CI, GroundSpectralTests.Test003.LI, GroundSpectralTests.Test003.UI, GroundSpectralTests.Test003.dc, GroundSpectralTests.Test003.dl, GroundSpectralTests.Test003.du, GroundSpectralTests.Test003.B, GroundSpectralTests.Test003.factor_arithmetic, GroundSpectralTests.Test003.box_return, GroundSpectralTests.Test003.defect_arithmetic⟩ (
  Fin.cases ⟨10, GroundSpectralTests.Test004.ell, GroundSpectralTests.Test004.sign, GroundSpectralTests.Test004.CI, GroundSpectralTests.Test004.LI, GroundSpectralTests.Test004.UI, GroundSpectralTests.Test004.dc, GroundSpectralTests.Test004.dl, GroundSpectralTests.Test004.du, GroundSpectralTests.Test004.B, GroundSpectralTests.Test004.factor_arithmetic, GroundSpectralTests.Test004.box_return, GroundSpectralTests.Test004.defect_arithmetic⟩ (
  Fin.cases ⟨11, GroundSpectralTests.Test005.ell, GroundSpectralTests.Test005.sign, GroundSpectralTests.Test005.CI, GroundSpectralTests.Test005.LI, GroundSpectralTests.Test005.UI, GroundSpectralTests.Test005.dc, GroundSpectralTests.Test005.dl, GroundSpectralTests.Test005.du, GroundSpectralTests.Test005.B, GroundSpectralTests.Test005.factor_arithmetic, GroundSpectralTests.Test005.box_return, GroundSpectralTests.Test005.defect_arithmetic⟩ (
  Fin.cases ⟨11, GroundSpectralTests.Test006.ell, GroundSpectralTests.Test006.sign, GroundSpectralTests.Test006.CI, GroundSpectralTests.Test006.LI, GroundSpectralTests.Test006.UI, GroundSpectralTests.Test006.dc, GroundSpectralTests.Test006.dl, GroundSpectralTests.Test006.du, GroundSpectralTests.Test006.B, GroundSpectralTests.Test006.factor_arithmetic, GroundSpectralTests.Test006.box_return, GroundSpectralTests.Test006.defect_arithmetic⟩ (
  (fun i => Fin.elim0 i))))))))

def actualL (i : Fin 14) : Field →L[ℝ] Field :=
  GroundNormalizedJacobian.normalizedJacobian (background originalBackground) (couplings i) (1/2)
    (GroundOriginalContinuation.branch (couplings i)).1

def shiftedDet (i : Fin 14) (ell : ℝ) : ℝ := (entries (actualL i) - ell • (1 : RMatrix)).det

theorem actual_signed_test (i : Fin 7) :
    0 < ((tests i).sign : ℝ) * shiftedDet (tests i).sample (tests i).ell := by
  apply actual_shifted_sign (tests i).defect_arithmetic
  · intro a j
    rw [(tests i).box_return]
    exact GroundOriginalResponses.actual_half_entries (tests i).sample a j
  · exact GroundTriangularArithmetic.determinant_sign (tests i).factor_arithmetic

theorem concrete_signs :
    0 < shiftedDet 12 (-1) ∧ shiftedDet 13 (-1) < 0 ∧ 0 < shiftedDet 10 (-1) ∧
    0 < shiftedDet 10 (-36/25) ∧ shiftedDet 10 (-71/50) < 0 ∧
    0 < shiftedDet 11 (-249/100) ∧ shiftedDet 11 (-247/100) < 0 := by
  have h0 := actual_signed_test 0
  have h1 := actual_signed_test 1
  have h2 := actual_signed_test 2
  have h3 := actual_signed_test 3
  have h4 := actual_signed_test 4
  have h5 := actual_signed_test 5
  have h6 := actual_signed_test 6
  change 0 < ((1 : ℤ) : ℝ) * shiftedDet 12 ((-1 : ℚ) : ℝ) at h0
  change 0 < ((-1 : ℤ) : ℝ) * shiftedDet 13 ((-1 : ℚ) : ℝ) at h1
  change 0 < ((1 : ℤ) : ℝ) * shiftedDet 10 ((-1 : ℚ) : ℝ) at h2
  change 0 < ((1 : ℤ) : ℝ) * shiftedDet 10 ((-36/25 : ℚ) : ℝ) at h3
  change 0 < ((-1 : ℤ) : ℝ) * shiftedDet 10 ((-71/50 : ℚ) : ℝ) at h4
  change 0 < ((1 : ℤ) : ℝ) * shiftedDet 11 ((-249/100 : ℚ) : ℝ) at h5
  change 0 < ((-1 : ℤ) : ℝ) * shiftedDet 11 ((-247/100 : ℚ) : ℝ) at h6
  norm_num only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, one_mul, neg_one_mul] at h0 h1 h2 h3 h4 h5 h6
  simpa only [neg_div] using
    (And.intro h0 (And.intro (neg_pos.mp h1) (And.intro h2
      (And.intro h3 (And.intro (neg_pos.mp h4) (And.intro h5 (neg_pos.mp h6)))))))

def contactDet (k : ℝ) : ℝ := GroundParameterSpectrum.crossingDet
  ((background originalBackground, k), (GroundOriginalContinuation.branch k).1)

theorem crossing_signs : 0 < contactDet (79/5) ∧ contactDet (159/10) < 0 ∧ 0 < contactDet 20 := by
  have h := concrete_signs
  have hk0 : couplings 12 = 79/5 := by decide +kernel
  have hk1 : couplings 13 = 159/10 := by decide +kernel
  have hk2 : couplings 10 = 20 := by decide +kernel
  have hs (i : Fin 14) : shiftedDet i (-1) = contactDet (couplings i) := by
    simp only [shiftedDet, actualL, contactDet, GroundParameterSpectrum.crossingDet,
      GroundParameterSpectrum.halfMatrix,
      neg_smul, one_smul, sub_neg_eq_add]
    rfl
  rw [hs, hk0] at h
  have h1 := concrete_signs.2.1
  have h2 := concrete_signs.2.2.1
  rw [hs, hk1] at h1
  rw [hs, hk2] at h2
  simpa only [Rat.cast_div, Rat.cast_ofNat] using (And.intro h.1 (And.intro h1 h2))

theorem actual_two_contacts :
    ∃ k₁ ∈ Set.Ioo (79/5 : ℝ) (159/10), ∃ k₂ ∈ Set.Ioo (159/10 : ℝ) 20, k₁ < k₂ ∧
      GroundParameterPatchReturn.ModeContact (background originalBackground)
        (GroundOriginalContinuation.branch k₁).1 GroundNativeControls.originalTolerance k₁ ∧
      GroundParameterPatchReturn.ModeContact (background originalBackground)
        (GroundOriginalContinuation.branch k₂).1 GroundNativeControls.originalTolerance k₂ := by
  apply GroundParameterPatchReturn.two_distinct_contacts GroundOriginalContinuation.cover
  · norm_num
  · norm_num
  · rw [GroundOriginalContinuation.domain_eq]
    intro k hk
    constructor <;> linarith [hk.1, hk.2]
  · exact GroundNativeControls.originalTolerance_guard.1
  · exact GroundNativeControls.originalTolerance_guard.2
  · exact mul_neg_of_pos_of_neg crossing_signs.1 crossing_signs.2.1
  · exact mul_neg_of_neg_of_pos crossing_signs.2.1 crossing_signs.2.2

theorem actual_twenty_mode :
    ∃ ell ∈ Set.Ioo (-36/25 : ℝ) (-71/50), ∃ v : GroundNativePhase.State, ‖v‖ = 1 ∧
      coordinateDerivative (fullBasis 10) (background originalBackground) 20 (1/2) (root 10) v = ell • v := by
  have hs := mul_neg_of_pos_of_neg concrete_signs.2.2.2.1 concrete_signs.2.2.2.2.1
  have hk : couplings 10 = 20 := by decide +kernel
  change (entries (actualL 10) - (-36/25 : ℝ) • (1 : RMatrix)).det *
    (entries (actualL 10) - (-71/50 : ℝ) • (1 : RMatrix)).det < 0 at hs
  dsimp only [actualL] at hs
  rw [hk] at hs
  exact GroundRealModeNormalize.bracket_full_mode (realBasis 10) (imagBasis 10)
    (background originalBackground) (root 10) 20 (1/2) (-36/25) (-71/50) (by norm_num) hs

theorem actual_thirty_mode :
    ∃ ell ∈ Set.Ioo (-249/100 : ℝ) (-247/100), ∃ v : GroundNativePhase.State, ‖v‖ = 1 ∧
      coordinateDerivative (fullBasis 11) (background originalBackground) 30 (1/2) (root 11) v = ell • v := by
  have hs := mul_neg_of_pos_of_neg concrete_signs.2.2.2.2.2.1 concrete_signs.2.2.2.2.2.2
  have hk : couplings 11 = 30 := by decide +kernel
  change (entries (actualL 11) - (-249/100 : ℝ) • (1 : RMatrix)).det *
    (entries (actualL 11) - (-247/100 : ℝ) • (1 : RMatrix)).det < 0 at hs
  dsimp only [actualL] at hs
  rw [hk] at hs
  exact GroundRealModeNormalize.bracket_full_mode (realBasis 11) (imagBasis 11)
    (background originalBackground) (root 11) 30 (1/2) (-249/100) (-247/100) (by norm_num) hs

/-- Arbitrarily close unit complex starts escape a fixed coordinate neighborhood
through a finite legal active native orbit segment. -/
theorem actual_twenty_native_escape :
    ∃ s > 0, ∀ ε > 0, ∃ z : ComplexField, ∃ N : ℕ,
      complexNormSq z = 1 ∧ ‖(fullBasis 10).symm (GroundNativePhase.unpack z) - (fullBasis 10).symm (root 10, 0)‖ < ε ∧
      s/2 ≤ ‖(fullBasis 10).symm (GroundNativePhase.unpack
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2))^[N] z)) -
        (fullBasis 10).symm (root 10, 0)‖ ∧
      ∀ j ≤ N, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) 20
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2))^[j] z) ∧
        NativeLegal GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2))^[j] z) := by
  obtain ⟨ell, hell, v, hv, he⟩ := actual_twenty_mode
  have hk : couplings 10 = 20 := by decide +kernel
  have hu := (sample_ground_return 10).2.2.1
  have hf := (sample_ground_return 10).2.2.2.2
  rw [hk] at hu hf
  have hn : ell < 0 := by linarith [hell.2]
  have heabs : |ell| = -ell := abs_of_neg hn
  have habs : 1 < |ell| := by rw [heabs]; linarith [hell.2]
  have hgap : ‖coordinateDerivative (fullBasis 10) (background originalBackground) 20 (1/2) (root 10)‖ < |ell|^2 := by
    rw [heabs]
    nlinarith [GroundOriginalCoordinates.actual_twenty_norm, hell.2]
  exact GroundNativeEscape.native_complex_local_escape (fullBasis 10) hu hf
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2 hv he habs hgap

/-- Arbitrarily close unit complex starts escape a fixed coordinate neighborhood
through a finite legal active native orbit segment. -/
theorem actual_thirty_native_escape :
    ∃ s > 0, ∀ ε > 0, ∃ z : ComplexField, ∃ N : ℕ,
      complexNormSq z = 1 ∧ ‖(fullBasis 11).symm (GroundNativePhase.unpack z) - (fullBasis 11).symm (root 11, 0)‖ < ε ∧
      s/2 ≤ ‖(fullBasis 11).symm (GroundNativePhase.unpack
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2))^[N] z)) -
        (fullBasis 11).symm (root 11, 0)‖ ∧
      ∀ j ≤ N, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) 30
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2))^[j] z) ∧
        NativeLegal GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2))^[j] z) := by
  obtain ⟨ell, hell, v, hv, he⟩ := actual_thirty_mode
  have hk : couplings 11 = 30 := by decide +kernel
  have hu := (sample_ground_return 11).2.2.1
  have hf := (sample_ground_return 11).2.2.2.2
  rw [hk] at hu hf
  have hn : ell < 0 := by linarith [hell.2]
  have heabs : |ell| = -ell := abs_of_neg hn
  have habs : 1 < |ell| := by rw [heabs]; linarith [hell.2]
  have hgap : ‖coordinateDerivative (fullBasis 11) (background originalBackground) 30 (1/2) (root 11)‖ < |ell|^2 := by
    rw [heabs]
    nlinarith [GroundOriginalCoordinates.actual_thirty_norm, hell.2]
  exact GroundNativeEscape.native_complex_local_escape (fullBasis 11) hu hf
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2 hv he habs hgap

end
end SbtCosmo.Derivation.GroundOriginalSpectrum
