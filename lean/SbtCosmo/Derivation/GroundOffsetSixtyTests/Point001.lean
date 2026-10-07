import SbtCosmo.Derivation.GroundOffsetPrefix.Point001
import SbtCosmo.Derivation.GroundComplexCoordinateBudget
import SbtCosmo.Derivation.GroundOriginalResiduals

/-! Failure of the actual source conjunction from a strict last-update lower bound. -/
namespace SbtCosmo.Derivation.GroundOffsetSixtyTests.Point001
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundOffsetSeedReturn GroundSourceDiagnostics GroundComplexEuclidean
open GroundComplexCoordinateBudget

def previousBox : StateBox := GroundOffsetPrefix.Point001.Step058.output
def currentBox : StateBox := GroundOffsetPrefix.Point001.Step059.output

theorem previous_enclosed : previousBox.Contains (unpack (orbit 1 59)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      GroundOffsetPrefix.Point001.certificate.enclosed (background_sound 1) ⟨59,by decide⟩

theorem current_enclosed : currentBox.Contains (unpack (orbit 1 60)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      GroundOffsetPrefix.Point001.certificate.enclosed (background_sound 1) ⟨60,by decide⟩

def difference : StateBox := GroundCertifiedNativeEntry.differenceBox currentBox previousBox
def εRat : ℚ := 3022314549036573/302231454903657293676544

theorem gap_arithmetic : εRat < -(difference.R 4).hi := by decide +kernel

theorem difference_enclosed : difference.Contains (unpack (orbit 1 60-orbit 1 59)) := by
  simpa only [← packCLE_symm_apply,map_sub] using
    GroundCertifiedNativeEntry.differenceBox_sound current_enclosed previous_enclosed

theorem last_update_fail : GroundOriginalResiduals.ε < lastUpdateResidual
    GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b 1) (κ 1 : ℝ)
      (1/2) (orbit 1 59) := by
  have he : GroundOriginalResiduals.ε = (εRat : ℝ) := by norm_num [GroundOriginalResiduals.ε,εRat]
  have hc : GroundOriginalResiduals.ε < ((-(difference.R 4).hi : ℚ) : ℝ) := by
    rw [he];exact_mod_cast gap_arithmetic
  have hj : (difference.R 4).Contains ((orbit 1 60-orbit 1 59) 4).re := (difference_enclosed 4).1
  have hb : ((-(difference.R 4).hi : ℚ) : ℝ) ≤ |((orbit 1 60-orbit 1 59) 4).re| := by
    simpa only [Rat.cast_neg] using (neg_le_neg hj.2).trans (neg_le_abs _)
  have hgap := hc.trans_le (hb.trans (real_component_le_l2 (orbit 1 60-orbit 1 59) 4))
  have hstep : nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b 1) (κ 1 : ℝ) (1/2) (orbit 1 59) = orbit 1 60 :=
    (Function.iterate_succ_apply' (f 1) 59 GroundOriginalSeed.initial).symm
  rw [lastUpdateResidual,hstep]
  exact hgap

theorem actual_four_source_tests_fail : ¬ MeetsConvergence GroundNativeControls.originalTolerance
    GroundOriginalResiduals.ε (GroundOriginalOffsets.rounded_b 1) (κ 1 : ℝ) (1/2)
      (orbit 1 59) (orbit 1 60) := by
  intro h
  exact (not_lt_of_ge h.1) last_update_fail

end
end SbtCosmo.Derivation.GroundOffsetSixtyTests.Point001
