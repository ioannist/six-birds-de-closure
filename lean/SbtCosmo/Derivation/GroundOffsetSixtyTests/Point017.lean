import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017
import SbtCosmo.Derivation.GroundComplexCoordinateBudget
import SbtCosmo.Derivation.GroundOriginalResiduals

/-! Failure of the actual source conjunction from a strict last-update lower bound. -/
namespace SbtCosmo.Derivation.GroundOffsetSixtyTests.Point017
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundOffsetSeedReturn GroundSourceDiagnostics GroundComplexEuclidean
open GroundComplexCoordinateBudget

def previousBox : StateBox := GroundOffsetSixtyPrefix.Point017.previousBox
def currentBox : StateBox := GroundOffsetSixtyPrefix.Point017.currentBox

theorem previous_enclosed : previousBox.Contains (unpack (orbit 17 59)) := by
  exact GroundOffsetSixtyPrefix.Point017.previous_enclosed

theorem current_enclosed : currentBox.Contains (unpack (orbit 17 60)) := by
  exact GroundOffsetSixtyPrefix.Point017.current_enclosed

def difference : StateBox := GroundCertifiedNativeEntry.differenceBox currentBox previousBox
def εRat : ℚ := 3022314549036573/302231454903657293676544

theorem gap_arithmetic : εRat < (difference.R 6).lo := by decide +kernel

theorem difference_enclosed : difference.Contains (unpack (orbit 17 60-orbit 17 59)) := by
  simpa only [← packCLE_symm_apply,map_sub] using
    GroundCertifiedNativeEntry.differenceBox_sound current_enclosed previous_enclosed

theorem last_update_fail : GroundOriginalResiduals.ε < lastUpdateResidual
    GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b 17) (κ 17 : ℝ)
      (1/2) (orbit 17 59) := by
  have he : GroundOriginalResiduals.ε = (εRat : ℝ) := by norm_num [GroundOriginalResiduals.ε,εRat]
  have hc : GroundOriginalResiduals.ε < (((difference.R 6).lo : ℚ) : ℝ) := by
    rw [he];exact_mod_cast gap_arithmetic
  have hj : (difference.R 6).Contains ((orbit 17 60-orbit 17 59) 6).re := (difference_enclosed 6).1
  have hb : (((difference.R 6).lo : ℚ) : ℝ) ≤ |((orbit 17 60-orbit 17 59) 6).re| := by
    exact hj.1.trans (le_abs_self _)
  have hgap := hc.trans_le (hb.trans (real_component_le_l2 (orbit 17 60-orbit 17 59) 6))
  have hstep : nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b 17) (κ 17 : ℝ) (1/2) (orbit 17 59) = orbit 17 60 :=
    (Function.iterate_succ_apply' (f 17) 59 GroundOriginalSeed.initial).symm
  rw [lastUpdateResidual,hstep]
  exact hgap

theorem actual_four_source_tests_fail : ¬ MeetsConvergence GroundNativeControls.originalTolerance
    GroundOriginalResiduals.ε (GroundOriginalOffsets.rounded_b 17) (κ 17 : ℝ) (1/2)
      (orbit 17 59) (orbit 17 60) := by
  intro h
  exact (not_lt_of_ge h.1) last_update_fail

end
end SbtCosmo.Derivation.GroundOffsetSixtyTests.Point017
