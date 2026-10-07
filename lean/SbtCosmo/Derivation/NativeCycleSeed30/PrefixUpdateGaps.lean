import SbtCosmo.Derivation.NativeCycleSeed30.PrefixFailures
import SbtCosmo.Derivation.NativeBoxLastUpdateGap
namespace SbtCosmo.Derivation.NativeCycleSeed30.PrefixUpdateGaps
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundSourceDiagnostics
open PrefixFailures NativeBoxLastUpdateGap

/-- Every original-source update1..60 changes the field by more than tolerance. -/
theorem all_first_sixty_update_gaps (n : ℕ) (hn : n < 60) :
    GroundOriginalResiduals.ε < lastUpdateResidual GroundNativeControls.originalTolerance
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
      (NativeCycleFrame30.κ : ℝ) (1/2) (Sixty.orbit n) := by
  by_cases h : n < 59
  · let j : Fin 59 := ⟨n,h⟩
    have he : GroundOriginalResiduals.ε = (εRat : ℝ) := by
      norm_num [GroundOriginalResiduals.ε,εRat]
    rw [he]
    exact last_update_gap_of_boxes (previous_enclosed j) (current_enclosed j)
      (imag j) (positive j) (coordinate j) (gap_arithmetic j)
      (Function.iterate_succ_apply' Sixty.g n GroundOriginalSeed.initial).symm
  · have he : n = 59 := by omega
    subst n
    have hε : GroundOriginalResiduals.ε < (1/4 : ℝ) := by
      norm_num [GroundOriginalResiduals.ε]
    exact hε.trans Sixty.last_update_gap
end
end SbtCosmo.Derivation.NativeCycleSeed30.PrefixUpdateGaps
