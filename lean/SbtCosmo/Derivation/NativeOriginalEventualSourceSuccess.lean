import SbtCosmo.Derivation.NativeOriginalSampleInterface
import SbtCosmo.Derivation.NativeEventualSourceSuccess
namespace SbtCosmo.Derivation.NativeOriginalEventualSourceSuccess
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundSourceDiagnostics Filter
open NativeOriginalSampleInterface
open scoped Topology

/-- Exact original-source eventual success, with the actual unit orbit and its
stable limit supplied explicitly. No finite stopping index is assumed. -/
theorem original_sample_eventual_tests_of_limit (i : Fin 12)
    (hz : ∀ n, complexNormSq (orbit i n) = 1)
    (ht : Tendsto (orbit i) atTop (nhds (target i))) :
    ∀ᶠ n in atTop, MeetsConvergence GroundNativeControls.originalTolerance
      GroundOriginalResiduals.ε b (κ i : ℝ) (1/2) (orbit i n) (orbit i (n+1)) := by
  have hground := GroundOriginalSamples.sample_ground_return ⟨i.val,by omega⟩
  rw [← coupling_return i] at hground
  have hf : GroundSourceJacobian.groundMap b (κ i : ℝ)
      (GroundOriginalContinuation.branch (κ i : ℝ)).1 =
      (GroundOriginalContinuation.branch (κ i : ℝ)).1 := hground.2.2.2.2
  apply NativeEventualSourceSuccess.eventual_tests_of_stable_limit
    GroundNativeControls.originalTolerance_guard.1
    GroundNativeControls.originalTolerance_guard.2
    (by norm_num [GroundOriginalResiduals.ε]) hf hz
  · intro n
    exact (Function.iterate_succ_apply' (g i) n GroundOriginalSeed.initial).symm
  · exact ht
end
end SbtCosmo.Derivation.NativeOriginalEventualSourceSuccess
