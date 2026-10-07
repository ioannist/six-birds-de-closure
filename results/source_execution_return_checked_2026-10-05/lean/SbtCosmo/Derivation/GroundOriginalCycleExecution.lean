import SbtCosmo.Derivation.GroundSourceExecutionReturn
import NativeCycleSeed20Return
import NativeCycleSeed30Return

/-! The earned original-seed cycle guards discharge normalization success.
These are executions of the exact mathematical source normalization branch,
not floating point traces or assertions about arbitrary seeds. -/
namespace SbtCosmo.Derivation.GroundOriginalCycleExecution
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativeIteration GroundSourceNormalization GroundSourceExecutionReturn

theorem coupling20_execution (N : ℕ) :
    ∃ w : ComplexField,
      run (GroundNativePrefixInitial.τ : ℝ)
        (nativeMixed (GroundNativePrefixInitial.τ : ℝ)
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
          (NativeCycleFrame20.κ : ℝ) (1/2)) GroundOriginalSeed.initial N = some w ∧
      w = (NativeCycleSeed20.g^[N]) GroundOriginalSeed.initial ∧
      ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeCycleFrame20.κ : ℝ) w ∧
      NativeLegal (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeCycleFrame20.κ : ℝ) (1/2) w ∧ complexNormSq w = 1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hg,_⟩ := NativeCycleSeed20.original_seed_cycle
  refine ⟨(NativeCycleSeed20.g^[N]) GroundOriginalSeed.initial,?_,rfl,hg N⟩
  exact native_run_guarded _ _ _ _ _ N (fun n _ => (hg n).2.1)

theorem coupling30_execution (N : ℕ) :
    ∃ w : ComplexField,
      run (GroundNativePrefixInitial.τ : ℝ)
        (nativeMixed (GroundNativePrefixInitial.τ : ℝ)
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
          (NativeCycleFrame30.κ : ℝ) (1/2)) GroundOriginalSeed.initial N = some w ∧
      w = (NativeCycleSeed30.g^[N]) GroundOriginalSeed.initial ∧
      ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeCycleFrame30.κ : ℝ) w ∧
      NativeLegal (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeCycleFrame30.κ : ℝ) (1/2) w ∧ complexNormSq w = 1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hg,_⟩ := NativeCycleSeed30.original_seed_cycle
  refine ⟨(NativeCycleSeed30.g^[N]) GroundOriginalSeed.initial,?_,rfl,hg N⟩
  exact native_run_guarded _ _ _ _ _ N (fun n _ => (hg n).2.1)

end
end SbtCosmo.Derivation.GroundOriginalCycleExecution
