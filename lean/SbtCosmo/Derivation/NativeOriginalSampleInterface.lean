import SbtCosmo.Derivation.GroundOriginalPositiveResiduals
import SbtCosmo.Derivation.GroundOriginalResiduals
import SbtCosmo.Derivation.GroundOriginalSamples
namespace SbtCosmo.Derivation.NativeOriginalSampleInterface
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundSourceDiagnostics Metric Filter
open scoped Topology

/-- Original twelve experiment couplings; the two later crossing probes are excluded. -/
def κ : Fin 12 → ℚ := ![0, (3602879701896397/36028797018963968),
  (5404319552844595/18014398509481984), (1/2),1,2,3,5,10,15,20,30]
def b : Field := GroundKernelTube.background GroundOriginalFirstTube.originalBackground
def g (i : Fin 12) : ComplexField → ComplexField :=
  nativeUpdate GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2)
def orbit (i : Fin 12) : ℕ → ComplexField := fun n => (g i)^[n] GroundOriginalSeed.initial
def target (i : Fin 12) : ComplexField := realEmbed (-(GroundOriginalContinuation.branch (κ i : ℝ)).1)

theorem coupling_return (i : Fin 12) : κ i =
    GroundOriginalSamples.couplings ⟨i.val,by omega⟩ := by
  fin_cases i <;> decide +kernel

theorem zero_seed_return : Tendsto (orbit 0) atTop (nhds (target 0)) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ 0 : ℝ) (orbit 0 n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ 0 : ℝ) (1/2) (orbit 0 n) ∧
      complexNormSq (orbit 0 n) = 1 := by
  have h := GroundOriginalSeed.actual_seed_zero_convergence
  refine ⟨?_,fun n => ⟨?_,?_,?_⟩⟩
  · have hf : orbit 0 = (fun n : ℕ =>
        (nativeUpdate GroundNativeControls.originalTolerance
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) 0 (1/2))^[n]
          GroundOriginalSeed.initial) := by
      funext n
      simp [NativeOriginalSampleInterface.orbit,NativeOriginalSampleInterface.g,
        NativeOriginalSampleInterface.b,NativeOriginalSampleInterface.κ]
    rw [hf]
    simpa [target,κ] using h.1
  · simpa [orbit,g,b,κ] using (h.2 n).1
  · simpa [orbit,g,b,κ] using (h.2 n).2
  · simpa [orbit,g,b,κ,GroundOriginalResiduals.orbit,GroundOriginalResiduals.τ,GroundOriginalResiduals.b]
      using GroundOriginalResiduals.orbit_unit n

theorem positive_seed_return : Tendsto (orbit 2) atTop (nhds (target 2)) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ 2 : ℝ) (orbit 2 n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ 2 : ℝ) (1/2) (orbit 2 n) ∧
      complexNormSq (orbit 2 n) = 1 := by
  refine ⟨?_,fun n => ⟨?_,?_,?_⟩⟩
  · simpa [orbit,g,b,κ,target,GroundOriginalNativePrefix.orbit,GroundOriginalNativePrefix.f,
      GroundOriginalBasin.u,GroundNativePrefixInitial.κ,GroundSamples.Point002.a]
      using GroundOriginalBasin.original_seed_converges_negative_ground
  · simpa [orbit,g,b,κ,GroundOriginalNativePrefix.orbit,GroundOriginalNativePrefix.f,GroundOriginalBasin.b,
      GroundNativePrefixInitial.κ,GroundSamples.Point002.a]
      using (GroundOriginalBasin.original_seed_all_guards n).1
  · simpa [orbit,g,b,κ,GroundOriginalNativePrefix.orbit,GroundOriginalNativePrefix.f,GroundOriginalBasin.b,
      GroundNativePrefixInitial.κ,GroundSamples.Point002.a]
      using (GroundOriginalBasin.original_seed_all_guards n).2
  · simpa [orbit,g,b,κ,GroundOriginalNativePrefix.orbit,GroundOriginalNativePrefix.f,GroundOriginalBasin.b,
      GroundNativePrefixInitial.κ,GroundSamples.Point002.a]
      using GroundOriginalBasin.original_seed_all_unit n

theorem zero_sixty_tests : MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
    b (κ 0 : ℝ) (1/2) (orbit 0 59) (orbit 0 60) := by
  simpa [orbit,g,b,κ,GroundOriginalResiduals.orbit,GroundOriginalResiduals.τ,GroundOriginalResiduals.b]
    using GroundOriginalResiduals.actual_seed_zero_sixty_convergence_tests.1

theorem positive_sixty_tests : MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
    b (κ 2 : ℝ) (1/2) (orbit 2 59) (orbit 2 60) := by
  simpa [orbit,g,b,κ,GroundOriginalPositiveResiduals.orbit,GroundOriginalPositiveResiduals.τ,
    GroundOriginalPositiveResiduals.ε,GroundOriginalResiduals.ε,GroundOriginalNativePrefix.orbit,
    GroundOriginalNativePrefix.f,GroundNativePrefixInitial.κ,GroundSamples.Point002.a]
    using GroundOriginalPositiveResiduals.actual_seed_positive_sixty_convergence_tests.1
end
end SbtCosmo.Derivation.NativeOriginalSampleInterface
