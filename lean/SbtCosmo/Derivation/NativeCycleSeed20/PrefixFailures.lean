import SbtCosmo.Derivation.NativeCycleSeed20.Sixty
import SbtCosmo.Derivation.NativeBoxUpdateGap
namespace SbtCosmo.Derivation.NativeCycleSeed20.PrefixFailures
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundSourceDiagnostics NativeBoxUpdateGap
open scoped Topology

def εRat : ℚ := 3022314549036573/302231454903657293676544
def imag : Fin 59 → Bool := ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]
def positive : Fin 59 → Bool := ![false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]
def coordinate : Fin 59 → Fin 8 := ![3,1,4,7,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,3,4,3,4,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4]
def previousBox (j : Fin 59) : StateBox :=
  (NativeFinitePairJets.steps Prefix060.tube ⟨j.val,by have h := j.isLt;change j.val < 60;omega⟩).jet.input
def currentBox (j : Fin 59) : StateBox :=
  (NativeFinitePairJets.steps Prefix060.tube ⟨j.val+1,by have h := j.isLt;change j.val+1 < 60;omega⟩).jet.input

/-- Kernel-checked coordinate gaps of the actual certified input boxes. -/
theorem gap_arithmetic (j : Fin 59) :
    εRat < gap (previousBox j) (currentBox j) (imag j) (positive j) (coordinate j) := by
  fin_cases j <;> decide +kernel

theorem previous_enclosed (j : Fin 59) :
    (previousBox j).Contains (unpack (Sixty.orbit j.val)) := by
  have h := NativeFiniteSourceBoxes.before_endpoint Prefix060.tube
    NativeCycleFrame20.background_sound Prefix060.initial
    ⟨j.val,by have h := j.isLt;change j.val < 60;omega⟩
  simpa only [previousBox,Sixty.orbit,Sixty.g,SixtyGeometry.g,Prefix060.g,
    GroundNativePrefixInitial.tolerance_return] using h

theorem current_enclosed (j : Fin 59) :
    (currentBox j).Contains (unpack (Sixty.orbit (j.val+1))) := by
  have h := NativeFiniteSourceBoxes.before_endpoint Prefix060.tube
    NativeCycleFrame20.background_sound Prefix060.initial
    ⟨j.val+1,by have h := j.isLt;change j.val+1 < 60;omega⟩
  simpa only [currentBox,Sixty.orbit,Sixty.g,SixtyGeometry.g,Prefix060.g,
    GroundNativePrefixInitial.tolerance_return] using h

/-- None of the actual exact-source stopping tests at updates1..60 passes. -/
theorem all_first_sixty_fail (n : ℕ) (hn : n < 60) :
    ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
      (NativeCycleFrame20.κ : ℝ) (1/2) (Sixty.orbit n) (Sixty.orbit (n+1)) := by
  by_cases h : n < 59
  · let j : Fin 59 := ⟨n,h⟩
    have he : GroundOriginalResiduals.ε = (εRat : ℝ) := by
      norm_num [GroundOriginalResiduals.ε,εRat]
    rw [he]
    apply tests_fail_of_gap (previous_enclosed j) (current_enclosed j)
      (imag j) (positive j) (coordinate j) (gap_arithmetic j)
    exact (Function.iterate_succ_apply' Sixty.g n GroundOriginalSeed.initial).symm
  · have he : n = 59 := by omega
    subst n
    exact Sixty.actual_four_source_tests_fail

/-- Failure is attached to a guarded original-seed execution at every earlier test. -/
theorem guarded_first_sixty_fail (n : ℕ) (hn : n < 60) :
    ActivePhase GroundNativeControls.originalTolerance
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
      (NativeCycleFrame20.κ : ℝ) (Sixty.orbit n) ∧
    NativeLegal GroundNativeControls.originalTolerance
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
      (NativeCycleFrame20.κ : ℝ) (1/2) (Sixty.orbit n) ∧
    ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
      (NativeCycleFrame20.κ : ℝ) (1/2) (Sixty.orbit n) (Sixty.orbit (n+1)) :=
  ⟨(Sixty.finite_guards n hn).1,(Sixty.finite_guards n hn).2,all_first_sixty_fail n hn⟩
end
end SbtCosmo.Derivation.NativeCycleSeed20.PrefixFailures
