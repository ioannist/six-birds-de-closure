import SbtCosmo.Derivation.NativeCycleSeed20.Prefix060
import SbtCosmo.Derivation.NativeCycleSeed20.SixtyGeometry
import SbtCosmo.Derivation.NativeFiniteSourceBoxes
namespace SbtCosmo.Derivation.NativeCycleSeed20.Sixty
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundNativeTransportGeometry GroundCertifiedNativeEntry GroundSourceDiagnostics GroundComplexEuclidean
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data Metric Filter
open scoped Topology

def g : ComplexField → ComplexField := SixtyGeometry.g
def orbit (n : ℕ) : ComplexField := (g^[n]) GroundOriginalSeed.initial

theorem previous_enclosed : SixtyGeometry.previousBox.Contains (unpack (orbit 59)) := by
  have h := NativeFiniteSourceBoxes.before_endpoint Prefix060.tube
    NativeCycleFrame20.background_sound Prefix060.initial ⟨59,by decide⟩
  change SixtyGeometry.previousBox.Contains (unpack ((Prefix060.g^[59]) GroundOriginalSeed.initial)) at h
  simpa only [Prefix060.g,SixtyGeometry.g,g,orbit,GroundNativePrefixInitial.tolerance_return] using h

theorem current_enclosed : SixtyGeometry.currentBox.Contains (unpack (orbit 60)) := by
  have hT : ‖NativeCycleFrame20.T.toContinuousLinearMap‖ ≤ (SixtyGeometry.s : ℝ) :=
    Step000.certificate.basis_norm Step000.basis_nonneg Step000.basis_rows
  have h := NativeFiniteSourceBoxes.at_endpoint Prefix060.tube
    NativeCycleFrame20.background_sound Prefix060.initial SixtyGeometry.current_u SixtyGeometry.current_v
    (ρ := SixtyGeometry.current_radius) (s := SixtyGeometry.s) (by rfl) (by rfl)
    Step000.basis_nonneg hT
  change SixtyGeometry.currentBox.Contains (unpack ((Prefix060.g^[60]) GroundOriginalSeed.initial)) at h
  simpa only [Prefix060.g,SixtyGeometry.g,g,orbit,GroundNativePrefixInitial.tolerance_return] using h

/-- A lower bound for the literal original source's update59 to update60,
with actual-seed membership earned from all thirty populated transport pairs. -/
theorem last_update_gap : (1/4 : ℝ) < lastUpdateResidual GroundNativeControls.originalTolerance
    (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame20.κ : ℝ) (1/2)
    (orbit 59) := SixtyGeometry.last_update_gap_of_enclosures previous_enclosed current_enclosed

theorem actual_four_source_tests_fail : ¬ MeetsConvergence GroundNativeControls.originalTolerance
    GroundOriginalResiduals.ε (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
    (NativeCycleFrame20.κ : ℝ) (1/2) (orbit 59) (orbit 60) :=
  SixtyGeometry.four_source_tests_fail_of_enclosures previous_enclosed current_enclosed

theorem finite_guards (n : ℕ) (hn : n < 60) :
    ActivePhase GroundNativeControls.originalTolerance
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame20.κ : ℝ) (orbit n) ∧
    NativeLegal GroundNativeControls.originalTolerance
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame20.κ : ℝ) (1/2) (orbit n) := by
  simpa only [Prefix060.g,Prefix060.N,SixtyGeometry.g,g,orbit,GroundNativePrefixInitial.tolerance_return] using
    Prefix060.guards_before n hn

theorem finite_unit (j : Fin 61) : complexNormSq (orbit j.val) = 1 := by
  simpa only [Prefix060.g,Prefix060.N,SixtyGeometry.g,g,orbit,GroundNativePrefixInitial.tolerance_return] using
    Prefix060.unit_before j
end
end SbtCosmo.Derivation.NativeCycleSeed20.Sixty
