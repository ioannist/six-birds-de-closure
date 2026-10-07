import SbtCosmo.Derivation.NativeStableSeed004.Transport
import SbtCosmo.Derivation.NativeStableSeed004.SixtyGeometry
namespace SbtCosmo.Derivation.NativeStableSeed004.Sixty
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval GroundNativeBox GroundSourceDiagnostics

theorem previous_included : NativeStableSeed004.previousBox.Included SixtyGeometry.previousBox := by
  unfold StateBox.Included included
  decide +kernel

theorem current_included : NativeStableSeed004.currentBox.Included SixtyGeometry.currentBox := by
  unfold StateBox.Included included
  decide +kernel

theorem previous_enclosed : SixtyGeometry.previousBox.Contains (unpack (SixtyGeometry.orbit 59)) := by
  have h := StateBox.included_sound previous_included NativeStableSeed004.previous_enclosed
  simpa only [SixtyGeometry.orbit,SixtyGeometry.g,SixtyGeometry.b,NativeStableSeed004.g,GroundNativePrefixInitial.tolerance_return] using h

theorem current_enclosed : SixtyGeometry.currentBox.Contains (unpack (SixtyGeometry.orbit 60)) := by
  have h := StateBox.included_sound current_included NativeStableSeed004.current_enclosed
  simpa only [SixtyGeometry.orbit,SixtyGeometry.g,SixtyGeometry.b,NativeStableSeed004.g,GroundNativePrefixInitial.tolerance_return] using h

theorem current_unit : complexNormSq (SixtyGeometry.orbit 60) = 1 := by
  simpa only [SixtyGeometry.orbit,SixtyGeometry.g,SixtyGeometry.b,NativeStableSeed004.g,GroundNativePrefixInitial.tolerance_return]
    using NativeStableSeed004.unit_before ⟨60,by decide⟩

/-- Unconditional original-seed verdict at update60 of the exact native map. -/
theorem actual_four_source_tests : MeetsConvergence GroundNativeControls.originalTolerance
    GroundOriginalResiduals.ε (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
      (NativeStableFrame004.κ : ℝ) (1/2) (SixtyGeometry.orbit 59) (SixtyGeometry.orbit 60) :=
  SixtyGeometry.actual_four_source_tests previous_enclosed current_enclosed current_unit
end
end SbtCosmo.Derivation.NativeStableSeed004.Sixty
