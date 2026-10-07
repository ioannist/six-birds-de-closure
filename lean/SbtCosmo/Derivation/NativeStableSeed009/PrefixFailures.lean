import SbtCosmo.Derivation.NativeStableSeed009.Prefix060
import SbtCosmo.Derivation.NativeStableSeed009.PrefixFailureGeometry
import SbtCosmo.Derivation.NativeFiniteSourceBoxes
import SbtCosmo.Derivation.NativeBoxLastUpdateGap
namespace SbtCosmo.Derivation.NativeStableSeed009.PrefixFailures
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundSourceDiagnostics PrefixFailureGeometry
open scoped Topology

/-- Candidate binding; not proved until the original-seed prefix dependencies close. -/
theorem input_included (j : Fin 60) :
    (NativeFinitePairJets.steps Prefix060.tube j).jet.input.Included (boxes j.castSucc) := by
  fin_cases j <;> (unfold StateBox.Included included;decide +kernel)

theorem endpoint_included : Prefix060.currentBox.Included (boxes (60 : Fin 61)) := by
  unfold StateBox.Included included
  decide +kernel

theorem boxes_enclosed (j : Fin 61) :
    (boxes j).Contains (unpack (SixtyGeometry.orbit j.val)) := by
  by_cases h : j.val < 60
  · let k : Fin 60 := ⟨j.val,h⟩
    have hs := NativeFiniteSourceBoxes.before_endpoint Prefix060.tube
      NativeStableFrame009.background_sound Prefix060.initial k
    have hb := StateBox.included_sound (input_included k) hs
    have hk : k.castSucc = j := by ext;rfl
    rw [hk] at hb
    simpa only [SixtyGeometry.orbit,SixtyGeometry.g,SixtyGeometry.b,Prefix060.g,
      GroundNativePrefixInitial.tolerance_return] using hb
  · have hj : j = (60 : Fin 61) := by apply Fin.ext;have hj := j.isLt;omega
    rw [hj]
    have hb := StateBox.included_sound endpoint_included Prefix060.current_enclosed
    simpa only [SixtyGeometry.orbit,SixtyGeometry.g,SixtyGeometry.b,Prefix060.g,
      GroundNativePrefixInitial.tolerance_return] using hb

theorem all_first_sixty_fail (n : ℕ) (hn : n < 60) :
    ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      SixtyGeometry.b (NativeStableFrame009.κ : ℝ) (1/2)
      (SixtyGeometry.orbit n) (SixtyGeometry.orbit (n+1)) :=
  all_first_sixty_fail_of_enclosures boxes_enclosed n hn

theorem guarded_first_sixty_fail (n : ℕ) (hn : n < 60) :
    ActivePhase GroundNativeControls.originalTolerance SixtyGeometry.b
      (NativeStableFrame009.κ : ℝ) (SixtyGeometry.orbit n) ∧
    NativeLegal GroundNativeControls.originalTolerance SixtyGeometry.b
      (NativeStableFrame009.κ : ℝ) (1/2) (SixtyGeometry.orbit n) ∧
    ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      SixtyGeometry.b (NativeStableFrame009.κ : ℝ) (1/2)
      (SixtyGeometry.orbit n) (SixtyGeometry.orbit (n+1)) := by
  have hg := Prefix060.guards_before n hn
  have hreturn : ActivePhase GroundNativeControls.originalTolerance SixtyGeometry.b
      (NativeStableFrame009.κ : ℝ) (SixtyGeometry.orbit n) ∧
    NativeLegal GroundNativeControls.originalTolerance SixtyGeometry.b
      (NativeStableFrame009.κ : ℝ) (1/2) (SixtyGeometry.orbit n) := by
    simpa only [SixtyGeometry.orbit,SixtyGeometry.g,SixtyGeometry.b,Prefix060.g,
      GroundNativePrefixInitial.tolerance_return] using hg
  exact ⟨hreturn.1,hreturn.2,all_first_sixty_fail n hn⟩

theorem all_first_sixty_update_gaps (n : ℕ) (hn : n < 60) :
    GroundOriginalResiduals.ε < lastUpdateResidual GroundNativeControls.originalTolerance
      SixtyGeometry.b (NativeStableFrame009.κ : ℝ) (1/2) (SixtyGeometry.orbit n) := by
  let j : Fin 60 := ⟨n,hn⟩
  have he : GroundOriginalResiduals.ε = (εRat : ℝ) := by
    norm_num [GroundOriginalResiduals.ε,εRat]
  rw [he]
  exact NativeBoxLastUpdateGap.last_update_gap_of_boxes
    (boxes_enclosed j.castSucc) (boxes_enclosed j.succ)
    (imag j) (positive j) (coordinate j) (gap_arithmetic j)
    (Function.iterate_succ_apply' SixtyGeometry.g n GroundOriginalSeed.initial).symm
end
end SbtCosmo.Derivation.NativeStableSeed009.PrefixFailures
