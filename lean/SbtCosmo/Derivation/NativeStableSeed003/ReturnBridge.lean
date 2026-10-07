import SbtCosmo.Derivation.NativeStable003.Return
import SbtCosmo.Derivation.GroundCertifiedNativeEntry
namespace SbtCosmo.Derivation.NativeStableSeed003.ReturnBridge
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundCertifiedNativeEntry Metric Filter
open scoped Topology

def g : ComplexField → ComplexField := NativeStable003.g
def orbit (n : ℕ) : ComplexField := (g^[n]) GroundOriginalSeed.initial

/-- An explicit conditional bridge. The entry and pre-entry guards must be
supplied by the populated finite original-seed transport, not by a record field. -/
theorem original_seed_return_of_entry (N : ℕ)
    (he : NativeStableFrame003.T.symm (unpack (orbit N)) ∈ closedBall (NativeStableFrame003.T.symm (-NativeStableFrame003.u,0)) (NativeStable003Arithmetic.ρ : ℝ))
    (hp : ∀ j : Fin N,
      ActivePhase GroundNativeControls.originalTolerance (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeStableFrame003.κ : ℝ) (orbit j.val) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeStableFrame003.κ : ℝ) (1/2) (orbit j.val)) :
    Tendsto orbit atTop (nhds (realEmbed (-NativeStableFrame003.u))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeStableFrame003.κ : ℝ) (orbit n) ∧
      NativeLegal GroundNativeControls.originalTolerance
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeStableFrame003.κ : ℝ) (1/2) (orbit n) ∧
      complexNormSq (orbit n) = 1 := by
  have hs := NativeStable003.negative_basin he
  have ht : Tendsto (fun n : ℕ => (g^[n]) (orbit N)) atTop (nhds (realEmbed (-NativeStableFrame003.u))) := hs.1
  have hg : ∀ n : ℕ,
      ActivePhase GroundNativeControls.originalTolerance (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeStableFrame003.κ : ℝ) (orbit n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeStableFrame003.κ : ℝ) (1/2) (orbit n) :=
    iterate_property_of_tail g GroundOriginalSeed.initial
      (fun z => ActivePhase GroundNativeControls.originalTolerance
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeStableFrame003.κ : ℝ) z ∧
        NativeLegal GroundNativeControls.originalTolerance
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeStableFrame003.κ : ℝ) (1/2) z)
      N hp (fun n => ⟨(hs.2 n).1,(hs.2 n).2.1⟩)
  have hu (n : ℕ) : complexNormSq (orbit n) = 1 := by
    induction n with
    | zero => exact GroundOriginalSeed.initial_unit
    | succ n _ =>
      rw [orbit,Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 (hg n).2
  exact ⟨iterate_tendsto_of_tail g GroundOriginalSeed.initial _ N ht,fun n => ⟨(hg n).1,(hg n).2,hu n⟩⟩

theorem original_seed_geometric_tail_of_entry (N : ℕ)
    (he : NativeStableFrame003.T.symm (unpack (orbit N)) ∈ closedBall (NativeStableFrame003.T.symm (-NativeStableFrame003.u,0)) (NativeStable003Arithmetic.ρ : ℝ)) (n : ℕ) :
    dist (NativeStableFrame003.T.symm (unpack (orbit (n+N)))) (NativeStableFrame003.T.symm (-NativeStableFrame003.u,0)) ≤
      (NativeStable003Arithmetic.rate : ℝ)^n * dist (NativeStableFrame003.T.symm (unpack (orbit N))) (NativeStableFrame003.T.symm (-NativeStableFrame003.u,0)) := by
  have hs := NativeStable003.negative_basin he
  simpa only [orbit,g,Function.iterate_add_apply] using (hs.2 n).2.2
end
end SbtCosmo.Derivation.NativeStableSeed003.ReturnBridge
