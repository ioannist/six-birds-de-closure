import SbtCosmo.Derivation.NativeCycleFrame20
import SbtCosmo.Derivation.GroundOriginalSamples
import SbtCosmo.Derivation.GroundCoordinates.Point005
namespace SbtCosmo.Derivation.NativeStableFrame005
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundRationalInterval GroundMatrixCoordinates GroundOriginalFirstTube
open GroundKernelTube GroundPointCoordinates
open scoped Topology

def B : Fin 8 → Interval := NativeCycleFrame20.B
def κ : ℚ := GroundSamples.Point005.a
def z : Fin 9 → ℚ := GroundSamples.Point005.z
def r : ℚ := GroundSamples.Point005.r
def S : QMatrix := GroundCoordinates.Point005.S
def P : QMatrix := GroundCoordinates.Point005.P
def R : QMatrix := GroundCoordinates.Point005.R
def Q : QMatrix := GroundCoordinates.Point005.Q
theorem real_inverse : InverseArithmetic S P := GroundCoordinates.Point005.real_inverse
theorem imag_inverse : InverseArithmetic R Q := GroundCoordinates.Point005.imag_inverse
def T : GroundNativePhase.State ≃L[ℝ] GroundNativePhase.State := (basis real_inverse).prodCongr (basis imag_inverse)

theorem background_sound : ∀ j : Fin 8, (B j).Contains (background originalBackground j) :=
  NativeCycleFrame20.background_sound

theorem coupling_return : GroundOriginalSamples.couplings 5 = κ := by decide +kernel

def u : Field := (GroundOriginalContinuation.branch (κ : ℝ)).1

theorem ground_data : normSq u = 1 ∧ GroundSourceJacobian.groundMap
    (background originalBackground) (κ : ℝ) u = u := by
  have h := GroundOriginalSamples.sample_ground_return 5
  rw [coupling_return] at h
  exact ⟨h.2.2.1,h.2.2.2.2⟩

theorem root_enclosed : ∀ j : Fin 8, (GroundBackgroundKernel.fieldBox z r j).Contains (u j) := by
  have hx := GroundOriginalSamples.branch_in_sample_ball 5
  rw [coupling_return] at hx
  change GroundOriginalContinuation.branch (κ : ℝ) ∈
    Metric.closedBall (center GroundSamples.Point005.z) (GroundSamples.Point005.r : ℝ) at hx
  have hb := box_sound originalBackground GroundSamples.Point005.a GroundSamples.Point005.c GroundSamples.Point005.z GroundSamples.Point005.r
    (κ := (κ : ℝ)) (by simp [κ,GroundSamples.Point005.a,GroundSamples.Point005.c]) hx
  intro j
  have h := hb (.state j.castSucc)
  simpa only [z,r,u,GroundBackgroundKernel.fieldBox,box,GroundResidualEnclosure.valuation,
    coord,Fin.lastCases_castSucc] using h
end
end SbtCosmo.Derivation.NativeStableFrame005
