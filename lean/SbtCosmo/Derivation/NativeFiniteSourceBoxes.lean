import SbtCosmo.Derivation.NativeFinitePairJets
import SbtCosmo.Derivation.NativePairOrbit
namespace NativeFiniteSourceBoxes
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox GroundNativeTransportGeometry
open NativePairCertificates NativeFinitePairJets Metric
open scoped Topology
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State} {N : ℕ}

theorem before_endpoint (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {z : ComplexField}
    (hi : T.symm (unpack z) ∈ closedBall (c.centers 0) (c.radii 0 : ℝ))
    (j : Fin (2*N)) :
    (steps c j).jet.input.Contains (unpack (((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[j.val]) z)) := by
  have hx : T.symm (unpack (((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[j.val]) z)) ∈
      closedBall (steps c j).center ((steps c j).radius : ℝ) := by
    rw [NativePairOrbit.coordinate_from_source]
    exact orbit_enclosed c hb hi j
  have hp := (steps c j).input_on_ball hx
  simpa only [T.apply_symm_apply] using hp

theorem at_endpoint (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {z : ComplexField}
    (hi : T.symm (unpack z) ∈ closedBall (c.centers 0) (c.radii 0 : ℝ))
    (u v : Fin 8 → ℚ) {ρ s : ℚ}
    (hcenter : c.centers (Fin.last N) = T.symm (point u v))
    (hradius : c.radii (Fin.last N) = ρ)
    (hs : 0 ≤ s) (hT : ‖T.toContinuousLinearMap‖ ≤ (s : ℝ)) :
    (around u v ρ s).Contains (unpack (((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[2*N]) z)) := by
  have hx : T.symm (unpack (((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[2*N]) z)) ∈
      closedBall (T.symm (point u v)) (ρ : ℝ) := by
    rw [NativePairOrbit.coordinate_from_source,← hcenter,← hradius]
    exact c.enclosed hb hi (Fin.last N)
  have hp := input_on_ball T u v hs hT hx
  simpa only [T.apply_symm_apply] using hp
end
end NativeFiniteSourceBoxes
