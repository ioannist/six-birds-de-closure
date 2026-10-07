import SbtCosmo.Derivation.NativeStable007.Arithmetic
namespace SbtCosmo.Derivation.NativeStable007
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundKernelTube GroundOriginalFirstTube
open GroundRationalInterval GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open NativeStable007Arithmetic Metric Filter
open scoped Topology

def g : ComplexField → ComplexField := nativeUpdate GroundNativeControls.originalTolerance
  (background originalBackground) (NativeStableFrame007.κ : ℝ) (1/2)

theorem frame_return : certificate.T = NativeStableFrame007.T := by rfl

/-- A populated explicit attraction neighborhood of the actual original
positive branch, with all guards and a geometric tail. Original-seed entry
is not a premise disguised as a field: it is a separate pending obligation. -/
theorem positive_basin {z : ComplexField}
    (hz : certificate.T.symm (unpack z) ∈ closedBall (certificate.T.symm (NativeStableFrame007.u,0)) (ρ : ℝ)) :
    Tendsto (fun n : ℕ => (g^[n]) z) atTop (nhds (realEmbed NativeStableFrame007.u)) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) (NativeStableFrame007.κ : ℝ) ((g^[n]) z) ∧
      NativeLegal GroundNativeControls.originalTolerance (background originalBackground) (NativeStableFrame007.κ : ℝ) (1/2) ((g^[n]) z) ∧
      dist (certificate.T.symm (unpack ((g^[n]) z))) (certificate.T.symm (NativeStableFrame007.u,0)) ≤
        (rate : ℝ)^n*dist (certificate.T.symm (unpack z)) (certificate.T.symm (NativeStableFrame007.u,0)) := by
  have ht : (GroundNativePrefixInitial.τ : ℝ) < 1 := by
    rw [GroundNativePrefixInitial.tolerance_return]
    exact GroundNativeControls.originalTolerance_guard.2
  have h := certificate.actual_ball_convergence responses response_included derivative_included rows
    NativeStableFrame007.background_sound NativeStableFrame007.ground_data.1 NativeStableFrame007.ground_data.2 ht
    (by exact_mod_cast radius_pos.le) basis_nonneg (certificate.basis_norm basis_nonneg basis_rows)
    NativeStableFrame007.root_enclosed (by intro j; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩) hz
  simpa only [g,certificate,GroundUncertainNativeBasin.Certificate.contractionRate,
    NNReal.coe_mk,GroundNativePrefixInitial.tolerance_return] using h

/-- Negative representatives retain the explicit radius and all guards by
active-region reflection. This is a local theorem, not original-seed entry. -/
theorem negative_basin {z : ComplexField}
    (hz : certificate.T.symm (unpack z) ∈ closedBall (certificate.T.symm (-NativeStableFrame007.u,0)) (ρ : ℝ)) :
    Tendsto (fun n : ℕ => (g^[n]) z) atTop (nhds (realEmbed (-NativeStableFrame007.u))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) (NativeStableFrame007.κ : ℝ) ((g^[n]) z) ∧
      NativeLegal GroundNativeControls.originalTolerance (background originalBackground) (NativeStableFrame007.κ : ℝ) (1/2) ((g^[n]) z) ∧
      dist (certificate.T.symm (unpack ((g^[n]) z))) (certificate.T.symm (-NativeStableFrame007.u,0)) ≤
        (rate : ℝ)^n*dist (certificate.T.symm (unpack z)) (certificate.T.symm (-NativeStableFrame007.u,0)) := by
  have ht : (GroundNativePrefixInitial.τ : ℝ) < 1 := by
    rw [GroundNativePrefixInitial.tolerance_return]
    exact GroundNativeControls.originalTolerance_guard.2
  have h := certificate.actual_negative_ball_convergence responses response_included derivative_included rows
    NativeStableFrame007.background_sound NativeStableFrame007.ground_data.1 NativeStableFrame007.ground_data.2 ht
    (by exact_mod_cast radius_pos.le) basis_nonneg (certificate.basis_norm basis_nonneg basis_rows)
    NativeStableFrame007.root_enclosed (by intro j; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩) hz
  simpa only [g,certificate,GroundUncertainNativeBasin.Certificate.contractionRate,
    NNReal.coe_mk,GroundNativePrefixInitial.tolerance_return] using h
end
end SbtCosmo.Derivation.NativeStable007
