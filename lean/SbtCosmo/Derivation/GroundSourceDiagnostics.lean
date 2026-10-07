import SbtCosmo.Derivation.GroundComplexResidual

/-! Mathematical reification of the four Step26/54 convergence diagnostics.
The final fixed-point gap retains both source phase_align calls. The sourcing
comparison repeats the same sourced expression, exactly as the source does. -/
namespace SbtCosmo.Derivation.GroundSourceDiagnostics
noncomputable section
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean GroundComplexResidual

def lastUpdateResidual (τ : ℝ) (b : Field) (κ m : ℝ) (previous : ComplexField) : ℝ :=
  l2 (nativeUpdate τ b κ m previous-previous)
def finalFixedGap (τ : ℝ) (b : Field) (κ : ℝ) (z : ComplexField) : ℝ :=
  l2 (nativePhase τ (nativePhase τ (nativeCandidate b κ z) z) z-z)
def finalEigenResidual (b : Field) (κ : ℝ) (z : ComplexField) : ℝ :=
  l2 (shifted (complexSourcePotential b κ z) (complexEnergy (complexSourcePotential b κ z) z) z)
def finalSourcingResidual (b : Field) (κ : ℝ) (z : ComplexField) : ℝ :=
  Real.sqrt (normSq (complexSourcePotential b κ z-complexSourcePotential b κ z))
def MeetsConvergence (τ ε : ℝ) (b : Field) (κ m : ℝ) (previous z : ComplexField) : Prop :=
  lastUpdateResidual τ b κ m previous ≤ ε ∧ finalFixedGap τ b κ z ≤ ε ∧
    finalEigenResidual b κ z ≤ ε ∧ finalSourcingResidual b κ z ≤ ε

theorem source_zero (b : Field) (z : ComplexField) : complexSourcePotential b 0 z = b := by
  funext i
  simp [complexSourcePotential, BackgroundSelection.potential]

theorem sourcing_self_comparison_zero (b : Field) (κ : ℝ) (z : ComplexField) :
    finalSourcingResidual b κ z = 0 := by simp [finalSourcingResidual, normSq]

theorem double_phase_real_sign {τ : ℝ} {g z : ComplexField} (hτ : 0 ≤ τ)
    (ho : τ < ‖overlap g z‖) :
    nativePhase τ (nativePhase τ (-g) z) z = nativePhase τ (nativePhase τ g z) z := by
  rw [nativePhase_real_sign_invariant hτ ho]

end
end SbtCosmo.Derivation.GroundSourceDiagnostics
