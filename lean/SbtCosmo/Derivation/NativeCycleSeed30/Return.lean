import SbtCosmo.Derivation.NativeCycleSeed30.Transport
import SbtCosmo.Derivation.NativeCycle30.OriginalReturn
import SbtCosmo.Derivation.NativeCycle30.Diagnostics
namespace SbtCosmo.Derivation.NativeCycleSeed30
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval Metric Filter
open scoped Topology

/-- Actual original-seed even/odd returns to the constructed source two-cycle,
with all guards, unit iterates, a persistent site-density oscillation, and no
state or density limit. Entry is discharged by the populated finite transport.
This file is generated but must not be treated as proved before its full build. -/
theorem original_seed_cycle :
    ∃ z₀ z₁ : ComplexField,
      g z₀ = z₁ ∧ g z₁ = z₀ ∧ complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
      (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
      Tendsto (fun n : ℕ => (g^[2*n]) GroundOriginalSeed.initial) atTop (nhds z₀) ∧
      Tendsto (fun n : ℕ => (g^[2*n+1]) GroundOriginalSeed.initial) atTop (nhds z₁) ∧
      (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ)
        ((g^[n]) GroundOriginalSeed.initial) ∧
        NativeLegal (GroundNativePrefixInitial.τ : ℝ)
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
          ((g^[n]) GroundOriginalSeed.initial) ∧
        complexNormSq ((g^[n]) GroundOriginalSeed.initial) = 1) ∧
      (¬ ∃ l, Tendsto (fun n : ℕ => (g^[n]) GroundOriginalSeed.initial) atTop (nhds l)) ∧
      Tendsto (fun n : ℕ => Complex.normSq ((g^[2*n]) GroundOriginalSeed.initial 4)) atTop (nhds (Complex.normSq (z₀ 4))) ∧
      Tendsto (fun n : ℕ => Complex.normSq ((g^[2*n+1]) GroundOriginalSeed.initial 4)) atTop (nhds (Complex.normSq (z₁ 4))) ∧
      (∀ᶠ n : ℕ in atTop, (9/20 : ℝ) < Complex.normSq ((g^[2*n+1]) GroundOriginalSeed.initial 4)-
        Complex.normSq ((g^[2*n]) GroundOriginalSeed.initial 4)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq ((g^[n]) GroundOriginalSeed.initial 4)) atTop (nhds l) := by
  exact NativeCycle30.original_seed_cycle_of_entry N original_seed_entry guards_before

/-- Successive source updates stay separated eventually and the literal four-test
conjunction fails eventually; the finite entry certificate is discharged. -/
theorem original_seed_eventual_source_failure :
    (∀ᶠ n : ℕ in atTop, (9/40 : ℝ) < GroundComplexEuclidean.l2
      ((g^[n+1]) GroundOriginalSeed.initial-(g^[n]) GroundOriginalSeed.initial)) ∧
    (∀ᶠ n : ℕ in atTop, ¬ GroundSourceDiagnostics.MeetsConvergence
      GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
      ((g^[n]) GroundOriginalSeed.initial) ((g^[n+1]) GroundOriginalSeed.initial)) := by
  exact NativeCycle30.original_seed_diagnostics_of_entry N original_seed_entry guards_before
end
end SbtCosmo.Derivation.NativeCycleSeed30
