import SbtCosmo.Derivation.NativeCycleSeed20.Return
import SbtCosmo.Derivation.NativeCycle20.RealOriginalReturn
namespace SbtCosmo.Derivation.NativeCycleSeed20.RealReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration NativeRealProfiles Metric Filter
open scoped Topology

/-- The same original-seed cycle return additionally has exactly real profiles.
Generated candidate: full finite entry/guards and this module must compile before
this is an unconditional mechanized original-seed theorem. -/
theorem original_seed_cycle_real :
    ∃ z₀ z₁ : ComplexField,
      IsReal z₀ ∧ IsReal z₁ ∧ g z₀ = z₁ ∧ g z₁ = z₀ ∧ complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
      (1/4 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
      Tendsto (fun n : ℕ => (g^[2*n]) GroundOriginalSeed.initial) atTop (nhds z₀) ∧
      Tendsto (fun n : ℕ => (g^[2*n+1]) GroundOriginalSeed.initial) atTop (nhds z₁) ∧
      (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame20.κ : ℝ)
        ((g^[n]) GroundOriginalSeed.initial) ∧
        NativeLegal (GroundNativePrefixInitial.τ : ℝ)
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame20.κ : ℝ) (1/2)
          ((g^[n]) GroundOriginalSeed.initial) ∧
        complexNormSq ((g^[n]) GroundOriginalSeed.initial) = 1) ∧
      (¬ ∃ l, Tendsto (fun n : ℕ => (g^[n]) GroundOriginalSeed.initial) atTop (nhds l)) ∧
      Tendsto (fun n : ℕ => Complex.normSq ((g^[2*n]) GroundOriginalSeed.initial 4)) atTop (nhds (Complex.normSq (z₀ 4))) ∧
      Tendsto (fun n : ℕ => Complex.normSq ((g^[2*n+1]) GroundOriginalSeed.initial 4)) atTop (nhds (Complex.normSq (z₁ 4))) ∧
      (∀ᶠ n : ℕ in atTop, (1/4 : ℝ) < Complex.normSq ((g^[2*n+1]) GroundOriginalSeed.initial 4)-
        Complex.normSq ((g^[2*n]) GroundOriginalSeed.initial 4)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq ((g^[n]) GroundOriginalSeed.initial 4)) atTop (nhds l) := by
  obtain ⟨a,c,h01,h10,hu0,hu1,hgap,he,ho,hguards,hn,hd0,hd1,hgapTail,hdn⟩ :=
    NativeCycleSeed20.original_seed_cycle
  have hr := NativeCycle20.RealOriginalReturn.limits_real_of_entry N original_seed_entry he ho
  exact ⟨a,c,hr.1,hr.2,h01,h10,hu0,hu1,hgap,he,ho,hguards,hn,hd0,hd1,hgapTail,hdn⟩
end
end SbtCosmo.Derivation.NativeCycleSeed20.RealReturn
