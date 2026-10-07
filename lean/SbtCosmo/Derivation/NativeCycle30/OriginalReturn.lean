import SbtCosmo.Derivation.NativeCycle30.Source
import SbtCosmo.Derivation.NativeOriginalSeedCycleReturn
namespace SbtCosmo.Derivation.NativeCycle30
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval Metric Filter
open scoped Topology

/-- Conditional composition of the constructed actual source cycle with an
earned original-seed even entry and the finite-prefix guards. The numerical
entry and guard obligations are explicitly visible until the transport family
supplies them; this is not yet an unconditional original-seed theorem. -/
theorem original_seed_cycle_of_entry (N : ℕ)
    (hentry : NativeCycleFrame30.T.symm (unpack ((g^[2*N]) GroundOriginalSeed.initial)) ∈
      closedBall pair.first.center (Step000.ρ : ℝ))
    (hbefore : ∀ n : ℕ, n < 2*N →
      ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ)
        ((g^[n]) GroundOriginalSeed.initial) ∧
      NativeLegal (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
        ((g^[n]) GroundOriginalSeed.initial)) :
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
  obtain ⟨z₀,z₁,h01,h10,hne,hu0,hu1,hgap,hr⟩ := actual_source_cycle
  have ht := hr ((g^[2*N]) GroundOriginalSeed.initial) hentry
  have heo := NativeOriginalSeedCycleReturn.even_entry_returns g N ht.1 ht.2.1
  have hguards (n : ℕ) : ActivePhase (GroundNativePrefixInitial.τ : ℝ)
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ)
      ((g^[n]) GroundOriginalSeed.initial) ∧
    NativeLegal (GroundNativePrefixInitial.τ : ℝ)
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
      ((g^[n]) GroundOriginalSeed.initial) := by
    by_cases hn : n < 2*N
    · exact hbefore n hn
    · have hi : n-2*N+2*N = n := by omega
      simpa only [← Function.iterate_add_apply,hi] using ht.2.2.1 (n-2*N)
  have hunit (n : ℕ) : complexNormSq ((g^[n]) GroundOriginalSeed.initial) = 1 :=
    NativeOriginalSeedCycleReturn.full_unit (by exact_mod_cast Step000.threshold_nonneg)
      GroundOriginalSeed.initial_unit (fun n => (hguards n).2) n
  have hd := NativeOriginalSeedCycleReturn.density_returns
    (u := fun n => (g^[n]) GroundOriginalSeed.initial) heo.1 heo.2 hgap (by norm_num)
  refine ⟨z₀,z₁,h01,h10,hu0,hu1,hgap,heo.1,heo.2,?_,?_,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2⟩
  · intro n
    exact ⟨(hguards n).1,(hguards n).2,hunit n⟩
  · exact NativeOriginalSeedCycleReturn.no_limit_of_distinct_subsequences
      (fun n => (g^[n]) GroundOriginalSeed.initial) heo.1 heo.2 hne
end
end SbtCosmo.Derivation.NativeCycle30
