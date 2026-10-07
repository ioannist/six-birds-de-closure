import SbtCosmo.Derivation.NativeCycle30.OriginalReturn
import SbtCosmo.Derivation.NativeCycleSourceFailure
namespace SbtCosmo.Derivation.NativeCycle30
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval Metric Filter
open scoped Topology

theorem original_seed_diagnostics_of_entry (N : ℕ)
    (hentry : NativeCycleFrame30.T.symm (unpack ((g^[2*N]) GroundOriginalSeed.initial)) ∈
      closedBall pair.first.center (Step000.ρ : ℝ))
    (hbefore : ∀ n : ℕ, n < 2*N →
      ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ)
        ((g^[n]) GroundOriginalSeed.initial) ∧
      NativeLegal (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
        ((g^[n]) GroundOriginalSeed.initial)) :
    (∀ᶠ n : ℕ in atTop, (9/40 : ℝ) < GroundComplexEuclidean.l2
      ((g^[n+1]) GroundOriginalSeed.initial-(g^[n]) GroundOriginalSeed.initial)) ∧
    (∀ᶠ n : ℕ in atTop, ¬ GroundSourceDiagnostics.MeetsConvergence
      GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
      ((g^[n]) GroundOriginalSeed.initial) ((g^[n+1]) GroundOriginalSeed.initial)) := by
  obtain ⟨a,b,_,_,_,_,hg,he,ho,hguards,_⟩ := original_seed_cycle_of_entry N hentry hbefore
  have hu (n : ℕ) := (hguards n).2.2
  have hn := NativeCycleSourceFailure.successive_l2_away he ho hu hg
  have hf := NativeCycleSourceFailure.source_tests_eventually_fail he ho hu hg
    (by norm_num [GroundOriginalResiduals.ε] : GroundOriginalResiduals.ε < (9/20 : ℝ)/2)
  constructor
  · norm_num only at hn
    exact hn
  · simpa only [g,GroundNativePrefixInitial.tolerance_return] using hf

/-- A populated local-source consequence, with an explicit unit initial state.
The original seed is covered only after its finite entry proof closes. -/
theorem local_source_tests_eventually_fail {z : ComplexField}
    (hz : NativeCycleFrame30.T.symm (unpack z) ∈ closedBall pair.first.center (Step000.ρ : ℝ))
    (hu : complexNormSq z = 1) :
    ∀ᶠ n : ℕ in atTop, ¬ GroundSourceDiagnostics.MeetsConvergence
      GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)
      ((g^[n]) z) ((g^[n+1]) z) := by
  obtain ⟨a,b,_,_,_,_,_,hg,hr⟩ := actual_source_cycle
  have h := hr z hz
  have hu' (n : ℕ) : complexNormSq ((g^[n]) z) = 1 :=
    NativeOriginalSeedCycleReturn.full_unit (by exact_mod_cast Step000.threshold_nonneg)
      hu (fun n => (h.2.2.1 n).2) n
  have hf := NativeCycleSourceFailure.source_tests_eventually_fail h.1 h.2.1 hu' hg
    (by norm_num [GroundOriginalResiduals.ε] : GroundOriginalResiduals.ε < (9/20 : ℝ)/2)
  simpa only [g,GroundNativePrefixInitial.tolerance_return] using hf
end
end SbtCosmo.Derivation.NativeCycle30
