import SbtCosmo.Derivation.GroundOriginalCycle30OpenReturn

/-! Exact consequences for the original stopping tests on a joint open
background/coupling neighborhood, and a coupling-only slice through it. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30OpenDiagnostics
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline GroundOriginalCycle30OpenReturn
open scoped Topology

theorem open_original_seed_source_failure : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    (∀ᶠ n : ℕ in atTop, (9/40 : ℝ) < GroundComplexEuclidean.l2
      (((native p)^[n+1]) GroundOriginalSeed.initial-((native p)^[n]) GroundOriginalSeed.initial)) ∧
    (∀ᶠ n : ℕ in atTop, ¬ GroundSourceDiagnostics.MeetsConvergence
      GroundNativeControls.originalTolerance GroundOriginalResiduals.ε p.1 p.2 (1/2)
      (((native p)^[n]) GroundOriginalSeed.initial) (((native p)^[n+1]) GroundOriginalSeed.initial)) := by
  obtain ⟨δ,hδ,hr⟩ := open_original_seed_source_cycle
  refine ⟨δ,hδ,fun p hp => ?_⟩
  obtain ⟨z₀,z₁,_,_,_,_,hgap,he,ho,hguards,_⟩ := hr p hp
  have hu (n : ℕ) := (hguards n).2.2
  have hn := NativeCycleSourceFailure.successive_l2_away
    (u := fun n => (native p)^[n] GroundOriginalSeed.initial) he ho hu hgap
  have hf := NativeCycleSourceFailure.source_tests_eventually_fail
    (τ := (GroundNativePrefixInitial.τ : ℝ)) (bg := p.1) (κ := p.2) (m := (1/2))
    (z := GroundOriginalSeed.initial) he ho hu hgap
    (by norm_num [GroundOriginalResiduals.ε] : GroundOriginalResiduals.ε < (9/20 : ℝ)/2)
  constructor
  · norm_num only at hn
    exact hn
  · simpa only [native,GroundNativePrefixInitial.tolerance_return] using hf

/-- A positive coupling interval through 30, with the original background and
original seed held exactly fixed. This is an interval result, not a universal
high-coupling runaway claim. -/
theorem open_coupling_nonconvergence : ∃ δ > 0, ∀ κ ∈ closedBall (30 : ℝ) δ,
    (¬ ∃ l, Tendsto (fun n : ℕ =>
      (native (baseline.1,κ))^[n] GroundOriginalSeed.initial) atTop (nhds l)) ∧
    (¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq
      ((native (baseline.1,κ))^[n] GroundOriginalSeed.initial 4)) atTop (nhds l)) ∧
    ∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ) baseline.1 κ
        ((native (baseline.1,κ))^[n] GroundOriginalSeed.initial) ∧
      NativeLegal (GroundNativePrefixInitial.τ : ℝ) baseline.1 κ (1/2)
        ((native (baseline.1,κ))^[n] GroundOriginalSeed.initial) ∧
      complexNormSq ((native (baseline.1,κ))^[n] GroundOriginalSeed.initial) = 1 := by
  obtain ⟨δ,hδ,hr⟩ := open_original_seed_source_cycle
  refine ⟨δ,hδ,fun κ hκ => ?_⟩
  have hp : (baseline.1,κ) ∈ closedBall baseline δ := by
    apply mem_closedBall.mpr
    change max (dist baseline.1 baseline.1) (dist κ baseline.2) ≤ δ
    rw [dist_self,max_eq_right (dist_nonneg (x := κ) (y := baseline.2))]
    simpa only [baseline,NativeCycleFrame30.κ,Rat.cast_ofNat] using mem_closedBall.mp hκ
  obtain ⟨z₀,z₁,_,_,_,_,_,_,_,hg,hn,_,hd⟩ := hr (baseline.1,κ) hp
  exact ⟨hn,hd,hg⟩
end
end SbtCosmo.Derivation.GroundOriginalCycle30OpenDiagnostics
