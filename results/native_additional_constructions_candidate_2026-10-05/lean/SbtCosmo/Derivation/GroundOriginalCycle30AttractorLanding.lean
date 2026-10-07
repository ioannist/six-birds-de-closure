import SbtCosmo.Derivation.GroundOriginalCycle30RealBasin

/-! Source-topological attraction and original-seed readouts of the same
constructed exactly real nearby two-cycle. A full complex neighborhood is
proved; it is not replaced by the lower-dimensional real or unit locus. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30AttractorLanding
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline GroundOriginalCycle30OpenReturn GroundOriginalCycle30BasinBridge
open scoped Topology ContDiff

theorem decode_continuous : Continuous decode :=
  NativeCycleFrame30.T.symm.continuous.comp packCLE.symm.continuous

theorem basin_near_cycle {a : State} {r : ℝ} {z : ComplexField} (hr : 0 < r)
    (hz : decode z ∈ closedBall a (r/4)) :
    {w : ComplexField | decode w ∈ closedBall a r} ∈ nhds z := by
  have hball : decode z ∈ ball a r := by
    apply mem_ball.mpr
    exact (mem_closedBall.mp hz).trans_lt (by linarith)
  filter_upwards [decode_continuous.continuousAt.eventually (isOpen_ball.mem_nhds hball)] with w hw
  exact mem_closedBall.mpr (mem_ball.mp hw).le

/-- Exactly real source two-cycles have a genuine full complex open attraction
neighborhood and the original complex seed converges to these same phases. -/
theorem open_real_attracting_cycle : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    ∃ z₀ z₁ : ComplexField,
      NativeRealProfiles.IsReal z₀ ∧ NativeRealProfiles.IsReal z₁ ∧
      native p z₀ = z₁ ∧ native p z₁ = z₀ ∧
      complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
      (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
      Tendsto (fun n : ℕ => (native p)^[2*n] GroundOriginalSeed.initial) atTop (nhds z₀) ∧
      Tendsto (fun n : ℕ => (native p)^[2*n+1] GroundOriginalSeed.initial) atTop (nhds z₁) ∧
      (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2
          ((native p)^[n] GroundOriginalSeed.initial) ∧
        NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2)
          ((native p)^[n] GroundOriginalSeed.initial) ∧
        complexNormSq ((native p)^[n] GroundOriginalSeed.initial) = 1) ∧
      ∃ s : Set ComplexField, s ∈ nhds z₀ ∧ ∀ z ∈ s,
        Tendsto (fun n : ℕ => (native p)^[2*n] z) atTop (nhds z₀) ∧
        Tendsto (fun n : ℕ => (native p)^[2*n+1] z) atTop (nhds z₁) ∧
        (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 ((native p)^[n] z) ∧
          NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2) ((native p)^[n] z)) ∧
        ∀ n : ℕ, complexNormSq ((native p)^[n+1] z) = 1 := by
  obtain ⟨a,_,δ,hδ,r,hr,hreturns⟩ := GroundOriginalCycle30RealBasin.open_real_source_basin
  refine ⟨δ,hδ,fun p hp => ?_⟩
  obtain ⟨z₀,z₁,hreal₀,hreal₁,h01,h10,hu₀,hu₁,hgap,hnear,he,ho,hguards,hlocal⟩ := hreturns p hp
  exact ⟨z₀,z₁,hreal₀,hreal₁,h01,h10,hu₀,hu₁,hgap,he,ho,hguards,
    {z | decode z ∈ closedBall a r},basin_near_cycle hr hnear,hlocal⟩

/-- Every choice of original-seed even/odd limit has the earned real profile;
realness does not depend on selecting convenient witnesses. -/
theorem nearby_original_limits_real : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    ∀ z₀ z₁ : ComplexField,
      Tendsto (fun n : ℕ => (native p)^[2*n] GroundOriginalSeed.initial) atTop (nhds z₀) →
      Tendsto (fun n : ℕ => (native p)^[2*n+1] GroundOriginalSeed.initial) atTop (nhds z₁) →
      NativeRealProfiles.IsReal z₀ ∧ NativeRealProfiles.IsReal z₁ := by
  obtain ⟨δ,hδ,hreturns⟩ := open_real_attracting_cycle
  refine ⟨δ,hδ,fun p hp z₀ z₁ he ho => ?_⟩
  obtain ⟨a,c,ha,hc,_,_,_,_,_,he',ho',_⟩ := hreturns p hp
  rw [tendsto_nhds_unique he he',tendsto_nhds_unique ho ho']
  exact ⟨ha,hc⟩

/-- The same real attracting cycle supplies both nonconvergent readouts and
the eventual failure of the actual original four-test stopping conjunction. -/
theorem open_real_original_seed_readouts : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    (¬ ∃ l, Tendsto (fun n : ℕ => (native p)^[n] GroundOriginalSeed.initial) atTop (nhds l)) ∧
    (¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq ((native p)^[n] GroundOriginalSeed.initial 4))
      atTop (nhds l)) ∧
    (∀ᶠ n : ℕ in atTop, (9/20 : ℝ) < Complex.normSq ((native p)^[2*n+1] GroundOriginalSeed.initial 4)-
      Complex.normSq ((native p)^[2*n] GroundOriginalSeed.initial 4)) ∧
    (∀ᶠ n : ℕ in atTop, (9/40 : ℝ) < GroundComplexEuclidean.l2
      (((native p)^[n+1]) GroundOriginalSeed.initial-((native p)^[n]) GroundOriginalSeed.initial)) ∧
    (∀ᶠ n : ℕ in atTop, ¬ GroundSourceDiagnostics.MeetsConvergence
      GroundNativeControls.originalTolerance GroundOriginalResiduals.ε p.1 p.2 (1/2)
      (((native p)^[n]) GroundOriginalSeed.initial) (((native p)^[n+1]) GroundOriginalSeed.initial)) := by
  obtain ⟨δ,hδ,hreturns⟩ := open_real_attracting_cycle
  refine ⟨δ,hδ,fun p hp => ?_⟩
  obtain ⟨a,c,_,_,_,_,_,_,hgap,he,ho,hguards,_⟩ := hreturns p hp
  have hne : c ≠ a := by
    intro h
    rw [h] at hgap
    linarith
  have hd := NativeOriginalSeedCycleReturn.density_returns
    (u := fun n => (native p)^[n] GroundOriginalSeed.initial) he ho hgap (by norm_num)
  have hu (n : ℕ) := (hguards n).2.2
  have hn := NativeCycleSourceFailure.successive_l2_away
    (u := fun n => (native p)^[n] GroundOriginalSeed.initial) he ho hu hgap
  have hf := NativeCycleSourceFailure.source_tests_eventually_fail
    (τ := (GroundNativePrefixInitial.τ : ℝ)) (bg := p.1) (κ := p.2) (m := (1/2))
    (z := GroundOriginalSeed.initial) he ho hu hgap
    (by norm_num [GroundOriginalResiduals.ε] : GroundOriginalResiduals.ε < (9/20 : ℝ)/2)
  refine ⟨NativeOriginalSeedCycleReturn.no_limit_of_distinct_subsequences
    (fun n => (native p)^[n] GroundOriginalSeed.initial) he ho hne,hd.2.2.2,hd.2.2.1,?_,?_⟩
  · norm_num only at hn
    exact hn
  · simpa only [native,GroundNativePrefixInitial.tolerance_return] using hf
end
end SbtCosmo.Derivation.GroundOriginalCycle30AttractorLanding
