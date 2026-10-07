import SbtCosmo.Derivation.GroundOriginalCycle30CoordinateBasin

/-! A common full complex attraction basin for the same exactly real nearby
cycle reached by the original complex seed. Realness is earned using the real
baseline centre's orbit, not a false realness premise on the original seed. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30RealBasin
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline GroundOriginalCycle30OpenReturn GroundOriginalCycle30BasinBridge
open scoped Topology ContDiff

theorem open_real_source_basin : ∃ a : State, NativeRealProfiles.IsReal (source a) ∧
    ∃ δ > 0, ∃ r > 0, ∀ p ∈ closedBall baseline δ,
      ∃ z₀ z₁ : ComplexField,
        NativeRealProfiles.IsReal z₀ ∧ NativeRealProfiles.IsReal z₁ ∧
        native p z₀ = z₁ ∧ native p z₁ = z₀ ∧
        complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
        (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
        decode z₀ ∈ closedBall a (r/4) ∧
        Tendsto (fun n : ℕ => (native p)^[2*n] GroundOriginalSeed.initial) atTop (nhds z₀) ∧
        Tendsto (fun n : ℕ => (native p)^[2*n+1] GroundOriginalSeed.initial) atTop (nhds z₁) ∧
        (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2
            ((native p)^[n] GroundOriginalSeed.initial) ∧
          NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2)
            ((native p)^[n] GroundOriginalSeed.initial) ∧
          complexNormSq ((native p)^[n] GroundOriginalSeed.initial) = 1) ∧
        ∀ z : ComplexField, decode z ∈ closedBall a r →
          Tendsto (fun n : ℕ => (native p)^[2*n] z) atTop (nhds z₀) ∧
          Tendsto (fun n : ℕ => (native p)^[2*n+1] z) atTop (nhds z₁) ∧
          (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 ((native p)^[n] z) ∧
            NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2) ((native p)^[n] z)) ∧
          ∀ n : ℕ, complexNormSq ((native p)^[n+1] z) = 1 := by
  obtain ⟨a,hreal,δ,hδ,r,hr,hreturns⟩ := GroundOriginalCycle30CoordinateBasin.open_coordinate_basin
  refine ⟨a,hreal,δ,hδ,r,hr,fun p hp => ?_⟩
  obtain ⟨v,hv,hfix,hvg,hgap,hseed,hseedguards,hlocal⟩ := hreturns p hp
  have hv' : GroundOriginalCycle30Baseline.map p (GroundOriginalCycle30Baseline.map p v) = v := by
    simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using hfix
  have h01 : native p (source v) = source (GroundOriginalCycle30Baseline.map p v) :=
    (GroundNativeCouplingContinuation.source_step NativeCycleFrame30.T _ _ p v).symm
  have h10 : native p (source (GroundOriginalCycle30Baseline.map p v)) = source v := by
    have hh : native p (source (GroundOriginalCycle30Baseline.map p v)) =
        source (GroundOriginalCycle30Baseline.map p (GroundOriginalCycle30Baseline.map p v)) :=
      (GroundNativeCouplingContinuation.source_step NativeCycleFrame30.T _ _ p
        (GroundOriginalCycle30Baseline.map p v)).symm
    simpa only [hv'] using hh
  have hu₁ : complexNormSq (source (GroundOriginalCycle30Baseline.map p v)) = 1 := by
    rw [← h01]
    exact GroundNativeEscape.nativeUpdate_unit threshold_nonneg hvg.1.2
  have hu₀ : complexNormSq (source v) = 1 := by
    rw [← h10]
    exact GroundNativeEscape.nativeUpdate_unit threshold_nonneg hvg.2.2
  have hcentre := source_returns_of_squared_limit (hlocal a (mem_closedBall_self hr.le)).1 hvg.1
  have hreal₀ : NativeRealProfiles.IsReal (source v) :=
    NativeRealProfiles.limit_real
      (fun n => NativeRealProfiles.iterate_real p.1 p.2 (1/2) threshold_nonneg hreal (2*n)) hcentre.1
  have hreal₁ : NativeRealProfiles.IsReal (source (GroundOriginalCycle30Baseline.map p v)) := by
    rw [← h01]
    exact NativeRealProfiles.update_real p.1 p.2 (1/2) threshold_nonneg hreal₀
  have hseedreturns := source_returns_of_squared_limit hseed hvg.1
  have he : Tendsto (fun n : ℕ => (native p)^[2*n] GroundOriginalSeed.initial)
      atTop (nhds (source v)) := by simpa only [source_seed] using hseedreturns.1
  have ho : Tendsto (fun n : ℕ => (native p)^[2*n+1] GroundOriginalSeed.initial)
      atTop (nhds (source (GroundOriginalCycle30Baseline.map p v))) := by
    simpa only [source_seed] using hseedreturns.2
  have hguards (n : ℕ) : ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2
      ((native p)^[n] GroundOriginalSeed.initial) ∧
    NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2)
      ((native p)^[n] GroundOriginalSeed.initial) := by
    simpa only [source_seed] using source_guards_of_all_guards hseedguards n
  have hunit (n : ℕ) : complexNormSq ((native p)^[n] GroundOriginalSeed.initial) = 1 := by
    cases n with
    | zero => exact GroundOriginalSeed.initial_unit
    | succ n =>
      rw [Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit threshold_nonneg (hguards n).2
  refine ⟨source v,source (GroundOriginalCycle30Baseline.map p v),hreal₀,hreal₁,h01,h10,
    hu₀,hu₁,hgap,?_,he,ho,?_,fun z hz => ?_⟩
  · simpa only [decode_source] using hv
  · intro n
    exact ⟨(hguards n).1,(hguards n).2,hunit n⟩
  · have hx := hlocal (decode z) hz
    have hret := source_returns_of_squared_limit hx.1 hvg.1
    have hg := source_guards_of_all_guards (all_guards_of_pair_guards hx.2)
    have hez : Tendsto (fun n : ℕ => (native p)^[2*n] z) atTop (nhds (source v)) := by
      simpa only [source_decode] using hret.1
    have hoz : Tendsto (fun n : ℕ => (native p)^[2*n+1] z)
        atTop (nhds (source (GroundOriginalCycle30Baseline.map p v))) := by
      simpa only [source_decode] using hret.2
    have hgz (n : ℕ) : ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 ((native p)^[n] z) ∧
        NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2) ((native p)^[n] z) := by
      simpa only [source_decode] using hg n
    refine ⟨hez,hoz,hgz,fun n => ?_⟩
    rw [Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit threshold_nonneg (hgz n).2
end
end SbtCosmo.Derivation.GroundOriginalCycle30RealBasin
