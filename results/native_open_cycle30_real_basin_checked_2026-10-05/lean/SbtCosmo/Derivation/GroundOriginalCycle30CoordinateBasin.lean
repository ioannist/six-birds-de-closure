import SbtCosmo.Derivation.GroundOriginalCycle30RealBaseline
import SbtCosmo.Derivation.GroundOriginalCycle30BasinBridge
import SbtCosmo.Derivation.GroundParametricSeedBasinReturn

/-! Nearby original-seed cycles together with a common full-state attraction
basin. The baseline basin centre has a separately earned real source profile. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30CoordinateBasin
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline GroundOriginalCycle30OpenReturn GroundOriginalCycle30BasinBridge
open scoped Topology ContDiff

theorem open_coordinate_basin : ∃ a : State, NativeRealProfiles.IsReal (source a) ∧
    ∃ δ > 0, ∃ r > 0, ∀ p ∈ closedBall baseline δ,
      ∃ v ∈ closedBall a (r/4), ((GroundOriginalCycle30Baseline.map p)^[2]) v = v ∧
        (p,v) ∈ pairGuard ∧
        (9/20 : ℝ) < Complex.normSq (source (GroundOriginalCycle30Baseline.map p v) 4)-
          Complex.normSq (source v 4) ∧
        Tendsto (fun n : ℕ => ((GroundOriginalCycle30Baseline.map p)^[2])^[n] seed)
          atTop (nhds v) ∧
        (∀ n : ℕ, (p,(GroundOriginalCycle30Baseline.map p)^[n] seed) ∈ guard) ∧
        ∀ x ∈ closedBall a r,
          Tendsto (fun n : ℕ => ((GroundOriginalCycle30Baseline.map p)^[2])^[n] x)
            atTop (nhds v) ∧
          ∀ n : ℕ, (p,((GroundOriginalCycle30Baseline.map p)^[2])^[n] x) ∈ pairGuard := by
  obtain ⟨a,hreal,hf,hd,hg,hgap,hlim⟩ := GroundOriginalCycle30RealBaseline.actual_real_baseline
  have hc := GroundNativeCouplingContinuation.squared_joint_regular_at NativeCycleFrame30.T
    threshold_nonneg hg
  have hs := GroundNativeCouplingContinuation.squared_joint_guards_near NativeCycleFrame30.T
    threshold_nonneg hg
  let target : Set (Parameter × State) := {q | q ∈ pairGuard ∧
    (9/20 : ℝ) < Complex.normSq (source (GroundOriginalCycle30Baseline.map q.1 q.2) 4)-Complex.normSq (source q.2 4)}
  have ht : target ∈ nhds (baseline,a) := by
    have hm := (GroundNativeCouplingContinuation.coordinate_joint_regular_at NativeCycleFrame30.T
      threshold_nonneg hg.1).continuousAt
    have h₁ : ContinuousAt (fun q : Parameter × State => Complex.normSq (source (GroundOriginalCycle30Baseline.map q.1 q.2) 4))
        (baseline,a) := density_continuous.continuousAt.comp hm
    have h₀ : ContinuousAt (fun q : Parameter × State => Complex.normSq (source q.2 4))
        (baseline,a) := density_continuous.continuousAt.comp continuous_snd.continuousAt
    exact inter_mem hs ((h₁.sub h₀).eventually (Ioi_mem_nhds hgap))
  have horbit (n : ℕ) : ContinuousAt
      (Function.uncurry (fun p => (GroundOriginalCycle30Baseline.map p)^[2])) (baseline,((GroundOriginalCycle30Baseline.map baseline)^[2])^[n] seed) :=
    (GroundNativeCouplingContinuation.squared_joint_regular_at NativeCycleFrame30.T
      threshold_nonneg (original_seed_pair_guards n)).continuousAt
  have hguards (n : ℕ) : pairGuard ∈ nhds (baseline,((GroundOriginalCycle30Baseline.map baseline)^[2])^[n] seed) :=
    GroundNativeCouplingContinuation.squared_joint_guards_near NativeCycleFrame30.T
      threshold_nonneg (original_seed_pair_guards n)
  obtain ⟨δ,hδ,r,hr,hr'⟩ := GroundParametricSeedBasinReturn.nearby_original_seed_target_basin_returns
    (f := fun p => (GroundOriginalCycle30Baseline.map p)^[2]) (p := baseline) (u := a) (a := seed)
    (s := pairGuard) (t := target) (hc.of_le (by simp)) hf hd hs ht horbit hguards hlim
  refine ⟨a,hreal,δ,hδ,r,hr,fun p hp => ?_⟩
  obtain ⟨v,hv,hvf,hvt,he,hg,hlocal⟩ := hr' p hp
  exact ⟨v,hv,hvf,hvt.1,hvt.2,he,all_guards_of_pair_guards hg,hlocal⟩
end
end SbtCosmo.Derivation.GroundOriginalCycle30CoordinateBasin
