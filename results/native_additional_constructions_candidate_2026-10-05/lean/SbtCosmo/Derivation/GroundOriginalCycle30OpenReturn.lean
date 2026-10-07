import SbtCosmo.Derivation.GroundOriginalCycle30Baseline
import SbtCosmo.Derivation.GroundParametricSeedTargetReturn

/-! A positive joint background/coupling neighborhood of the original-seed
attracting two-cycle. The nearby cycle and seed attraction are conclusions.
The two native guards and the certified density gap are preserved. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30OpenReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline
open scoped Topology ContDiff

def native (p : Parameter) : ComplexField → ComplexField :=
  nativeUpdate (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2)

theorem density_continuous : Continuous (fun x : State => Complex.normSq (source x 4)) :=
  (by fun_prop : Continuous (fun z : ComplexField => Complex.normSq (z 4))).comp source_continuous

theorem original_seed_pair_guards (n : ℕ) :
    (baseline,((GroundOriginalCycle30Baseline.map baseline)^[2])^[n] seed) ∈ pairGuard := by
  constructor
  · simpa only [← Function.iterate_mul] using original_seed_guards (2*n)
  · simpa only [← Function.iterate_mul,Function.iterate_succ_apply'] using original_seed_guards (2*n+1)

/-- Nearby coordinate cycles are constructed from the full-state two-step
contraction, and the actual original seed is carried into their basins. -/
theorem open_original_seed_coordinate_cycle : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    ∃ v : State, ((GroundOriginalCycle30Baseline.map p)^[2]) v = v ∧ (p,v) ∈ pairGuard ∧
      (9/20 : ℝ) < Complex.normSq (source (GroundOriginalCycle30Baseline.map p v) 4)-Complex.normSq (source v 4) ∧
      Tendsto (fun n : ℕ => ((GroundOriginalCycle30Baseline.map p)^[2])^[n] seed) atTop (nhds v) ∧
      ∀ n : ℕ, (p,(GroundOriginalCycle30Baseline.map p)^[n] seed) ∈ guard := by
  obtain ⟨a,hf,hd,hg,hgap,hlim⟩ := actual_baseline
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
  obtain ⟨δ,hδ,r,_,hr⟩ := GroundParametricSeedTargetReturn.nearby_original_seed_target_returns
    (f := fun p => (GroundOriginalCycle30Baseline.map p)^[2]) (p := baseline) (u := a) (a := seed)
    (s := pairGuard) (t := target) (hc.of_le (by simp)) hf hd hs ht horbit hguards hlim
  refine ⟨δ,hδ,fun p hp => ?_⟩
  obtain ⟨v,_,hv,hvt,he,hg⟩ := hr p hp
  refine ⟨v,hv,hvt.1,hvt.2,he,fun n => ?_⟩
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hi : n = 2*(n/2) := by omega
    rw [hi,Function.iterate_mul]
    exact (hg (n/2)).1
  · have hi : n = 2*(n/2)+1 := by omega
    rw [hi,Function.iterate_succ_apply',Function.iterate_mul]
    exact (hg (n/2)).2

/-- Robust source-level two-cycle return from the literal original seed.
The parameter ball has eight background coordinates and one coupling coordinate.
No numerical radius or IEEE-arithmetic interpretation is claimed. -/
theorem open_original_seed_source_cycle : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    ∃ z₀ z₁ : ComplexField,
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
      (¬ ∃ l, Tendsto (fun n : ℕ => (native p)^[n] GroundOriginalSeed.initial) atTop (nhds l)) ∧
      (∀ᶠ n : ℕ in atTop, (9/20 : ℝ) <
        Complex.normSq ((native p)^[2*n+1] GroundOriginalSeed.initial 4)-
        Complex.normSq ((native p)^[2*n] GroundOriginalSeed.initial 4)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq ((native p)^[n] GroundOriginalSeed.initial 4))
        atTop (nhds l) := by
  obtain ⟨δ,hδ,hr⟩ := open_original_seed_coordinate_cycle
  refine ⟨δ,hδ,fun p hp => ?_⟩
  obtain ⟨v,hv,hvg,hgap,he,hguards⟩ := hr p hp
  have hv' : GroundOriginalCycle30Baseline.map p (GroundOriginalCycle30Baseline.map p v) = v := by
    simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using hv
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
  have he' : Tendsto (fun n : ℕ => (native p)^[2*n] GroundOriginalSeed.initial)
      atTop (nhds (source v)) := by
    have hh := source_continuous.continuousAt.tendsto.comp he
    simpa only [Function.comp_def,← Function.iterate_mul,source_iterate,source_seed,native] using hh
  have hm : ContinuousAt (GroundOriginalCycle30Baseline.map p) v := by
    have hc := (GroundNativeCouplingContinuation.coordinate_joint_regular_at NativeCycleFrame30.T
      threshold_nonneg hvg.1).continuousAt
    simpa only [Function.uncurry,Function.comp_def] using
      (ContinuousAt.comp (g := Function.uncurry (GroundOriginalCycle30Baseline.map)) (f := fun x : State => (p,x))
        (x := v) hc (continuousAt_const.prodMk continuousAt_id))
  have ho' : Tendsto (fun n : ℕ => (native p)^[2*n+1] GroundOriginalSeed.initial)
      atTop (nhds (source (GroundOriginalCycle30Baseline.map p v))) := by
    have hh := (source_continuous.continuousAt.tendsto.comp hm.tendsto).comp he
    simpa only [Function.comp_def,← Function.iterate_mul,← Function.iterate_succ_apply',
      source_iterate,source_seed,native] using hh
  have hg (n : ℕ) : ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2
      ((native p)^[n] GroundOriginalSeed.initial) ∧
    NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2)
      ((native p)^[n] GroundOriginalSeed.initial) := by
    have h := hguards n
    change ActivePhase _ _ _ (source _) ∧ NativeLegal _ _ _ _ (source _) at h
    simpa only [source_iterate,source_seed,native] using h
  have hu (n : ℕ) : complexNormSq ((native p)^[n] GroundOriginalSeed.initial) = 1 := by
    cases n with
    | zero => exact GroundOriginalSeed.initial_unit
    | succ n =>
      rw [Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit threshold_nonneg (hg n).2
  have hne : source (GroundOriginalCycle30Baseline.map p v) ≠ source v := by
    intro h
    rw [h] at hgap
    linarith
  have hd := NativeOriginalSeedCycleReturn.density_returns
    (u := fun n => (native p)^[n] GroundOriginalSeed.initial) he' ho' hgap (by norm_num)
  refine ⟨source v,source (GroundOriginalCycle30Baseline.map p v),h01,h10,hu₀,hu₁,hgap,he',ho',?_,?_,hd.2.2.1,hd.2.2.2⟩
  · intro n
    exact ⟨(hg n).1,(hg n).2,hu n⟩
  · exact NativeOriginalSeedCycleReturn.no_limit_of_distinct_subsequences
      (fun n => (native p)^[n] GroundOriginalSeed.initial) he' ho' hne
end
end SbtCosmo.Derivation.GroundOriginalCycle30OpenReturn
