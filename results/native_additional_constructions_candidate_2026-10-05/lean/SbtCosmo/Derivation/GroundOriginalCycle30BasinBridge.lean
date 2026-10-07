import SbtCosmo.Derivation.GroundOriginalCycle30OpenReturn

/-! Exact source returns for arbitrary full complex initial states.
Norm-one at iteration zero is not imposed on the ambient attraction basin. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30BasinBridge
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline GroundOriginalCycle30OpenReturn
open scoped Topology ContDiff

def decode (z : ComplexField) : State := NativeCycleFrame30.T.symm (unpack z)

theorem source_decode (z : ComplexField) : source (decode z) = z := by
  dsimp [source,decode]
  rw [NativeCycleFrame30.T.apply_symm_apply]
  exact packCLE.apply_symm_apply _

theorem decode_source (x : State) : decode (source x) = x := by
  change NativeCycleFrame30.T.symm (packCLE.symm (packCLE (NativeCycleFrame30.T x))) = x
  rw [packCLE.symm_apply_apply,NativeCycleFrame30.T.symm_apply_apply]

theorem source_returns_of_squared_limit {p : Parameter} {x v : State}
    (he : Tendsto (fun n : ℕ => ((GroundOriginalCycle30Baseline.map p)^[2])^[n] x)
      atTop (nhds v)) (hg : (p,v) ∈ guard) :
    Tendsto (fun n : ℕ => (native p)^[2*n] (source x)) atTop (nhds (source v)) ∧
    Tendsto (fun n : ℕ => (native p)^[2*n+1] (source x)) atTop
      (nhds (source (GroundOriginalCycle30Baseline.map p v))) := by
  have hm : ContinuousAt (GroundOriginalCycle30Baseline.map p) v := by
    have hc := (GroundNativeCouplingContinuation.coordinate_joint_regular_at NativeCycleFrame30.T
      threshold_nonneg hg).continuousAt
    simpa only [Function.uncurry,Function.comp_def] using
      (ContinuousAt.comp (g := Function.uncurry (GroundOriginalCycle30Baseline.map))
        (f := fun x : State => (p,x)) (x := v) hc (continuousAt_const.prodMk continuousAt_id))
  constructor
  · have hh := source_continuous.continuousAt.tendsto.comp he
    simpa only [Function.comp_def,← Function.iterate_mul,source_iterate,native] using hh
  · have hh := (source_continuous.continuousAt.tendsto.comp hm.tendsto).comp he
    simpa only [Function.comp_def,← Function.iterate_mul,← Function.iterate_succ_apply',
      source_iterate,native] using hh

theorem all_guards_of_pair_guards {p : Parameter} {x : State}
    (hg : ∀ n : ℕ, (p,((GroundOriginalCycle30Baseline.map p)^[2])^[n] x) ∈ pairGuard) :
    ∀ n : ℕ, (p,(GroundOriginalCycle30Baseline.map p)^[n] x) ∈ guard := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hi : n = 2*(n/2) := by omega
    rw [hi,Function.iterate_mul]
    exact (hg (n/2)).1
  · have hi : n = 2*(n/2)+1 := by omega
    rw [hi,Function.iterate_succ_apply',Function.iterate_mul]
    exact (hg (n/2)).2

theorem source_guards_of_all_guards {p : Parameter} {x : State}
    (hg : ∀ n : ℕ, (p,(GroundOriginalCycle30Baseline.map p)^[n] x) ∈ guard) :
    ∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 ((native p)^[n] (source x)) ∧
      NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2) ((native p)^[n] (source x)) := by
  intro n
  have h := hg n
  change ActivePhase _ _ _ (source _) ∧ NativeLegal _ _ _ _ (source _) at h
  simpa only [source_iterate,native] using h
end
end SbtCosmo.Derivation.GroundOriginalCycle30BasinBridge
