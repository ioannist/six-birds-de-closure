import SbtCosmo.Derivation.GroundNativeCouplingSmooth
import SbtCosmo.Derivation.GroundNativeBackgroundContinuation

/-! The literal native map with both background and coupling variable.
Two-step smoothness and open guards require, and are earned from, both stages.
The source conjugacy is exact even on totalized fallback branches. -/
namespace SbtCosmo.Derivation.GroundNativeCouplingContinuation
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeJacobian
open GroundNativeLocal Filter Metric
open scoped Topology ContDiff
abbrev Parameter := Field × ℝ

def f (T : State ≃L[ℝ] State) (τ m : ℝ) (p : Parameter) : State → State :=
  coordinateMap T τ p.1 p.2 m

def guard (T : State ≃L[ℝ] State) (τ m : ℝ) : Set (Parameter × State) :=
  {p | ActivePhase τ p.1.1 p.1.2 (pack (T p.2)) ∧
    NativeLegal τ p.1.1 p.1.2 m (pack (T p.2))}

def pairGuard (T : State ≃L[ℝ] State) (τ m : ℝ) : Set (Parameter × State) :=
  {p | p ∈ guard T τ m ∧ (p.1,f T τ m p.1 p.2) ∈ guard T τ m}

theorem coordinate_joint_regular_at (T : State ≃L[ℝ] State) {τ m : ℝ}
    {p : Parameter} {x : State} (hτ : 0 ≤ τ) (hg : (p,x) ∈ guard T τ m) :
    ContDiffAt ℝ ∞ (Function.uncurry (f T τ m)) (p,x) := by
  have h := GroundNativeBackgroundContinuation.pair_guard_data hτ hg.1 hg.2
  have hc := GroundNativeCouplingSmooth.nativePairMap_joint_smooth_at hτ h.1
    (Real.sqrt_pos.mp (hτ.trans_lt h.2))
  have hp : ContDiff ℝ ∞ (fun q : Parameter × State => (q.1,T q.2)) := by fun_prop
  have hcomp := ContDiffAt.comp
    (g := fun q : Parameter × State => nativePairMap τ q.1.1 q.1.2 m q.2)
    (f := fun q : Parameter × State => (q.1,T q.2)) (p,x) hc hp.contDiffAt
  exact T.symm.contDiff.contDiffAt.comp (p,x) hcomp

theorem coordinate_joint_guards_near (T : State ≃L[ℝ] State) {τ m : ℝ}
    {p : Parameter} {x : State} (hτ : 0 ≤ τ) (hg : (p,x) ∈ guard T τ m) :
    guard T τ m ∈ nhds (p,x) := by
  have h := GroundNativeBackgroundContinuation.pair_guard_data hτ hg.1 hg.2
  have hp : ContinuousAt (fun q : Parameter × State => (q.1,T q.2)) (p,x) := by fun_prop
  exact hp.eventually (GroundNativeCouplingSmooth.native_guards_joint_near hτ h.1 h.2)

theorem squared_joint_regular_at (T : State ≃L[ℝ] State) {τ m : ℝ}
    {p : Parameter} {x : State} (hτ : 0 ≤ τ) (hg : (p,x) ∈ pairGuard T τ m) :
    ContDiffAt ℝ ∞ (Function.uncurry (fun q => (f T τ m q)^[2])) (p,x) := by
  have hc₀ := coordinate_joint_regular_at T hτ hg.1
  have hc₁ := coordinate_joint_regular_at T hτ hg.2
  have hp : ContDiffAt ℝ ∞ (fun q : Parameter × State => (q.1,f T τ m q.1 q.2)) (p,x) :=
    contDiff_fst.contDiffAt.prodMk hc₀
  simpa only [Function.uncurry,Function.comp_def,Function.iterate_succ_apply',
    Function.iterate_zero_apply] using
    (ContDiffAt.comp (g := Function.uncurry (f T τ m))
      (f := fun q : Parameter × State => (q.1,f T τ m q.1 q.2)) (p,x) hc₁ hp)

theorem squared_joint_guards_near (T : State ≃L[ℝ] State) {τ m : ℝ}
    {p : Parameter} {x : State} (hτ : 0 ≤ τ) (hg : (p,x) ∈ pairGuard T τ m) :
    pairGuard T τ m ∈ nhds (p,x) := by
  have hp : ContinuousAt (fun q : Parameter × State => (q.1,f T τ m q.1 q.2)) (p,x) :=
    continuous_fst.continuousAt.prodMk (coordinate_joint_regular_at T hτ hg.1).continuousAt
  have he := hp.eventually (coordinate_joint_guards_near T hτ hg.2)
  filter_upwards [coordinate_joint_guards_near T hτ hg.1,he] with q h₀ h₁
  exact ⟨h₀,h₁⟩

theorem source_step (T : State ≃L[ℝ] State) (τ m : ℝ) (p : Parameter) (x : State) :
    pack (T (f T τ m p x)) = nativeUpdate τ p.1 p.2 m (pack (T x)) := by
  unfold f coordinateMap nativePairMap
  rw [T.apply_symm_apply]
  exact packCLE.apply_symm_apply _

theorem source_iterate (T : State ≃L[ℝ] State) (τ m : ℝ) (p : Parameter) (x : State) (n : ℕ) :
    pack (T ((f T τ m p)^[n] x)) = (nativeUpdate τ p.1 p.2 m)^[n] (pack (T x)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',source_step,Function.iterate_succ_apply',ih]
end
end SbtCosmo.Derivation.GroundNativeCouplingContinuation
