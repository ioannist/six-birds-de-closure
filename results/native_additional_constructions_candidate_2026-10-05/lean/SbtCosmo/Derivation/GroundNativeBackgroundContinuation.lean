import SbtCosmo.Derivation.GroundNativeParameterSmooth
import SbtCosmo.Derivation.GroundNativeReflection
import SbtCosmo.Derivation.GroundParametricBranchReturn

/-! Continuation helpers for the literal native update. Reflection is an exact
coordinate conjugacy; agreement with the positive map is used only locally on
the proved active phase branch. -/
namespace SbtCosmo.Derivation.GroundNativeBackgroundContinuation
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeJacobian
open GroundNativeLocal GroundNativeReflection GroundSourceJacobian Filter Metric
open scoped Topology ContDiff

theorem pair_guard_data {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ b κ (pack x))
    (hn : NativeLegal τ b κ m (pack x)) :
    τ < overlapNorm b κ x ∧ τ < Real.sqrt (stateNormSq (mixed b κ m x)) := by
  have ho : τ < overlapNorm b κ x := by
    simpa only [ActivePhase,nativeCandidate_pack,overlap_norm_pair] using ha
  refine ⟨ho,?_⟩
  simpa only [NativeLegal,← pack_mixed_native hτ b κ m x ho,norm_pack] using hn

theorem native_joint_regular_at {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ b κ (pack x))
    (hn : NativeLegal τ b κ m (pack x)) :
    ContDiffAt ℝ ∞ (fun p : Field × State => nativePairMap τ p.1 κ m p.2) (b,x) := by
  have h := pair_guard_data hτ ha hn
  exact GroundNativeParameterSmooth.nativePairMap_joint_smooth_at hτ h.1
    (Real.sqrt_pos.mp (hτ.trans_lt h.2))

theorem native_joint_guards_near {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ b κ (pack x))
    (hn : NativeLegal τ b κ m (pack x)) :
    {p : Field × State | ActivePhase τ p.1 κ (pack p.2) ∧
      NativeLegal τ p.1 κ m (pack p.2)} ∈ nhds (b,x) := by
  have h := pair_guard_data hτ ha hn
  exact GroundNativeParameterSmooth.native_guards_joint_near hτ h.1 h.2

def reflectedMap (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ) (x : State) : State :=
  -(coordinateMap T τ b κ m (-x))

def reflectedRegion (T : State ≃L[ℝ] State) (τ κ m : ℝ) : Set (Field × State) :=
  {p | ActivePhase τ p.1 κ (pack (T (-p.2))) ∧
    NativeLegal τ p.1 κ m (pack (T (-p.2)))}

theorem reflected_step_return (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ)
    (x : State) :
    pack (T (-reflectedMap T τ b κ m x)) = nativeUpdate τ b κ m (pack (T (-x))) := by
  simp only [reflectedMap,neg_neg,coordinateMap,T.apply_symm_apply,nativePairMap]
  exact packCLE.apply_symm_apply _

theorem reflected_iterate_return (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ)
    (x : State) (n : ℕ) :
    pack (T (-((reflectedMap T τ b κ m)^[n] x))) =
      (nativeUpdate τ b κ m)^[n] (pack (T (-x))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',reflected_step_return,Function.iterate_succ_apply',ih]

theorem reflected_joint_regular_at (T : State ≃L[ℝ] State) {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ b κ (pack (T (-x))))
    (hn : NativeLegal τ b κ m (pack (T (-x)))) :
    ContDiffAt ℝ ∞ (fun p : Field × State => reflectedMap T τ p.1 κ m p.2) (b,x) := by
  have hc := native_joint_regular_at hτ ha hn
  have hp : ContDiff ℝ ∞ (fun p : Field × State => (p.1,T (-p.2))) := by fun_prop
  have hcomp := ContDiffAt.comp (g := fun p : Field × State => nativePairMap τ p.1 κ m p.2)
    (f := fun p : Field × State => (p.1,T (-p.2))) (b,x) hc hp.contDiffAt
  exact (T.symm.contDiff.contDiffAt.comp (b,x) hcomp).neg

theorem reflected_joint_guards_near (T : State ≃L[ℝ] State) {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ b κ (pack (T (-x))))
    (hn : NativeLegal τ b κ m (pack (T (-x)))) :
    reflectedRegion T τ κ m ∈ nhds (b,x) := by
  have hp : ContinuousAt (fun p : Field × State => (p.1,T (-p.2))) (b,x) := by fun_prop
  exact hp.eventually (native_joint_guards_near hτ ha hn)

theorem reflected_eventual_return_at_root (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    reflectedMap T τ b κ m =ᶠ[nhds (T.symm (u,0))] coordinateMap T τ b κ m := by
  have hp : Tendsto T (nhds (T.symm (u,0))) (nhds (u,(0 : Field))) := by
    simpa only [T.apply_symm_apply] using T.continuous.continuousAt.tendsto (x := T.symm (u,0))
  filter_upwards [hp.eventually (nativeUpdate_near_fixed (m := m) hu hf hτ0 hτ1)] with x hx
  have hpack : pack (T (-x)) = -pack (T x) := by
    change packCLE (T (-x)) = -packCLE (T x)
    rw [map_neg,map_neg]
  unfold reflectedMap coordinateMap nativePairMap
  rw [hpack,nativeUpdate_neg b κ m _ hτ0 hx.2.1,unpack_neg,map_neg,neg_neg]

theorem reflected_root_derivative (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    HasFDerivAt (reflectedMap T τ b κ m) (coordinateDerivative T b κ m u) (T.symm (u,0)) :=
  (coordinate_hasFDerivAt T hu hf hτ0 hτ1).congr_of_eventuallyEq
    (reflected_eventual_return_at_root T hu hf hτ0 hτ1)

theorem reflected_root_fixed (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    reflectedMap T τ b κ m (T.symm (u,0)) = T.symm (u,0) := by
  rw [(reflected_eventual_return_at_root T hu hf hτ0 hτ1).self_of_nhds]
  exact coordinate_fixed T hu hf hτ0 hτ1
end
end SbtCosmo.Derivation.GroundNativeBackgroundContinuation
