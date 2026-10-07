import SbtCosmo.Derivation.GroundNativeCouplingContinuation

/-! Joint background/coupling/state regularity on the original complex source
carrier, with exact pair/source conversion and both literal open guards. -/
namespace SbtCosmo.Derivation.GroundNativeSourceParameterSmooth
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeJacobian Filter
open scoped Topology ContDiff
abbrev Parameter := Field × ℝ

theorem pack_unpack (z : ComplexField) : pack (unpack z) = z := packCLE.apply_symm_apply z

theorem encode_nativePairMap (τ m : ℝ) (p : Parameter) (z : ComplexField) :
    pack (nativePairMap τ p.1 p.2 m (unpack z)) = nativeUpdate τ p.1 p.2 m z := by
  unfold nativePairMap
  rw [pack_unpack,pack_unpack]

theorem native_joint_smooth_at {τ m : ℝ} {p : Parameter} {z : ComplexField}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ p.1 p.2 z) (hn : NativeLegal τ p.1 p.2 m z) :
    ContDiffAt ℝ ∞ (fun q : Parameter × ComplexField => nativeUpdate τ q.1.1 q.1.2 m q.2) (p,z) := by
  have ha' : ActivePhase τ p.1 p.2 (pack (unpack z)) := by simpa only [pack_unpack] using ha
  have hn' : NativeLegal τ p.1 p.2 m (pack (unpack z)) := by simpa only [pack_unpack] using hn
  have hg := GroundNativeBackgroundContinuation.pair_guard_data hτ ha' hn'
  have hc := GroundNativeCouplingSmooth.nativePairMap_joint_smooth_at hτ hg.1
    (Real.sqrt_pos.mp (hτ.trans_lt hg.2))
  have hu : ContDiff ℝ ∞ (fun q : Parameter × ComplexField => (q.1,unpack q.2)) := by
    have hcu : ContDiff ℝ ∞ unpack := packCLE.symm.contDiff
    fun_prop
  have hcomp := ContDiffAt.comp
    (g := fun q : Parameter × State => nativePairMap τ q.1.1 q.1.2 m q.2)
    (f := fun q : Parameter × ComplexField => (q.1,unpack q.2)) (p,z) hc hu.contDiffAt
  simpa only [packCLE_apply,encode_nativePairMap] using (packCLE.contDiff.contDiffAt.comp (p,z) hcomp)

theorem native_joint_guards_near {τ m : ℝ} {p : Parameter} {z : ComplexField}
    (hτ : 0 ≤ τ) (ha : ActivePhase τ p.1 p.2 z) (hn : NativeLegal τ p.1 p.2 m z) :
    {q : Parameter × ComplexField | ActivePhase τ q.1.1 q.1.2 q.2 ∧
      NativeLegal τ q.1.1 q.1.2 m q.2} ∈ nhds (p,z) := by
  have ha' : ActivePhase τ p.1 p.2 (pack (unpack z)) := by simpa only [pack_unpack] using ha
  have hn' : NativeLegal τ p.1 p.2 m (pack (unpack z)) := by simpa only [pack_unpack] using hn
  have hg := GroundNativeBackgroundContinuation.pair_guard_data hτ ha' hn'
  have hu : ContinuousAt (fun q : Parameter × ComplexField => (q.1,unpack q.2)) (p,z) := by
    have hcu : Continuous unpack := packCLE.symm.continuous
    fun_prop
  filter_upwards [hu.eventually (GroundNativeCouplingSmooth.native_guards_joint_near hτ hg.1 hg.2)] with q hq
  simpa only [pack_unpack] using hq
end
end SbtCosmo.Derivation.GroundNativeSourceParameterSmooth
