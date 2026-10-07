import SbtCosmo.Derivation.GroundNativeGeneralDerivative

/-! Joint background/state regularity of the unchanged native source map.
Smoothness is restricted to active phase and nonzero mixed normalization.
Open seed-return and nearby coupled-root constructions are separate obligations. -/
namespace SbtCosmo.Derivation.GroundNativeParameterSmooth
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration Filter
open scoped ContDiff Topology BigOperators
abbrev ParameterState := Field × State

theorem pairSource_joint_smooth (κ : ℝ) :
    ContDiff ℝ ∞ (fun p : ParameterState => pairSource p.1 κ p.2) := by
  unfold pairSource GroundState.gradient
  fun_prop

theorem selected_joint_smooth (κ : ℝ) :
    ContDiff ℝ ∞ (fun p : ParameterState => selected p.1 κ p.2) :=
  GroundSmooth.positiveGround_smooth.comp (pairSource_joint_smooth κ)

theorem realOverlap_joint_smooth (κ : ℝ) :
    ContDiff ℝ ∞ (fun p : ParameterState => realOverlap p.1 κ p.2) := by
  have hg := selected_joint_smooth κ
  unfold realOverlap dot
  fun_prop

theorem imagOverlap_joint_smooth (κ : ℝ) :
    ContDiff ℝ ∞ (fun p : ParameterState => imagOverlap p.1 κ p.2) := by
  have hg := selected_joint_smooth κ
  unfold imagOverlap dot
  fun_prop

theorem overlapSq_joint_smooth (κ : ℝ) :
    ContDiff ℝ ∞ (fun p : ParameterState => overlapSq p.1 κ p.2) :=
  ((realOverlap_joint_smooth κ).pow 2).add ((imagOverlap_joint_smooth κ).pow 2)

theorem overlapNorm_joint_continuous (κ : ℝ) :
    Continuous (fun p : ParameterState => overlapNorm p.1 κ p.2) :=
  (overlapSq_joint_smooth κ).continuous.sqrt

theorem overlapNorm_joint_smooth_at {b : Field} {κ : ℝ} {x : State}
    (ho : 0 < overlapSq b κ x) :
    ContDiffAt ℝ ∞ (fun p : ParameterState => overlapNorm p.1 κ p.2) (b,x) :=
  (overlapSq_joint_smooth κ).contDiffAt.sqrt ho.ne'

theorem aligned_joint_smooth_at {b : Field} {κ : ℝ} {x : State}
    (ho : 0 < overlapSq b κ x) :
    ContDiffAt ℝ ∞ (fun p : ParameterState => aligned p.1 κ p.2) (b,x) := by
  have hn : overlapNorm b κ x ≠ 0 := (Real.sqrt_pos.mpr ho).ne'
  have hd := overlapNorm_joint_smooth_at ho
  have hg := (selected_joint_smooth κ).contDiffAt (x := (b,x))
  exact (((realOverlap_joint_smooth κ).contDiffAt.div hd hn).smul hg).prodMk
    (((imagOverlap_joint_smooth κ).neg.contDiffAt.div hd hn).smul hg)

theorem mixed_joint_smooth_at {b : Field} {κ m : ℝ} {x : State}
    (ho : 0 < overlapSq b κ x) :
    ContDiffAt ℝ ∞ (fun p : ParameterState => mixed p.1 κ m p.2) (b,x) :=
  (contDiff_snd.contDiffAt.const_smul (1-m)).add ((aligned_joint_smooth_at ho).const_smul m)

theorem fullMap_joint_smooth_at {b : Field} {κ m : ℝ} {x : State}
    (ho : 0 < overlapSq b κ x) (hn : 0 < stateNormSq (mixed b κ m x)) :
    ContDiffAt ℝ ∞ (fun p : ParameterState => fullMap p.1 κ m p.2) (b,x) :=
  (normalizeState_smooth_at hn).comp (b,x) (mixed_joint_smooth_at ho)

theorem nativePairMap_joint_eventual_return {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ x) :
    (fun p : ParameterState => GroundNativeJacobian.nativePairMap τ p.1 κ m p.2) =ᶠ[nhds (b,x)]
      (fun p : ParameterState => fullMap p.1 κ m p.2) := by
  have he : ∀ᶠ p : ParameterState in nhds (b,x), τ < overlapNorm p.1 κ p.2 :=
    (overlapNorm_joint_continuous κ).continuousAt.eventually (lt_mem_nhds ho)
  filter_upwards [he] with p hp
  change unpack (nativeUpdate τ p.1 κ m (pack p.2)) = fullMap p.1 κ m p.2
  rw [← fullMap_native_return hτ p.1 κ m p.2 hp]
  exact packCLE.symm_apply_apply _

theorem nativePairMap_joint_smooth_at {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ x)
    (hn : 0 < stateNormSq (mixed b κ m x)) :
    ContDiffAt ℝ ∞
      (fun p : ParameterState => GroundNativeJacobian.nativePairMap τ p.1 κ m p.2) (b,x) := by
  have hp : 0 < overlapSq b κ x := Real.sqrt_pos.mp (hτ.trans_lt ho)
  exact (fullMap_joint_smooth_at hp hn).congr_of_eventuallyEq
    (nativePairMap_joint_eventual_return hτ ho)

/-- Both literal source guards persist in a joint open neighborhood. -/
theorem native_guards_joint_near {b : Field} {κ m τ : ℝ} {x : State}
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ x)
    (hn : τ < Real.sqrt (stateNormSq (mixed b κ m x))) :
    ∀ᶠ p : ParameterState in nhds (b,x),
      ActivePhase τ p.1 κ (pack p.2) ∧ NativeLegal τ p.1 κ m (pack p.2) := by
  have hp : 0 < overlapSq b κ x := Real.sqrt_pos.mp (hτ.trans_lt ho)
  have hc : ContinuousAt (fun p : ParameterState => Real.sqrt (stateNormSq (mixed p.1 κ m p.2))) (b,x) :=
    Real.continuous_sqrt.continuousAt.comp
      (stateNormSq_smooth.continuous.continuousAt.comp (mixed_joint_smooth_at hp).continuousAt)
  have he : ∀ᶠ p : ParameterState in nhds (b,x), τ < overlapNorm p.1 κ p.2 :=
    (overlapNorm_joint_continuous κ).continuousAt.eventually (lt_mem_nhds ho)
  filter_upwards [he, hc.eventually (lt_mem_nhds hn)] with p hphase hnorm
  constructor
  · simpa [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using hphase
  · simpa only [NativeLegal, ← pack_mixed_native hτ p.1 κ m p.2 hphase, norm_pack] using hnorm
end
end SbtCosmo.Derivation.GroundNativeParameterSmooth
