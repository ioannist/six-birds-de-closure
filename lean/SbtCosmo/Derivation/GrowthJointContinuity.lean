import SbtCosmo.Derivation.GrowthParameter
import SbtCosmo.Derivation.GrowthLimit

/-! Joint continuity of the actual finite-start quadrature and its sensitivities.
A positive root margin is earned uniformly before applying parametric integration. -/
namespace SbtCosmo.Derivation.GrowthJointContinuity
noncomputable section
open Set Filter MeasureTheory GrowthExistence GrowthParameter GrowthScaleReturn
open scoped Topology

def safeIntegrand (eps c x : ℝ) : ℝ :=
  Real.exp (-2*x)/(Real.sqrt (max (rootSquared c x) eps))^3

theorem safeIntegrand_continuous {eps : ℝ} (he : 0 < eps) :
    Continuous (Function.uncurry (safeIntegrand eps)) := by
  apply Continuous.div (by fun_prop) (by unfold rootSquared; fun_prop)
  intro p
  exact pow_ne_zero _ (Real.sqrt_pos.mpr (he.trans_le (le_max_right _ _))).ne'

theorem exists_live_extension {c x : ℝ} (hx : 0 ≤ x) (hp : 0 < rootSquared c x) :
    ∃ L : ℝ, x < L ∧ 0 < L ∧ 0 < rootSquared c L := by
  have hc : Continuous (rootSquared c) := by unfold rootSquared; fun_prop
  have hn : ∀ᶠ L in 𝓝 x, 0 < rootSquared c L :=
    continuousAt_const.eventually_lt hc.continuousAt hp
  have hs : ∀ᶠ L in 𝓝[>] x, x < L := self_mem_nhdsWithin
  have ht : ∀ᶠ L in 𝓝[>] x, 0 < rootSquared c L := hn.filter_mono nhdsWithin_le_nhds
  obtain ⟨L,hL,hpL⟩ := (hs.and ht).exists
  exact ⟨L,hL,lt_of_le_of_lt hx hL,hpL⟩

theorem root_margin_below {c d L t : ℝ} (hd : c-rootSquared c L/2 ≤ d) (ht : t ≤ L) :
    rootSquared c L/2 ≤ rootSquared d t := by
  have he : Real.exp (-3*L) ≤ Real.exp (-3*t) := Real.exp_le_exp.mpr (by linarith)
  dsimp [rootSquared] at *
  linarith

/-- One neighborhood supplies the same root margin over every moving integration interval. -/
theorem moving_interval_margin {p : ℝ × ℝ} (hx : 0 ≤ p.2) (hp : 0 < rootSquared p.1 p.2) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ᶠ q : ℝ × ℝ in 𝓝 p,
      ∀ t ∈ uIcc 0 q.2, eps ≤ rootSquared q.1 t := by
  obtain ⟨L,hxL,hL,hpL⟩ := exists_live_extension hx hp
  let eps := rootSquared p.1 L/2
  have he : 0 < eps := by dsimp [eps]; linarith
  have hc : ∀ᶠ q : ℝ × ℝ in 𝓝 p, p.1-eps < q.1 :=
    continuousAt_const.eventually_lt continuousAt_fst (by linarith)
  have ht : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 < L :=
    continuousAt_snd.eventually_lt continuousAt_const hxL
  refine ⟨eps,he,?_⟩
  filter_upwards [hc,ht] with q hqc hqt t htt
  exact root_margin_below hqc.le ((htt.2).trans (max_le hL.le hqt.le))

theorem primitive_joint_continuousAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    ContinuousAt (fun q : ℝ × ℝ => primitive q.1 q.2) p := by
  obtain ⟨eps,he,hnear⟩ := moving_interval_margin hx hp
  have hc : Continuous (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, safeIntegrand eps q.1 t) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous (safeIntegrand_continuous he)
  apply hc.continuousAt.congr
  filter_upwards [hnear] with q hq
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [safeIntegrand,integrand,root,max_eq_left (hq t ht)]

theorem primitiveParameter_joint_continuousAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    ContinuousAt (fun q : ℝ × ℝ => primitiveParameter q.1 q.2) p := by
  obtain ⟨eps,he,hnear⟩ := moving_interval_margin hx hp
  have hc : Continuous (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, safeParameter eps q.1 t) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous (safeParameter_continuous he)
  apply hc.continuousAt.congr
  filter_upwards [hnear] with q hq
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [safeParameter,integrandParameter,root,max_eq_left (hq t ht)]

theorem root_joint_continuous : Continuous (fun q : ℝ × ℝ => root q.1 q.2) := by
  unfold root rootSquared
  fun_prop

theorem growth_joint_continuousAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) : ContinuousAt (fun q : ℝ × ℝ => growth q.1 q.2) p := by
  have h0 : 0 < rootSquared p.1 0 := by
    have he := Real.exp_le_exp.mpr (show -3*p.2 ≤ -3*(0:ℝ) by linarith)
    dsimp [rootSquared] at *
    linarith
  have hr0 : ContinuousAt (fun q : ℝ × ℝ => root q.1 0) p := by
    unfold root rootSquared
    fun_prop
  exact root_joint_continuous.continuousAt.mul ((hr0.inv₀ (root_positive h0).ne').add
    ((by unfold prefactor; fun_prop : ContinuousAt (fun q : ℝ × ℝ => prefactor q.1) p).mul
      (primitive_joint_continuousAt hx hp)))

theorem velocity_joint_continuousAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) : ContinuousAt (fun q : ℝ × ℝ => velocity q.1 q.2) p := by
  have hrate : ContinuousAt (fun q : ℝ × ℝ => rate q.1 q.2) p := by
    apply ContinuousAt.div (by fun_prop) (by unfold rootSquared; fun_prop)
    exact mul_ne_zero (by norm_num) hp.ne'
  exact (hrate.neg.mul (growth_joint_continuousAt hx hp)).add
    ((by unfold prefactor; fun_prop : ContinuousAt (fun q : ℝ × ℝ =>
      prefactor q.1*Real.exp (-2*q.2)) p).div (root_joint_continuous.continuousAt.pow 2)
        (pow_ne_zero _ (root_positive hp).ne'))

theorem growthParameter_joint_continuousAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) : ContinuousAt (fun q : ℝ × ℝ => growthParameter q.1 q.2) p := by
  have h0 : 0 < rootSquared p.1 0 := by
    have he := Real.exp_le_exp.mpr (show -3*p.2 ≤ -3*(0:ℝ) by linarith)
    dsimp [rootSquared] at *
    linarith
  have hr : ContinuousAt (fun q : ℝ × ℝ => root q.1 q.2) p := root_joint_continuous.continuousAt
  have hr0 : ContinuousAt (fun q : ℝ × ℝ => root q.1 0) p := by
    unfold root rootSquared
    fun_prop
  have hrp : ContinuousAt (fun q : ℝ × ℝ => rootParameter q.1 q.2) p :=
    continuousAt_const.div (hr.const_mul 2) (mul_ne_zero (by norm_num) (root_positive hp).ne')
  have hrp0 : ContinuousAt (fun q : ℝ × ℝ => rootParameter q.1 0) p :=
    continuousAt_const.div (hr0.const_mul 2) (mul_ne_zero (by norm_num) (root_positive h0).ne')
  have hf : ContinuousAt (fun q : ℝ × ℝ => prefactor q.1) p := by unfold prefactor; fun_prop
  have hI := primitive_joint_continuousAt hx hp
  have hIp := primitiveParameter_joint_continuousAt hx hp
  exact (hrp.mul ((hr0.inv₀ (root_positive h0).ne').add (hf.mul hI))).add
    (hr.mul (((hrp0.neg.div (hr0.pow 2) (pow_ne_zero _ (root_positive h0).ne')).add hI).add (hf.mul hIp)))

theorem native_log_chart_continuousAt {a0 : ℝ} {p : ℝ × ℝ} (ha0 : 0 < a0) (ha : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => (q.1*a0^3,logScale a0 q.2)) p := by
  have hc : ContinuousAt (fun q : ℝ × ℝ => q.1*a0^3) p := continuousAt_fst.mul_const _
  have hx : ContinuousAt (fun q : ℝ × ℝ => logScale a0 q.2) p := by
    unfold logScale
    exact (continuousAt_snd.div_const a0).log (div_pos ha ha0).ne'
  exact ContinuousAt.prodMk hc hx

theorem native_growth_joint_continuousAt {a0 A : ℝ} {p : ℝ × ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < p.1) (ha : p.2 ∈ Icc a0 A) :
    ContinuousAt (fun q : ℝ × ℝ => nativeGrowth a0 q.1 q.2) p := by
  have ht := logScale_mem ha0 ha
  have hp := GrowthExistence.rootLive_of_live
    (GrowthComparison.live_of_horizon ha0 (GrowthComparison.scale_log_horizon ha0 (ha0.trans_le hA)) hl) _ ht
  exact ContinuousAt.comp (f := fun q : ℝ × ℝ => (q.1*a0^3,logScale a0 q.2)) (x := p)
    (growth_joint_continuousAt ht.1 hp) (native_log_chart_continuousAt ha0 (ha0.trans_le ha.1))

theorem native_velocity_joint_continuousAt {a0 A : ℝ} {p : ℝ × ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < p.1) (ha : p.2 ∈ Icc a0 A) :
    ContinuousAt (fun q : ℝ × ℝ => nativeDerivative a0 q.1 q.2) p := by
  have ht := logScale_mem ha0 ha
  have hp := GrowthExistence.rootLive_of_live
    (GrowthComparison.live_of_horizon ha0 (GrowthComparison.scale_log_horizon ha0 (ha0.trans_le hA)) hl) _ ht
  exact (ContinuousAt.comp (f := fun q : ℝ × ℝ => (q.1*a0^3,logScale a0 q.2)) (x := p)
    (velocity_joint_continuousAt ht.1 hp) (native_log_chart_continuousAt ha0 (ha0.trans_le ha.1))).div
      continuousAt_snd (ha0.trans_le ha.1).ne'

theorem native_sensitivity_joint_continuousAt {a0 A : ℝ} {p : ℝ × ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < p.1) (ha : p.2 ∈ Icc a0 A) :
    ContinuousAt (fun q : ℝ × ℝ => finalSensitivity a0 (logScale a0 q.2) q.1) p := by
  have ht := logScale_mem ha0 ha
  have hp := GrowthExistence.rootLive_of_live
    (GrowthComparison.live_of_horizon ha0 (GrowthComparison.scale_log_horizon ha0 (ha0.trans_le hA)) hl) _ ht
  exact continuousAt_const.mul (ContinuousAt.comp
    (f := fun q : ℝ × ℝ => (q.1*a0^3,logScale a0 q.2)) (x := p)
    (growthParameter_joint_continuousAt ht.1 hp) (native_log_chart_continuousAt ha0 (ha0.trans_le ha.1)))

end
end SbtCosmo.Derivation.GrowthJointContinuity
