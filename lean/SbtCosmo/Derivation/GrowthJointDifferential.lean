import SbtCosmo.Derivation.GrowthUnitDifferential
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Actual joint growth differentiation: differentiability is earned through the
original primitive before coordinate restrictions identify the derivative. -/
namespace SbtCosmo.Derivation.GrowthJointDifferential
noncomputable section
open Set Filter GrowthExistence GrowthParameter GrowthScaleReturn GrowthJointContinuity GrowthUnitDifferential
open scoped Topology

/-- Partial derivatives identify an already earned joint derivative; they do not
serve as a substitute for joint differentiability. -/
theorem product_gradient_of_partials {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {s v : ℝ}
    (hf : DifferentiableAt ℝ f p)
    (hs : HasDerivAt (fun c => f (c,p.2)) s p.1)
    (hv : HasDerivAt (fun x => f (p.1,x)) v p.2) :
    HasFDerivAt f (s • ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hc := hf.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  have hx := hf.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  have hcs : (fderiv ℝ f p) (1,0) = s := by
    simpa using hc.hasDerivAt.unique hs
  have hxv : (fderiv ℝ f p) (0,1) = v := by
    simpa using hx.hasDerivAt.unique hv
  apply hf.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  have hw : w = w.1 • ((1,0) : ℝ × ℝ) + w.2 • ((0,1) : ℝ × ℝ) := by ext <;> simp
  calc
    (fderiv ℝ f p) w = w.1 * (fderiv ℝ f p) (1,0) + w.2 * (fderiv ℝ f p) (0,1) := by
      conv_lhs => rw [hw]
      simp only [map_add,map_smul,smul_eq_mul]
    _ = _ := by simp [hcs,hxv,smul_eq_mul]; ring

theorem root_joint_differentiableAt {p : ℝ × ℝ} (hp : 0 < rootSquared p.1 p.2) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => root q.1 q.2) p := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => rootSquared q.1 q.2) p := by
    unfold rootSquared
    fun_prop
  exact hd.sqrt hp.ne'

theorem growth_joint_differentiableAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => growth q.1 q.2) p := by
  have h0 : 0 < rootSquared p.1 0 := by
    have he := Real.exp_le_exp.mpr (show -3*p.2 ≤ -3*(0:ℝ) by linarith)
    dsimp [rootSquared] at *
    linarith
  have hr0 : DifferentiableAt ℝ (fun q : ℝ × ℝ => root q.1 0) p := by
    exact (root_parameter_derivative h0).differentiableAt.comp p differentiableAt_fst
  have hf : DifferentiableAt ℝ (fun q : ℝ × ℝ => prefactor q.1) p := by
    unfold prefactor
    fun_prop
  exact (root_joint_differentiableAt hp).mul ((hr0.inv (root_positive h0).ne').add
    (hf.mul (primitive_joint_hasFDerivAt hx hp).differentiableAt))

def growthGradient (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  growthParameter p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    velocity p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem growth_joint_hasFDerivAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    HasFDerivAt (fun q => growth q.1 q.2) (growthGradient p) p := by
  have hl : RootLive p.1 p.2 := by
    intro t ht
    have he := Real.exp_le_exp.mpr (show -3*p.2 ≤ -3*t by linarith [ht.2])
    dsimp [rootSquared] at *
    linarith
  exact product_gradient_of_partials (growth_joint_differentiableAt hx hp)
    (growth_parameter_derivative hx hp) (growth_derivative hl ⟨hx,le_rfl⟩)

theorem growthGradient_continuousAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) : ContinuousAt growthGradient p :=
  ((growthParameter_joint_continuousAt hx hp).smul continuousAt_const).add
    ((velocity_joint_continuousAt hx hp).smul continuousAt_const)

theorem native_growth_joint_differentiableAt {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.1) (ha : p.2 ∈ Icc a0 A) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => nativeGrowth a0 q.1 q.2) p := by
  have ht := logScale_mem ha0 ha
  have hp := GrowthExistence.rootLive_of_live
    (GrowthComparison.live_of_horizon ha0 (GrowthComparison.scale_log_horizon ha0 (ha0.trans_le hA)) hl) _ ht
  have hc : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1*a0^3) p := by fun_prop
  have hx : DifferentiableAt ℝ (fun q : ℝ × ℝ => logScale a0 q.2) p :=
    (hasDerivAt_logScale ha0.ne' (ha0.trans_le ha.1).ne').differentiableAt.comp p differentiableAt_snd
  exact (growth_joint_differentiableAt ht.1 hp).comp p (hc.prodMk hx)

def nativeGradient (a0 : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  finalSensitivity a0 (logScale a0 p.2) p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    nativeDerivative a0 p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem native_growth_joint_hasFDerivAt {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.1) (ha : p.2 ∈ Icc a0 A) :
    HasFDerivAt (fun q => nativeGrowth a0 q.1 q.2) (nativeGradient a0 p) p :=
  product_gradient_of_partials (native_growth_joint_differentiableAt ha0 hA hl ha)
    (native_parameter_derivative ha0 hA hl ha) (native_growth_derivative ha0 hA hl ha)

theorem nativeGradient_continuousAt {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.1) (ha : p.2 ∈ Icc a0 A) :
    ContinuousAt (nativeGradient a0) p :=
  ((native_sensitivity_joint_continuousAt ha0 hA hl ha).smul continuousAt_const).add
    ((native_velocity_joint_continuousAt ha0 hA hl ha).smul continuousAt_const)

theorem native_growth_joint_c1 {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℝ => nativeGrowth a0 q.1 q.2)
      (Ioi (-(1/A^3)) ×ˢ Ioo a0 A) := by
  have hd : ContinuousOn (fderiv ℝ (fun q : ℝ × ℝ => nativeGrowth a0 q.1 q.2))
      (Ioi (-(1/A^3)) ×ˢ Ioo a0 A) := by
    apply (show ContinuousOn (nativeGradient a0) (Ioi (-(1/A^3)) ×ˢ Ioo a0 A) from
      fun p hp => (nativeGradient_continuousAt ha0 hA hp.1 ⟨hp.2.1.le,hp.2.2.le⟩).continuousWithinAt).congr
    intro p hp
    exact (native_growth_joint_hasFDerivAt ha0 hA hp.1 ⟨hp.2.1.le,hp.2.2.le⟩).fderiv
  rw [show (1 : WithTop ℕ∞) = 0+1 from rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)]
  exact ⟨fun p hp => (native_growth_joint_hasFDerivAt ha0 hA hp.1
    ⟨hp.2.1.le,hp.2.2.le⟩).differentiableAt.differentiableWithinAt,by simp,contDiffOn_zero.mpr hd⟩

end
end SbtCosmo.Derivation.GrowthJointDifferential
