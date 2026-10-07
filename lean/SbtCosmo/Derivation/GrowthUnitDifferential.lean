import SbtCosmo.Derivation.GrowthJointContinuity
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Joint derivative of the original primitive through exact fixed-unit-interval
transport. Uniform derivative bounds are earned on an actual live neighborhood. -/
namespace SbtCosmo.Derivation.GrowthUnitDifferential
noncomputable section
open Set Filter MeasureTheory GrowthExistence GrowthParameter GrowthJointContinuity
open scoped Topology

def unitKernel (p : ℝ × ℝ) (t : ℝ) : ℝ := integrand p.1 (p.2*t)
def unitGradient (p : ℝ × ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-3*Real.exp (-2*p.2*t)/(2*(root p.1 (p.2*t))^5)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
  (t*(-2*Real.exp (-2*p.2*t)/(root p.1 (p.2*t))^3 +
    9*Real.exp (-2*p.2*t)*Real.exp (-3*p.2*t)/(2*(root p.1 (p.2*t))^5))) • ContinuousLinearMap.snd ℝ ℝ ℝ

def safeGradient (eps : ℝ) (p : ℝ × ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-3*Real.exp (-2*p.2*t)/(2*(Real.sqrt (max (rootSquared p.1 (p.2*t)) eps))^5)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
  (t*(-2*Real.exp (-2*p.2*t)/(Real.sqrt (max (rootSquared p.1 (p.2*t)) eps))^3 +
    9*Real.exp (-2*p.2*t)*Real.exp (-3*p.2*t)/(2*(Real.sqrt (max (rootSquared p.1 (p.2*t)) eps))^5))) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem safeGradient_continuous {eps : ℝ} (he : 0 < eps) :
    Continuous (Function.uncurry (safeGradient eps)) := by
  let R (q : (ℝ × ℝ) × ℝ) := Real.sqrt (max (rootSquared q.1.1 (q.1.2*q.2)) eps)
  have hR : Continuous R := by dsimp [R]; unfold rootSquared; fun_prop
  have hn (q : (ℝ × ℝ) × ℝ) : R q ≠ 0 :=
    (Real.sqrt_pos.mpr (he.trans_le (le_max_right _ _))).ne'
  have h1 : Continuous (fun q : (ℝ × ℝ) × ℝ => -3*Real.exp (-2*q.1.2*q.2)/(2*(R q)^5)) :=
    Continuous.div (by fun_prop) (continuous_const.mul (hR.pow 5))
      (fun q => mul_ne_zero (by norm_num) (pow_ne_zero _ (hn q)))
  have h2 : Continuous (fun q : (ℝ × ℝ) × ℝ => q.2*(-2*Real.exp (-2*q.1.2*q.2)/(R q)^3 +
      9*Real.exp (-2*q.1.2*q.2)*Real.exp (-3*q.1.2*q.2)/(2*(R q)^5))) := by
    exact continuous_snd.mul ((Continuous.div (by fun_prop) (hR.pow 3) (fun q => pow_ne_zero _ (hn q))).add
      (Continuous.div (by fun_prop) (continuous_const.mul (hR.pow 5))
        (fun q => mul_ne_zero (by norm_num) (pow_ne_zero _ (hn q)))))
  exact (h1.smul continuous_const).add (h2.smul continuous_const)

theorem safeGradient_eq {eps t : ℝ} {p : ℝ × ℝ} (hm : eps ≤ rootSquared p.1 (p.2*t)) :
    safeGradient eps p t = unitGradient p t := by
  simp only [safeGradient,unitGradient,root,max_eq_left hm]

theorem unitKernel_hasFDerivAt {p : ℝ × ℝ} {t : ℝ} (hp : 0 < rootSquared p.1 (p.2*t)) :
    HasFDerivAt (fun q : ℝ × ℝ => unitKernel q t) (unitGradient p t) p := by
  have h2 := ((hasFDerivAt_snd (p := p)).const_mul (-2*t)).exp
  have h3 := ((hasFDerivAt_snd (p := p)).const_mul (-3*t)).exp
  have harg : Real.exp (-3*t*p.2) + p.1 = rootSquared p.1 (p.2*t) := by
    unfold rootSquared
    congr 2
    ring
  have hn : Real.exp (-3*t*p.2) + p.1 ≠ 0 := by rw [harg]; exact hp.ne'
  have hroot := (h3.add (hasFDerivAt_fst (p := p))).sqrt hn
  have hden : (Real.sqrt (Real.exp (-3*t*p.2) + p.1))^3 ≠ 0 := by
    exact pow_ne_zero _ (Real.sqrt_ne_zero'.mpr (by rw [harg]; exact hp))
  have hcalc := h2.mul ((hasFDerivAt_inv hden).comp p (hroot.pow 3))
  have hactual := hcalc.congr_of_eventuallyEq (f₁ := fun q => unitKernel q t)
    (Eventually.of_forall (fun q => by
      simp [unitKernel,integrand,root,rootSquared,div_eq_mul_inv,
        mul_assoc,mul_left_comm,mul_comm]))
  apply hactual.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  dsimp [unitGradient,root,rootSquared]
  simp
  have hr : Real.sqrt (Real.exp (-3*t*p.2) + p.1) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by rw [harg]; exact hp)
  simp only [mul_neg,mul_assoc,mul_left_comm,mul_comm] at hr ⊢
  field_simp [hr]
  ring

theorem unitGradient_measurable (p : ℝ × ℝ) : Measurable (unitGradient p) := by
  unfold unitGradient root rootSquared
  fun_prop

theorem primitive_unit_return (c x : ℝ) :
    primitive c x = x*(∫ t in (0:ℝ)..1, unitKernel (c,x) t) := by
  simpa only [primitive,unitKernel,smul_eq_mul,mul_zero,mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (integrand c) x (a := 0) (b := 1)).symm

/-- A compact live rectangle and one positive margin cover all nearby unit kernels. -/
theorem unit_live_rectangle {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    ∃ (eps : ℝ) (U K : Set (ℝ × ℝ)), 0 < eps ∧ U ∈ 𝓝 p ∧ IsCompact K ∧ U ⊆ K ∧
      ∀ q ∈ K, ∀ t ∈ Icc (0:ℝ) 1, eps ≤ rootSquared q.1 (q.2*t) := by
  obtain ⟨L,hxL,hL,hpL⟩ := exists_live_extension hx hp
  let eps := rootSquared p.1 L/2
  have he : 0 < eps := by dsimp [eps]; linarith
  let U := Ioo (p.1-eps) (p.1+eps) ×ˢ Ioo (p.2-1) L
  let K := Icc (p.1-eps) (p.1+eps) ×ˢ Icc (p.2-1) L
  refine ⟨eps,U,K,he,prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
    (Ioo_mem_nhds (by linarith) hxL),isCompact_Icc.prod isCompact_Icc,?_,?_⟩
  · intro q hq
    exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,⟨hq.2.1.le,hq.2.2.le⟩⟩
  · intro q hq t ht
    apply root_margin_below hq.1.1
    by_cases hqpos : 0 ≤ q.2
    · exact (mul_le_of_le_one_right hqpos ht.2).trans hq.2.2
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hqpos) ht.1).trans hL.le

/-- The bound and all differentiation hypotheses are constructed, not supplied. -/
theorem unit_uniform_derivative_bound {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    ∃ (U : Set (ℝ × ℝ)) (B : ℝ), U ∈ 𝓝 p ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ q ∈ U,
        ‖unitGradient q t‖ ≤ B ∧ HasFDerivAt (fun r => unitKernel r t) (unitGradient q t) q := by
  obtain ⟨eps,U,K,he,hU,hK,hUK,hm⟩ := unit_live_rectangle hx hp
  have hsafe : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => ‖safeGradient eps r.1 r.2‖)
      (K ×ˢ Icc (0:ℝ) 1) := (safeGradient_continuous he).norm.continuousOn
  obtain ⟨B,hB⟩ := (hK.prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).bddAbove_image hsafe
  refine ⟨U,B,hU,?_⟩
  intro t ht q hq
  have hmargin := hm q (hUK hq) t ht
  constructor
  · rw [← safeGradient_eq (eps := eps) (p := q) (t := t) hmargin]
    exact hB (show ‖safeGradient eps q t‖ ∈
      (fun r : (ℝ × ℝ) × ℝ => ‖safeGradient eps r.1 r.2‖) '' (K ×ˢ Icc (0:ℝ) 1) from
      ⟨(q,t),⟨hUK hq,ht⟩,rfl⟩)
  · exact unitKernel_hasFDerivAt (p := q) (t := t) (he.trans_le hmargin)

theorem unitKernel_measurable (p : ℝ × ℝ) : Measurable (unitKernel p) := by
  unfold unitKernel integrand root rootSquared
  fun_prop

theorem unit_integral_hasFDerivAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    HasFDerivAt (fun q => ∫ t in (0:ℝ)..1, unitKernel q t)
      (∫ t in (0:ℝ)..1, unitGradient p t) p := by
  obtain ⟨U,B,hU,hbound⟩ := unit_uniform_derivative_bound hx hp
  have hcont : ContinuousOn (unitKernel p) (Icc (0:ℝ) 1) := by
    intro t ht
    have hroot : 0 < rootSquared p.1 (p.2*t) := by
      have hle : p.2*t ≤ p.2 := mul_le_of_le_one_right hx ht.2
      have he : Real.exp (-3*p.2) ≤ Real.exp (-3*(p.2*t)) :=
        Real.exp_le_exp.mpr (by linarith)
      dsimp [rootSquared] at *
      linarith
    exact ((integrand_continuousAt hroot).comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := unitKernel) (F' := unitGradient) (s := U) (bound := fun _ => B) hU
  · exact Eventually.of_forall (fun q => (unitKernel_measurable q).stronglyMeasurable.aestronglyMeasurable)
  · exact hcont.intervalIntegrable_of_Icc (by norm_num)
  · exact (unitGradient_measurable p).stronglyMeasurable.aestronglyMeasurable
  · apply ae_of_all
    intro t ht q hq
    have ht' : t ∈ Icc (0:ℝ) 1 := by
      simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc ht
    exact (hbound t ht' q hq).1
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro t ht q hq
    have ht' : t ∈ Icc (0:ℝ) 1 := by
      simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc ht
    exact (hbound t ht' q hq).2

def primitiveGradient (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  p.2 • (∫ t in (0:ℝ)..1, unitGradient p t) +
    (∫ t in (0:ℝ)..1, unitKernel p t) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem primitive_joint_hasFDerivAt {p : ℝ × ℝ} (hx : 0 ≤ p.2)
    (hp : 0 < rootSquared p.1 p.2) :
    HasFDerivAt (fun q => primitive q.1 q.2) (primitiveGradient p) p := by
  have hcalc := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).mul (unit_integral_hasFDerivAt hx hp)
  exact hcalc.congr_of_eventuallyEq
    (Eventually.of_forall (fun q => primitive_unit_return q.1 q.2))

end
end SbtCosmo.Derivation.GrowthUnitDifferential
