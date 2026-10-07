import SbtCosmo.Derivation.GrowthScaleReturn
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Parameter differentiation of the actual finite-start quadrature, with a derived uniform bound. -/
namespace SbtCosmo.Derivation.GrowthParameter
noncomputable section
open Set Filter MeasureTheory GrowthComparison GrowthExistence
open scoped Topology

def rootParameter (c x : ℝ) : ℝ := 1 / (2 * root c x)
def rateParameter (c x : ℝ) : ℝ := -3 * Real.exp (-3 * x) / (2 * (rootSquared c x)^2)
def integrandParameter (c x : ℝ) : ℝ := -3 * Real.exp (-2 * x) / (2 * (root c x)^5)
def primitiveParameter (c x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, integrandParameter c t

theorem root_parameter_derivative {c x : ℝ} (hp : 0 < rootSquared c x) :
    HasDerivAt (fun d => root d x) (rootParameter c x) c := by
  simpa [rootParameter, root, rootSquared] using
    ((hasDerivAt_id c).const_add (Real.exp (-3 * x))).sqrt hp.ne'

theorem rate_parameter_derivative {c x : ℝ} (hp : 0 < rootSquared c x) :
    HasDerivAt (fun d => rate d x) (rateParameter c x) c := by
  convert (hasDerivAt_const c (3 * Real.exp (-3 * x))).div
    (((hasDerivAt_id c).const_add (Real.exp (-3 * x))).const_mul 2)
    (mul_ne_zero (by norm_num) hp.ne') using 1
  unfold rateParameter rootSquared
  simp only [id_eq]
  field_simp
  ring

theorem integrand_parameter_derivative {c x : ℝ} (hp : 0 < rootSquared c x) :
    HasDerivAt (fun d => integrand d x) (integrandParameter c x) c := by
  have hr := (root_positive hp).ne'
  convert (hasDerivAt_const c (Real.exp (-2 * x))).div
    ((root_parameter_derivative hp).pow 3) (pow_ne_zero _ hr) using 1
  unfold integrandParameter rootParameter
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem integrandParameter_measurable (c : ℝ) : Measurable (integrandParameter c) := by
  exact (by fun_prop : Measurable (fun x : ℝ => -3 * Real.exp (-2 * x))).div
    ((continuous_root c).measurable.pow_const 5 |>.const_mul 2)

theorem integrandParameter_continuousAt {c x : ℝ} (hp : 0 < rootSquared c x) :
    ContinuousAt (integrandParameter c) x := by
  apply ContinuousAt.div (by fun_prop) ((continuous_root c).continuousAt.pow 5 |>.const_mul 2)
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (root_positive hp).ne')

def safeParameter (ε c x : ℝ) : ℝ :=
  -3 * Real.exp (-2 * x) / (2 * (Real.sqrt (max (rootSquared c x) ε))^5)

theorem safeParameter_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (Function.uncurry (safeParameter ε)) := by
  apply Continuous.div (by fun_prop)
    (by unfold rootSquared; fun_prop : Continuous (fun p : ℝ × ℝ =>
      2 * (Real.sqrt (max (rootSquared p.1 p.2) ε))^5))
  intro p
  exact mul_ne_zero (by norm_num)
    (pow_ne_zero _ (Real.sqrt_pos.mpr (hε.trans_le (le_max_right _ _))).ne')

/-- A single positive root margin holds throughout a parameter neighborhood and the full time interval. -/
theorem uniform_root_margin {c d L x : ℝ}
    (hd : c - rootSquared c L / 2 ≤ d) (hx : x ∈ Icc 0 L) :
    rootSquared c L / 2 ≤ rootSquared d x := by
  have he : Real.exp (-3 * L) ≤ Real.exp (-3 * x) := Real.exp_le_exp.mpr (by nlinarith [hx.2])
  dsimp [rootSquared] at *
  linarith

/-- The derivative-under-integral hypotheses are all constructed on a compact parameter/time rectangle. -/
theorem primitive_parameter_differentiation {c L : ℝ} (hL : 0 ≤ L)
    (hp : 0 < rootSquared c L) :
    IntervalIntegrable (integrandParameter c) volume 0 L ∧
      HasDerivAt (fun d => primitive d L) (primitiveParameter c L) c := by
  let ε := rootSquared c L / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hv : Ioo (c - ε) (c + ε) ∈ 𝓝 c := Ioo_mem_nhds (by linarith) (by linarith)
  have hmargin (d : ℝ) (hd : d ∈ Icc (c - ε) (c + ε)) (x : ℝ) (hx : x ∈ Icc 0 L) :
      ε ≤ rootSquared d x := uniform_root_margin hd.1 hx
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    ((safeParameter_continuous hε).norm.continuousOn :
      ContinuousOn (fun p : ℝ × ℝ => ‖safeParameter ε p.1 p.2‖)
        (Icc (c - ε) (c + ε) ×ˢ Icc 0 L))
  have hcont : ContinuousOn (integrand c) (Icc 0 L) := by
    intro x hx
    have hm := hmargin c ⟨by linarith, by linarith⟩ x hx
    exact (integrand_continuousAt (hε.trans_le hm)).continuousWithinAt
  apply intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := integrand) (F' := integrandParameter) (s := Ioo (c - ε) (c + ε))
    (bound := fun _ => K) hv
  · exact Eventually.of_forall (fun d => (integrand_measurable d).stronglyMeasurable.aestronglyMeasurable)
  · exact hcont.intervalIntegrable_of_Icc hL
  · exact (integrandParameter_measurable c).stronglyMeasurable.aestronglyMeasurable
  · apply ae_of_all
    intro x hx d hd
    have hx' : x ∈ Icc 0 L := by
      simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hx
    have hd' : d ∈ Icc (c - ε) (c + ε) := ⟨hd.1.le, hd.2.le⟩
    have hm := hmargin d hd' x hx'
    have he : safeParameter ε d x = integrandParameter d x := by
      simp only [safeParameter, integrandParameter, root, max_eq_left hm]
    rw [← he]
    exact hK (mem_image_of_mem _ (show (d, x) ∈
      Icc (c - ε) (c + ε) ×ˢ Icc 0 L from ⟨hd', hx'⟩))
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro x hx d hd
    have hx' : x ∈ Icc 0 L := by
      simpa only [uIcc_of_le hL] using uIoc_subset_uIcc hx
    exact integrand_parameter_derivative (hε.trans_le (hmargin d ⟨hd.1.le, hd.2.le⟩ x hx'))

theorem primitiveParameter_time_derivative {c L x : ℝ} (hl : RootLive c L)
    (hx : x ∈ Icc 0 L) :
    HasDerivAt (primitiveParameter c) (integrandParameter c x) x := by
  have hcont : ContinuousOn (integrandParameter c) (Icc 0 x) := by
    intro t ht
    exact (integrandParameter_continuousAt (hl t ⟨ht.1, ht.2.trans hx.2⟩)).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable_of_Icc hx.1)
    (integrandParameter_measurable c).stronglyMeasurable.stronglyMeasurableAtFilter
    (integrandParameter_continuousAt (hl x hx))

def growthParameter (c x : ℝ) : ℝ :=
  rootParameter c x * ((root c 0)⁻¹ + prefactor c * primitive c x) +
    root c x * (-rootParameter c 0 / (root c 0)^2 +
      primitive c x + prefactor c * primitiveParameter c x)

def velocityParameter (c x : ℝ) : ℝ :=
  -rateParameter c x * growth c x - rate c x * growthParameter c x +
    Real.exp (-2 * x) / (root c x)^2 - prefactor c * Real.exp (-2 * x) / (root c x)^4

theorem growth_parameter_derivative {c x : ℝ} (hx : 0 ≤ x)
    (hp : 0 < rootSquared c x) :
    HasDerivAt (fun d => growth d x) (growthParameter c x) c := by
  have h0 : 0 < rootSquared c 0 := by
    have he := Real.exp_le_exp.mpr (show -3 * x ≤ -3 * 0 by linarith)
    dsimp [rootSquared] at *
    linarith
  have hf : HasDerivAt prefactor 1 c := by
    exact (hasDerivAt_id c).add_const ((5 : ℝ) / 2)
  convert (root_parameter_derivative hp).mul
    (((root_parameter_derivative h0).inv (root_positive h0).ne').add
      (hf.mul (primitive_parameter_differentiation hx hp).2)) using 1
  unfold growthParameter
  simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
  ring

theorem velocity_parameter_derivative {c x : ℝ} (hx : 0 ≤ x)
    (hp : 0 < rootSquared c x) :
    HasDerivAt (fun d => velocity d x) (velocityParameter c x) c := by
  have hr := (root_positive hp).ne'
  have hf : HasDerivAt prefactor 1 c := by
    exact (hasDerivAt_id c).add_const ((5 : ℝ) / 2)
  convert ((rate_parameter_derivative hp).neg.mul (growth_parameter_derivative hx hp)).add
    ((hf.mul (hasDerivAt_const c (Real.exp (-2 * x)))).div
      ((root_parameter_derivative hp).pow 2) (pow_ne_zero _ hr)) using 1
  unfold velocityParameter rootParameter
  simp only [Pi.pow_apply, Pi.neg_apply, Pi.mul_apply]
  field_simp
  ring

theorem rootParameter_time_derivative {c x : ℝ} (hp : 0 < rootSquared c x) :
    HasDerivAt (rootParameter c) (rate c x * rootParameter c x) x := by
  have hr := (root_positive hp).ne'
  convert (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_root hp).const_mul 2) (mul_ne_zero (by norm_num) hr) using 1
  unfold rootParameter
  field_simp
  ring

theorem rateParameter_time_derivative {c x : ℝ} (hp : 0 < rootSquared c x) :
    HasDerivAt (rateParameter c) ((4 * rate c x - 3) * rateParameter c x) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-3 * t)) (-3 * Real.exp (-3 * x)) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-3)).exp
  convert (he.const_mul (-3)).div (((he.add_const c).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne')) using 1
  norm_num only [Pi.pow_apply, pow_one]
  change (4 * rate c x - 3) * rateParameter c x =
    ((-3 * (-3 * Real.exp (-3 * x))) * (2 * (rootSquared c x)^2) -
      (-3 * Real.exp (-3 * x)) * (2 * (2 * rootSquared c x * (-3 * Real.exp (-3 * x))))) /
        (2 * (rootSquared c x)^2)^2
  unfold rateParameter rate
  field_simp [hp.ne']
  ring

theorem growthParameter_time_derivative {c L x : ℝ} (hl : RootLive c L)
    (hx : x ∈ Icc 0 L) :
    HasDerivAt (growthParameter c) (velocityParameter c x) x := by
  have hr := (root_positive (hl x hx)).ne'
  have hs := root_sq (hl x hx)
  convert ((rootParameter_time_derivative (hl x hx)).mul
    (((primitive_derivative hl hx).const_mul (prefactor c)).const_add ((root c 0)⁻¹))).add
      ((hasDerivAt_root (hl x hx)).mul
        (((primitive_derivative hl hx).add
          ((primitiveParameter_time_derivative hl hx).const_mul (prefactor c))).const_add
            (-rootParameter c 0 / (root c 0)^2))) using 1
  · ext t
    dsimp [growthParameter]
    ring
  · unfold velocityParameter growthParameter growth rootParameter integrand integrandParameter
      rateParameter rate
    simp only [Pi.add_apply]
    rw [← hs]
    field_simp
    ring

theorem velocityParameter_time_derivative {c L x : ℝ} (hl : RootLive c L)
    (hx : x ∈ Icc 0 L) :
    HasDerivAt (velocityParameter c)
      (rate c x * growthParameter c x + (rate c x - 2) * velocityParameter c x +
        rateParameter c x * (growth c x + velocity c x)) x := by
  have hr := (root_positive (hl x hx)).ne'
  have hs := root_sq (hl x hx)
  have he : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (-2 * Real.exp (-2 * x)) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-2)).exp
  have h1 := (rateParameter_time_derivative (hl x hx)).neg.mul (growth_derivative hl hx)
  have h2 := (hasDerivAt_rate (hl x hx)).mul (growthParameter_time_derivative hl hx)
  have h3 := he.div ((hasDerivAt_root (hl x hx)).pow 2) (pow_ne_zero _ hr)
  have h4 := (he.const_mul (prefactor c)).div ((hasDerivAt_root (hl x hx)).pow 4)
    (pow_ne_zero _ hr)
  convert ((h1.sub h2).add h3).sub h4 using 1
  unfold velocityParameter velocity rateParameter rate
  simp only [Pi.pow_apply, Pi.neg_apply]
  rw [← hs]
  field_simp
  ring

theorem growthParameter_initial {c : ℝ} (hp : 0 < rootSquared c 0) :
    growthParameter c 0 = 0 := by
  have hr := (root_positive hp).ne'
  simp only [growthParameter, primitive, primitiveParameter, intervalIntegral.integral_same,
    mul_zero, add_zero, rootParameter]
  field_simp
  ring

theorem velocityParameter_initial {c : ℝ} (hp : 0 < rootSquared c 0) :
    velocityParameter c 0 = 0 := by
  have hr := (root_positive hp).ne'
  have hs := root_sq hp
  unfold velocityParameter
  rw [growth_initial hp, growthParameter_initial hp]
  unfold rateParameter prefactor
  simp only [mul_zero, Real.exp_zero, mul_one, sub_zero]
  rw [← hs]
  have hsq : (root c 0)^2 = 1 + c := by simpa [rootSquared] using hs
  field_simp
  nlinarith [hsq]

theorem rateParameter_negative {c x : ℝ} (hp : 0 < rootSquared c x) :
    rateParameter c x < 0 := by
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _))
    (mul_pos (by norm_num) (pow_pos hp 2))

/-- Strict negativity is obtained from the derived variational ODE, not from strict ordering alone. -/
theorem sensitivity_strict_negative {a0 lam L : ℝ} (hL : 0 ≤ L)
    (hl : Live a0 lam L) :
    ∀ x ∈ Icc 0 L, 0 < x →
      growthParameter (lam * a0^3) x < 0 ∧ velocityParameter (lam * a0^3) x < 0 := by
  let c := lam * a0^3
  have hr : RootLive c L := rootLive_of_live hl
  have h0 := hr 0 ⟨le_rfl, hL⟩
  obtain ⟨K, hK⟩ := coefficient_bounded hl
  have hp := growth_positive hL hl (constructed_growthSolution hL hl)
  let q := fun x => -rateParameter c x * (growth c x + velocity c x)
  have hq : ∀ x ∈ Icc 0 L, 0 < q x := by
    intro x hx
    exact mul_pos (neg_pos.mpr (rateParameter_negative (hr x hx)))
      (add_pos (hp x hx).1 (hp x hx).2)
  have hD : ∀ x ∈ Icc 0 L,
      HasDerivAt (fun t => -growthParameter c t) (-velocityParameter c x) x := by
    intro x hx
    exact (growthParameter_time_derivative hr hx).neg
  have hv : ∀ x ∈ Icc 0 L, HasDerivAt (fun t => -velocityParameter c t)
      (coefficient a0 lam x * (-growthParameter c x) +
        (coefficient a0 lam x - 2) * (-velocityParameter c x) + q x) x := by
    intro x hx
    convert (velocityParameter_time_derivative hr hx).neg using 1
    dsimp [q, c]
    rw [rate_eq_coefficient (hl x hx).ne']
    ring
  have hn := cooperative_strict_forcing (K := K) hL
    (fun x hx => (hD x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hv x hx).continuousAt.continuousWithinAt)
    hD hv hK hq (by simp [growthParameter_initial h0])
      (by simp [velocityParameter_initial h0])
  intro x hx hxp
  exact ⟨neg_pos.mp (hn x hx hxp).1, neg_pos.mp (hn x hx hxp).2⟩

def finalSensitivity (a0 L lam : ℝ) : ℝ := a0^3 * growthParameter (lam * a0^3) L

theorem finalGrowth_parameter_derivative {a0 lam L : ℝ} (hL : 0 ≤ L)
    (hl : Live a0 lam L) :
    HasDerivAt (finalGrowth a0 L) (finalSensitivity a0 L lam) lam := by
  simpa [finalGrowth, finalSensitivity, mul_comm] using
    (growth_parameter_derivative hL (rootLive_of_live hl L ⟨hL, le_rfl⟩)).comp lam
      ((hasDerivAt_id lam).mul_const (a0^3))

theorem finalSensitivity_negative {a0 lam L : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hl : Live a0 lam L) : finalSensitivity a0 L lam < 0 := by
  exact mul_neg_of_pos_of_neg (pow_pos ha 3)
    (sensitivity_strict_negative hL.le hl L ⟨hL.le, le_rfl⟩ hL).1

theorem native_parameter_derivative {a0 A lam a : ℝ} (ha : 0 < a0)
    (hA : a0 ≤ A) (hlam : -(1 / A^3) < lam) (hx : a ∈ Icc a0 A) :
    HasDerivAt (fun d => GrowthScaleReturn.nativeGrowth a0 d a)
      (finalSensitivity a0 (GrowthScaleReturn.logScale a0 a) lam) lam := by
  have hl := live_of_horizon ha (scale_log_horizon ha (ha.trans_le hA)) hlam
  have ht := GrowthScaleReturn.logScale_mem ha hx
  exact finalGrowth_parameter_derivative ht.1
    (fun x hx' => hl x ⟨hx'.1, hx'.2.trans ht.2⟩)

theorem native_parameter_derivative_negative {a0 A lam a : ℝ} (ha : 0 < a0)
    (hA : a0 ≤ A) (hlam : -(1 / A^3) < lam) (hx : a ∈ Ioc a0 A) :
    deriv (fun d => GrowthScaleReturn.nativeGrowth a0 d a) lam < 0 := by
  have ht : 0 < GrowthScaleReturn.logScale a0 a :=
    Real.log_pos ((lt_div_iff₀ ha).mpr (by simpa using hx.1))
  rw [(native_parameter_derivative ha hA hlam ⟨hx.1.le, hx.2⟩).deriv]
  exact finalSensitivity_negative ha ht
    (live_of_horizon ha (scale_log_horizon ha (ha.trans hx.1))
      ((WindowRecords.negative_horizon_tightens (ha.trans hx.1) hx.2).trans_lt hlam))

theorem native_velocity_parameter_derivative {a0 A lam a : ℝ} (ha : 0 < a0)
    (hA : a0 ≤ A) (hlam : -(1 / A^3) < lam) (hx : a ∈ Icc a0 A) :
    HasDerivAt (fun d => GrowthScaleReturn.nativeDerivative a0 d a)
      (a0^3 * velocityParameter (lam * a0^3) (GrowthScaleReturn.logScale a0 a) / a) lam := by
  have hl := live_of_horizon ha (scale_log_horizon ha (ha.trans_le hA)) hlam
  have hr := rootLive_of_live hl
  have ht := GrowthScaleReturn.logScale_mem ha hx
  simpa [GrowthScaleReturn.nativeDerivative, mul_comm] using
    ((velocity_parameter_derivative ht.1 (hr _ ht)).comp lam
      ((hasDerivAt_id lam).mul_const (a0^3))).div_const a

theorem native_velocity_parameter_derivative_negative {a0 A lam a : ℝ} (ha : 0 < a0)
    (hA : a0 ≤ A) (hlam : -(1 / A^3) < lam) (hx : a ∈ Ioc a0 A) :
    deriv (fun d => GrowthScaleReturn.nativeDerivative a0 d a) lam < 0 := by
  have hl := live_of_horizon ha (scale_log_horizon ha (ha.trans_le hA)) hlam
  have ht := GrowthScaleReturn.logScale_mem ha ⟨hx.1.le, hx.2⟩
  have htp : 0 < GrowthScaleReturn.logScale a0 a :=
    Real.log_pos ((lt_div_iff₀ ha).mpr (by simpa using hx.1))
  rw [(native_velocity_parameter_derivative ha hA hlam ⟨hx.1.le, hx.2⟩).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (pow_pos ha 3)
    (sensitivity_strict_negative (GrowthScaleReturn.horizon_log_nonneg ha hA) hl _ ht htp).2)
      (ha.trans hx.1)

theorem primitiveParameter_continuous_parameter {c L : ℝ} (hL : 0 ≤ L)
    (hp : 0 < rootSquared c L) : ContinuousAt (fun d => primitiveParameter d L) c := by
  let ε := rootSquared c L / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hc : c - ε < c := by linarith
  have hsafe : Continuous (fun d => ∫ x in (0 : ℝ)..L, safeParameter ε d x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (safeParameter_continuous hε) 0 L
  apply hsafe.continuousAt.congr
  filter_upwards [Ioi_mem_nhds hc] with d hd
  change c - ε < d at hd
  unfold primitiveParameter
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hL] at hx
  have hm : ε ≤ rootSquared d x := uniform_root_margin hd.le hx
  simp only [safeParameter, integrandParameter, root, max_eq_left hm]

theorem rootParameter_continuous_parameter {c x : ℝ} (hp : 0 < rootSquared c x) :
    ContinuousAt (fun d => rootParameter d x) c := by
  exact continuousAt_const.div ((root_continuous_parameter x).continuousAt.const_mul 2)
    (mul_ne_zero (by norm_num) (root_positive hp).ne')

theorem growthParameter_continuous_parameter {c L : ℝ} (hL : 0 ≤ L)
    (hp : 0 < rootSquared c L) : ContinuousAt (fun d => growthParameter d L) c := by
  have h0 : 0 < rootSquared c 0 := by
    have he := Real.exp_le_exp.mpr (show -3 * L ≤ -3 * 0 by linarith)
    dsimp [rootSquared] at *
    linarith
  have hf : ContinuousAt prefactor c := by unfold prefactor; fun_prop
  exact ((rootParameter_continuous_parameter hp).mul
    (((root_continuous_parameter 0).continuousAt.inv₀ (root_positive h0).ne').add
      (hf.mul (primitive_continuous_parameter hL hp)))).add
        ((root_continuous_parameter L).continuousAt.mul
          ((((rootParameter_continuous_parameter h0).neg.div
            ((root_continuous_parameter 0).continuousAt.pow 2)
              (pow_ne_zero _ (root_positive h0).ne')).add
                (primitive_continuous_parameter hL hp)).add
                  (hf.mul (primitiveParameter_continuous_parameter hL hp))))

theorem finalSensitivity_continuousAt {a0 lam L : ℝ} (hL : 0 ≤ L)
    (hl : Live a0 lam L) : ContinuousAt (finalSensitivity a0 L) lam := by
  exact continuousAt_const.mul
    (ContinuousAt.comp (f := fun d : ℝ => d * a0^3) (x := lam)
      (growthParameter_continuous_parameter hL (rootLive_of_live hl L ⟨hL, le_rfl⟩))
      (by fun_prop))

end
end SbtCosmo.Derivation.GrowthParameter
