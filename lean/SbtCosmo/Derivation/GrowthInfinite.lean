import SbtCosmo.Derivation.GrowthFirstRecordLive
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Constructed infinite-time growth of the original finite-start IVP.
The improper integral is proved integrable; no limiting-growth law is assumed. -/
namespace SbtCosmo.Derivation.GrowthInfinite
noncomputable section
open Set Filter MeasureTheory GrowthComparison GrowthExistence GrowthLimit GrowthScaleReturn
open scoped Topology

def infiniteIntegral (c : ℝ) : ℝ := ∫ x : ℝ in Ioi 0, integrand c x
def infiniteGrowth (c : ℝ) : ℝ := Real.sqrt c * ((root c 0)⁻¹ + prefactor c * infiniteIntegral c)
def nativeInfinite (a0 lam : ℝ) : ℝ := infiniteGrowth (lam * a0^3)

theorem rootLive_positive {c : ℝ} (hc : 0 < c) (L : ℝ) : RootLive c L := by
  intro x _
  exact add_pos (Real.exp_pos _) hc

theorem root_lower (c x : ℝ) : Real.sqrt c ≤ root c x := by
  unfold root rootSquared
  exact Real.sqrt_le_sqrt (by linarith [Real.exp_pos (-3 * x)])

theorem integrand_bounds {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 ≤ integrand c x ∧ integrand c x ≤ Real.exp (-2 * x) / (Real.sqrt c)^3 := by
  have hr : 0 < root c x := root_positive (add_pos (Real.exp_pos _) hc)
  refine ⟨div_nonneg (Real.exp_pos _).le (pow_pos hr 3).le, ?_⟩
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos (Real.sqrt_pos.mpr hc) 3)
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (root_lower c x) 3)

theorem integrable_integrand {c : ℝ} (hc : 0 < c) : IntegrableOn (integrand c) (Ioi 0) := by
  have hg := (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).div_const
    ((Real.sqrt c)^3)
  apply hg.mono' (integrand_measurable c).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integrand_bounds hc x).1]
    exact (integrand_bounds hc x).2)

theorem infiniteIntegral_nonnegative {c : ℝ} (hc : 0 < c) : 0 ≤ infiniteIntegral c :=
  integral_nonneg (fun x => (integrand_bounds hc x).1)

theorem infiniteIntegral_upper {c : ℝ} (hc : 0 < c) :
    infiniteIntegral c ≤ 1 / (2 * (Real.sqrt c)^3) := by
  have hg := (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).div_const
    ((Real.sqrt c)^3)
  have h := integral_mono_ae (integrable_integrand hc) hg
    (ae_of_all _ (fun x => (integrand_bounds hc x).2))
  have he : (∫ x : ℝ in Ioi 0, Real.exp (-2 * x)) = 1 / 2 := by
    rw [integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
    norm_num
  rw [integral_div, he] at h
  convert h using 1
  ring

theorem primitive_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (primitive c) atTop (𝓝 (infiniteIntegral c)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (integrable_integrand hc) tendsto_id

theorem root_tendsto (c : ℝ) : Tendsto (root c) atTop (𝓝 (Real.sqrt c)) := by
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-3 : ℝ) < 0))
  simpa only [zero_add] using Real.continuous_sqrt.continuousAt.tendsto.comp
    (he.add_const c)

theorem growth_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (growth c) atTop (𝓝 (infiniteGrowth c)) := by
  exact (root_tendsto c).mul (tendsto_const_nhds.add
    (tendsto_const_nhds.mul (primitive_tendsto hc)))

theorem growth_strictMono {c : ℝ} (hc : 0 < c) : StrictMonoOn (growth c) (Ici 0) := by
  intro x hx y hy hxy
  have hl := live_nonnegative (a0 := (1 : ℝ)) (L := y) (by norm_num) hc.le
  have h := growth_strict_in_time hy hl (constructed_growthSolution hy hl)
    ⟨hx, hxy.le⟩ ⟨hy, le_rfl⟩ hxy
  simpa only [one_pow, mul_one] using h

theorem growth_le_infinite {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    growth c x ≤ infiniteGrowth c := by
  apply ge_of_tendsto (growth_tendsto hc)
  filter_upwards [eventually_ge_atTop x] with y hy
  exact (growth_strictMono hc).monotoneOn hx (hx.trans hy) hy

theorem growth_lt_infinite {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    growth c x < infiniteGrowth c :=
  ((growth_strictMono hc) hx (show x + 1 ∈ Ici 0 by change 0 ≤ x + 1; linarith) (by linarith)).trans_le
    (growth_le_infinite hc (by linarith : 0 ≤ x + 1))

theorem infiniteGrowth_upper {c : ℝ} (hc : 0 < c) :
    infiniteGrowth c < 3 / 2 + 5 / (4 * c) := by
  have hs := Real.sqrt_pos.mpr hc
  have hs2 := Real.sq_sqrt hc.le
  have hr0 : 0 < root c 0 := root_positive (add_pos (Real.exp_pos _) hc)
  have hratio : Real.sqrt c / root c 0 < 1 := by
    apply (div_lt_one hr0).mpr
    unfold root rootSquared
    apply Real.sqrt_lt_sqrt hc.le
    norm_num
  have hα : 0 < prefactor c := by unfold prefactor; linarith
  have hi := mul_le_mul_of_nonneg_left (infiniteIntegral_upper hc)
    (mul_pos hs hα).le
  have he : Real.sqrt c * prefactor c * (1 / (2 * (Real.sqrt c)^3)) = prefactor c / (2 * c) := by
    field_simp
    nlinarith [hs2]
  rw [he] at hi
  have hb : infiniteGrowth c ≤ Real.sqrt c / root c 0 + prefactor c / (2 * c) := by
    unfold infiniteGrowth
    rw [div_eq_mul_inv]
    nlinarith
  have he' : 1 + prefactor c / (2 * c) = 3 / 2 + 5 / (4 * c) := by
    unfold prefactor
    field_simp
    ring
  rw [← he']
  linarith

theorem freeGrowth_tendsto : Tendsto freeGrowth atTop (𝓝 (3 / 2)) := by
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (he.div_const 2)

theorem infiniteGrowth_lower {c : ℝ} (hc : 0 < c) : 3 / 2 ≤ infiniteGrowth c := by
  apply le_of_tendsto_of_tendsto freeGrowth_tendsto (growth_tendsto hc)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h := (growth_free_bound (a0 := (1 : ℝ)) (lam := c) (by norm_num) hx hc.le x ⟨hx, le_rfl⟩).1
  simpa only [one_pow, mul_one, sub_nonneg] using h

theorem infiniteGrowth_parameter_limit : Tendsto infiniteGrowth atTop (𝓝 (3 / 2)) := by
  have hden : Tendsto (fun c : ℝ => 4 * c) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have he := squeeze_zero'
    ((eventually_gt_atTop (0 : ℝ)).mono (fun c hc => sub_nonneg.mpr (infiniteGrowth_lower hc)))
    ((eventually_gt_atTop (0 : ℝ)).mono (fun c hc => by
      have h := infiniteGrowth_upper hc
      exact (show infiniteGrowth c - 3 / 2 ≤ 5 / (4 * c) by linarith))) (hden.const_div_atTop 5)
  simpa using he.add (tendsto_const_nhds (x := (3 / 2 : ℝ)))

theorem native_tendsto {a0 lam : ℝ} (ha0 : 0 < a0) (hlam : 0 < lam) :
    Tendsto (nativeGrowth a0 lam) atTop (𝓝 (nativeInfinite a0 lam)) := by
  exact (growth_tendsto (mul_pos hlam (pow_pos ha0 3))).comp
    (Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const ha0))

theorem native_lt_infinite {a0 lam a : ℝ} (ha0 : 0 < a0) (hlam : 0 < lam) (ha : a0 ≤ a) :
    nativeGrowth a0 lam a < nativeInfinite a0 lam :=
  growth_lt_infinite (mul_pos hlam (pow_pos ha0 3)) (horizon_log_nonneg ha0 ha)

theorem native_infinite_upper {a0 lam : ℝ} (ha0 : 0 < a0) (hlam : 0 < lam) :
    nativeInfinite a0 lam < 3 / 2 + 5 / (4 * (lam * a0^3)) :=
  infiniteGrowth_upper (mul_pos hlam (pow_pos ha0 3))

/-- A locally uniform, integrable tail majorant earns parameter continuity. -/
theorem infiniteIntegral_continuousAt {c : ℝ} (hc : 0 < c) :
    ContinuousAt infiniteIntegral c := by
  have hh : 0 < c / 2 := half_pos hc
  have he : ∀ᶠ d in 𝓝 c, c / 2 < d := eventually_gt_nhds (by linarith : c / 2 < c)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => Real.exp (-2 * x) / (Real.sqrt (c / 2))^3)
  · exact Eventually.of_forall (fun d => (integrand_measurable d).aestronglyMeasurable)
  · filter_upwards [he] with d hd
    apply ae_of_all
    intro x
    have hd0 : 0 < d := hh.trans hd
    rw [Real.norm_eq_abs, abs_of_nonneg (integrand_bounds hd0 x).1]
    exact (integrand_bounds hd0 x).2.trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos (Real.sqrt_pos.mpr hh) 3)
        (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hd.le) 3))
  · exact (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).div_const _
  · apply ae_of_all
    intro x
    exact continuousAt_const.div ((root_continuous_parameter x).continuousAt.pow 3)
      (pow_ne_zero _ (root_positive (add_pos (Real.exp_pos _) hc)).ne')

theorem infiniteGrowth_continuousAt {c : ℝ} (hc : 0 < c) :
    ContinuousAt infiniteGrowth c := by
  exact Real.continuous_sqrt.continuousAt.mul
    (((root_continuous_parameter 0).continuousAt.inv₀
      (root_positive (add_pos (Real.exp_pos _) hc)).ne').add
      ((by unfold prefactor; fun_prop : ContinuousAt prefactor c).mul
        (infiniteIntegral_continuousAt hc)))

/-- The actual velocity gap keeps the growth gap increasing, so strictness survives the limit. -/
theorem growth_gap_strictMono {c1 c2 : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (h12 : c1 < c2) :
    StrictMonoOn (fun x => growth c1 x - growth c2 x) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact ((growth_derivative (rootLive_positive h1 x) ⟨hx.le, le_rfl⟩).sub
      (growth_derivative (rootLive_positive h2 x) ⟨hx.le, le_rfl⟩)).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := interior_subset hx
    change 0 < deriv (growth c1 - growth c2) x
    rw [((growth_derivative (rootLive_positive h1 x) ⟨hx0.le, le_rfl⟩).sub
      (growth_derivative (rootLive_positive h2 x) ⟨hx0.le, le_rfl⟩)).deriv]
    have hl1 := live_nonnegative (a0 := (1 : ℝ)) (L := x) (by norm_num) h1.le
    have hl2 := live_nonnegative (a0 := (1 : ℝ)) (L := x) (by norm_num) h2.le
    have hv := (growth_strict_parameter (by norm_num) hx0.le hl1 hl2 h12
      (constructed_growthSolution hx0.le hl1) (constructed_growthSolution hx0.le hl2)
      x ⟨hx0.le, le_rfl⟩ hx0).2
    simpa only [one_pow, mul_one, sub_pos] using hv

theorem infiniteGrowth_strictAntiOn : StrictAntiOn infiniteGrowth (Ioi 0) := by
  intro c1 h1 c2 h2 h12
  have hl1 := live_nonnegative (a0 := (1 : ℝ)) (L := (1 : ℝ)) (by norm_num) h1.le
  have hl2 := live_nonnegative (a0 := (1 : ℝ)) (L := (1 : ℝ)) (by norm_num) h2.le
  have hp := (growth_strict_parameter (by norm_num) (by norm_num) hl1 hl2 h12
    (constructed_growthSolution (by norm_num) hl1) (constructed_growthSolution (by norm_num) hl2)
    1 ⟨by norm_num, le_rfl⟩ (by norm_num)).1
  simp only [one_pow, mul_one] at hp
  have hb : growth c1 1 - growth c2 1 ≤ infiniteGrowth c1 - infiniteGrowth c2 := by
    apply ge_of_tendsto ((growth_tendsto h1).sub (growth_tendsto h2))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (growth_gap_strictMono h1 h2 h12).monotoneOn (by norm_num)
      (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  linarith

theorem native_infinite_continuousAt {a0 lam : ℝ} (ha0 : 0 < a0) (hlam : 0 < lam) :
    ContinuousAt (nativeInfinite a0) lam :=
  (infiniteGrowth_continuousAt (mul_pos hlam (pow_pos ha0 3))).comp
    (f := fun d : ℝ => d * a0^3) (x := lam) (by fun_prop)

theorem native_infinite_strictAntiOn {a0 : ℝ} (ha0 : 0 < a0) :
    StrictAntiOn (nativeInfinite a0) (Ioi 0) := by
  intro lam1 h1 lam2 h2 h12
  exact infiniteGrowth_strictAntiOn (mul_pos h1 (pow_pos ha0 3))
    (mul_pos h2 (pow_pos ha0 3)) (mul_lt_mul_of_pos_right h12 (pow_pos ha0 3))

theorem native_infinite_parameter_limit {a0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (nativeInfinite a0) atTop (𝓝 (3 / 2)) :=
  infiniteGrowth_parameter_limit.comp (tendsto_id.atTop_mul_const (pow_pos ha0 3))

/-- Equality with the limiting growth is never reached at a finite epoch. -/
theorem native_eventual_threshold_iff {a0 lam T : ℝ} (ha0 : 0 < a0) (hlam : 0 < lam) :
    (∃ a : ℝ, a0 ≤ a ∧ T ≤ nativeGrowth a0 lam a) ↔ T < nativeInfinite a0 lam := by
  constructor
  · rintro ⟨a, ha, hT⟩
    exact hT.trans_lt (native_lt_infinite ha0 hlam ha)
  · intro hT
    obtain ⟨a, hTa, ha⟩ := ((native_tendsto ha0 hlam).eventually_const_lt hT).and
      (eventually_ge_atTop a0) |>.exists
    exact ⟨a, ha, hTa.le⟩

/-- A coarse global bound, valid at every finite epoch, rather than just at a fixed horizon. -/
theorem native_global_bound {a0 lam a : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a)
    (hc : 1 ≤ lam * a0^3) : nativeGrowth a0 lam a < 3 := by
  have hlam : 0 < lam := by
    have hp := pow_pos ha0 3
    nlinarith
  have hd : 0 < 4 * (lam * a0^3) := by nlinarith
  have hf : 5 / (4 * (lam * a0^3)) ≤ 5 / 4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have h := (native_lt_infinite ha0 hlam ha).trans (native_infinite_upper ha0 hlam)
  linarith

end
end SbtCosmo.Derivation.GrowthInfinite
