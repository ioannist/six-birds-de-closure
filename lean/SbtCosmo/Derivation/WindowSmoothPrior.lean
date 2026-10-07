import SbtCosmo.Derivation.WindowPatchRobustEdge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A smooth strictly positive prior can put arbitrarily high mass on actual
small-ratio records. Local regularity at zero cannot force upper-edge typicality.
The normalized density is on the full positive window, not an atomic prior. -/
namespace SbtCosmo.Derivation.WindowSmoothPrior
noncomputable section
open Set WindowPatchRobust WindowPatchRobustEdge WindowRobustRecord
open scoped ContDiff

def raw (k t : ℝ) : ℝ := k * Real.exp (-k*t)
def density (k U t : ℝ) : ℝ := raw k t / (1-Real.exp (-k*U))

theorem raw_continuous (k : ℝ) : Continuous (raw k) :=
  continuous_const.mul (Real.continuous_exp.comp (continuous_const.neg.mul continuous_id))

theorem raw_integral (k a b : ℝ) :
    (∫ t in a..b, raw k t) = Real.exp (-k*a)-Real.exp (-k*b) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-k*t)) (raw k t) t := by
    convert (((hasDerivAt_id t).const_mul (-k)).exp).neg using 1
    dsimp [raw]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((raw_continuous k).intervalIntegrable a b)
  simpa only [sub_neg_eq_add,neg_add_eq_sub] using h

theorem normalizer_positive {k U : ℝ} (hk : 0 < k) (hU : 0 < U) :
    0 < 1-Real.exp (-k*U) := by
  have he : Real.exp (-k*U) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  linarith

theorem density_positive {k U : ℝ} (hk : 0 < k) (hU : 0 < U) (t : ℝ) :
    0 < density k U t := div_pos (mul_pos hk (Real.exp_pos _)) (normalizer_positive hk hU)

theorem density_smooth (k U : ℝ) : ContDiff ℝ ∞ (density k U) :=
  (contDiff_const.mul ((contDiff_const.neg.mul contDiff_id).exp)).div_const _

theorem density_integral {k U : ℝ} (hk : 0 < k) (hU : 0 < U) :
    (∫ t in 0..U, density k U t) = 1 := by
  unfold density
  rw [intervalIntegral.integral_div,raw_integral]
  simp only [mul_zero,Real.exp_zero]
  exact div_self (normalizer_positive hk hU).ne'

theorem prefix_integral (k U a : ℝ) :
    (∫ t in 0..a, density k U t) = (1-Real.exp (-k*a))/(1-Real.exp (-k*U)) := by
  unfold density
  rw [intervalIntegral.integral_div,raw_integral]
  simp only [mul_zero,Real.exp_zero]

theorem concentration {k a U eta : ℝ} (hk : 0 < k) (ha : 0 < a)
    (haU : a ≤ U) (he : eta ∈ Ioo 0 1) (hdecay : Real.exp (-k*a) ≤ eta/2) :
    1-eta < ∫ t in 0..a, density k U t := by
  have hU : 0 < U := ha.trans_le haU
  have hz := normalizer_positive hk hU
  have heU := Real.exp_pos (-k*U)
  rw [prefix_integral,lt_div_iff₀ hz]
  nlinarith [he.1,he.2]

theorem rate_constructed {a eta : ℝ} (ha : 0 < a) (he : eta ∈ Ioo 0 1) :
    0 < Real.log (2/eta)/a ∧
      Real.exp (-(Real.log (2/eta)/a)*a) = eta/2 := by
  have harg : 1 < (2:ℝ)/eta := (lt_div_iff₀ he.1).mpr (by linarith [he.2])
  refine ⟨div_pos (Real.log_pos harg) ha,?_⟩
  rw [neg_mul,div_mul_cancel₀ _ ha.ne',Real.exp_neg,
    Real.exp_log (by linarith [harg] : (0:ℝ) < 2/eta)]
  field_simp

/-- The SAME raw exponential rate concentrates all three original populations'
full positive window, and all seeds and knob points share the same low-ratio
interval. Normalization is separately earned for each actual window. -/
theorem actual_all_windows_smooth_small_ratio {epsilon eta : ℝ} (he : 0 < epsilon)
    (heta : eta ∈ Ioo 0 1) :
    ∃ k a : ℝ, 0 < k ∧ 0 < a ∧ a ≤ minimumEndpoint ∧
      ∀ d s : ℝ, Rectangle d s → (∀ v : Bool,
        (ContDiff ℝ ∞ (density k (upper v d s))) ∧
        (∀ t : ℝ, 0 < density k (upper v d s) t) ∧
        (∫ t in 0..upper v d s, density k (upper v d s) t) = 1 ∧
        1-eta < (∫ t in 0..a, density k (upper v d s) t) ∧
        ∀ lam ∈ Icc 0 a, gate v d s lam ∧
          ∀ j : Fin 12, 0 ≤ ratio v d s j lam ∧ ratio v d s j lam < epsilon) ∧
      ContDiff ℝ ∞ (density k (WindowSensitivity.scaledEndpoint d s)) ∧
      (∀ t : ℝ, 0 < density k (WindowSensitivity.scaledEndpoint d s) t) ∧
      (∫ t in 0..WindowSensitivity.scaledEndpoint d s,
        density k (WindowSensitivity.scaledEndpoint d s) t) = 1 ∧
      1-eta < (∫ t in 0..a, density k (WindowSensitivity.scaledEndpoint d s) t) ∧
      ∀ lam ∈ Icc 0 a, WindowRobustRecord.gate d s lam ∧
        ∀ j : Fin 12, 0 ≤ WindowRobustRatio.ratio d s j lam ∧
          WindowRobustRatio.ratio d s j lam < epsilon := by
  have hmin : 0 < minimumEndpoint := (endpoint_spec corner_rectangles.1 false).1
  let a := min minimumEndpoint (epsilon/16000)
  have ha : 0 < a := lt_min hmin (div_pos he (by norm_num))
  have ham : a ≤ minimumEndpoint := min_le_left _ _
  have has : a ≤ epsilon/16000 := min_le_right _ _
  let k := Real.log (2/eta)/a
  have hk : 0 < k := (rate_constructed ha heta).1
  have hdecay : Real.exp (-k*a) = eta/2 := (rate_constructed ha heta).2
  refine ⟨k,a,hk,ha,ham,?_⟩
  intro d s hR
  constructor
  · intro v
    have hu := (endpoint_spec hR v).1
    have hau : a ≤ upper v d s := ham.trans (common_corner_bounds hR v).1
    refine ⟨density_smooth _ _,density_positive hk hu,density_integral hk hu,
      concentration hk ha hau heta hdecay.le,?_⟩
    intro lam hl
    have hg := common_positive_window hR ⟨hl.1,hl.2.trans ham⟩ v
    refine ⟨hg,?_⟩
    intro j
    exact ⟨ratio_nonnegative hR hg j,by
      have hb := ratio_nonnegative_upper hR hg hl.1 j
      linarith [hl.2]⟩
  · have hu := (WindowRobustRecord.endpoint_spec hR).1
    have hau : a ≤ WindowSensitivity.scaledEndpoint d s :=
      (ham.trans (common_corner_bounds hR false).1).trans (endpoint_order hR).1.le
    refine ⟨density_smooth _ _,density_positive hk hu,density_integral hk hu,
      concentration hk ha hau heta hdecay.le,?_⟩
    intro lam hl
    have hg32 := common_positive_window hR ⟨hl.1,hl.2.trans ham⟩ false
    have hg := (gate_inclusions hR lam).1 hg32
    refine ⟨hg,?_⟩
    intro j
    exact ⟨WindowRobustRatio.ratio_nonnegative hR hg j,by
      have hb := WindowRobustRatio.ratio_nonnegative_upper hR hg hl.1 j
      linarith [hl.2]⟩


end
end SbtCosmo.Derivation.WindowSmoothPrior
