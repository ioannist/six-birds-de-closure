import SbtCosmo.Derivation.GrowthFirstRecordLive

/-! Derived bounds for the actual negative-parameter expanding IVP. -/
namespace SbtCosmo.Derivation.GrowthNegativeBounds
noncomputable section
open Set GrowthComparison GrowthExistence GrowthScaleReturn

def integralBarrier (c x : ℝ) : ℝ := (2 / 3) * (Real.exp x / root c x) - primitive c x

theorem integralBarrier_derivative {c L x : ℝ} (hr : RootLive c L) (hx : x ∈ Icc 0 L) :
    HasDerivAt (integralBarrier c) ((2 / 3) * (Real.exp x / root c x)) x := by
  have hp := root_positive (hr x hx)
  have h := (((Real.hasDerivAt_exp x).div (hasDerivAt_root (hr x hx)) hp.ne').const_mul (2 / 3)).sub
    (primitive_derivative hr hx)
  have he : Real.exp x * Real.exp (-3 * x) = Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert h using 1
  have hsq := root_sq (hr x hx)
  unfold integrand rate
  rw [← hsq]
  field_simp [hp.ne']
  simp only [neg_mul] at he
  nlinarith [he]

theorem integralBarrier_monotone {c L : ℝ} (hr : RootLive c L) :
    MonotoneOn (integralBarrier c) (Icc 0 L) := by
  apply (strictMonoOn_of_deriv_pos (convex_Icc 0 L)
    (fun x hx => (integralBarrier_derivative hr hx).continuousAt.continuousWithinAt) ?_).monotoneOn
  intro x hx
  rw [(integralBarrier_derivative hr (interior_subset hx)).deriv]
  exact mul_pos (by norm_num) (div_pos (Real.exp_pos _) (root_positive (hr x (interior_subset hx))))

theorem growth_linear_upper {c L x : ℝ} (hL : 0 ≤ L) (hr : RootLive c L)
    (hc : c ≤ 0) (hx : x ∈ Icc 0 L) : growth c x < (5 / 3) * Real.exp x := by
  have hr0 := root_positive (hr 0 ⟨le_rfl, hL⟩)
  have hrx := root_positive (hr x hx)
  have hc0 : -1 < c := by
    have h := hr 0 ⟨le_rfl, hL⟩
    norm_num [rootSquared] at h
    linarith
  have hα : 3 / 2 < prefactor c := by unfold prefactor; linarith
  have hb := integralBarrier_monotone hr ⟨le_rfl, hL⟩ hx hx.1
  have hz : primitive c 0 = 0 := by simp [primitive]
  unfold integralBarrier at hb
  rw [Real.exp_zero, hz] at hb
  have hi : primitive c x ≤ (2 / 3) * (Real.exp x / root c x - 1 / root c 0) := by linarith
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ prefactor c)) hrx.le
  have he : root c x * ((root c 0)⁻¹ + prefactor c * ((2 / 3) * (Real.exp x / root c x - 1 / root c 0))) =
      (2 / 3) * prefactor c * Real.exp x + (1 - (2 / 3) * prefactor c) * (root c x / root c 0) := by
    field_simp
    ring
  have hs : (1 - (2 / 3) * prefactor c) * (root c x / root c 0) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (div_pos hrx hr0)
  have hg : growth c x ≤ (2 / 3) * prefactor c * Real.exp x +
      (1 - (2 / 3) * prefactor c) * (root c x / root c 0) := by
    rw [← he]
    unfold growth
    nlinarith
  have hp : (2 / 3) * prefactor c ≤ (5 : ℝ) / 3 := by unfold prefactor; linarith
  have hu := mul_le_mul_of_nonneg_right hp (Real.exp_pos x).le
  linarith

theorem native_linear_upper {a0 a lam : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a)
    (hlam : -(1 / a^3) < lam) (hnonpos : lam ≤ 0) : nativeGrowth a0 lam a < (5 / 3) * (a / a0) := by
  have hL := horizon_log_nonneg ha0 ha
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le ha)) hlam
  have h := growth_linear_upper hL (rootLive_of_live hl)
    (mul_nonpos_of_nonpos_of_nonneg hnonpos (pow_pos ha0 3).le) ⟨hL, le_rfl⟩
  simpa only [logScale, Real.exp_log (div_pos (ha0.trans_le ha) ha0)] using h

end
end SbtCosmo.Derivation.GrowthNegativeBounds
