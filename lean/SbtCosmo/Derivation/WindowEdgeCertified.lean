import SbtCosmo.Derivation.GrowthQuadrature
import SbtCosmo.Derivation.GrowthQuadratureData
import SbtCosmo.Derivation.WindowSample
import SbtCosmo.Derivation.WindowSensitivity

/-! Kernel-certified quadrature brackets for the actual original-population window endpoint. -/
namespace SbtCosmo.Derivation.WindowEdgeCertified
noncomputable section
open Set GrowthQuadrature GrowthScaleReturn GrowthComparison

theorem integral_lower_at_three : (2227 : ℝ) / 10000 ≤ integral 3 (1 / 1000) 20 := by
  have hcell : ∀ i < 264,
      0 < (GrowthQuadratureData.grid i : ℝ) ∧
      (GrowthQuadratureData.grid i : ℝ) ≤ GrowthQuadratureData.grid (i + 1) ∧
      0 ≤ (GrowthQuadratureData.lower i : ℝ) ∧
      (GrowthQuadratureData.lower i : ℝ)^2 * (1 + 3 * (GrowthQuadratureData.grid (i + 1) : ℝ)^3)^3 ≤
        (GrowthQuadratureData.grid i : ℝ)^3 ∧
      (GrowthQuadratureData.grid (i + 1) : ℝ)^3 ≤ (1 + 3 * (GrowthQuadratureData.grid i : ℝ)^3)^3 := by
    intro i hi
    exact_mod_cast GrowthQuadratureData.lower_cells ⟨i, hi⟩
  have hb := integral_grid_bounds (n := 264) (a := fun i => (GrowthQuadratureData.grid i : ℝ))
    (lo := fun i => (GrowthQuadratureData.lower i : ℝ)) (hi := fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 3) (by
      intro i hi
      obtain ⟨ha, hab, hlo, hbelow, habove⟩ := hcell i hi
      exact ⟨ha, hab, hlo, by norm_num, hbelow, by simpa using habove⟩)
  have hs : (2227 : ℝ) / 10000 ≤
      ∑ i ∈ Finset.range 264, ((GrowthQuadratureData.grid (i + 1) : ℝ) - GrowthQuadratureData.grid i) *
        (GrowthQuadratureData.lower i : ℝ) := by
    have hq : ((2227 / 10000 : ℚ) : ℝ) ≤
        ((∑ i ∈ Finset.range 264, (GrowthQuadratureData.grid (i + 1) - GrowthQuadratureData.grid i) *
          GrowthQuadratureData.lower i : ℚ) : ℝ) := by exact_mod_cast GrowthQuadratureData.lower_sum
    push_cast at hq
    exact hq
  have h0 : (GrowthQuadratureData.grid 0 : ℝ) = 1 / 1000 := by
    rw [GrowthQuadratureData.grid_endpoints.1]
    norm_num
  have hn : (GrowthQuadratureData.grid 264 : ℝ) = 20 := by
    exact_mod_cast GrowthQuadratureData.grid_endpoints.2
  dsimp only at hb
  rw [h0, hn] at hb
  exact hs.trans hb.1

theorem integral_upper_at_four : integral 4 (1 / 1000) 20 ≤ (187 : ℝ) / 1000 := by
  have hcell : ∀ i < 264,
      0 < (GrowthQuadratureData.grid i : ℝ) ∧
      (GrowthQuadratureData.grid i : ℝ) ≤ GrowthQuadratureData.grid (i + 1) ∧
      0 ≤ (GrowthQuadratureData.upper i : ℝ) ∧
      (GrowthQuadratureData.grid (i + 1) : ℝ)^3 ≤ (GrowthQuadratureData.upper i : ℝ)^2 *
        (1 + 4 * (GrowthQuadratureData.grid i : ℝ)^3)^3 := by
    intro i hi
    exact_mod_cast GrowthQuadratureData.upper_cells ⟨i, hi⟩
  have hb := integral_grid_bounds (n := 264) (a := fun i => (GrowthQuadratureData.grid i : ℝ))
    (lo := fun _ => 0) (hi := fun i => (GrowthQuadratureData.upper i : ℝ))
    (by norm_num : (0 : ℝ) ≤ 4) (by
      intro i hi
      obtain ⟨ha, hab, hhi, habove⟩ := hcell i hi
      exact ⟨ha, hab, by norm_num, hhi, by simp; positivity, habove⟩)
  have hs : (∑ i ∈ Finset.range 264,
      ((GrowthQuadratureData.grid (i + 1) : ℝ) - GrowthQuadratureData.grid i) *
        (GrowthQuadratureData.upper i : ℝ)) ≤ (187 : ℝ) / 1000 := by
    have hq : ((∑ i ∈ Finset.range 264, (GrowthQuadratureData.grid (i + 1) - GrowthQuadratureData.grid i) *
        GrowthQuadratureData.upper i : ℚ) : ℝ) ≤ ((187 / 1000 : ℚ) : ℝ) := by
      exact_mod_cast GrowthQuadratureData.upper_sum
    push_cast at hq
    exact hq
  have h0 : (GrowthQuadratureData.grid 0 : ℝ) = 1 / 1000 := by
    rw [GrowthQuadratureData.grid_endpoints.1]
    norm_num
  have hn : (GrowthQuadratureData.grid 264 : ℝ) = 20 := by
    exact_mod_cast GrowthQuadratureData.grid_endpoints.2
  dsimp only at hb
  rw [h0, hn] at hb
  exact hb.2.trans hs

theorem native_growth_at_three_lower : (964 : ℝ) < nativeGrowth (1 / 1000) 3 20 := by
  rw [native_growth_quadrature (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 20) (by norm_num : (0 : ℝ) ≤ 3)]
  have hr : (1732 : ℝ) / 1000 ≤ nativeRoot 3 20 := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα : (2500 : ℝ) ≤ nativePrefactor 3 (1 / 1000) := by norm_num [nativePrefactor]
  have hp := mul_le_mul hα integral_lower_at_three (by norm_num : (0 : ℝ) ≤ 2227 / 10000)
    (by norm_num [nativePrefactor] : 0 ≤ nativePrefactor 3 (1 / 1000))
  have hb : (2500 : ℝ) * (2227 / 10000) ≤ (nativeRoot 3 (1 / 1000))⁻¹ +
      nativePrefactor 3 (1 / 1000) * integral 3 (1 / 1000) 20 :=
    hp.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by norm_num : (0 : ℝ) ≤ 2500 * (2227 / 10000))
    (Real.sqrt_nonneg _)
  exact (by norm_num : (964 : ℝ) < (1732 / 1000) * (2500 * (2227 / 10000))).trans_le hm

theorem native_growth_at_four_upper : nativeGrowth (1 / 1000) 4 20 < (936 : ℝ) := by
  rw [native_growth_quadrature (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 20) (by norm_num : (0 : ℝ) ≤ 4)]
  have hr : nativeRoot 4 20 ≤ (200004 : ℝ) / 100000 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hr0 : (30000 : ℝ) ≤ nativeRoot 4 (1 / 1000) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hinv : (nativeRoot 4 (1 / 1000))⁻¹ ≤ (1 : ℝ) / 30000 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 30000) hr0
  have hα : 0 ≤ nativePrefactor 4 (1 / 1000) := by norm_num [nativePrefactor]
  have hb := add_le_add hinv (mul_le_mul_of_nonneg_left integral_upper_at_four hα)
  have hm := (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hr (by norm_num [nativePrefactor] :
      (0 : ℝ) ≤ 1 / 30000 + nativePrefactor 4 (1 / 1000) * (187 / 1000)))
  exact hm.trans_lt (by norm_num [nativePrefactor])

theorem sampled_threshold_tight_bounds : (960 : ℝ) < WindowSample.aggregateThreshold ∧
    WindowSample.aggregateThreshold < 961 := by
  rw [WindowSample.sampled_threshold_exact]
  norm_num

def upper : ℝ := WindowSample.exists_unique_realized_window.choose

theorem upper_spec : 0 < upper ∧ nativeGrowth (1 / 1000) upper 20 = WindowSample.aggregateThreshold ∧
    ∀ lam : ℝ, WindowSample.realizedGate lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ upper :=
  WindowSample.exists_unique_realized_window.choose_spec.1

/-- A certified endpoint bracket for the original exact population and continuum model. -/
theorem upper_certified_bounds : (3 : ℝ) < upper ∧ upper < 4 := by
  have hs := upper_spec
  have hm := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20)
  have hu : upper ∈ Ioi (-(1 / (20 : ℝ)^3)) := by change -(1 / (20 : ℝ)^3) < upper; linarith [hs.1]
  constructor
  · apply (hm.lt_iff_gt hu (by norm_num : (3 : ℝ) ∈ Ioi (-(1 / (20 : ℝ)^3)))).mp
    rw [hs.2.1]
    linarith [sampled_threshold_tight_bounds.2, native_growth_at_three_lower]
  · apply (hm.lt_iff_gt (by norm_num : (4 : ℝ) ∈ Ioi (-(1 / (20 : ℝ)^3))) hu).mp
    rw [hs.2.1]
    linarith [sampled_threshold_tight_bounds.1, native_growth_at_four_upper]

theorem paper_bracket_certified : (233 : ℝ) / 100 < upper ∧ upper < (531 : ℝ) / 100 := by
  constructor <;> linarith [upper_certified_bounds.1, upper_certified_bounds.2]

theorem inside_three_outside_four : WindowSample.realizedGate 3 ∧ ¬ WindowSample.realizedGate 4 := by
  rw [upper_spec.2.2 3, upper_spec.2.2 4]
  constructor
  · exact ⟨by norm_num, upper_certified_bounds.1.le⟩
  · intro h
    exact upper_certified_bounds.2.not_ge h.2

theorem upper_eq_scaled_endpoint : upper = WindowSensitivity.scaledEndpoint WindowSample.delta 1 := by
  have hth : WindowSensitivity.scaledThreshold WindowSample.delta 1 = WindowSample.aggregateThreshold := by
    simp [WindowSensitivity.scaledThreshold, WindowSensitivity.original_delta_positive.ne']
  have hT : WindowSensitivity.scaledThreshold WindowSample.delta 1 ∈
      Ioo (GrowthLimit.freeGrowth (Real.log 20000)) 20000 := by
    rw [hth]
    constructor
    · unfold GrowthLimit.freeGrowth
      linarith [Real.exp_pos (-2 * Real.log (20000 : ℝ)), sampled_threshold_tight_bounds.1]
    · linarith [sampled_threshold_tight_bounds.2]
  have hw := WindowSensitivity.scaled_endpoint_native_window WindowSensitivity.original_delta_positive
    (by norm_num : (0 : ℝ) < 1) hT
  have he : nativeGrowth (1 / 1000) (WindowSensitivity.scaledEndpoint WindowSample.delta 1) 20 =
      WindowSample.aggregateThreshold := by simpa only [hth] using hw.2.1
  have hg : ∀ lam : ℝ, WindowSample.realizedGate lam ↔ -(1 / 8000 : ℝ) < lam ∧
      lam ≤ WindowSensitivity.scaledEndpoint WindowSample.delta 1 := by
    have ha : WindowSensitivity.scaledAmplitude 1 = WindowSample.amplitude := by
      funext j i
      simp only [WindowSensitivity.scaledAmplitude, one_mul]
    simpa only [ha, WindowSample.realizedGate] using hw.2.2
  exact (WindowSample.exists_unique_realized_window.choose_spec.2 _ ⟨hw.1, he, hg⟩).symm

theorem paper_inside_outside : WindowSample.realizedGate ((233 : ℝ) / 100) ∧
    ¬ WindowSample.realizedGate ((531 : ℝ) / 100) := by
  rw [upper_spec.2.2 (233 / 100), upper_spec.2.2 (531 / 100)]
  constructor
  · exact ⟨by norm_num, paper_bracket_certified.1.le⟩
  · intro h
    exact paper_bracket_certified.2.not_ge h.2

/-- A unique original aggregate continuum window with a certified numerical upper bracket. -/
theorem exists_unique_certified_window : ∃! u : ℝ, 3 < u ∧ u < 4 ∧
    nativeGrowth (1 / 1000) u 20 = WindowSample.aggregateThreshold ∧
      ∀ lam : ℝ, WindowSample.realizedGate lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ u := by
  refine ⟨upper, ⟨upper_certified_bounds.1, upper_certified_bounds.2,
    upper_spec.2.1, upper_spec.2.2⟩, ?_⟩
  intro u hu
  exact WindowSample.exists_unique_realized_window.choose_spec.2 u
    ⟨by linarith [hu.1], hu.2.2.1, hu.2.2.2⟩

end
end SbtCosmo.Derivation.WindowEdgeCertified
