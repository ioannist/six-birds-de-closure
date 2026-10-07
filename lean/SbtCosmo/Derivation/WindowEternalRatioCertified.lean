import SbtCosmo.Derivation.WindowEternalRatioData
import SbtCosmo.Derivation.WindowEndpointRatio
import SbtCosmo.Derivation.WindowEternalBounds

/-! Sharp infinite endpoint bracket from exact native quadrature plus the derived actual IVP tail. -/
namespace SbtCosmo.Derivation.WindowEternalRatioCertified
noncomputable section
open Set GrowthQuadrature GrowthScaleReturn GrowthInfinite GrowthInfiniteTail

theorem integral_horizon_upper_sharp : integral (17 / 5) (1 / 1000) 20 ≤ (4159 : ℝ) / 20000 := by
  have hcell : ∀ i < 1024,
      0 < (WindowEternalRatioData.grid i : ℝ) ∧
      (WindowEternalRatioData.grid i : ℝ) ≤ WindowEternalRatioData.grid (i+1) ∧
      0 ≤ (WindowEternalRatioData.upper i : ℝ) ∧
      ((2 * (17/5) * (WindowEternalRatioData.grid (i+1) : ℝ)^3 ≤ 1 ∧
        (WindowEternalRatioData.grid (i+1) : ℝ)^3 ≤ (WindowEternalRatioData.upper i : ℝ)^2 *
          (1 + (17/5) * (WindowEternalRatioData.grid (i+1) : ℝ)^3)^3) ∨
      (1 ≤ 2 * (17/5) * (WindowEternalRatioData.grid i : ℝ)^3 ∧
        (WindowEternalRatioData.grid i : ℝ)^3 ≤ (WindowEternalRatioData.upper i : ℝ)^2 *
          (1 + (17/5) * (WindowEternalRatioData.grid i : ℝ)^3)^3) ∨
      4 ≤ 27 * (17/5) * (WindowEternalRatioData.upper i : ℝ)^2) := by
    intro i hi
    rw [show (17 / 5 : ℝ) = ((17 / 5 : ℚ) : ℝ) by norm_num]
    exact_mod_cast WindowEternalRatioData.upper_cells ⟨i, hi⟩
  have hb := GrowthQuadratureSharp.integral_grid_bounds (n := 1024)
    (a := fun i => (WindowEternalRatioData.grid i : ℝ)) (lo := fun _ => 0)
    (hi := fun i => (WindowEternalRatioData.upper i : ℝ))
    (by norm_num : (0 : ℝ) ≤ 17 / 5) (by
      intro i hi
      obtain ⟨ha, hab, hhi, hcert⟩ := hcell i hi
      refine ⟨ha, hab, ?_⟩
      intro x hx
      exact ⟨density_nonnegative, GrowthQuadratureSharp.density_cell_upper (by norm_num) ha.le hx hhi hcert⟩)
  have hs : (∑ i ∈ Finset.range 1024,
      ((WindowEternalRatioData.grid (i+1) : ℝ) - WindowEternalRatioData.grid i) *
        (WindowEternalRatioData.upper i : ℝ)) ≤ (4159 : ℝ) / 20000 := by
    have hq : ((∑ i ∈ Finset.range 1024, (WindowEternalRatioData.grid (i+1) - WindowEternalRatioData.grid i) *
          WindowEternalRatioData.upper i : ℚ) : ℝ) ≤ ((4159 / 20000 : ℚ) : ℝ) := by
      exact_mod_cast WindowEternalRatioData.upper_sum
    push_cast at hq
    exact hq
  have h0 : (WindowEternalRatioData.grid 0 : ℝ) = 1 / 1000 := by
    rw [WindowEternalRatioData.grid_endpoints.1]
    norm_num
  have hn : (WindowEternalRatioData.grid 1024 : ℝ) = 20 := by
    exact_mod_cast WindowEternalRatioData.grid_endpoints.2
  dsimp only at hb
  rw [h0, hn] at hb
  exact hb.2.trans hs

theorem horizon_growth_upper_sharp : nativeGrowth (1 / 1000) (17 / 5) 20 < (959 : ℝ) := by
  rw [native_growth_quadrature (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 20) (by norm_num : (0 : ℝ) ≤ 17 / 5)]
  have hr : nativeRoot (17 / 5) 20 ≤ (1844 : ℝ) / 1000 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hr0 : (30000 : ℝ) ≤ nativeRoot (17 / 5) (1 / 1000) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hinv : (nativeRoot (17 / 5) (1 / 1000))⁻¹ ≤ (1 : ℝ) / 30000 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 30000) hr0
  have hα : 0 ≤ nativePrefactor (17 / 5) (1 / 1000) := by norm_num [nativePrefactor]
  have hb := add_le_add hinv (mul_le_mul_of_nonneg_left integral_horizon_upper_sharp hα)
  have hm := (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hr (by norm_num [nativePrefactor] :
      (0 : ℝ) ≤ 1 / 30000 + nativePrefactor (17 / 5) (1 / 1000) * (4159 / 20000)))
  exact hm.trans_lt (by norm_num [nativePrefactor])


theorem limiting_growth_upper_sharp : nativeInfinite (1 / 1000) (17 / 5) < (960 : ℝ) := by
  have ht := native_tail_bound (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (0 : ℝ) < 17 / 5) (by norm_num : (1 / 1000 : ℝ) ≤ 20)
  norm_num at ht
  linarith [horizon_growth_upper_sharp]

theorem infinite_upper_tight_bounds : (3 : ℝ) < WindowEternalRecords.upper ∧
    WindowEternalRecords.upper < 17 / 5 := by
  have hs := WindowEternalRecords.upper_spec
  refine ⟨WindowEternalBounds.infinite_upper_bracket.1, ?_⟩
  apply ((native_infinite_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)).lt_iff_gt
    (by norm_num : (0 : ℝ) < 17 / 5) hs.1).mp
  rw [hs.2]
  linarith [WindowEdgeCertified.sampled_threshold_tight_bounds.1, limiting_growth_upper_sharp]

end
end SbtCosmo.Derivation.WindowEternalRatioCertified
