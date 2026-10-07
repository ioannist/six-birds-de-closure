import SbtCosmo.Derivation.GrowthQuadratureSharp
import SbtCosmo.Derivation.WindowEndpointRatioData
import SbtCosmo.Derivation.WindowFirstRecord

/-! Certified ratios at the actual original positive endpoint and throughout its positive window. -/
namespace SbtCosmo.Derivation.WindowEndpointRatio
noncomputable section
open Set GrowthQuadrature GrowthScaleReturn GrowthFirstRecord WindowFirstRecord

theorem integral_prefix_lower : (1938 : ℝ) / 10000 ≤ integral (17 / 5) (1 / 1000) (5 / 2) := by
  have hcell : ∀ i < 512,
      0 < (WindowEndpointRatioData.grid i : ℝ) ∧
      (WindowEndpointRatioData.grid i : ℝ) ≤ WindowEndpointRatioData.grid (i + 1) ∧
      0 ≤ (WindowEndpointRatioData.lower i : ℝ) ∧
      (WindowEndpointRatioData.lower i : ℝ)^2 * (1 + (17/5) * (WindowEndpointRatioData.grid i : ℝ)^3)^3 ≤
        (WindowEndpointRatioData.grid i : ℝ)^3 ∧
      (WindowEndpointRatioData.lower i : ℝ)^2 * (1 + (17/5) * (WindowEndpointRatioData.grid (i+1) : ℝ)^3)^3 ≤
        (WindowEndpointRatioData.grid (i+1) : ℝ)^3 := by
    intro i hi
    rw [show (17 / 5 : ℝ) = ((17 / 5 : ℚ) : ℝ) by norm_num]
    exact_mod_cast WindowEndpointRatioData.lower_cells ⟨i, hi⟩
  have hb := GrowthQuadratureSharp.integral_grid_bounds (n := 512)
    (a := fun i => (WindowEndpointRatioData.grid i : ℝ))
    (lo := fun i => (WindowEndpointRatioData.lower i : ℝ)) (hi := fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 17 / 5) (by
      intro i hi
      obtain ⟨ha, hab, hlo, hl, hr⟩ := hcell i hi
      refine ⟨ha, hab, ?_⟩
      intro x hx
      exact ⟨GrowthQuadratureSharp.density_cell_lower (by norm_num) ha.le hx hlo hl hr,
        GrowthQuadratureSharp.density_global_upper (by norm_num) (ha.le.trans hx.1) (by norm_num) (by norm_num)⟩)
  have hs : (1938 : ℝ) / 10000 ≤
      ∑ i ∈ Finset.range 512, ((WindowEndpointRatioData.grid (i+1) : ℝ) - WindowEndpointRatioData.grid i) *
        (WindowEndpointRatioData.lower i : ℝ) := by
    have hq : ((1938 / 10000 : ℚ) : ℝ) ≤
        ((∑ i ∈ Finset.range 512, (WindowEndpointRatioData.grid (i+1) - WindowEndpointRatioData.grid i) *
          WindowEndpointRatioData.lower i : ℚ) : ℝ) := by exact_mod_cast WindowEndpointRatioData.lower_sum
    push_cast at hq
    exact hq
  have h0 : (WindowEndpointRatioData.grid 0 : ℝ) = 1 / 1000 := by
    rw [WindowEndpointRatioData.grid_endpoints.1]
    norm_num
  have hn : (WindowEndpointRatioData.grid 512 : ℝ) = 5 / 2 := by
    rw [WindowEndpointRatioData.grid_endpoints.2.1]
    norm_num
  dsimp only at hb
  rw [h0, hn] at hb
  exact hs.trans hb.1

theorem integral_horizon_upper : integral (17 / 5) (1 / 1000) 20 ≤ (2082 : ℝ) / 10000 := by
  have hcell : ∀ i < 704,
      0 < (WindowEndpointRatioData.grid i : ℝ) ∧
      (WindowEndpointRatioData.grid i : ℝ) ≤ WindowEndpointRatioData.grid (i+1) ∧
      0 ≤ (WindowEndpointRatioData.upper i : ℝ) ∧
      ((2 * (17/5) * (WindowEndpointRatioData.grid (i+1) : ℝ)^3 ≤ 1 ∧
        (WindowEndpointRatioData.grid (i+1) : ℝ)^3 ≤ (WindowEndpointRatioData.upper i : ℝ)^2 *
          (1 + (17/5) * (WindowEndpointRatioData.grid (i+1) : ℝ)^3)^3) ∨
      (1 ≤ 2 * (17/5) * (WindowEndpointRatioData.grid i : ℝ)^3 ∧
        (WindowEndpointRatioData.grid i : ℝ)^3 ≤ (WindowEndpointRatioData.upper i : ℝ)^2 *
          (1 + (17/5) * (WindowEndpointRatioData.grid i : ℝ)^3)^3) ∨
      4 ≤ 27 * (17/5) * (WindowEndpointRatioData.upper i : ℝ)^2) := by
    intro i hi
    rw [show (17 / 5 : ℝ) = ((17 / 5 : ℚ) : ℝ) by norm_num]
    exact_mod_cast WindowEndpointRatioData.upper_cells ⟨i, hi⟩
  have hb := GrowthQuadratureSharp.integral_grid_bounds (n := 704)
    (a := fun i => (WindowEndpointRatioData.grid i : ℝ)) (lo := fun _ => 0)
    (hi := fun i => (WindowEndpointRatioData.upper i : ℝ))
    (by norm_num : (0 : ℝ) ≤ 17 / 5) (by
      intro i hi
      obtain ⟨ha, hab, hhi, hcert⟩ := hcell i hi
      refine ⟨ha, hab, ?_⟩
      intro x hx
      exact ⟨density_nonnegative, GrowthQuadratureSharp.density_cell_upper (by norm_num) ha.le hx hhi hcert⟩)
  have hs : (∑ i ∈ Finset.range 704,
      ((WindowEndpointRatioData.grid (i+1) : ℝ) - WindowEndpointRatioData.grid i) *
        (WindowEndpointRatioData.upper i : ℝ)) ≤ (2082 : ℝ) / 10000 := by
    have hq : ((∑ i ∈ Finset.range 704, (WindowEndpointRatioData.grid (i+1) - WindowEndpointRatioData.grid i) *
          WindowEndpointRatioData.upper i : ℚ) : ℝ) ≤ ((2082 / 10000 : ℚ) : ℝ) := by
      exact_mod_cast WindowEndpointRatioData.upper_sum
    push_cast at hq
    exact hq
  have h0 : (WindowEndpointRatioData.grid 0 : ℝ) = 1 / 1000 := by
    rw [WindowEndpointRatioData.grid_endpoints.1]
    norm_num
  have hn : (WindowEndpointRatioData.grid 704 : ℝ) = 20 := by
    exact_mod_cast WindowEndpointRatioData.grid_endpoints.2.2
  dsimp only at hb
  rw [h0, hn] at hb
  exact hb.2.trans hs

theorem prefix_growth_lower : (901 : ℝ) < nativeGrowth (1 / 1000) (17 / 5) (5 / 2) := by
  rw [native_growth_quadrature (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 5 / 2) (by norm_num : (0 : ℝ) ≤ 17 / 5)]
  have hr : (1861 : ℝ) / 1000 ≤ nativeRoot (17 / 5) (5 / 2) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα : (2500 : ℝ) ≤ nativePrefactor (17 / 5) (1 / 1000) := by norm_num [nativePrefactor]
  have hp := mul_le_mul hα integral_prefix_lower (by norm_num : (0 : ℝ) ≤ 1938 / 10000)
    (by norm_num [nativePrefactor] : 0 ≤ nativePrefactor (17 / 5) (1 / 1000))
  have hb : (2500 : ℝ) * (1938 / 10000) ≤ (nativeRoot (17 / 5) (1 / 1000))⁻¹ +
      nativePrefactor (17 / 5) (1 / 1000) * integral (17 / 5) (1 / 1000) (5 / 2) :=
    hp.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by norm_num : (0 : ℝ) ≤ 2500 * (1938 / 10000))
    (Real.sqrt_nonneg _)
  exact (by norm_num : (901 : ℝ) < (1861 / 1000) * (2500 * (1938 / 10000))).trans_le hm

theorem horizon_growth_upper : nativeGrowth (1 / 1000) (17 / 5) 20 < (960 : ℝ) := by
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
  have hb := add_le_add hinv (mul_le_mul_of_nonneg_left integral_horizon_upper hα)
  have hm := (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hr (by norm_num [nativePrefactor] :
      (0 : ℝ) ≤ 1 / 30000 + nativePrefactor (17 / 5) (1 / 1000) * (2082 / 10000)))
  exact hm.trans_lt (by norm_num [nativePrefactor])

theorem upper_tight_bounds : (3 : ℝ) < WindowEdgeCertified.upper ∧ WindowEdgeCertified.upper < 17 / 5 := by
  have hs := WindowEdgeCertified.upper_spec
  have hm := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20)
  have hu : WindowEdgeCertified.upper ∈ Ioi (-(1 / (20 : ℝ)^3)) := by
    change -(1 / (20 : ℝ)^3) < WindowEdgeCertified.upper
    linarith [hs.1]
  refine ⟨WindowEdgeCertified.upper_certified_bounds.1, ?_⟩
  apply (hm.lt_iff_gt (by norm_num : (17 / 5 : ℝ) ∈ Ioi (-(1 / (20 : ℝ)^3))) hu).mp
  rw [hs.2.1]
  linarith [WindowEdgeCertified.sampled_threshold_tight_bounds.1, horizon_growth_upper]

theorem final_above_threshold {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    threshold j ≤ nativeGrowth (1 / 1000) lam 20 := by
  have hu : 0 < WindowEdgeCertified.upper := WindowEdgeCertified.upper_spec.1
  have hanti := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20)
  have hg := hanti.antitoneOn
    (show lam ∈ Ioi (-(1 / (20 : ℝ)^3)) by change -(1 / (20 : ℝ)^3) < lam; linarith [hlam.1])
    (show WindowEdgeCertified.upper ∈ Ioi (-(1 / (20 : ℝ)^3)) by
      change -(1 / (20 : ℝ)^3) < WindowEdgeCertified.upper; linarith) hlam.2
  rw [WindowEdgeCertified.upper_spec.2.1] at hg
  linarith [(threshold_bounds j).2, WindowEdgeCertified.sampled_threshold_tight_bounds.1]

theorem time_spec {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    time j lam ∈ Icc (1 / 1000) 20 ∧ nativeGrowth (1 / 1000) lam (time j lam) = threshold j := by
  exact firstTime_spec (by norm_num) (by norm_num) hlam.1
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)

theorem time_iff_any_collapse {lam a : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper)
    (ha : a ∈ Icc (1 / 1000) 20) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a) ↔
      time j lam ≤ a := by
  have hD := (native_positive (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num)
    (show -(1 / (20 : ℝ)^3) < lam by linarith [hlam.1]) a ha).1.le
  exact (any_patch_collapse_iff (maximum_spec j).1 hD (maximum_spec j).2.1
    (maximum_spec j).2.2).trans (firstTime_iff_threshold (by norm_num) (by norm_num)
      hlam.1 (show 1 < threshold j by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j) ha)

theorem time_is_first_collapse {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam (time j lam)) ∧
      ∀ a ∈ Icc (1 / 1000) 20, a < time j lam →
        ¬ ∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a := by
  refine ⟨(time_iff_any_collapse hlam (time_spec hlam j).1 j).mpr le_rfl, ?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hlam ha j).mp hc)

theorem time_lower {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    (1 : ℝ) / 2 < time j lam := by
  have h := firstTime_lower_matter (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num) hlam.1
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)
  change (1 / 1000 : ℝ) * threshold j ≤ time j lam at h
  linarith [(threshold_bounds j).1]

theorem prefix_above_threshold {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    threshold j ≤ nativeGrowth (1 / 1000) lam (5 / 2) := by
  have hanti := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 5 / 2)
  have hparam : lam ≤ (17 : ℝ) / 5 := hlam.2.trans upper_tight_bounds.2.le
  have hg := hanti.antitoneOn
    (show lam ∈ Ioi (-(1 / (5 / 2 : ℝ)^3)) by change -(1 / (5 / 2 : ℝ)^3) < lam; linarith [hlam.1])
    (by norm_num) hparam
  linarith [(threshold_bounds j).2, prefix_growth_lower]

theorem time_upper {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    time j lam ≤ 5 / 2 := by
  apply (firstTime_iff_threshold (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num)
    hlam.1 (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)
    (by norm_num : (5 / 2 : ℝ) ∈ Icc (1 / 1000) 20)).mp
  exact prefix_above_threshold hlam j

theorem time_strictMono (j : Fin 12) : StrictMonoOn (time j) (Icc 0 WindowEdgeCertified.upper) := by
  intro l1 h1 l2 h2 h12
  exact firstTime_strict_parameter (by norm_num) (by norm_num) h1.1 h12
    (by linarith [(threshold_bounds j).1]) (final_above_threshold h1 j) (final_above_threshold h2 j)

theorem ratio_strictMono (j : Fin 12) : StrictMonoOn (ratio j) (Icc 0 WindowEdgeCertified.upper) := by
  intro l1 h1 l2 h2 h12
  have ht := (time_strictMono j h1 h2 h12).le
  have hp1 : 0 ≤ time j l1 := by linarith [time_lower h1 j]
  have hp2 : 0 < (time j l2)^3 := pow_pos (by linarith [time_lower h2 j]) 3
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp1 ht 3) h1.1
  have hs := mul_lt_mul_of_pos_right h12 hp2
  simpa only [ratio, abs_of_nonneg h1.1, abs_of_nonneg h2.1] using hb.trans_lt hs

theorem ratio_upper_linear {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    ratio j lam ≤ (125 : ℝ) / 8 * lam := by
  have hp : 0 ≤ time j lam := by linarith [time_lower hlam j]
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp (time_upper hlam j) 3) hlam.1
  rw [ratio, abs_of_nonneg hlam.1]
  nlinarith

theorem ratio_positive {lam : ℝ} (hlam : lam ∈ Ioc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    0 < ratio j lam := by
  unfold ratio
  exact mul_pos (abs_pos.mpr hlam.1.ne')
    (pow_pos (by linarith [time_lower ⟨hlam.1.le, hlam.2⟩ j]) 3)

theorem ratio_upper {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEdgeCertified.upper) (j : Fin 12) :
    ratio j lam < (425 : ℝ) / 8 := by
  have h := ratio_upper_linear hlam j
  linarith [upper_tight_bounds.2, hlam.2]

theorem near_edge_ratios {lam : ℝ} (hlam : lam ∈ Icc 3 WindowEdgeCertified.upper) (j : Fin 12) :
    (3 : ℝ) / 8 < ratio j lam ∧ ratio j lam < 425 / 8 := by
  have h0 : lam ∈ Icc 0 WindowEdgeCertified.upper := ⟨by linarith [hlam.1], hlam.2⟩
  have ht := time_lower h0 j
  have hp := pow_lt_pow_left₀ ht (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : 3 ≠ 0)
  have hm := mul_le_mul_of_nonneg_right hlam.1
    (pow_nonneg (by linarith : 0 ≤ time j lam) 3)
  refine ⟨?_, ratio_upper h0 j⟩
  rw [ratio, abs_of_nonneg h0.1]
  nlinarith

/-- Original-population ratio at the actual unique positive endpoint, not a sampled witness. -/
theorem endpoint_ratios (j : Fin 12) : (3 : ℝ) / 8 < ratio j WindowEdgeCertified.upper ∧
    ratio j WindowEdgeCertified.upper < 425 / 8 :=
  near_edge_ratios ⟨upper_tight_bounds.1.le, le_rfl⟩ j

/-- Uniform upper bound throughout the entire nonnegative admitted window. -/
theorem positive_window_ratios {lam : ℝ} (hlam : 0 ≤ lam) (hgate : WindowSample.realizedGate lam)
    (j : Fin 12) : 0 ≤ ratio j lam ∧ ratio j lam < (425 : ℝ) / 8 := by
  have hi : lam ∈ Icc 0 WindowEdgeCertified.upper :=
    ⟨hlam, ((WindowEdgeCertified.upper_spec.2.2 lam).mp hgate).2⟩
  exact ⟨mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [time_lower hi j]) 3), ratio_upper hi j⟩

end
end SbtCosmo.Derivation.WindowEndpointRatio
