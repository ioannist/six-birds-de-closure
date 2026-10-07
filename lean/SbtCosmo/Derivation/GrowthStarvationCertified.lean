import SbtCosmo.Derivation.WindowStarvationData
import SbtCosmo.Derivation.GrowthQuadratureSharp
import SbtCosmo.Derivation.GrowthInfiniteTail
import SbtCosmo.Derivation.GrowthPopulation

/-! Exact finite native quadrature and a derived infinite-time tail give a modest global cutoff. -/
namespace SbtCosmo.Derivation.GrowthStarvationCertified
noncomputable section
open Set GrowthQuadrature GrowthScaleReturn GrowthInfinite GrowthInfiniteTail GrowthPopulation

theorem integral_upper : integral 32 (1 / 1000) 4 ≤ (341 : ℝ) / 10000 := by
  have hcell : ∀ i < 64,
      0 < (WindowStarvationData.grid i : ℝ) ∧
      (WindowStarvationData.grid i : ℝ) ≤ WindowStarvationData.grid (i+1) ∧
      0 ≤ (WindowStarvationData.upper i : ℝ) ∧
      ((2 * 32 * (WindowStarvationData.grid (i+1) : ℝ)^3 ≤ 1 ∧
        (WindowStarvationData.grid (i+1) : ℝ)^3 ≤ (WindowStarvationData.upper i : ℝ)^2 *
          (1 + 32 * (WindowStarvationData.grid (i+1) : ℝ)^3)^3) ∨
      (1 ≤ 2 * 32 * (WindowStarvationData.grid i : ℝ)^3 ∧
        (WindowStarvationData.grid i : ℝ)^3 ≤ (WindowStarvationData.upper i : ℝ)^2 *
          (1 + 32 * (WindowStarvationData.grid i : ℝ)^3)^3) ∨
      4 ≤ 27 * 32 * (WindowStarvationData.upper i : ℝ)^2) := by
    intro i hi
    exact_mod_cast WindowStarvationData.upper_cells ⟨i, hi⟩
  have hb := GrowthQuadratureSharp.integral_grid_bounds (n := 64)
    (a := fun i => (WindowStarvationData.grid i : ℝ)) (lo := fun _ => 0)
    (hi := fun i => (WindowStarvationData.upper i : ℝ))
    (by norm_num : (0 : ℝ) ≤ 32) (by
      intro i hi
      obtain ⟨ha, hab, hhi, hcert⟩ := hcell i hi
      refine ⟨ha, hab, ?_⟩
      intro x hx
      exact ⟨density_nonnegative, GrowthQuadratureSharp.density_cell_upper (by norm_num) ha.le hx hhi hcert⟩)
  have hs : (∑ i ∈ Finset.range 64,
      ((WindowStarvationData.grid (i+1) : ℝ) - WindowStarvationData.grid i) *
        (WindowStarvationData.upper i : ℝ)) ≤ (341 : ℝ) / 10000 := by
    have hq : ((∑ i ∈ Finset.range 64, (WindowStarvationData.grid (i+1) - WindowStarvationData.grid i) *
          WindowStarvationData.upper i : ℚ) : ℝ) ≤ ((341 / 10000 : ℚ) : ℝ) := by
      exact_mod_cast WindowStarvationData.upper_sum
    push_cast at hq
    exact hq
  have h0 : (WindowStarvationData.grid 0 : ℝ) = 1 / 1000 := by
    rw [WindowStarvationData.grid_endpoints.1]
    norm_num
  have hn : (WindowStarvationData.grid 64 : ℝ) = 4 := by
    exact_mod_cast WindowStarvationData.grid_endpoints.2
  dsimp only at hb
  rw [h0, hn] at hb
  exact hb.2.trans hs

theorem finite_growth_upper : nativeGrowth (1 / 1000) 32 4 < (9651 : ℝ) / 20 := by
  rw [native_growth_quadrature (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 32)]
  have hr : nativeRoot 32 4 ≤ (566 : ℝ) / 100 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hr0 : (30000 : ℝ) ≤ nativeRoot 32 (1 / 1000) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hinv : (nativeRoot 32 (1 / 1000))⁻¹ ≤ (1 : ℝ) / 30000 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 30000) hr0
  have hα : 0 ≤ nativePrefactor 32 (1 / 1000) := by norm_num [nativePrefactor]
  have hb := add_le_add hinv (mul_le_mul_of_nonneg_left integral_upper hα)
  have hm := (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hr (by norm_num [nativePrefactor] :
      (0 : ℝ) ≤ 1 / 30000 + nativePrefactor 32 (1 / 1000) * (341 / 10000)))
  exact hm.trans_lt (by norm_num [nativePrefactor])


theorem limiting_growth_upper : nativeInfinite (1 / 1000) 32 < (485 : ℝ) := by
  have ht := native_tail_bound (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (0 : ℝ) < 32) (by norm_num : (1 / 1000 : ℝ) ≤ 4)
  norm_num at ht
  linarith [finite_growth_upper]

theorem global_growth_upper {lam a : ℝ} (hlam : (32 : ℝ) ≤ lam)
    (ha : (1 / 1000 : ℝ) ≤ a) : nativeGrowth (1 / 1000) lam a < 485 := by
  have hp : 0 < lam := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hlam
  have hm := (native_infinite_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)).antitoneOn
    (by norm_num : (32 : ℝ) ∈ Ioi 0) hp hlam
  exact (native_lt_infinite (by norm_num) hp ha).trans_le hm |>.trans limiting_growth_upper

/-- A sufficient all-time no-collapse return, with the amplitude margin explicit. -/
theorem patch_never_collapses {lam amp delta : ℝ} (hlam : (32 : ℝ) ≤ lam)
    (hp : 0 ≤ amp) (hmargin : 485 * amp < delta) :
    ¬ ∃ a : ℝ, (1 / 1000 : ℝ) ≤ a ∧ delta ≤ amp * nativeGrowth (1 / 1000) lam a := by
  rintro ⟨a, ha, hc⟩
  have hb := mul_le_mul_of_nonneg_left (global_growth_upper hlam ha).le hp
  nlinarith

/-- Any tag history requiring collapse is empty under the same amplitude margins. -/
theorem no_native_record {ι : Type*} {amp : ι → ℝ} {tag : ι → Bool} {lam A delta : ℝ}
    (hlam : (32 : ℝ) ≤ lam) (hp : ∀ i, 0 ≤ amp i) (hmargin : ∀ i, 485 * amp i < delta) :
    ¬ nativeRecord amp tag (1 / 1000) A delta lam := by
  rintro ⟨i, j, ⟨a, ha, hc⟩, _, _⟩
  exact patch_never_collapses hlam (hp i) (hmargin i) ⟨a, ha.1, hc⟩

end
end SbtCosmo.Derivation.GrowthStarvationCertified
