import SbtCosmo.Derivation.GrowthFirstRecord
import SbtCosmo.Derivation.WindowEdgeCertified
import SbtCosmo.Derivation.WindowFirstRecordData

/-! The actual first collapse of any original patch and its matter ratio. -/
namespace SbtCosmo.Derivation.WindowFirstRecord
noncomputable section
open Set GrowthFirstRecord GrowthScaleReturn GrowthQuadrature

/-- Largest amplitude, irrespective of its tag. -/
def maximum (j : Fin 12) : ℝ := max (WindowSample.maximumFalse j) (WindowSample.maximumTrue j)
def threshold (j : Fin 12) : ℝ := WindowSample.delta / maximum j

theorem maximum_spec (j : Fin 12) : 0 < maximum j ∧
    (∀ i, WindowSample.amplitude j i ≤ maximum j) ∧
      ∃ i, WindowSample.amplitude j i = maximum j := by
  obtain ⟨_, h0, _, hm0, hm1⟩ := WindowSample.sampled_maxima j
  refine ⟨h0.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro i
    cases hi : WindowSampleData.tag j i
    · exact (hm0.bounds i hi).trans (le_max_left _ _)
    · exact (hm1.bounds i hi).trans (le_max_right _ _)
  · by_cases h : WindowSample.maximumFalse j ≤ WindowSample.maximumTrue j
    · obtain ⟨i, _, he⟩ := hm1.attained
      exact ⟨i, he.trans (max_eq_right h).symm⟩
    · obtain ⟨i, _, he⟩ := hm0.attained
      exact ⟨i, he.trans (max_eq_left (le_of_not_ge h)).symm⟩

theorem threshold_bounds (j : Fin 12) : (500 : ℝ) < threshold j ∧ threshold j < 897 := by
  have h := WindowFirstRecordData.first_threshold_bounds j
  have he : threshold j = (WindowFirstRecordData.firstThresholdRat j : ℝ) := by
    simp only [threshold, maximum, WindowSample.delta, WindowSample.maximumFalse,
      WindowSample.maximumTrue, WindowFirstRecordData.firstThresholdRat, Rat.cast_div, Rat.cast_max]
  rw [he]
  exact_mod_cast h

theorem final_above_threshold {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) :
    threshold j ≤ nativeGrowth (1 / 1000) lam 20 := by
  have hanti := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20)
  have hg := hanti.antitoneOn (show lam ∈ Ioi (-(1 / (20 : ℝ)^3)) by
    change -(1 / (20 : ℝ)^3) < lam; linarith [hlam.1]) (by norm_num) hlam.2
  linarith [(threshold_bounds j).2, WindowEdgeCertified.native_growth_at_three_lower]

def time (j : Fin 12) (lam : ℝ) : ℝ := firstTime (1 / 1000) 20 (threshold j) lam

theorem time_spec {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) :
    time j lam ∈ Icc (1 / 1000) 20 ∧ nativeGrowth (1 / 1000) lam (time j lam) = threshold j := by
  exact firstTime_spec (by norm_num) (by norm_num) hlam.1
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)

/-- First collapse of ANY patch, matching the original runtime readout. -/
theorem time_iff_any_collapse {lam a : ℝ} (hlam : lam ∈ Icc 0 3)
    (ha : a ∈ Icc (1 / 1000) 20) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a) ↔
      time j lam ≤ a := by
  have hD := (native_positive (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num)
    (show -(1 / (20 : ℝ)^3) < lam by linarith [hlam.1]) a ha).1.le
  exact (any_patch_collapse_iff (maximum_spec j).1 hD (maximum_spec j).2.1
    (maximum_spec j).2.2).trans (firstTime_iff_threshold (by norm_num) (by norm_num)
      hlam.1 (show 1 < threshold j by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j) ha)

theorem time_is_first_collapse {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam (time j lam)) ∧
      ∀ a ∈ Icc (1 / 1000) 20, a < time j lam →
        ¬ ∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a := by
  refine ⟨(time_iff_any_collapse hlam (time_spec hlam j).1 j).mpr le_rfl, ?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hlam ha j).mp hc)

theorem time_lower {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) : (1 : ℝ) / 2 < time j lam := by
  have h := firstTime_lower_matter (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num) hlam.1
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)
  change (1 / 1000 : ℝ) * threshold j ≤ time j lam at h
  linarith [(threshold_bounds j).1]

theorem time_strictMono (j : Fin 12) : StrictMonoOn (time j) (Icc 0 3) := by
  intro l1 h1 l2 h2 h12
  exact firstTime_strict_parameter (by norm_num) (by norm_num) h1.1 h12
    (by linarith [(threshold_bounds j).1]) (final_above_threshold h1 j) (final_above_threshold h2 j)

/-- Exact lambda-to-matter ratio, with matter density a^(-3). -/
def ratio (j : Fin 12) (lam : ℝ) : ℝ := |lam| * (time j lam)^3

theorem ratio_density_readout (lam : ℝ) (j : Fin 12) :
    ratio j lam = |lam| / ((time j lam)^3)⁻¹ := by
  simp only [ratio, div_inv_eq_mul]

theorem ratio_positive {lam : ℝ} (hlam : lam ∈ Ioc 0 3) (j : Fin 12) : 0 < ratio j lam := by
  unfold ratio
  exact mul_pos (abs_pos.mpr hlam.1.ne') (pow_pos (by linarith [time_lower ⟨hlam.1.le, hlam.2⟩ j]) 3)

theorem ratio_upper {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) :
    ratio j lam ≤ 8000 * lam := by
  have ht := time_spec hlam j
  have hp : (time j lam)^3 ≤ (20 : ℝ)^3 := pow_le_pow_left₀ (by linarith [ht.1.1]) ht.1.2 3
  have hm := mul_le_mul_of_nonneg_left hp hlam.1
  simpa only [ratio, abs_of_nonneg hlam.1] using (by nlinarith : lam * (time j lam)^3 ≤ 8000 * lam)

theorem ratio_zero (j : Fin 12) : ratio j 0 = 0 := by simp [ratio]

theorem gate_on_interval {lam : ℝ} (hlam : lam ∈ Icc 0 3) : WindowSample.realizedGate lam := by
  rw [WindowEdgeCertified.upper_spec.2.2]
  exact ⟨by linarith [hlam.1], hlam.2.trans WindowEdgeCertified.upper_certified_bounds.1.le⟩

/-- No positive pinching bound: all twelve ratios can be arbitrarily small simultaneously. -/
theorem ratios_arbitrarily_small {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ WindowSample.realizedGate lam ∧
      ∀ j : Fin 12, 0 < ratio j lam ∧ ratio j lam < epsilon := by
  let lam : ℝ := min 1 (epsilon / 16000)
  have hl : 0 < lam := lt_min (by norm_num) (div_pos he (by norm_num))
  have h1 : lam ≤ 1 := min_le_left _ _
  have h3 : lam ≤ 3 := h1.trans (by norm_num)
  have hε : lam ≤ epsilon / 16000 := min_le_right _ _
  refine ⟨lam, hl, h1, gate_on_interval ⟨hl.le, h3⟩, ?_⟩
  intro j
  refine ⟨ratio_positive ⟨hl, h3⟩ j, ?_⟩
  have hr := ratio_upper ⟨hl.le, h3⟩ j
  linarith

theorem integral_lower_at_three : (204 : ℝ) / 1000 ≤ integral 3 (1 / 1000) 2 := by
  have hcell : ∀ i < 384,
      0 < (WindowFirstRecordData.grid i : ℝ) ∧
      (WindowFirstRecordData.grid i : ℝ) ≤ WindowFirstRecordData.grid (i + 1) ∧
      0 ≤ (WindowFirstRecordData.lower i : ℝ) ∧
      (WindowFirstRecordData.lower i : ℝ)^2 * (1 + 3 * (WindowFirstRecordData.grid (i + 1) : ℝ)^3)^3 ≤
        (WindowFirstRecordData.grid i : ℝ)^3 ∧
      (WindowFirstRecordData.grid (i + 1) : ℝ)^3 ≤ (1 + 3 * (WindowFirstRecordData.grid i : ℝ)^3)^3 := by
    intro i hi
    exact_mod_cast WindowFirstRecordData.lower_cells ⟨i, hi⟩
  have hb := integral_grid_bounds (n := 384) (a := fun i => (WindowFirstRecordData.grid i : ℝ))
    (lo := fun i => (WindowFirstRecordData.lower i : ℝ)) (hi := fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 3) (by
      intro i hi
      obtain ⟨ha, hab, hlo, hbelow, habove⟩ := hcell i hi
      exact ⟨ha, hab, hlo, by norm_num, hbelow, by simpa using habove⟩)
  have hs : (204 : ℝ) / 1000 ≤
      ∑ i ∈ Finset.range 384, ((WindowFirstRecordData.grid (i + 1) : ℝ) - WindowFirstRecordData.grid i) *
        (WindowFirstRecordData.lower i : ℝ) := by
    have hq : ((204 / 1000 : ℚ) : ℝ) ≤
        ((∑ i ∈ Finset.range 384, (WindowFirstRecordData.grid (i + 1) - WindowFirstRecordData.grid i) *
          WindowFirstRecordData.lower i : ℚ) : ℝ) := by exact_mod_cast WindowFirstRecordData.lower_sum
    push_cast at hq
    exact hq
  have h0 : (WindowFirstRecordData.grid 0 : ℝ) = 1 / 1000 := by
    rw [WindowFirstRecordData.grid_endpoints.1]
    norm_num
  have hn : (WindowFirstRecordData.grid 384 : ℝ) = 2 := by
    exact_mod_cast WindowFirstRecordData.grid_endpoints.2
  dsimp only at hb
  rw [h0, hn] at hb
  exact hs.trans hb.1

theorem native_growth_at_three_lower : (901 : ℝ) < nativeGrowth (1 / 1000) 3 2 := by
  rw [native_growth_quadrature (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]
  have hr : (1767 : ℝ) / 1000 ≤ nativeRoot 3 2 := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα : (2500 : ℝ) ≤ nativePrefactor 3 (1 / 1000) := by norm_num [nativePrefactor]
  have hp := mul_le_mul hα integral_lower_at_three (by norm_num : (0 : ℝ) ≤ 204 / 1000)
    (by norm_num [nativePrefactor] : 0 ≤ nativePrefactor 3 (1 / 1000))
  have hb : (2500 : ℝ) * (204 / 1000) ≤ (nativeRoot 3 (1 / 1000))⁻¹ +
      nativePrefactor 3 (1 / 1000) * integral 3 (1 / 1000) 2 :=
    hp.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by norm_num : (0 : ℝ) ≤ 2500 * (204 / 1000))
    (Real.sqrt_nonneg _)
  exact (by norm_num : (901 : ℝ) < (1767 / 1000) * (2500 * (204 / 1000))).trans_le hm

theorem time_at_three_upper (j : Fin 12) : time j 3 ≤ 2 := by
  apply (firstTime_iff_threshold (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num)
    (by norm_num) (by linarith [(threshold_bounds j).1])
    (final_above_threshold (by norm_num) j) (by norm_num : (2 : ℝ) ∈ Icc (1 / 1000) 20)).mp
  linarith [(threshold_bounds j).2, native_growth_at_three_lower]

/-- Every original first-record ratio is bounded at an interior near-edge parameter. -/
theorem ratios_at_three (j : Fin 12) : (3 : ℝ) / 8 < ratio j 3 ∧ ratio j 3 ≤ 24 := by
  have hl := time_lower (by norm_num : (3 : ℝ) ∈ Icc 0 3) j
  have hu := time_at_three_upper j
  have hp : 0 ≤ time j 3 := by linarith
  have hl3 := pow_lt_pow_left₀ hl (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : 3 ≠ 0)
  have hu3 := pow_le_pow_left₀ hp hu 3
  norm_num [ratio]
  constructor <;> nlinarith

theorem three_near_upper : (3 : ℝ) / 4 < 3 / WindowEdgeCertified.upper ∧
    3 / WindowEdgeCertified.upper < 1 := by
  have hu := WindowEdgeCertified.upper_certified_bounds
  constructor
  · apply (lt_div_iff₀ (by linarith : 0 < WindowEdgeCertified.upper)).mpr
    linarith [hu.2]
  · apply (div_lt_iff₀ (by linarith : 0 < WindowEdgeCertified.upper)).mpr
    linarith [hu.1]

theorem ratio_strictMono (j : Fin 12) : StrictMonoOn (ratio j) (Icc 0 3) := by
  intro l1 h1 l2 h2 h12
  have ht := (time_strictMono j h1 h2 h12).le
  have hp1 : 0 ≤ time j l1 := by linarith [time_lower h1 j]
  have hp2 : 0 < (time j l2)^3 := pow_pos (by linarith [time_lower h2 j]) 3
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp1 ht 3) h1.1
  have hs := mul_lt_mul_of_pos_right h12 hp2
  simpa only [ratio, abs_of_nonneg h1.1, abs_of_nonneg h2.1] using hb.trans_lt hs

theorem time_upper_two {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) : time j lam ≤ 2 := by
  exact ((time_strictMono j).monotoneOn hlam (by norm_num) hlam.2).trans (time_at_three_upper j)

theorem ratio_upper_sharp {lam : ℝ} (hlam : lam ∈ Icc 0 3) (j : Fin 12) :
    ratio j lam ≤ 8 * lam := by
  have hp : 0 ≤ time j lam := by linarith [time_lower hlam j]
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp (time_upper_two hlam j) 3) hlam.1
  simpa only [ratio, abs_of_nonneg hlam.1] using (by nlinarith : lam * (time j lam)^3 ≤ 8 * lam)

theorem ratios_one_to_three {lam : ℝ} (hlam : lam ∈ Icc 1 3) (j : Fin 12) :
    (1 : ℝ) / 8 < ratio j lam ∧ ratio j lam ≤ 24 := by
  have h0 : lam ∈ Icc 0 3 := ⟨by linarith [hlam.1], hlam.2⟩
  have ht := time_lower h0 j
  have hp := pow_lt_pow_left₀ ht (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : 3 ≠ 0)
  have hm := mul_le_mul_of_nonneg_right hlam.1
    (pow_nonneg (by linarith : 0 ≤ time j lam) 3)
  have hu := ratio_upper_sharp h0 j
  rw [ratio, abs_of_nonneg h0.1] at hu ⊢
  constructor <;> nlinarith [hlam.2]

end
end SbtCosmo.Derivation.WindowFirstRecord
