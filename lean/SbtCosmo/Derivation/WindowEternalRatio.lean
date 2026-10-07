import SbtCosmo.Derivation.WindowEternalRatioCertified

/-! Actual finite first collapses and coincidence ratios at the infinite limiting edge.
The same original first-time selector is used; its finite-horizon guards are now earned on the enlarged domain. -/
namespace SbtCosmo.Derivation.WindowEternalRatio
noncomputable section
open Set GrowthFirstRecord GrowthScaleReturn WindowFirstRecord

theorem prefix_above_threshold {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    threshold j ≤ nativeGrowth (1 / 1000) lam (5 / 2) := by
  have hanti := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 5 / 2)
  have hparam : lam ≤ (17 : ℝ) / 5 := hlam.2.trans WindowEternalRatioCertified.infinite_upper_tight_bounds.2.le
  have hg := hanti.antitoneOn
    (show lam ∈ Ioi (-(1 / (5 / 2 : ℝ)^3)) by change -(1 / (5 / 2 : ℝ)^3) < lam; linarith [hlam.1])
    (by norm_num) hparam
  linarith [(threshold_bounds j).2, WindowEndpointRatio.prefix_growth_lower]


theorem final_above_threshold {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    threshold j ≤ nativeGrowth (1 / 1000) lam 20 := by
  have hcut : -(1 / (20 : ℝ)^3) < lam := by linarith [hlam.1]
  have hg := (native_strictMonoOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 20) hcut).monotoneOn
    (by norm_num : (5 / 2 : ℝ) ∈ Icc (1 / 1000) 20)
    (by norm_num : (20 : ℝ) ∈ Icc (1 / 1000) 20) (by norm_num : (5 / 2 : ℝ) ≤ 20)
  exact (prefix_above_threshold hlam j).trans hg

theorem time_spec {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    time j lam ∈ Icc (1 / 1000) 20 ∧ nativeGrowth (1 / 1000) lam (time j lam) = threshold j := by
  exact firstTime_spec (by norm_num) (by norm_num) hlam.1
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)


/-- The first-any-patch readout is valid at every finite epoch, including epochs beyond twenty. -/
theorem time_iff_any_collapse {lam a : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper)
    (ha : (1 / 1000 : ℝ) ≤ a) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a) ↔
      time j lam ≤ a := by
  have hAp : 0 < a := (by norm_num : (0 : ℝ) < 1 / 1000).trans_le ha
  have hcutA : -(1 / a^3) < lam :=
    (neg_neg_of_pos (one_div_pos.mpr (pow_pos hAp 3))).trans_le hlam.1
  have hD := (native_positive (by norm_num : (0 : ℝ) < 1 / 1000) ha hcutA a ⟨ha, le_rfl⟩).1.le
  have hfirst := time_spec hlam j
  let B := max 20 a
  have hB : (1 / 1000 : ℝ) ≤ B := by dsimp [B]; exact ha.trans (le_max_right _ _)
  have hBp : 0 < B := (by norm_num : (0 : ℝ) < 1 / 1000).trans_le hB
  have hcutB : -(1 / B^3) < lam :=
    (neg_neg_of_pos (one_div_pos.mpr (pow_pos hBp 3))).trans_le hlam.1
  have htime : time j lam ∈ Icc (1 / 1000) B :=
    ⟨hfirst.1.1, hfirst.1.2.trans (le_max_left _ _)⟩
  have he := (native_strictMonoOn (by norm_num : (0 : ℝ) < 1 / 1000) hB hcutB).le_iff_le
    htime ⟨ha, le_max_right _ _⟩
  rw [hfirst.2] at he
  exact (any_patch_collapse_iff (maximum_spec j).1 hD (maximum_spec j).2.1 (maximum_spec j).2.2).trans he

theorem time_is_first_collapse {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam (time j lam)) ∧
      ∀ a : ℝ, (1 / 1000 : ℝ) ≤ a → a < time j lam →
        ¬ ∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a := by
  refine ⟨(time_iff_any_collapse hlam (time_spec hlam j).1.1 j).mpr le_rfl, ?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hlam ha j).mp hc)

theorem time_lower {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    (1 : ℝ) / 2 < time j lam := by
  have h := firstTime_lower_matter (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num) hlam.1
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)
  change (1 / 1000 : ℝ) * threshold j ≤ time j lam at h
  linarith [(threshold_bounds j).1]

theorem time_upper {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    time j lam ≤ 5 / 2 := by
  apply (firstTime_iff_threshold (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num)
    hlam.1 (by linarith [(threshold_bounds j).1]) (final_above_threshold hlam j)
    (by norm_num : (5 / 2 : ℝ) ∈ Icc (1 / 1000) 20)).mp
  exact prefix_above_threshold hlam j

theorem time_strictMono (j : Fin 12) : StrictMonoOn (time j) (Icc 0 WindowEternalRecords.upper) := by
  intro l1 h1 l2 h2 h12
  exact firstTime_strict_parameter (by norm_num) (by norm_num) h1.1 h12
    (by linarith [(threshold_bounds j).1]) (final_above_threshold h1 j) (final_above_threshold h2 j)

theorem ratio_strictMono (j : Fin 12) : StrictMonoOn (ratio j) (Icc 0 WindowEternalRecords.upper) := by
  intro l1 h1 l2 h2 h12
  have ht := (time_strictMono j h1 h2 h12).le
  have hp1 : 0 ≤ time j l1 := by linarith [time_lower h1 j]
  have hp2 : 0 < (time j l2)^3 := pow_pos (by linarith [time_lower h2 j]) 3
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp1 ht 3) h1.1
  have hs := mul_lt_mul_of_pos_right h12 hp2
  simpa only [ratio, abs_of_nonneg h1.1, abs_of_nonneg h2.1] using hb.trans_lt hs

theorem ratio_upper_linear {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    ratio j lam ≤ (125 : ℝ) / 8 * lam := by
  have hp : 0 ≤ time j lam := by linarith [time_lower hlam j]
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp (time_upper hlam j) 3) hlam.1
  rw [ratio, abs_of_nonneg hlam.1]
  nlinarith

theorem ratio_positive {lam : ℝ} (hlam : lam ∈ Ioc 0 WindowEternalRecords.upper) (j : Fin 12) :
    0 < ratio j lam := by
  unfold ratio
  exact mul_pos (abs_pos.mpr hlam.1.ne')
    (pow_pos (by linarith [time_lower ⟨hlam.1.le, hlam.2⟩ j]) 3)

theorem ratio_upper {lam : ℝ} (hlam : lam ∈ Icc 0 WindowEternalRecords.upper) (j : Fin 12) :
    ratio j lam < (425 : ℝ) / 8 := by
  have h := ratio_upper_linear hlam j
  linarith [WindowEternalRatioCertified.infinite_upper_tight_bounds.2, hlam.2]

theorem near_edge_ratios {lam : ℝ} (hlam : lam ∈ Icc 3 WindowEternalRecords.upper) (j : Fin 12) :
    (3 : ℝ) / 8 < ratio j lam ∧ ratio j lam < 425 / 8 := by
  have h0 : lam ∈ Icc 0 WindowEternalRecords.upper := ⟨by linarith [hlam.1], hlam.2⟩
  have ht := time_lower h0 j
  have hp := pow_lt_pow_left₀ ht (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : 3 ≠ 0)
  have hm := mul_le_mul_of_nonneg_right hlam.1
    (pow_nonneg (by linarith : 0 ≤ time j lam) 3)
  refine ⟨?_, ratio_upper h0 j⟩
  rw [ratio, abs_of_nonneg h0.1]
  nlinarith


/-- Each seed has a finite first patch collapse at this limiting parameter;
the separate aggregate both-tag gate still excludes the endpoint. -/
theorem endpoint_ratios (j : Fin 12) : (3 : ℝ) / 8 < ratio j WindowEternalRecords.upper ∧
    ratio j WindowEternalRecords.upper < 425 / 8 :=
  near_edge_ratios ⟨WindowEternalRatioCertified.infinite_upper_tight_bounds.1.le, le_rfl⟩ j

theorem eternal_window_ratios {lam : ℝ} (hgate : WindowEternalRecords.eternalGate lam) (j : Fin 12) :
    0 ≤ ratio j lam ∧ ratio j lam < (425 : ℝ) / 8 := by
  have hg := (WindowEternalRecords.eternal_gate_iff lam).mp hgate
  have hi : lam ∈ Icc 0 WindowEternalRecords.upper := ⟨hg.1, hg.2.le⟩
  exact ⟨mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [time_lower hi j]) 3), ratio_upper hi j⟩

theorem time_at_zero (j : Fin 12) : time j 0 = threshold j / 1000 := by
  have hi : (0 : ℝ) ∈ Icc 0 WindowEternalRecords.upper := ⟨le_rfl, WindowEternalRecords.upper_spec.1.le⟩
  have ht := time_spec hi j
  rw [GrowthFirstRecordLive.native_matter_at_zero (by norm_num) ht.1.1] at ht
  linarith [ht.2]

theorem ratio_at_zero (j : Fin 12) : ratio j 0 = 0 := by norm_num [WindowFirstRecord.ratio]

/-- The infinite window still does not force a positive order-one coincidence ratio. -/
theorem arbitrarily_small_ratios {eps : ℝ} (heps : 0 < eps) :
    ∃ lam : ℝ, 0 < lam ∧ WindowEternalRecords.eternalGate lam ∧
      ∀ j : Fin 12, 0 < ratio j lam ∧ ratio j lam < eps := by
  let lam := min (WindowEternalRecords.upper / 2) (eps / 32)
  have hp : 0 < lam := lt_min (half_pos WindowEternalRecords.upper_spec.1) (by positivity)
  have hu : lam < WindowEternalRecords.upper := (min_le_left _ _).trans_lt
    (by linarith [WindowEternalRecords.upper_spec.1])
  have hi : lam ∈ Icc 0 WindowEternalRecords.upper := ⟨hp.le, hu.le⟩
  refine ⟨lam, hp, (WindowEternalRecords.eternal_gate_iff lam).mpr ⟨hp.le, hu⟩, ?_⟩
  intro j
  have hb := ratio_upper_linear hi j
  have he : lam ≤ eps / 32 := min_le_right _ _
  exact ⟨ratio_positive ⟨hp, hu.le⟩ j, by linarith⟩

end
end SbtCosmo.Derivation.WindowEternalRatio
