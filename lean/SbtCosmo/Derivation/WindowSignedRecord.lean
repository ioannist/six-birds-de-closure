import SbtCosmo.Derivation.GrowthFirstRecordLive
import SbtCosmo.Derivation.WindowEndpointRatio

/-! Actual first records and matter ratios throughout the original full signed window. -/
namespace SbtCosmo.Derivation.WindowSignedRecord
noncomputable section
open Set GrowthScaleReturn WindowFirstRecord

def time (j : Fin 12) (lam : ℝ) : ℝ :=
  GrowthFirstRecordLive.firstTime (1 / 1000) 20 (threshold j) lam

def ratio (j : Fin 12) (lam : ℝ) : ℝ := |lam| * (time j lam)^3

theorem gate_iff_window (lam : ℝ) : WindowSample.realizedGate lam ↔
    lam ∈ Ioc (-(1 / 8000 : ℝ)) WindowEdgeCertified.upper := WindowEdgeCertified.upper_spec.2.2 lam

theorem gate_cutoff {lam : ℝ} (hgate : WindowSample.realizedGate lam) : -(1 / (20 : ℝ)^3) < lam := by
  convert ((gate_iff_window lam).mp hgate).1 using 1
  norm_num

theorem final_above_threshold {lam : ℝ} (hgate : WindowSample.realizedGate lam) (j : Fin 12) :
    threshold j ≤ nativeGrowth (1 / 1000) lam 20 := by
  have hg := (WindowSample.realized_gate_iff_threshold lam).mp hgate
  linarith [(threshold_bounds j).2, WindowEdgeCertified.sampled_threshold_tight_bounds.1, hg.2]

theorem time_spec {lam : ℝ} (hgate : WindowSample.realizedGate lam) (j : Fin 12) :
    time j lam ∈ Icc (1 / 1000) 20 ∧ nativeGrowth (1 / 1000) lam (time j lam) = threshold j := by
  exact GrowthFirstRecordLive.firstTime_spec (by norm_num) (by norm_num) (gate_cutoff hgate)
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hgate j)

theorem time_positive {lam : ℝ} (hgate : WindowSample.realizedGate lam) (j : Fin 12) : 0 < time j lam := by
  linarith [(time_spec hgate j).1.1]

/-- Both constructions select the same actual root on the nonnegative window. -/
theorem time_eq_nonnegative {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hlam : 0 ≤ lam)
    (j : Fin 12) : time j lam = WindowFirstRecord.time j lam := by
  exact GrowthFirstRecordLive.firstTime_eq_nonnegative (by norm_num) (by norm_num) hlam
    (by linarith [(threshold_bounds j).1]) (final_above_threshold hgate j)

theorem ratio_eq_nonnegative {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hlam : 0 ≤ lam)
    (j : Fin 12) : ratio j lam = WindowFirstRecord.ratio j lam := by
  unfold ratio
  rw [time_eq_nonnegative hgate hlam j]
  rfl

theorem time_iff_any_collapse {lam a : ℝ} (hgate : WindowSample.realizedGate lam)
    (ha : a ∈ Icc (1 / 1000) 20) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a) ↔ time j lam ≤ a := by
  have hD := (native_positive (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num) (gate_cutoff hgate) a ha).1.le
  exact (GrowthFirstRecord.any_patch_collapse_iff (maximum_spec j).1 hD (maximum_spec j).2.1
    (maximum_spec j).2.2).trans (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num) (by norm_num)
      (gate_cutoff hgate) (show 1 < threshold j by linarith [(threshold_bounds j).1])
      (final_above_threshold hgate j) ha)

theorem time_is_first_collapse {lam : ℝ} (hgate : WindowSample.realizedGate lam) (j : Fin 12) :
    (∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam (time j lam)) ∧
      ∀ a ∈ Icc (1 / 1000) 20, a < time j lam →
        ¬ ∃ i, WindowSample.delta ≤ WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a := by
  refine ⟨(time_iff_any_collapse hgate (time_spec hgate j).1 j).mpr le_rfl, ?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hgate ha j).mp hc)

theorem time_at_zero (j : Fin 12) : time j 0 = threshold j / 1000 := by
  have hg : WindowSample.realizedGate 0 := WindowFirstRecord.gate_on_interval (by norm_num)
  calc
    time j 0 = (1 / 1000 : ℝ) * threshold j :=
      GrowthFirstRecordLive.firstTime_at_zero (by norm_num) (by norm_num)
        (by linarith [(threshold_bounds j).1]) (final_above_threshold hg j)
    _ = threshold j / 1000 := by ring

theorem time_nonpositive_upper {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hlam : lam ≤ 0)
    (j : Fin 12) : time j lam ≤ threshold j / 1000 := by
  have h := GrowthFirstRecordLive.firstTime_nonpositive_upper (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num) (gate_cutoff hgate) hlam (by linarith [(threshold_bounds j).1]) (final_above_threshold hgate j)
  change time j lam ≤ (1 / 1000 : ℝ) * threshold j at h
  convert h using 1
  ring

theorem time_nonpositive_small {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hlam : lam ≤ 0)
    (j : Fin 12) : time j lam < (897 : ℝ) / 1000 := by
  have h := time_nonpositive_upper hgate hlam j
  linarith [(threshold_bounds j).2]

theorem time_strictMono (j : Fin 12) : StrictMonoOn (time j)
    (Ioc (-(1 / 8000 : ℝ)) WindowEdgeCertified.upper) := by
  intro l1 h1 l2 h2 h12
  have hg1 := (gate_iff_window l1).mpr h1
  have hg2 := (gate_iff_window l2).mpr h2
  exact GrowthFirstRecordLive.firstTime_strict_parameter (by norm_num) (by norm_num)
    (gate_cutoff hg1) h12 (by linarith [(threshold_bounds j).1])
    (final_above_threshold hg1 j) (final_above_threshold hg2 j)

theorem ratio_density_readout (lam : ℝ) (j : Fin 12) :
    ratio j lam = |lam| / ((time j lam)^3)⁻¹ := by simp only [ratio, div_inv_eq_mul]

theorem ratio_positive {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hne : lam ≠ 0)
    (j : Fin 12) : 0 < ratio j lam :=
  mul_pos (abs_pos.mpr hne) (pow_pos (time_positive hgate j) 3)

theorem ratio_zero (j : Fin 12) : ratio j 0 = 0 := by simp [ratio]

theorem ratio_nonpositive_upper {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hlam : lam ≤ 0)
    (j : Fin 12) : ratio j lam < (1 : ℝ) / 8000 := by
  have ht : time j lam ≤ 1 := by linarith [time_nonpositive_small hgate hlam j]
  have hc := pow_le_pow_left₀ (time_positive hgate j).le ht 3
  have hm := mul_le_mul_of_nonneg_left hc (abs_nonneg lam)
  have ha : |lam| < (1 : ℝ) / 8000 := by
    rw [abs_of_nonpos hlam]
    linarith [((gate_iff_window lam).mp hgate).1]
  have hr : ratio j lam ≤ |lam| := by simpa only [ratio, one_pow, mul_one] using hm
  exact hr.trans_lt ha

theorem negative_ratios {lam : ℝ} (hgate : WindowSample.realizedGate lam) (hlam : lam < 0)
    (j : Fin 12) : 0 < ratio j lam ∧ ratio j lam < (1 : ℝ) / 8000 :=
  ⟨ratio_positive hgate hlam.ne j, ratio_nonpositive_upper hgate hlam.le j⟩

/-- Full signed-window upper bound for the actual original first-record readout. -/
theorem full_window_ratios {lam : ℝ} (hgate : WindowSample.realizedGate lam) (j : Fin 12) :
    0 ≤ ratio j lam ∧ ratio j lam < (425 : ℝ) / 8 := by
  by_cases h : 0 ≤ lam
  · rw [ratio_eq_nonnegative hgate h j]
    exact WindowEndpointRatio.positive_window_ratios h hgate j
  · have hn : lam < 0 := lt_of_not_ge h
    exact ⟨(ratio_positive hgate hn.ne j).le, (ratio_nonpositive_upper hgate hn.le j).trans (by norm_num)⟩

theorem endpoint_ratios (j : Fin 12) : (3 : ℝ) / 8 < ratio j WindowEdgeCertified.upper ∧
    ratio j WindowEdgeCertified.upper < 425 / 8 := by
  have hg : WindowSample.realizedGate WindowEdgeCertified.upper :=
    (gate_iff_window _).mpr ⟨by linarith [WindowEdgeCertified.upper_spec.1], le_rfl⟩
  rw [ratio_eq_nonnegative hg WindowEdgeCertified.upper_spec.1.le j]
  exact WindowEndpointRatio.endpoint_ratios j

theorem ratios_arbitrarily_small {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ WindowSample.realizedGate lam ∧
      ∀ j : Fin 12, 0 < ratio j lam ∧ ratio j lam < epsilon := by
  obtain ⟨lam, hl, h1, hg, hr⟩ := WindowFirstRecord.ratios_arbitrarily_small he
  refine ⟨lam, hl, h1, hg, ?_⟩
  intro j
  rw [ratio_eq_nonnegative hg hl.le j]
  exact hr j

end
end SbtCosmo.Derivation.WindowSignedRecord
