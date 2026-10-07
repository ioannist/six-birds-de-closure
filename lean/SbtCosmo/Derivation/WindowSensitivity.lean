import SbtCosmo.Derivation.GrowthPopulationSensitivity
import SbtCosmo.Derivation.WindowSample

/-! Sensitivity returns to the original realization with coupled exact amplitude rescaling. -/
namespace SbtCosmo.Derivation.WindowSensitivity
noncomputable section
open Set GrowthEndpointSensitivity GrowthLimit GrowthScaleReturn
attribute [local instance] Classical.propDecidable

theorem original_maximum_false (j : Fin 12) :
    GrowthPopulationSensitivity.tagMaximumValue (WindowSample.amplitude j) (WindowSampleData.tag j) false =
      WindowSample.maximumFalse j :=
  GrowthPopulationSensitivity.tagMaximumValue_eq_of_maximum (WindowSample.sampled_maxima j).2.2.2.1

theorem original_maximum_true (j : Fin 12) :
    GrowthPopulationSensitivity.tagMaximumValue (WindowSample.amplitude j) (WindowSampleData.tag j) true =
      WindowSample.maximumTrue j :=
  GrowthPopulationSensitivity.tagMaximumValue_eq_of_maximum (WindowSample.sampled_maxima j).2.2.2.2

theorem original_aggregate_threshold :
    GrowthPopulationSensitivity.aggregateThreshold WindowSample.amplitude WindowSampleData.tag WindowSample.delta 10 =
      WindowSample.aggregateThreshold := by
  have hf : GrowthPopulationSensitivity.seedThresholds WindowSample.amplitude WindowSampleData.tag WindowSample.delta =
      WindowSample.seedThreshold := by
    funext j
    simp only [GrowthPopulationSensitivity.seedThresholds, original_maximum_false,
      original_maximum_true, WindowSample.seedThreshold_eq]
  rw [GrowthPopulationSensitivity.aggregateThreshold, hf]
  apply GrowthRankSensitivity.rankThreshold_eq_of_certificate (by norm_num) (by norm_num)
  · rw [WindowSample.sampled_rank_counts.1]
    norm_num
  · exact WindowSample.sampled_rank_counts.2.ge

theorem original_delta_positive : 0 < WindowSample.delta := by
  rw [WindowSample.sampled_delta_exact]
  norm_num

def scaledAmplitude (s : ℝ) (j : Fin 12) (i : Fin 64) : ℝ := s * WindowSample.amplitude j i
def scaledThreshold (d s : ℝ) : ℝ := d / (WindowSample.delta * s) * WindowSample.aggregateThreshold
def scaledEndpoint (d s : ℝ) : ℝ := endpoint (1 / 1000) (Real.log 20000) (scaledThreshold d s)

/-- Exact real rescaling of the same amplitudes/tags, with no new random population. -/
theorem scaled_aggregate_threshold {d s : ℝ} (hd : 0 < d) (hs : 0 < s) :
    GrowthPopulationSensitivity.aggregateThreshold (scaledAmplitude s) WindowSampleData.tag d 10 =
      scaledThreshold d s := by
  have hc := div_pos hd original_delta_positive
  have hδ := GrowthPopulationSensitivity.aggregateThreshold_delta_mul_pos WindowSample.amplitude
    WindowSampleData.tag WindowSample.delta (by norm_num : 0 < 10) (by norm_num) hc
  have he : d / WindowSample.delta * WindowSample.delta = d :=
    div_mul_cancel₀ d original_delta_positive.ne'
  rw [he] at hδ
  change GrowthPopulationSensitivity.aggregateThreshold (fun j i => s * WindowSample.amplitude j i)
    WindowSampleData.tag d 10 = scaledThreshold d s
  rw [GrowthPopulationSensitivity.aggregateThreshold_amplitude_mul_pos _ _ _
    (by norm_num : 0 < 10) (by norm_num) hs, hδ, original_aggregate_threshold]
  unfold scaledThreshold
  field_simp

theorem scaled_endpoint_continuousAt {p : ℝ × ℝ} (hs : 0 < p.2)
    (hT : scaledThreshold p.1 p.2 ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    ContinuousAt (fun q : ℝ × ℝ => scaledEndpoint q.1 q.2) p := by
  have hL : 0 < Real.log (20000 : ℝ) := Real.log_pos (by norm_num)
  have hTlog : scaledThreshold p.1 p.2 ∈ Ioo (freeGrowth (Real.log 20000)) (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT
  have hc : ContinuousAt (fun q : ℝ × ℝ => scaledThreshold q.1 q.2) p := by
    exact (continuousAt_fst.div (continuousAt_const.mul continuousAt_snd)
      (mul_ne_zero original_delta_positive.ne' hs.ne')).mul continuousAt_const
  exact ContinuousAt.comp (f := fun q : ℝ × ℝ => scaledThreshold q.1 q.2) (x := p)
    (endpoint_continuousAt (by norm_num : (0 : ℝ) < 1 / 1000) hL hTlog) hc

/-- The sensitivity function is the actual record-window boundary for each admissible rescaling. -/
theorem scaled_endpoint_native_window {d s : ℝ} (hd : 0 < d) (hs : 0 < s)
    (hT : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    0 < scaledEndpoint d s ∧ nativeGrowth (1 / 1000) (scaledEndpoint d s) 20 = scaledThreshold d s ∧
      ∀ lam : ℝ, GrowthPopulation.nativeAggregate (scaledAmplitude s) WindowSampleData.tag
        (1 / 1000) 20 d 10 lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ scaledEndpoint d s := by
  have hp : ∀ j i, 0 ≤ scaledAmplitude s j i := fun j i =>
    mul_nonneg hs.le ((WindowSample.sampled_maxima j).1 i)
  have hpatch : ∀ (j : Fin 12) (b : Bool), ∃ i, WindowSampleData.tag j i = b ∧
      0 < scaledAmplitude s j i := by
    intro j b
    cases b with
    | false =>
      obtain ⟨i, hi, he⟩ := (WindowSample.sampled_maxima j).2.2.2.1.attained
      exact ⟨i, hi, mul_pos hs (he ▸ (WindowSample.sampled_maxima j).2.1)⟩
    | true =>
      obtain ⟨i, hi, he⟩ := (WindowSample.sampled_maxima j).2.2.2.2.attained
      exact ⟨i, hi, mul_pos hs (he ▸ (WindowSample.sampled_maxima j).2.2.1)⟩
  have hratio : (20 : ℝ) / (1 / 1000) = 20000 := by norm_num
  have hthreshold := scaled_aggregate_threshold hd hs
  have ht : GrowthPopulationSensitivity.aggregateThreshold (scaledAmplitude s) WindowSampleData.tag d 10 ∈
      Ioo (freeGrowth (Real.log ((20 : ℝ) / (1 / 1000)))) ((20 : ℝ) / (1 / 1000)) := by
    simpa only [hthreshold, hratio] using hT
  have hw := GrowthPopulationSensitivity.populationEndpoint_native_window
    (scaledAmplitude s) WindowSampleData.tag (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20) (by norm_num : 0 < 10) (by norm_num) hp hpatch ht
  have hcut : -(1 / (20 : ℝ)^3) = -(1 / 8000 : ℝ) := by norm_num
  simpa only [GrowthPopulationSensitivity.populationEndpoint, hthreshold, hratio, hcut,
    scaledEndpoint] using hw

theorem original_aggregate_bounds : (900 : ℝ) < WindowSample.aggregateThreshold ∧
    WindowSample.aggregateThreshold < 1000 := by
  rw [WindowSample.sampled_threshold_exact]
  norm_num

/-- Every declared delta/scale robustness point lies in a whole admissible rectangle. -/
theorem robustness_rectangle_admissible {d s : ℝ} (hd : d ∈ Icc (6 / 5) 2)
    (hs : s ∈ Icc (1 / 3) 3) :
    scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000 := by
  have hdp : 0 < d := by linarith [hd.1]
  have hsp : 0 < s := by linarith [hs.1]
  have hden := mul_pos original_delta_positive hsp
  have htpos := (by norm_num : (0 : ℝ) < 900).trans original_aggregate_bounds.1
  have hlprod : (6 / 5 : ℝ) * 900 ≤ d * WindowSample.aggregateThreshold :=
    mul_le_mul hd.1 original_aggregate_bounds.1.le (by norm_num) hdp.le
  have huprod : d * WindowSample.aggregateThreshold ≤ (2 : ℝ) * 1000 :=
    mul_le_mul hd.2 original_aggregate_bounds.2.le htpos.le (by norm_num)
  have he : scaledThreshold d s = d * WindowSample.aggregateThreshold / (WindowSample.delta * s) := by
    unfold scaledThreshold
    ring
  have hl : (3 / 2 : ℝ) < scaledThreshold d s := by
    rw [he]
    apply (lt_div_iff₀ hden).mpr
    rw [WindowSample.sampled_delta_exact]
    nlinarith [hs.2]
  have hu : scaledThreshold d s < 20000 := by
    rw [he]
    apply (div_lt_iff₀ hden).mpr
    rw [WindowSample.sampled_delta_exact]
    nlinarith [hs.1]
  refine ⟨?_, hu⟩
  unfold freeGrowth
  have hexp := Real.exp_pos (-2 * Real.log (20000 : ℝ))
  linarith

theorem scaled_endpoint_continuous_rectangle :
    ContinuousOn (fun q : ℝ × ℝ => scaledEndpoint q.1 q.2)
      {q | q.1 ∈ Icc (6 / 5) 2 ∧ q.2 ∈ Icc (1 / 3) 3} := by
  intro p hp
  exact (scaled_endpoint_continuousAt (by linarith [hp.2.1])
    (robustness_rectangle_admissible hp.1 hp.2)).continuousWithinAt

theorem robustness_rectangle_native_window {d s : ℝ} (hd : d ∈ Icc (6 / 5) 2)
    (hs : s ∈ Icc (1 / 3) 3) :
    0 < scaledEndpoint d s ∧ nativeGrowth (1 / 1000) (scaledEndpoint d s) 20 = scaledThreshold d s ∧
      ∀ lam : ℝ, GrowthPopulation.nativeAggregate (scaledAmplitude s) WindowSampleData.tag
        (1 / 1000) 20 d 10 lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ scaledEndpoint d s :=
  scaled_endpoint_native_window (by linarith [hd.1]) (by linarith [hs.1])
    (robustness_rectangle_admissible hd hs)

theorem scaled_endpoint_strict_delta {d1 d2 s : ℝ} (hs : 0 < s) (h12 : d1 < d2)
    (hT1 : scaledThreshold d1 s ∈ Ioo (freeGrowth (Real.log 20000)) 20000)
    (hT2 : scaledThreshold d2 s ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    scaledEndpoint d2 s < scaledEndpoint d1 s := by
  have hT : scaledThreshold d1 s < scaledThreshold d2 s := by
    exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right h12 (mul_pos original_delta_positive hs))
      ((by norm_num : (0 : ℝ) < 900).trans original_aggregate_bounds.1)
  have he := endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (Real.log_pos (by norm_num : (1 : ℝ) < 20000))
  apply he _ _ hT
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT1
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT2

theorem scaled_endpoint_strict_amplitude {d s1 s2 : ℝ} (hd : 0 < d)
    (hs1 : 0 < s1) (h12 : s1 < s2)
    (hT1 : scaledThreshold d s1 ∈ Ioo (freeGrowth (Real.log 20000)) 20000)
    (hT2 : scaledThreshold d s2 ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    scaledEndpoint d s1 < scaledEndpoint d s2 := by
  have hT : scaledThreshold d s2 < scaledThreshold d s1 := by
    exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_left hd (mul_pos original_delta_positive hs1)
      (mul_lt_mul_of_pos_left h12 original_delta_positive))
      ((by norm_num : (0 : ℝ) < 900).trans original_aggregate_bounds.1)
  have he := endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (Real.log_pos (by norm_num : (1 : ℝ) < 20000))
  apply he _ _ hT
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT2
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT1

end
end SbtCosmo.Derivation.WindowSensitivity
