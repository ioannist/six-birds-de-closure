import SbtCosmo.Derivation.GrowthRescaledCertificate
import SbtCosmo.Derivation.WindowRobustRatio

/-! Numerically certified actual edge ratios on the full rescaling rectangle.
The dimensionless brackets return to the original IVP and first-collapse readout. -/
namespace SbtCosmo.Derivation.WindowRobustEdge
noncomputable section
open Set GrowthScaleReturn WindowSensitivity WindowRobustRecord WindowRobustRatio
open GrowthRescaledCertificate

theorem original_aggregate_tight : (960:ℝ) < WindowSample.aggregateThreshold ∧
    WindowSample.aggregateThreshold < 970 := by
  rw [WindowSample.sampled_threshold_exact]
  norm_num

theorem endpoint_normalized_bounds {d s : ℝ} (hR : Rectangle d s) :
    (3:ℝ) < scaledEndpoint d s*(factor d s)^3 ∧
      scaledEndpoint d s*(factor d s)^3 < 7/2 := by
  let c := factor d s
  have hc : c ∈ Ioo (1/5) 4 := factor_bounds hR
  have hp : 0 < c := factor_positive hR
  have hp3 := pow_pos hp 3
  have he := endpoint_spec hR
  have hu : -(1/(20:ℝ)^3) < scaledEndpoint d s := by linarith [he.1]
  have hl : -(1/(20:ℝ)^3) < 3/c^3 := by
    have hpos : (0:ℝ) < 3/c^3 := by positivity
    norm_num
    linarith
  have hh : -(1/(20:ℝ)^3) < (7/2)/c^3 := by
    have hpos : (0:ℝ) < (7/2)/c^3 := by positivity
    norm_num
    linarith
  have hprefix : nativeGrowth (1/1000) (3/c^3) (5*c) ≤ nativeGrowth (1/1000) (3/c^3) 20 := by
    exact (GrowthFirstRecord.native_strictMonoOn (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num) hl).monotoneOn ⟨by linarith [hc.1],by linarith [hc.2]⟩ (by norm_num)
      (by linarith [hc.2])
  have hlower : scaledThreshold d s < nativeGrowth (1/1000) (3/c^3) 20 := by
    have h0 := mul_lt_mul_of_pos_left original_aggregate_tight.2 hp
    rw [mul_comm c 970] at h0
    exact h0.trans ((lower_prefix_growth hc).trans_le hprefix)
  have hupper : nativeGrowth (1/1000) ((7/2)/c^3) 20 < scaledThreshold d s := by
    have h0 := mul_lt_mul_of_pos_left original_aggregate_tight.1 hp
    rw [mul_comm c 960] at h0
    exact (upper_horizon_growth hc).trans h0
  have hm := native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)
  have hlu : 3/c^3 < scaledEndpoint d s := by
    apply (hm.lt_iff_gt hu hl).mp
    rw [he.2]
    exact hlower
  have huu : scaledEndpoint d s < (7/2)/c^3 := by
    apply (hm.lt_iff_gt hh hu).mp
    rw [he.2]
    exact hupper
  exact ⟨(div_lt_iff₀ hp3).mp hlu,(lt_div_iff₀ hp3).mp huu⟩

theorem endpoint_time_bounds {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    factor d s/2 < time d s j (scaledEndpoint d s) ∧
      time d s j (scaledEndpoint d s) ≤ (8/3)*factor d s := by
  let c := factor d s
  have hc : c ∈ Ioo (1/5) 4 := factor_bounds hR
  have hp : 0 < c := factor_positive hR
  have hu := (endpoint_spec hR).1
  have hg : gate d s (scaledEndpoint d s) :=
    (gate_iff_window hR _).mpr ⟨by linarith [hu],le_rfl⟩
  have hT := mul_lt_mul_of_pos_left (WindowFirstRecord.threshold_bounds j).1 hp
  have hlower := time_nonnegative_lower hR hg hu.le j
  have hnorm := endpoint_normalized_bounds hR
  have hparam : scaledEndpoint d s < (7/2)/c^3 := (lt_div_iff₀ (pow_pos hp 3)).mpr hnorm.2
  have hA : (8/3)*c ∈ Icc (1/1000) 20 := ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hcutu : -(1/(((8/3)*c)^3)) < scaledEndpoint d s := by
    have hn : -(1/(((8/3)*c)^3)) < (0:ℝ) :=
      neg_neg_of_pos (div_pos (by norm_num) (by positivity))
    exact hn.trans hu
  have hcuthi : -(1/(((8/3)*c)^3)) < (7/2)/c^3 := by
    have hn : -(1/(((8/3)*c)^3)) < (0:ℝ) :=
      neg_neg_of_pos (div_pos (by norm_num) (by positivity))
    exact hn.trans (by positivity)
  have henergy := (native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by linarith [hc.1] : (1/1000:ℝ) < (8/3)*c)).antitoneOn hcutu hcuthi hparam.le
  have hthreshold := mul_lt_mul_of_pos_left (WindowFirstRecord.threshold_bounds j).2 hp
  rw [mul_comm c 897] at hthreshold
  have hD : threshold d s j ≤ nativeGrowth (1/1000) (scaledEndpoint d s) ((8/3)*c) :=
    hthreshold.le.trans ((upper_prefix_growth hc).le.trans henergy)
  refine ⟨?_,?_⟩
  · change c/2 < time d s j (scaledEndpoint d s)
    change c*WindowFirstRecord.threshold j/1000 ≤ time d s j (scaledEndpoint d s) at hlower
    linarith
  · exact (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num) (gate_cutoff hR hg) (by linarith [(threshold_bounds hR j).1])
      (final_above_threshold hR hg j) hA).mp hD

theorem endpoint_ratios {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    (3:ℝ)/8 < ratio d s j (scaledEndpoint d s) ∧
      ratio d s j (scaledEndpoint d s) < 1792/27 := by
  have hp := factor_positive hR
  have hu := (endpoint_spec hR).1
  have ht := endpoint_time_bounds hR j
  have hn := endpoint_normalized_bounds hR
  have htimepos : 0 < time d s j (scaledEndpoint d s) := by linarith [ht.1]
  have hlo := pow_lt_pow_left₀ ht.1 (by positivity : (0:ℝ) ≤ factor d s/2) (by norm_num : 3 ≠ 0)
  have hhi := pow_le_pow_left₀ htimepos.le ht.2 3
  have hmullo := mul_lt_mul_of_pos_left hlo hu
  have hmulhi := mul_le_mul_of_nonneg_left hhi hu.le
  rw [ratio,abs_of_pos hu]
  constructor <;> nlinarith

/-- Tight explicit finite bound on every signed admitted ratio, uniformly in both knobs. -/
theorem full_window_ratios {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    0 ≤ ratio d s j lam ∧ ratio d s j lam < 1792/27 := by
  refine ⟨ratio_nonnegative hR hg j,?_⟩
  by_cases hl : 0 ≤ lam
  · have hu := (endpoint_spec hR).1
    exact ((ratio_strictMono_nonnegative hR j).monotoneOn
      ⟨hl,((gate_iff_window hR lam).mp hg).2⟩ ⟨hu.le,le_rfl⟩
      ((gate_iff_window hR lam).mp hg).2).trans_lt (endpoint_ratios hR j).2
  · exact (ratio_nonpositive_small hR hg (le_of_not_ge hl) j).trans (by norm_num)

end
end SbtCosmo.Derivation.WindowRobustEdge
