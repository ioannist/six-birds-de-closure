import SbtCosmo.Derivation.WindowPatchCounts
import SbtCosmo.Derivation.WindowPatchCountFirstData
import SbtCosmo.Derivation.GrowthRescaledCertificate
import SbtCosmo.Derivation.GrowthFirstRecordLive

/-! Actual first-ANY-patch times and numerical endpoint ratios for the original
separately realized N32/N128 populations, on their full signed native windows. -/
namespace SbtCosmo.Derivation.WindowPatchCountRatio
noncomputable section
open Set GrowthScaleReturn GrowthRescaledCertificate WindowPatchCounts

def scale (v : Bool) : ℝ := aggregateThreshold v / 965
def maximum (v : Bool) (j : Fin 12) : ℝ := max (maximumFalse v j) (maximumTrue v j)
def threshold (v : Bool) (j : Fin 12) : ℝ := delta / maximum v j
def time (v : Bool) (j : Fin 12) (lam : ℝ) : ℝ :=
  GrowthFirstRecordLive.firstTime (1/1000) 20 (threshold v j) lam
def ratio (v : Bool) (j : Fin 12) (lam : ℝ) : ℝ := |lam| * (time v j lam)^3

theorem scale_bounds (v : Bool) : scale v ∈ Ioo (1/5) 4 := by
  have he : scale v = (WindowPatchCountFirstData.scaleRat v : ℝ) := by
    simp [scale,aggregateThreshold,WindowPatchCountFirstData.scaleRat]
  rw [he]
  change (1:ℝ)/5 < (WindowPatchCountFirstData.scaleRat v : ℝ) ∧
    (WindowPatchCountFirstData.scaleRat v : ℝ) < 4
  constructor
  · have h : (((1:ℚ)/5 : ℚ) : ℝ) < (WindowPatchCountFirstData.scaleRat v : ℝ) :=
      Rat.cast_lt.mpr (WindowPatchCountFirstData.rational_scale_bounds v).1
    norm_num at h ⊢
    exact h
  · exact_mod_cast (WindowPatchCountFirstData.rational_scale_bounds v).2

theorem scale_tight : (129:ℝ)/100 < scale false ∧ scale false < 131/100 ∧
    83/100 < scale true ∧ scale true < 84/100 := by
  have he (v : Bool) : scale v = (WindowPatchCountFirstData.scaleRat v : ℝ) := by
    simp [scale,aggregateThreshold,WindowPatchCountFirstData.scaleRat]
  rw [he false,he true]
  refine ⟨?_,?_,?_,?_⟩
  · have h : (((129:ℚ)/100 : ℚ) : ℝ) < (WindowPatchCountFirstData.scaleRat false : ℝ) :=
      Rat.cast_lt.mpr WindowPatchCountFirstData.rational_scale_tight.1
    norm_num at h ⊢
    exact h
  · have h : (WindowPatchCountFirstData.scaleRat false : ℝ) < (((131:ℚ)/100 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr WindowPatchCountFirstData.rational_scale_tight.2.1
    norm_num at h ⊢
    exact h
  · have h : (((83:ℚ)/100 : ℚ) : ℝ) < (WindowPatchCountFirstData.scaleRat true : ℝ) :=
      Rat.cast_lt.mpr WindowPatchCountFirstData.rational_scale_tight.2.2.1
    norm_num at h ⊢
    exact h
  · have h : (WindowPatchCountFirstData.scaleRat true : ℝ) < (((84:ℚ)/100 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr WindowPatchCountFirstData.rational_scale_tight.2.2.2
    norm_num at h ⊢
    exact h

theorem aggregate_normalized (v : Bool) : aggregateThreshold v = 965*scale v := by
  unfold scale
  ring

theorem maximum_spec (v : Bool) (j : Fin 12) : 0 < maximum v j ∧
    (∀ i, amplitude v j i ≤ maximum v j) ∧ ∃ i, amplitude v j i = maximum v j := by
  obtain ⟨_,h0,_,hm0,hm1⟩ := sampled_maxima v j
  refine ⟨h0.trans_le (le_max_left _ _),?_,?_⟩
  · intro i
    cases hi : WindowPatchCountData.tag v j i
    · exact (hm0.bounds i hi).trans (le_max_left _ _)
    · exact (hm1.bounds i hi).trans (le_max_right _ _)
  · by_cases h : maximumFalse v j ≤ maximumTrue v j
    · obtain ⟨i,_,he⟩ := hm1.attained
      exact ⟨i,he.trans (max_eq_right h).symm⟩
    · obtain ⟨i,_,he⟩ := hm0.attained
      exact ⟨i,he.trans (max_eq_left (le_of_not_ge h)).symm⟩

theorem threshold_bounds (v : Bool) (j : Fin 12) :
    1 < threshold v j ∧ threshold v j < 2000 ∧
      450*scale v < threshold v j ∧ threshold v j < 897*scale v := by
  have he : threshold v j = (WindowPatchCountFirstData.firstThresholdRat v j : ℝ) := by
    simp [threshold,maximum,delta,maximumFalse,maximumTrue,
      WindowPatchCountFirstData.firstThresholdRat]
  have hc : scale v = (WindowPatchCountFirstData.scaleRat v : ℝ) := by
    simp [scale,aggregateThreshold,WindowPatchCountFirstData.scaleRat]
  rw [he,hc]
  exact_mod_cast WindowPatchCountFirstData.rational_first_bounds v j

theorem gate_cutoff {v : Bool} {lam : ℝ} (hg : realizedGate v lam) : -(1/(20:ℝ)^3) < lam := by
  convert ((upper_spec v).2.2 lam).mp hg |>.1 using 1
  norm_num

theorem final_above_threshold {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (j : Fin 12) :
    threshold v j ≤ nativeGrowth (1/1000) lam 20 := by
  have hc := scale_bounds v
  have hT := (threshold_bounds v j).2.2.2
  have hG := ((realized_gate_iff_threshold v lam).mp hg).2
  rw [aggregate_normalized v] at hG
  linarith [hc.1]

theorem endpoint_normalized_bounds (v : Bool) :
    (3:ℝ) < upper v*(scale v)^3 ∧ upper v*(scale v)^3 < 7/2 := by
  let c := scale v
  have hc := scale_bounds v
  have hp : 0 < c := by dsimp [c]; linarith [hc.1]
  have he := upper_spec v
  have hu : -(1/(20:ℝ)^3) < upper v := by linarith [he.1]
  have hl : -(1/(20:ℝ)^3) < 3/c^3 := by
    have hpos : (0:ℝ) < 3/c^3 := by positivity
    norm_num
    linarith
  have hh : -(1/(20:ℝ)^3) < (7/2)/c^3 := by
    have hpos : (0:ℝ) < (7/2)/c^3 := by positivity
    norm_num
    linarith
  have hprefix : nativeGrowth (1/1000) (3/c^3) (5*c) ≤ nativeGrowth (1/1000) (3/c^3) 20 :=
    (GrowthFirstRecord.native_strictMonoOn (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num) hl).monotoneOn ⟨by linarith [hc.1],by linarith [hc.2]⟩ (by norm_num)
      (by linarith [hc.2])
  have hlow : aggregateThreshold v < nativeGrowth (1/1000) (3/c^3) 20 := by
    rw [aggregate_normalized v]
    exact (by nlinarith : 965*scale v < 970*c).trans
      ((lower_prefix_growth hc).trans_le hprefix)
  have hhigh : nativeGrowth (1/1000) ((7/2)/c^3) 20 < aggregateThreshold v := by
    rw [aggregate_normalized v]
    exact (upper_horizon_growth hc).trans (by nlinarith)
  have hm := native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)
  have hlu : 3/c^3 < upper v := by
    apply (hm.lt_iff_gt hu hl).mp
    rw [he.2.1]
    exact hlow
  have huu : upper v < (7/2)/c^3 := by
    apply (hm.lt_iff_gt hh hu).mp
    rw [he.2.1]
    exact hhigh
  exact ⟨(div_lt_iff₀ (pow_pos hp 3)).mp hlu,(lt_div_iff₀ (pow_pos hp 3)).mp huu⟩

theorem endpoint_numerical : (13:ℝ)/10 < upper false ∧ upper false < 17/10 ∧
    5 < upper true ∧ upper true < 25/4 := by
  have h32 := endpoint_normalized_bounds false
  have h128 := endpoint_normalized_bounds true
  have hp32 : 0 ≤ upper false := (upper_spec false).1.le
  have hp128 : 0 ≤ upper true := (upper_spec true).1.le
  have hlo32 := pow_lt_pow_left₀ scale_tight.1 (by norm_num : (0:ℝ) ≤ 129/100) (by norm_num : 3 ≠ 0)
  have hhi32 := pow_lt_pow_left₀ scale_tight.2.1 (by linarith [scale_tight.1] : 0 ≤ scale false) (by norm_num : 3 ≠ 0)
  have hlo128 := pow_lt_pow_left₀ scale_tight.2.2.1 (by norm_num : (0:ℝ) ≤ 83/100) (by norm_num : 3 ≠ 0)
  have hhi128 := pow_lt_pow_left₀ scale_tight.2.2.2 (by linarith [scale_tight.2.2.1] : 0 ≤ scale true) (by norm_num : 3 ≠ 0)
  norm_num at hlo32 hhi32 hlo128 hhi128
  have h32a := mul_le_mul_of_nonneg_left hhi32.le hp32
  have h32b := mul_le_mul_of_nonneg_left hlo32.le hp32
  have h128a := mul_le_mul_of_nonneg_left hhi128.le hp128
  have h128b := mul_le_mul_of_nonneg_left hlo128.le hp128
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem endpoint_gate (v : Bool) : realizedGate v (upper v) :=
  ((upper_spec v).2.2 _).mpr ⟨by linarith [(upper_spec v).1],le_rfl⟩

theorem time_spec {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (j : Fin 12) :
    time v j lam ∈ Icc (1/1000) 20 ∧ nativeGrowth (1/1000) lam (time v j lam) = threshold v j :=
  GrowthFirstRecordLive.firstTime_spec (by norm_num) (by norm_num) (gate_cutoff hg)
    (threshold_bounds v j).1 (final_above_threshold hg j)

theorem time_positive {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (j : Fin 12) : 0 < time v j lam := by
  linarith [(time_spec hg j).1.1]

theorem time_iff_any_collapse {v : Bool} {lam a : ℝ} (hg : realizedGate v lam)
    (ha : a ∈ Icc (1/1000) 20) (j : Fin 12) :
    (∃ i, delta ≤ amplitude v j i*nativeGrowth (1/1000) lam a) ↔ time v j lam ≤ a := by
  have hD := (native_positive (by norm_num : (0:ℝ) < 1/1000) (by norm_num) (gate_cutoff hg) a ha).1.le
  exact (GrowthFirstRecord.any_patch_collapse_iff (maximum_spec v j).1 hD
    (maximum_spec v j).2.1 (maximum_spec v j).2.2).trans
    (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num) (by norm_num)
      (gate_cutoff hg) (threshold_bounds v j).1 (final_above_threshold hg j) ha)

theorem time_is_first_collapse {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (j : Fin 12) :
    (∃ i, delta ≤ amplitude v j i*nativeGrowth (1/1000) lam (time v j lam)) ∧
      ∀ a ∈ Icc (1/1000) 20, a < time v j lam →
        ¬ ∃ i, delta ≤ amplitude v j i*nativeGrowth (1/1000) lam a := by
  refine ⟨(time_iff_any_collapse hg (time_spec hg j).1 j).mpr le_rfl,?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hg ha j).mp hc)

theorem time_at_zero (v : Bool) (j : Fin 12) : time v j 0 = threshold v j/1000 := by
  have he := GrowthFirstRecordLive.firstTime_at_zero (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) (threshold_bounds v j).1 (final_above_threshold (zero_passes v) j)
  change time v j 0 = (1/1000:ℝ)*threshold v j at he
  convert he using 1
  ring

theorem time_strictMono (v : Bool) (j : Fin 12) : StrictMonoOn (time v j)
    (Ioc (-(1/8000:ℝ)) (upper v)) := by
  intro l1 h1 l2 h2 h12
  have hg1 := ((upper_spec v).2.2 l1).mpr h1
  have hg2 := ((upper_spec v).2.2 l2).mpr h2
  exact GrowthFirstRecordLive.firstTime_strict_parameter (by norm_num) (by norm_num)
    (gate_cutoff hg1) h12 (threshold_bounds v j).1
    (final_above_threshold hg1 j) (final_above_threshold hg2 j)

theorem time_nonnegative_lower {v : Bool} {lam : ℝ} (hg : realizedGate v lam)
    (hl : 0 ≤ lam) (j : Fin 12) : (9/20:ℝ)*scale v < time v j lam := by
  have h := GrowthFirstRecord.firstTime_lower_matter (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) hl (threshold_bounds v j).1 (final_above_threshold hg j)
  rw [← GrowthFirstRecordLive.firstTime_eq_nonnegative (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) hl (threshold_bounds v j).1 (final_above_threshold hg j)] at h
  change (1/1000:ℝ)*threshold v j ≤ time v j lam at h
  linarith [(threshold_bounds v j).2.2.1]

theorem time_nonpositive_upper {v : Bool} {lam : ℝ} (hg : realizedGate v lam)
    (hl : lam ≤ 0) (j : Fin 12) : time v j lam < 2 := by
  have h := GrowthFirstRecordLive.firstTime_nonpositive_upper (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) (gate_cutoff hg) hl (threshold_bounds v j).1 (final_above_threshold hg j)
  change time v j lam ≤ (1/1000:ℝ)*threshold v j at h
  linarith [(threshold_bounds v j).2.1]

theorem endpoint_time_bounds (v : Bool) (j : Fin 12) :
    (9/20:ℝ)*scale v < time v j (upper v) ∧ time v j (upper v) ≤ (8/3)*scale v := by
  let c := scale v
  have hc := scale_bounds v
  have hp : 0 < c := by dsimp [c]; linarith [hc.1]
  have hu := (upper_spec v).1
  have hparam : upper v < (7/2)/c^3 :=
    (lt_div_iff₀ (pow_pos hp 3)).mpr (endpoint_normalized_bounds v).2
  have hA : (8/3)*c ∈ Icc (1/1000) 20 := ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hn : -(1/(((8/3)*c)^3)) < (0:ℝ) :=
    neg_neg_of_pos (div_pos (by norm_num) (by positivity))
  have henergy := (native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by linarith [hc.1] : (1/1000:ℝ) < (8/3)*c)).antitoneOn (hn.trans hu)
      (hn.trans (by positivity : (0:ℝ) < (7/2)/c^3)) hparam.le
  have hD : threshold v j ≤ nativeGrowth (1/1000) (upper v) ((8/3)*c) :=
    (threshold_bounds v j).2.2.2.le.trans ((upper_prefix_growth hc).le.trans henergy)
  exact ⟨time_nonnegative_lower (endpoint_gate v) hu.le j,
    (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num) (gate_cutoff (endpoint_gate v)) (threshold_bounds v j).1
      (final_above_threshold (endpoint_gate v) j) hA).mp hD⟩

theorem ratio_density_readout (v : Bool) (j : Fin 12) (lam : ℝ) :
    ratio v j lam = |lam|/((time v j lam)^3)⁻¹ := by simp only [ratio,div_inv_eq_mul]

theorem ratio_nonnegative {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (j : Fin 12) :
    0 ≤ ratio v j lam := mul_nonneg (abs_nonneg _) (pow_nonneg (time_positive hg j).le _)

theorem ratio_positive {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (hne : lam ≠ 0) (j : Fin 12) :
    0 < ratio v j lam := mul_pos (abs_pos.mpr hne) (pow_pos (time_positive hg j) 3)

theorem ratio_zero (v : Bool) (j : Fin 12) : ratio v j 0 = 0 := by simp [ratio]

theorem ratio_strictMono_nonnegative (v : Bool) (j : Fin 12) :
    StrictMonoOn (ratio v j) (Icc 0 (upper v)) := by
  intro l1 h1 l2 h2 h12
  have hw (l : ℝ) (h : l ∈ Icc 0 (upper v)) : l ∈ Ioc (-(1/8000:ℝ)) (upper v) :=
    ⟨by linarith [h.1],h.2⟩
  have ht := (time_strictMono v j (hw _ h1) (hw _ h2) h12).le
  have hg1 := ((upper_spec v).2.2 l1).mpr (hw _ h1)
  have hg2 := ((upper_spec v).2.2 l2).mpr (hw _ h2)
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (time_positive hg1 j).le ht 3) h1.1
  have hs := mul_lt_mul_of_pos_right h12 (pow_pos (time_positive hg2 j) 3)
  simpa only [ratio,abs_of_nonneg h1.1,abs_of_nonneg h2.1] using hb.trans_lt hs

theorem ratio_nonpositive_small {v : Bool} {lam : ℝ} (hg : realizedGate v lam)
    (hl : lam ≤ 0) (j : Fin 12) : ratio v j lam < (1:ℝ)/1000 := by
  have ht := pow_le_pow_left₀ (time_positive hg j).le (time_nonpositive_upper hg hl j).le 3
  have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg lam)
  have ha : |lam| < (1:ℝ)/8000 := by
    rw [abs_of_nonpos hl]
    linarith [gate_cutoff hg]
  change ratio v j lam ≤ |lam| * 2^3 at hm
  nlinarith

theorem ratio_nonnegative_upper {v : Bool} {lam : ℝ} (hg : realizedGate v lam)
    (hl : 0 ≤ lam) (j : Fin 12) : ratio v j lam ≤ 8000*lam := by
  have ht := pow_le_pow_left₀ (time_positive hg j).le (time_spec hg j).1.2 3
  have hm := mul_le_mul_of_nonneg_left ht hl
  simpa only [ratio,abs_of_nonneg hl] using (by nlinarith : lam*(time v j lam)^3 ≤ 8000*lam)

theorem endpoint_ratios (v : Bool) (j : Fin 12) :
    (2187:ℝ)/8000 < ratio v j (upper v) ∧ ratio v j (upper v) < 1792/27 := by
  have hp : 0 < scale v := by linarith [(scale_bounds v).1]
  have hu := (upper_spec v).1
  have ht := endpoint_time_bounds v j
  have hn := endpoint_normalized_bounds v
  have hlo := pow_lt_pow_left₀ ht.1 (by positivity : (0:ℝ) ≤ (9/20)*scale v) (by norm_num : 3 ≠ 0)
  have hhi := pow_le_pow_left₀ (time_positive (endpoint_gate v) j).le ht.2 3
  have hmlo := mul_lt_mul_of_pos_left hlo hu
  have hmhi := mul_le_mul_of_nonneg_left hhi hu.le
  rw [ratio,abs_of_pos hu]
  constructor <;> nlinarith

theorem full_window_ratios {v : Bool} {lam : ℝ} (hg : realizedGate v lam) (j : Fin 12) :
    0 ≤ ratio v j lam ∧ ratio v j lam < 1792/27 := by
  refine ⟨ratio_nonnegative hg j,?_⟩
  by_cases hl : 0 ≤ lam
  · have hu := (upper_spec v).1
    exact ((ratio_strictMono_nonnegative v j).monotoneOn
      ⟨hl,(((upper_spec v).2.2 lam).mp hg).2⟩ ⟨hu.le,le_rfl⟩
      (((upper_spec v).2.2 lam).mp hg).2).trans_lt (endpoint_ratios v j).2
  · exact (ratio_nonpositive_small hg (le_of_not_ge hl) j).trans (by norm_num)

/-- One positive parameter makes every first-record ratio arbitrarily small
simultaneously for both separately realized populations and all twelve seeds. -/
theorem ratios_uniformly_arbitrarily_small {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : Bool, realizedGate v lam ∧
      ∀ j : Fin 12, 0 < ratio v j lam ∧ ratio v j lam < epsilon := by
  let lam : ℝ := min (min (upper false) (upper true)) (epsilon/16000)
  have hl : 0 < lam := lt_min (lt_min (upper_spec false).1 (upper_spec true).1)
    (div_pos he (by norm_num))
  have hu (v : Bool) : lam ≤ upper v := by
    cases v
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
  have hε : lam ≤ epsilon/16000 := min_le_right _ _
  refine ⟨lam,hl,?_⟩
  intro v
  have hg : realizedGate v lam := ((upper_spec v).2.2 lam).mpr ⟨by linarith,hu v⟩
  refine ⟨hg,?_⟩
  intro j
  exact ⟨ratio_positive hg hl.ne' j,by linarith [ratio_nonnegative_upper hg hl.le j]⟩

end
end SbtCosmo.Derivation.WindowPatchCountRatio
