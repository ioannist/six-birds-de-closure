import SbtCosmo.Derivation.WindowSensitivity
import SbtCosmo.Derivation.WindowSignedRecord

/-! Actual first collapse throughout the declared coupled rescaling rectangle.
The same reified amplitudes/tags and original growth IVP are retained. -/
namespace SbtCosmo.Derivation.WindowRobustRecord
noncomputable section
open Set GrowthScaleReturn WindowSensitivity

def Rectangle (d s : ℝ) : Prop := d ∈ Icc (6/5) 2 ∧ s ∈ Icc (1/3) 3
def factor (d s : ℝ) : ℝ := d / (WindowSample.delta*s)
def maximum (s : ℝ) (j : Fin 12) : ℝ := s*WindowFirstRecord.maximum j
def threshold (d s : ℝ) (j : Fin 12) : ℝ := factor d s*WindowFirstRecord.threshold j
def time (d s : ℝ) (j : Fin 12) (lam : ℝ) : ℝ :=
  GrowthFirstRecordLive.firstTime (1/1000) 20 (threshold d s j) lam
def gate (d s lam : ℝ) : Prop := GrowthPopulation.nativeAggregate
  (scaledAmplitude s) WindowSampleData.tag (1/1000) 20 d 10 lam

theorem rectangle_positive {d s : ℝ} (hR : Rectangle d s) : 0<d ∧ 0<s := by
  exact ⟨by linarith [hR.1.1],by linarith [hR.2.1]⟩

theorem factor_positive {d s : ℝ} (hR : Rectangle d s) : 0<factor d s :=
  div_pos (rectangle_positive hR).1 (mul_pos original_delta_positive (rectangle_positive hR).2)

/-- Exact bounds use only declared parameter ranges and the original delta. -/
theorem factor_corner_bounds {d s : ℝ} (hR : Rectangle d s) :
    factor (6/5) 3 ≤ factor d s ∧ factor d s ≤ factor 2 (1/3) := by
  have hs := (rectangle_positive hR).2
  unfold factor
  rw [WindowSample.sampled_delta_exact]
  constructor
  · apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<(843/500)*3)
      (mul_pos (by norm_num : (0:ℝ)<843/500) hs)).mpr
    nlinarith [hR.1.1,hR.2.2]
  · apply (div_le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<843/500) hs)
      (by norm_num : (0:ℝ)<(843/500)*(1/3))).mpr
    nlinarith [hR.1.2,hR.2.1]

theorem factor_bounds {d s : ℝ} (hR : Rectangle d s) : (1:ℝ)/5<factor d s ∧ factor d s<4 := by
  have h := factor_corner_bounds hR
  norm_num [factor,WindowSample.sampled_delta_exact] at h
  unfold factor
  rw [WindowSample.sampled_delta_exact]
  constructor <;> linarith

/-- Largest scaled patch, with an actual attained witness. -/
theorem maximum_spec {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    0<maximum s j ∧ (∀ i, scaledAmplitude s j i ≤ maximum s j) ∧
      ∃ i, scaledAmplitude s j i=maximum s j := by
  have hs := (rectangle_positive hR).2
  obtain ⟨hm,hb,i,hi⟩ := WindowFirstRecord.maximum_spec j
  refine ⟨mul_pos hs hm,fun i => mul_le_mul_of_nonneg_left (hb i) hs.le,i,?_⟩
  exact congrArg (fun x : ℝ => s*x) hi

theorem threshold_return (d s : ℝ) (j : Fin 12) :
    d/maximum s j=threshold d s j := by
  unfold maximum threshold factor WindowFirstRecord.threshold
  field_simp [original_delta_positive.ne']

theorem threshold_bounds {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    (100:ℝ)<threshold d s j ∧ threshold d s j<3588 := by
  have hc := factor_bounds hR
  have ht := WindowFirstRecord.threshold_bounds j
  have hlo := mul_lt_mul hc.1 ht.1.le (by norm_num : (0:ℝ)<500) (factor_positive hR).le
  have hhi := mul_lt_mul hc.2 ht.2.le (by linarith : (0:ℝ)<WindowFirstRecord.threshold j) (by norm_num : (0:ℝ)≤4)
  unfold threshold
  constructor <;> nlinarith

theorem threshold_below_aggregate {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    threshold d s j<scaledThreshold d s := by
  change factor d s*WindowFirstRecord.threshold j<factor d s*WindowSample.aggregateThreshold
  exact mul_lt_mul_of_pos_left
    ((WindowFirstRecord.threshold_bounds j).2.trans (by linarith [original_aggregate_bounds.1])) (factor_positive hR)

theorem gate_iff_window {d s : ℝ} (hR : Rectangle d s) (lam : ℝ) :
    gate d s lam ↔ lam ∈ Ioc (-(1/8000:ℝ)) (scaledEndpoint d s) :=
  (robustness_rectangle_native_window hR.1 hR.2).2.2 lam

theorem endpoint_spec {d s : ℝ} (hR : Rectangle d s) :
    0<scaledEndpoint d s ∧ nativeGrowth (1/1000) (scaledEndpoint d s) 20=scaledThreshold d s :=
  ⟨(robustness_rectangle_native_window hR.1 hR.2).1,
    (robustness_rectangle_native_window hR.1 hR.2).2.1⟩

theorem gate_cutoff {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) :
    -(1/(20:ℝ)^3)<lam := by
  have h := ((gate_iff_window hR lam).mp hg).1
  norm_num at h ⊢
  exact h

theorem final_above_threshold {d s lam : ℝ} (hR : Rectangle d s)
    (hg : gate d s lam) (j : Fin 12) : threshold d s j≤nativeGrowth (1/1000) lam 20 := by
  have hw := (gate_iff_window hR lam).mp hg
  have hc := gate_cutoff hR hg
  have he := endpoint_spec hR
  have hm := (native_endpoint_strictAntiOn (by norm_num : (0:ℝ)<1/1000)
    (by norm_num : (1/1000:ℝ)<20)).antitoneOn hc
    (show -(1/(20:ℝ)^3)<scaledEndpoint d s by linarith [he.1]) hw.2
  rw [he.2] at hm
  exact (threshold_below_aggregate hR j).le.trans hm

theorem time_spec {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    time d s j lam ∈ Icc (1/1000) 20 ∧
      nativeGrowth (1/1000) lam (time d s j lam)=threshold d s j :=
  GrowthFirstRecordLive.firstTime_spec (by norm_num) (by norm_num) (gate_cutoff hR hg)
    (by linarith [(threshold_bounds hR j).1]) (final_above_threshold hR hg j)

/-- This is the original ANY-patch first-record readout, including negative lambda. -/
theorem time_iff_any_collapse {d s lam a : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (ha : a ∈ Icc (1/1000) 20) (j : Fin 12) :
    (∃ i, d≤scaledAmplitude s j i*nativeGrowth (1/1000) lam a) ↔ time d s j lam≤a := by
  have hD := (native_positive (by norm_num : (0:ℝ)<1/1000) (by norm_num) (gate_cutoff hR hg) a ha).1.le
  have hm := maximum_spec hR j
  have hcollapse := GrowthFirstRecord.any_patch_collapse_iff hm.1 hD hm.2.1 hm.2.2 (δ := d)
  rw [threshold_return d s j] at hcollapse
  exact hcollapse.trans
    (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num) (by norm_num) (gate_cutoff hR hg)
      (by linarith [(threshold_bounds hR j).1])
      (final_above_threshold hR hg j) ha)

theorem time_is_first_collapse {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    (∃ i, d≤scaledAmplitude s j i*nativeGrowth (1/1000) lam (time d s j lam)) ∧
      ∀ a ∈ Icc (1/1000) 20, a<time d s j lam →
        ¬∃ i, d≤scaledAmplitude s j i*nativeGrowth (1/1000) lam a := by
  refine ⟨(time_iff_any_collapse hR hg (time_spec hR hg j).1 j).mpr le_rfl,?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hR hg ha j).mp hc)

theorem gate_zero {d s : ℝ} (hR : Rectangle d s) : gate d s 0 :=
  (gate_iff_window hR 0).mpr ⟨by norm_num,(endpoint_spec hR).1.le⟩

theorem time_at_zero {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    time d s j 0=threshold d s j/1000 := by
  have h := GrowthFirstRecordLive.firstTime_at_zero (by norm_num : (0:ℝ)<1/1000)
    (by norm_num) (by linarith [(threshold_bounds hR j).1]) (final_above_threshold hR (gate_zero hR) j)
  change time d s j 0=(1/1000:ℝ)*threshold d s j at h
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using h

theorem time_positive {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    0<time d s j lam := by linarith [(time_spec hR hg j).1.1]

theorem time_nonpositive_upper {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (hl : lam≤0) (j : Fin 12) : time d s j lam≤threshold d s j/1000 := by
  have h := GrowthFirstRecordLive.firstTime_nonpositive_upper (by norm_num : (0:ℝ)<1/1000)
    (by norm_num) (gate_cutoff hR hg) hl (by linarith [(threshold_bounds hR j).1]) (final_above_threshold hR hg j)
  change time d s j lam≤(1/1000:ℝ)*threshold d s j at h
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using h

theorem time_nonnegative_lower {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (hl : 0≤lam) (j : Fin 12) : threshold d s j/1000≤time d s j lam := by
  have h := GrowthFirstRecord.firstTime_lower_matter (by norm_num : (0:ℝ)<1/1000) (by norm_num)
    hl (by linarith [(threshold_bounds hR j).1]) (final_above_threshold hR hg j)
  rw [← GrowthFirstRecordLive.firstTime_eq_nonnegative (by norm_num) (by norm_num) hl
    (by linarith [(threshold_bounds hR j).1]) (final_above_threshold hR hg j)] at h
  change (1/1000:ℝ)*threshold d s j≤time d s j lam at h
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using h

theorem time_strictMono {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    StrictMonoOn (time d s j) (Ioc (-(1/8000:ℝ)) (scaledEndpoint d s)) := by
  intro l1 h1 l2 h2 h12
  have hg1 := (gate_iff_window hR l1).mpr h1
  have hg2 := (gate_iff_window hR l2).mpr h2
  exact GrowthFirstRecordLive.firstTime_strict_parameter (by norm_num) (by norm_num)
    (gate_cutoff hR hg1) h12 (by linarith [(threshold_bounds hR j).1])
    (final_above_threshold hR hg1 j) (final_above_threshold hR hg2 j)

/-- At the original scaling, the full signed first-record construction is unchanged. -/
theorem original_time_return (j : Fin 12) (lam : ℝ) :
    time WindowSample.delta 1 j lam=WindowSignedRecord.time j lam := by
  have he : threshold WindowSample.delta 1 j=WindowFirstRecord.threshold j := by
    unfold threshold factor
    rw [mul_one,div_self original_delta_positive.ne',one_mul]
  unfold time WindowSignedRecord.time
  rw [he]

end
end SbtCosmo.Derivation.WindowRobustRecord
