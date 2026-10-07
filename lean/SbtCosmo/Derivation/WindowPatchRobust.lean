import SbtCosmo.Derivation.WindowPatchCountRatio
import SbtCosmo.Derivation.GrowthPopulationSensitivity
import SbtCosmo.Derivation.GrowthEndpointDerivative

/-! Actual N32/N128 populations throughout the original coupled parameter
rectangle. Populations remain separately realized; only amplitudes are scaled. -/
namespace SbtCosmo.Derivation.WindowPatchRobust
noncomputable section
open Set GrowthScaleReturn GrowthLimit GrowthEndpointSensitivity WindowRobustRecord
attribute [local instance] Classical.propDecidable

def scaledAmplitude (v : Bool) (s : ℝ) (j : Fin 12) (i : Fin (WindowPatchCountData.patchCount v)) : ℝ :=
  s * WindowPatchCounts.amplitude v j i
def aggregate (v : Bool) (d s : ℝ) : ℝ := factor d s * WindowPatchCounts.aggregateThreshold v
def upper (v : Bool) (d s : ℝ) : ℝ := endpoint (1/1000) (Real.log 20000) (aggregate v d s)
def gate (v : Bool) (d s lam : ℝ) : Prop :=
  GrowthPopulation.nativeAggregate (scaledAmplitude v s) (WindowPatchCountData.tag v) (1/1000) 20 d 10 lam
def normalization (v : Bool) (d s : ℝ) : ℝ := factor d s * WindowPatchCountRatio.scale v
def threshold (v : Bool) (d s : ℝ) (j : Fin 12) : ℝ := factor d s * WindowPatchCountRatio.threshold v j
def time (v : Bool) (d s : ℝ) (j : Fin 12) (lam : ℝ) : ℝ :=
  GrowthFirstRecordLive.firstTime (1/1000) 20 (threshold v d s j) lam
def ratio (v : Bool) (d s : ℝ) (j : Fin 12) (lam : ℝ) : ℝ := |lam| * (time v d s j lam)^3

theorem original_aggregate_return (v : Bool) :
    GrowthPopulationSensitivity.aggregateThreshold (WindowPatchCounts.amplitude v)
      (WindowPatchCountData.tag v) WindowSample.delta 10 = WindowPatchCounts.aggregateThreshold v := by
  have hm (j : Fin 12) (b : Bool) :
      GrowthPopulationSensitivity.tagMaximumValue (WindowPatchCounts.amplitude v j)
        (WindowPatchCountData.tag v j) b =
      if b then WindowPatchCounts.maximumTrue v j else WindowPatchCounts.maximumFalse v j := by
    cases b
    · exact GrowthPopulationSensitivity.tagMaximumValue_eq_of_maximum
        (WindowPatchCounts.sampled_maxima v j).2.2.2.1
    · exact GrowthPopulationSensitivity.tagMaximumValue_eq_of_maximum
        (WindowPatchCounts.sampled_maxima v j).2.2.2.2
  have he : GrowthPopulationSensitivity.seedThresholds (WindowPatchCounts.amplitude v)
      (WindowPatchCountData.tag v) WindowSample.delta = WindowPatchCounts.seedThreshold v := by
    funext j
    simp only [GrowthPopulationSensitivity.seedThresholds,hm,Bool.false_eq_true,if_false,if_true,
      WindowPatchCounts.seedThreshold_eq]
    rfl
  rw [GrowthPopulationSensitivity.aggregateThreshold,he]
  apply GrowthRankSensitivity.rankThreshold_eq_of_certificate (by norm_num) (by norm_num)
  · rw [(WindowPatchCounts.sampled_rank_counts v).1]
    norm_num
  · exact (WindowPatchCounts.sampled_rank_counts v).2.ge

theorem scaled_aggregate_return {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (v : Bool) :
    GrowthPopulationSensitivity.aggregateThreshold (scaledAmplitude v s)
      (WindowPatchCountData.tag v) d 10 = aggregate v d s := by
  have hdelta := GrowthPopulationSensitivity.aggregateThreshold_delta_mul_pos
    (WindowPatchCounts.amplitude v) (WindowPatchCountData.tag v) WindowSample.delta
    (by norm_num : 0 < 10) (by norm_num) (div_pos hd WindowSensitivity.original_delta_positive)
  rw [div_mul_cancel₀ d WindowSensitivity.original_delta_positive.ne'] at hdelta
  unfold scaledAmplitude
  rw [GrowthPopulationSensitivity.aggregateThreshold_amplitude_mul_pos _ _ _
    (by norm_num : 0 < 10) (by norm_num) hs,hdelta,original_aggregate_return]
  unfold aggregate factor
  field_simp

theorem original_scale_bounds (v : Bool) :
    (83:ℝ)/100 < WindowPatchCountRatio.scale v ∧ WindowPatchCountRatio.scale v < 131/100 := by
  cases v
  · exact ⟨by linarith [WindowPatchCountRatio.scale_tight.1],WindowPatchCountRatio.scale_tight.2.1⟩
  · exact ⟨WindowPatchCountRatio.scale_tight.2.2.1,by linarith [WindowPatchCountRatio.scale_tight.2.2.2]⟩

/-- This broader combined range is earned from original exact corner values. -/
theorem normalization_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    normalization v d s ∈ Ioo (1/6) 5 := by
  have hf := factor_corner_bounds hR
  have hc := original_scale_bounds v
  have hlo := (mul_lt_mul_of_pos_left hc.1
    (show 0 < factor (6/5) 3 by norm_num [factor,WindowSample.sampled_delta_exact])).trans_le
    (mul_le_mul_of_nonneg_right hf.1 (by linarith [hc.1]))
  have hhi := (mul_lt_mul_of_pos_left hc.2 (factor_positive hR)).trans_le
    (mul_le_mul_of_nonneg_right hf.2 (by norm_num : (0:ℝ) ≤ 131/100))
  norm_num [factor,WindowSample.sampled_delta_exact] at hlo hhi
  unfold normalization factor
  rw [WindowSample.sampled_delta_exact]
  constructor <;> linarith

/-- Both sides of the old (1/5,4) estimate fail to cover actual combined corners. -/
theorem normalization_outside_old_range :
    4 < normalization false 2 (1/3) ∧ normalization true (6/5) 3 < (1:ℝ)/5 := by
  unfold normalization factor
  rw [WindowSample.sampled_delta_exact]
  norm_num
  constructor
  · linarith [WindowPatchCountRatio.scale_tight.1]
  · linarith [WindowPatchCountRatio.scale_tight.2.2.2]

theorem aggregate_normalized (v : Bool) (d s : ℝ) :
    aggregate v d s = 965*normalization v d s := by
  unfold aggregate normalization
  rw [WindowPatchCountRatio.aggregate_normalized]
  ring

theorem aggregate_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    (160:ℝ) < aggregate v d s ∧ aggregate v d s < 4825 := by
  rw [aggregate_normalized]
  have hc := normalization_bounds hR v
  constructor <;> linarith [hc.1,hc.2]

theorem aggregate_admissible {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    aggregate v d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000 := by
  have hb := aggregate_bounds hR v
  unfold freeGrowth
  have he := Real.exp_pos (-2*Real.log (20000:ℝ))
  constructor <;> linarith

theorem endpoint_native_window {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    0 < upper v d s ∧ nativeGrowth (1/1000) (upper v d s) 20 = aggregate v d s ∧
      ∀ lam, gate v d s lam ↔ -(1/8000:ℝ) < lam ∧ lam ≤ upper v d s := by
  have hd := (rectangle_positive hR).1
  have hs := (rectangle_positive hR).2
  have hpatch : ∀ (j : Fin 12) (b : Bool), ∃ i, WindowPatchCountData.tag v j i = b ∧
      0 < scaledAmplitude v s j i := by
    intro j b
    cases b
    · obtain ⟨i,hi,he⟩ := (WindowPatchCounts.sampled_maxima v j).2.2.2.1.attained
      exact ⟨i,hi,mul_pos hs (he ▸ (WindowPatchCounts.sampled_maxima v j).2.1)⟩
    · obtain ⟨i,hi,he⟩ := (WindowPatchCounts.sampled_maxima v j).2.2.2.2.attained
      exact ⟨i,hi,mul_pos hs (he ▸ (WindowPatchCounts.sampled_maxima v j).2.2.1)⟩
  have hratio : (20:ℝ)/(1/1000) = 20000 := by norm_num
  have hw := GrowthPopulationSensitivity.populationEndpoint_native_window
    (scaledAmplitude v s) (WindowPatchCountData.tag v) (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20) (by norm_num : 0 < 10) (by norm_num)
    (fun j i => mul_nonneg hs.le ((WindowPatchCounts.sampled_maxima v j).1 i))
    (delta := d) hpatch (by simpa only [scaled_aggregate_return hd hs v,hratio] using aggregate_admissible hR v)
  norm_num [GrowthPopulationSensitivity.populationEndpoint,scaled_aggregate_return hd hs v,
    hratio,upper,gate] at hw ⊢
  exact hw

theorem endpoint_spec {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    0 < upper v d s ∧ nativeGrowth (1/1000) (upper v d s) 20 = aggregate v d s :=
  ⟨(endpoint_native_window hR v).1,(endpoint_native_window hR v).2.1⟩

theorem gate_iff_window {d s : ℝ} (hR : Rectangle d s) (v : Bool) (lam : ℝ) :
    gate v d s lam ↔ lam ∈ Ioc (-(1/8000:ℝ)) (upper v d s) :=
  (endpoint_native_window hR v).2.2 lam

theorem gate_cutoff {v : Bool} {d s lam : ℝ} (hR : Rectangle d s) (hg : gate v d s lam) :
    -(1/(20:ℝ)^3) < lam := by
  have hl := ((gate_iff_window hR v lam).mp hg).1
  norm_num at hl ⊢
  exact hl

theorem gate_zero {d s : ℝ} (hR : Rectangle d s) (v : Bool) : gate v d s 0 :=
  (gate_iff_window hR v 0).mpr ⟨by norm_num,(endpoint_spec hR v).1.le⟩

theorem threshold_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    450*normalization v d s < threshold v d s j ∧ threshold v d s j < 897*normalization v d s := by
  have hf := factor_positive hR
  have ht := WindowPatchCountRatio.threshold_bounds v j
  unfold normalization threshold
  constructor
  · nlinarith [mul_lt_mul_of_pos_left ht.2.2.1 hf]
  · nlinarith [mul_lt_mul_of_pos_left ht.2.2.2 hf]

theorem threshold_interior_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    1 < threshold v d s j ∧ threshold v d s j < aggregate v d s := by
  have ht := threshold_bounds hR v j
  have hc := normalization_bounds hR v
  rw [aggregate_normalized]
  constructor <;> linarith [ht.1,ht.2,hc.1]

theorem strict_final {v : Bool} {d s lam : ℝ} (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) :
    threshold v d s j < nativeGrowth (1/1000) lam 20 := by
  have he := endpoint_spec hR v
  have hw := (gate_iff_window hR v lam).mp hg
  have hm := (native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)).antitoneOn (gate_cutoff hR hg)
      (show -(1/(20:ℝ)^3) < upper v d s by linarith [he.1]) hw.2
  rw [he.2] at hm
  exact (threshold_interior_bounds hR v j).2.trans_le hm

theorem time_spec {v : Bool} {d s lam : ℝ} (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) :
    time v d s j lam ∈ Icc (1/1000) 20 ∧ nativeGrowth (1/1000) lam (time v d s j lam) = threshold v d s j :=
  GrowthFirstRecordLive.firstTime_spec (by norm_num) (by norm_num) (gate_cutoff hR hg)
    (threshold_interior_bounds hR v j).1 (strict_final hR hg j).le

theorem maximum_spec {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    0 < s*WindowPatchCountRatio.maximum v j ∧
      (∀ i, scaledAmplitude v s j i ≤ s*WindowPatchCountRatio.maximum v j) ∧
      ∃ i, scaledAmplitude v s j i = s*WindowPatchCountRatio.maximum v j := by
  have hs := (rectangle_positive hR).2
  obtain ⟨hp,hb,i,he⟩ := WindowPatchCountRatio.maximum_spec v j
  exact ⟨mul_pos hs hp,fun i => mul_le_mul_of_nonneg_left (hb i) hs.le,
    i,congrArg (fun x : ℝ => s*x) he⟩

theorem threshold_return (v : Bool) (d s : ℝ) (j : Fin 12) :
    d/(s*WindowPatchCountRatio.maximum v j) = threshold v d s j := by
  unfold threshold factor WindowPatchCountRatio.threshold
  change d/(s*WindowPatchCountRatio.maximum v j) =
    d/(WindowSample.delta*s)*(WindowSample.delta/WindowPatchCountRatio.maximum v j)
  field_simp [WindowSensitivity.original_delta_positive.ne']

theorem time_iff_any_collapse {v : Bool} {d s lam a : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (ha : a ∈ Icc (1/1000) 20) (j : Fin 12) :
    (∃ i, d ≤ scaledAmplitude v s j i*nativeGrowth (1/1000) lam a) ↔ time v d s j lam ≤ a := by
  have hm := maximum_spec hR v j
  have hc := GrowthFirstRecord.any_patch_collapse_iff hm.1
    (native_positive (by norm_num : (0:ℝ) < 1/1000) (by norm_num) (gate_cutoff hR hg) a ha).1.le hm.2.1 hm.2.2 (δ := d)
  rw [threshold_return] at hc
  exact hc.trans (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num) (by norm_num)
    (gate_cutoff hR hg) (threshold_interior_bounds hR v j).1 (strict_final hR hg j).le ha)

theorem time_is_first_collapse {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) :
    (∃ i, d ≤ scaledAmplitude v s j i*nativeGrowth (1/1000) lam (time v d s j lam)) ∧
      ∀ a ∈ Icc (1/1000) 20, a < time v d s j lam →
        ¬ ∃ i, d ≤ scaledAmplitude v s j i*nativeGrowth (1/1000) lam a := by
  refine ⟨(time_iff_any_collapse hR hg (time_spec hR hg j).1 j).mpr le_rfl,?_⟩
  intro a ha hlt hc
  exact hlt.not_ge ((time_iff_any_collapse hR hg ha j).mp hc)

theorem time_positive {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) : 0 < time v d s j lam := by
  linarith [(time_spec hR hg j).1.1]

theorem original_gate_return (v : Bool) (lam : ℝ) :
    gate v WindowSample.delta 1 lam ↔ WindowPatchCounts.realizedGate v lam := by
  have he : scaledAmplitude v 1 = WindowPatchCounts.amplitude v := by
    funext j i
    simp only [scaledAmplitude,one_mul]
  rw [gate,he]
  rfl

theorem original_time_return (v : Bool) (j : Fin 12) (lam : ℝ) :
    time v WindowSample.delta 1 j lam = WindowPatchCountRatio.time v j lam := by
  simp only [time,threshold,factor,mul_one,div_self WindowSensitivity.original_delta_positive.ne',one_mul]
  rfl

theorem original_ratio_return (v : Bool) (j : Fin 12) (lam : ℝ) :
    ratio v WindowSample.delta 1 j lam = WindowPatchCountRatio.ratio v j lam := by
  unfold ratio WindowPatchCountRatio.ratio
  rw [original_time_return]

theorem endpoint_order {d s : ℝ} (hR : Rectangle d s) :
    upper false d s < WindowSensitivity.scaledEndpoint d s ∧
      WindowSensitivity.scaledEndpoint d s < upper true d s := by
  have h32 := endpoint_spec hR false
  have h64 := WindowRobustRecord.endpoint_spec hR
  have h128 := endpoint_spec hR true
  have hm := native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)
  have hcut32 : -(1/(20:ℝ)^3) < upper false d s := by linarith [h32.1]
  have hcut64 : -(1/(20:ℝ)^3) < WindowSensitivity.scaledEndpoint d s := by linarith [h64.1]
  have hcut128 : -(1/(20:ℝ)^3) < upper true d s := by linarith [h128.1]
  constructor
  · apply (hm.lt_iff_gt hcut64 hcut32).mp
    rw [h32.2,h64.2]
    exact mul_lt_mul_of_pos_left WindowPatchCounts.threshold_order.2 (factor_positive hR)
  · apply (hm.lt_iff_gt hcut128 hcut64).mp
    rw [h128.2,h64.2]
    exact mul_lt_mul_of_pos_left WindowPatchCounts.threshold_order.1 (factor_positive hR)

theorem gate_inclusions {d s : ℝ} (hR : Rectangle d s) (lam : ℝ) :
    (gate false d s lam → WindowRobustRecord.gate d s lam) ∧
      (WindowRobustRecord.gate d s lam → gate true d s lam) := by
  rw [gate_iff_window hR false,WindowRobustRecord.gate_iff_window hR,gate_iff_window hR true]
  exact ⟨fun h => ⟨h.1,h.2.trans (endpoint_order hR).1.le⟩,
    fun h => ⟨h.1,h.2.trans (endpoint_order hR).2.le⟩⟩

theorem strict_gate_witnesses {d s : ℝ} (hR : Rectangle d s) :
    (WindowRobustRecord.gate d s (WindowSensitivity.scaledEndpoint d s) ∧
      ¬ gate false d s (WindowSensitivity.scaledEndpoint d s)) ∧
    (gate true d s (upper true d s) ∧ ¬ WindowRobustRecord.gate d s (upper true d s)) := by
  rw [WindowRobustRecord.gate_iff_window hR,gate_iff_window hR false,
    gate_iff_window hR true,WindowRobustRecord.gate_iff_window hR]
  exact ⟨⟨⟨by linarith [(WindowRobustRecord.endpoint_spec hR).1],le_rfl⟩,
    fun h => (endpoint_order hR).1.not_ge h.2⟩,
    ⟨⟨by linarith [(endpoint_spec hR true).1],le_rfl⟩,
    fun h => (endpoint_order hR).2.not_ge h.2⟩⟩

end
end SbtCosmo.Derivation.WindowPatchRobust
