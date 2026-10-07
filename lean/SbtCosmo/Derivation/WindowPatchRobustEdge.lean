import SbtCosmo.Derivation.GrowthCombinedCertificate
import SbtCosmo.Derivation.WindowPatchRobustRegularity
import SbtCosmo.Derivation.WindowRobustRatio

/-! Explicit actual combined-sweep endpoint/first-record ratio certificates and
uniform no-pinching. Original separately realized populations and IVP retained. -/
namespace SbtCosmo.Derivation.WindowPatchRobustEdge
noncomputable section
open Set GrowthScaleReturn WindowRobustRecord WindowPatchRobust GrowthCombinedCertificate

theorem endpoint_normalized_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    (5:ℝ)/2 < upper v d s*(normalization v d s)^3 ∧ upper v d s*(normalization v d s)^3 < 7/2 := by
  let c := normalization v d s
  have hc := normalization_bounds hR v
  have hp : 0 < c := by dsimp [c]; linarith [hc.1]
  have he := endpoint_spec hR v
  have hu : -(1/(20:ℝ)^3) < upper v d s := by linarith [he.1]
  have hl : -(1/(20:ℝ)^3) < (5/2)/c^3 := by
    have hpos : (0:ℝ) < (5/2)/c^3 := by positivity
    norm_num
    linarith
  have hh : -(1/(20:ℝ)^3) < (7/2)/c^3 := by
    have hpos : (0:ℝ) < (7/2)/c^3 := by positivity
    norm_num
    linarith
  have hprefix : nativeGrowth (1/1000) ((5/2)/c^3) (4*c) ≤ nativeGrowth (1/1000) ((5/2)/c^3) 20 :=
    (GrowthFirstRecord.native_strictMonoOn (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num) hl).monotoneOn ⟨by linarith [hc.1],by linarith [hc.2]⟩ (by norm_num)
      (by linarith [hc.2])
  have hlow : aggregate v d s < nativeGrowth (1/1000) ((5/2)/c^3) 20 := by
    rw [aggregate_normalized v d s]
    exact (by nlinarith : 965*normalization v d s < 970*c).trans
      ((lower_prefix_growth hc).trans_le hprefix)
  have hhigh : nativeGrowth (1/1000) ((7/2)/c^3) 20 < aggregate v d s := by
    rw [aggregate_normalized v d s]
    exact (upper_horizon_growth hc).trans (by nlinarith)
  have hm := native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)
  have hlu : (5/2)/c^3 < upper v d s := by
    apply (hm.lt_iff_gt hu hl).mp
    rw [he.2]
    exact hlow
  have huu : upper v d s < (7/2)/c^3 := by
    apply (hm.lt_iff_gt hh hu).mp
    rw [he.2]
    exact hhigh
  exact ⟨(div_lt_iff₀ (pow_pos hp 3)).mp hlu,(lt_div_iff₀ (pow_pos hp 3)).mp huu⟩

theorem original_endpoint_return (v : Bool) :
    upper v WindowSample.delta 1 = WindowPatchCounts.upper v := by
  have hR : Rectangle WindowSample.delta 1 := by
    norm_num [Rectangle,WindowSample.sampled_delta_exact]
  have he := endpoint_spec hR v
  have ho := WindowPatchCounts.upper_spec v
  have hT : aggregate v WindowSample.delta 1 = WindowPatchCounts.aggregateThreshold v := by
    simp only [aggregate,factor,mul_one,div_self WindowSensitivity.original_delta_positive.ne',one_mul]
  rw [hT] at he
  have hcut : -(1/(20:ℝ)^3) < upper v WindowSample.delta 1 := by
    norm_num
    linarith [he.1]
  have hcut0 : -(1/(20:ℝ)^3) < WindowPatchCounts.upper v := by
    norm_num
    linarith [ho.1]
  exact (native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)).injOn hcut hcut0 (he.2.trans ho.2.1.symm)

theorem endpoint_gate {d s : ℝ} (hR : Rectangle d s) (v : Bool) : gate v d s (upper v d s) :=
  (gate_iff_window hR v _).mpr ⟨by linarith [(endpoint_spec hR v).1],le_rfl⟩

theorem time_nonnegative_lower {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (hl : 0 ≤ lam) (j : Fin 12) :
    threshold v d s j/1000 ≤ time v d s j lam := by
  have h := GrowthFirstRecord.firstTime_lower_matter (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
    hl (threshold_interior_bounds hR v j).1 (strict_final hR hg j).le
  rw [← GrowthFirstRecordLive.firstTime_eq_nonnegative (by norm_num) (by norm_num) hl
    (threshold_interior_bounds hR v j).1 (strict_final hR hg j).le] at h
  simpa only [WindowPatchRobust.time,div_eq_mul_inv,mul_comm,one_mul] using h

theorem time_nonpositive_upper {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (hl : lam ≤ 0) (j : Fin 12) :
    time v d s j lam ≤ threshold v d s j/1000 := by
  have h := GrowthFirstRecordLive.firstTime_nonpositive_upper (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) (gate_cutoff hR hg) hl (threshold_interior_bounds hR v j).1 (strict_final hR hg j).le
  simpa only [WindowPatchRobust.time,div_eq_mul_inv,mul_comm,one_mul] using h

theorem time_strictMono {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    StrictMonoOn (time v d s j) (Ioc (-(1/8000:ℝ)) (upper v d s)) := by
  intro l1 h1 l2 h2 h12
  have hg1 := (gate_iff_window hR v l1).mpr h1
  have hg2 := (gate_iff_window hR v l2).mpr h2
  exact GrowthFirstRecordLive.firstTime_strict_parameter (by norm_num) (by norm_num)
    (gate_cutoff hR hg1) h12 (threshold_interior_bounds hR v j).1
    (strict_final hR hg1 j).le (strict_final hR hg2 j).le

theorem endpoint_time_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    (9/20:ℝ)*normalization v d s < time v d s j (upper v d s) ∧
      time v d s j (upper v d s) ≤ (8/3)*normalization v d s := by
  let c := normalization v d s
  have hc := normalization_bounds hR v
  have hp : 0 < c := by dsimp [c]; linarith [hc.1]
  have hu := (endpoint_spec hR v).1
  have hg := endpoint_gate hR v
  have hlower := time_nonnegative_lower hR hg hu.le j
  have hnorm := endpoint_normalized_bounds hR v
  have hparam : upper v d s < (7/2)/c^3 := (lt_div_iff₀ (pow_pos hp 3)).mpr hnorm.2
  have hA : (8/3)*c ∈ Icc (1/1000) 20 := ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hcutu : -(1/(((8/3)*c)^3)) < upper v d s := by
    have hn : -(1/(((8/3)*c)^3)) < (0:ℝ) := neg_neg_of_pos (div_pos (by norm_num) (by positivity))
    exact hn.trans hu
  have hcuthi : -(1/(((8/3)*c)^3)) < (7/2)/c^3 := by
    have hn : -(1/(((8/3)*c)^3)) < (0:ℝ) := neg_neg_of_pos (div_pos (by norm_num) (by positivity))
    exact hn.trans (by positivity)
  have henergy := (native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by linarith [hc.1] : (1/1000:ℝ) < (8/3)*c)).antitoneOn hcutu hcuthi hparam.le
  have hthreshold := (threshold_bounds hR v j).2
  have hD : threshold v d s j ≤ nativeGrowth (1/1000) (upper v d s) ((8/3)*c) :=
    hthreshold.le.trans ((upper_prefix_growth hc).le.trans henergy)
  constructor
  · linarith [(threshold_bounds hR v j).1]
  · exact (GrowthFirstRecordLive.firstTime_iff_threshold (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num) (gate_cutoff hR hg) (threshold_interior_bounds hR v j).1 (strict_final hR hg j).le hA).mp hD

theorem endpoint_ratios {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    (3645:ℝ)/16000 < ratio v d s j (upper v d s) ∧ ratio v d s j (upper v d s) < 1792/27 := by
  have hc := normalization_bounds hR v
  have hp : 0 < normalization v d s := by linarith [hc.1]
  have hu := (endpoint_spec hR v).1
  have ht := endpoint_time_bounds hR v j
  have hn := endpoint_normalized_bounds hR v
  have htpos := time_positive hR (endpoint_gate hR v) j
  have hlo := pow_lt_pow_left₀ ht.1 (by positivity : (0:ℝ) ≤ (9/20)*normalization v d s)
    (by norm_num : 3 ≠ 0)
  have hhi := pow_le_pow_left₀ htpos.le ht.2 3
  have hmullo := mul_lt_mul_of_pos_left hlo hu
  have hmulhi := mul_le_mul_of_nonneg_left hhi hu.le
  rw [ratio,abs_of_pos hu]
  constructor <;> nlinarith

theorem ratio_nonnegative {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) : 0 ≤ ratio v d s j lam :=
  mul_nonneg (abs_nonneg _) (pow_nonneg (time_positive hR hg j).le _)

theorem ratio_positive {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (hl : lam ≠ 0) (j : Fin 12) : 0 < ratio v d s j lam :=
  mul_pos (abs_pos.mpr hl) (pow_pos (time_positive hR hg j) 3)

theorem ratio_nonnegative_upper {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (hl : 0 ≤ lam) (j : Fin 12) :
    ratio v d s j lam ≤ 8000*lam := by
  have hp := pow_le_pow_left₀ (time_positive hR hg j).le (time_spec hR hg j).1.2 3
  have hm := mul_le_mul_of_nonneg_left hp hl
  rw [ratio,abs_of_nonneg hl]
  nlinarith

theorem ratio_nonpositive_small {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (hl : lam ≤ 0) (j : Fin 12) :
    ratio v d s j lam < (1:ℝ)/64 := by
  have ht : time v d s j lam ≤ 5 := by
    have hb := time_nonpositive_upper hR hg hl j
    linarith [(threshold_bounds hR v j).2,(normalization_bounds hR v).2]
  have hp := pow_le_pow_left₀ (time_positive hR hg j).le ht 3
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg lam)
  have ha : |lam| < (1:ℝ)/8000 := by
    rw [abs_of_nonpos hl]
    linarith [((gate_iff_window hR v lam).mp hg).1]
  unfold ratio
  nlinarith

theorem ratio_strictMono_nonnegative {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    StrictMonoOn (ratio v d s j) (Icc 0 (upper v d s)) := by
  intro l1 h1 l2 h2 h12
  have hg1 := (gate_iff_window hR v l1).mpr ⟨by linarith [h1.1],h1.2⟩
  have hg2 := (gate_iff_window hR v l2).mpr ⟨by linarith [h2.1],h2.2⟩
  have ht := (time_strictMono hR v j ⟨by linarith [h1.1],h1.2⟩ ⟨by linarith [h2.1],h2.2⟩ h12).le
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (time_positive hR hg1 j).le ht 3) h1.1
  have hs := mul_lt_mul_of_pos_right h12 (pow_pos (time_positive hR hg2 j) 3)
  simpa only [ratio,abs_of_nonneg h1.1,abs_of_nonneg h2.1] using hb.trans_lt hs

theorem full_window_ratios {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) :
    0 ≤ ratio v d s j lam ∧ ratio v d s j lam < 1792/27 := by
  refine ⟨ratio_nonnegative hR hg j,?_⟩
  by_cases hl : 0 ≤ lam
  · have hu := (endpoint_spec hR v).1
    exact ((ratio_strictMono_nonnegative hR v j).monotoneOn
      ⟨hl,((gate_iff_window hR v lam).mp hg).2⟩ ⟨hu.le,le_rfl⟩
      ((gate_iff_window hR v lam).mp hg).2).trans_lt (endpoint_ratios hR v j).2
  · exact (ratio_nonpositive_small hR hg (le_of_not_ge hl) j).trans (by norm_num)

def minimumEndpoint : ℝ := upper false 2 (1/3)
def maximumEndpoint : ℝ := upper true (6/5) 3

theorem corner_rectangles : Rectangle 2 (1/3) ∧ Rectangle (6/5) 3 := by norm_num [Rectangle]

theorem endpoint_corner_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    upper v 2 (1/3) ≤ upper v d s ∧ upper v d s ≤ upper v (6/5) 3 := by
  have hc := factor_corner_bounds hR
  have hp : 0 ≤ WindowPatchCounts.aggregateThreshold v :=
    (by linarith [(WindowPatchCounts.sampled_threshold_bounds v).1])
  have hl : aggregate v d s ≤ aggregate v 2 (1/3) := mul_le_mul_of_nonneg_right hc.2 hp
  have hh : aggregate v (6/5) 3 ≤ aggregate v d s := mul_le_mul_of_nonneg_right hc.1 hp
  have ht (d s : ℝ) (h : Rectangle d s) : aggregate v d s ∈
      Ioo (GrowthLimit.freeGrowth (Real.log 20000)) (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 20000)] using aggregate_admissible h v
  have hm := (GrowthEndpointSensitivity.endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (Real.log_pos (by norm_num : (1:ℝ) < 20000))).antitoneOn
  exact ⟨hm (ht _ _ hR) (ht _ _ corner_rectangles.1) hl,
    hm (ht _ _ corner_rectangles.2) (ht _ _ hR) hh⟩

theorem common_corner_bounds {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    minimumEndpoint ≤ upper v d s ∧ upper v d s ≤ maximumEndpoint := by
  have hc := endpoint_corner_bounds hR v
  have hlo := endpoint_order corner_rectangles.1
  have hhi := endpoint_order corner_rectangles.2
  cases v
  · exact ⟨hc.1,hc.2.trans (hhi.1.trans hhi.2).le⟩
  · exact ⟨(hlo.1.trans hlo.2).le.trans hc.1,hc.2⟩

theorem common_positive_window {d s lam : ℝ} (hR : Rectangle d s)
    (hl : lam ∈ Icc 0 minimumEndpoint) (v : Bool) : gate v d s lam :=
  (gate_iff_window hR v lam).mpr ⟨by linarith [hl.1],hl.2.trans (common_corner_bounds hR v).1⟩

/-- One positive parameter works for all combined points, both populations and every seed. -/
theorem ratios_uniformly_arbitrarily_small {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ minimumEndpoint ∧
      ∀ d s : ℝ, Rectangle d s → ∀ v : Bool, gate v d s lam ∧
        ∀ j : Fin 12, 0 < ratio v d s j lam ∧ ratio v d s j lam < epsilon := by
  have hp : 0 < minimumEndpoint := (endpoint_spec corner_rectangles.1 false).1
  let lam := min minimumEndpoint (epsilon/16000)
  have hl : 0 < lam := lt_min hp (div_pos he (by norm_num))
  have hmax : lam ≤ minimumEndpoint := min_le_left _ _
  have hsmall : lam ≤ epsilon/16000 := min_le_right _ _
  refine ⟨lam,hl,hmax,?_⟩
  intro d s hR v
  have hg := common_positive_window hR ⟨hl.le,hmax⟩ v
  refine ⟨hg,?_⟩
  intro j
  exact ⟨ratio_positive hR hg hl.ne' j,by linarith [ratio_nonnegative_upper hR hg hl.le j]⟩

/-- The very same parameter also works for the unchanged N64 population. -/
theorem all_populations_uniformly_arbitrarily_small {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ d s : ℝ, Rectangle d s →
      (∀ v : Bool, gate v d s lam ∧ ∀ j : Fin 12, 0 < ratio v d s j lam ∧ ratio v d s j lam < epsilon) ∧
      WindowRobustRecord.gate d s lam ∧
        ∀ j : Fin 12, 0 < WindowRobustRatio.ratio d s j lam ∧ WindowRobustRatio.ratio d s j lam < epsilon := by
  have hp : 0 < minimumEndpoint := (endpoint_spec corner_rectangles.1 false).1
  let lam := min minimumEndpoint (epsilon/16000)
  have hl : 0 < lam := lt_min hp (div_pos he (by norm_num))
  have hmax : lam ≤ minimumEndpoint := min_le_left _ _
  have hsmall : lam ≤ epsilon/16000 := min_le_right _ _
  refine ⟨lam,hl,?_⟩
  intro d s hR
  have hg (v : Bool) := common_positive_window hR ⟨hl.le,hmax⟩ v
  have hg64 := (gate_inclusions hR lam).1 (hg false)
  refine ⟨fun v => ⟨hg v,fun j => ⟨ratio_positive hR (hg v) hl.ne' j,
    by linarith [ratio_nonnegative_upper hR (hg v) hl.le j]⟩⟩,hg64,?_⟩
  intro j
  exact ⟨WindowRobustRatio.ratio_positive hR hg64 hl.ne' j,
    by linarith [WindowRobustRatio.ratio_nonnegative_upper hR hg64 hl.le j]⟩

end
end SbtCosmo.Derivation.WindowPatchRobustEdge
