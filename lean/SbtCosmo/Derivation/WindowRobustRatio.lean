import SbtCosmo.Derivation.WindowRobustRecord

/-! Uniform signed-window ratio and no-pinching statements for the full declared
coupled rescaling rectangle. Endpoint bounds retain actual corner roots. -/
namespace SbtCosmo.Derivation.WindowRobustRatio
noncomputable section
open Set GrowthScaleReturn WindowSensitivity WindowRobustRecord

def minimumEndpoint : ℝ := scaledEndpoint 2 (1/3)
def maximumEndpoint : ℝ := scaledEndpoint (6/5) 3
def ratio (d s : ℝ) (j : Fin 12) (lam : ℝ) : ℝ := |lam| *(time d s j lam)^3

theorem corner_rectangles : Rectangle 2 (1/3) ∧ Rectangle (6/5) 3 := by
  norm_num [Rectangle]

theorem corner_endpoints_positive : 0<minimumEndpoint ∧ 0<maximumEndpoint :=
  ⟨(endpoint_spec corner_rectangles.1).1,(endpoint_spec corner_rectangles.2).1⟩

/-- Actual native boundary roots at the extreme rescalings, not a fitted bound. -/
theorem endpoint_corner_bounds {d s : ℝ} (hR : Rectangle d s) :
    minimumEndpoint≤scaledEndpoint d s ∧ scaledEndpoint d s≤maximumEndpoint := by
  have hc := factor_corner_bounds hR
  have hT := original_aggregate_bounds.1
  have hp : 0≤WindowSample.aggregateThreshold := by linarith
  have hlow : scaledThreshold d s≤scaledThreshold 2 (1/3) :=
    mul_le_mul_of_nonneg_right hc.2 hp
  have hhigh : scaledThreshold (6/5) 3≤scaledThreshold d s :=
    mul_le_mul_of_nonneg_right hc.1 hp
  have hm := (GrowthEndpointSensitivity.endpoint_strictAntiOn (by norm_num : (0:ℝ)<1/1000)
    (Real.log_pos (by norm_num : (1:ℝ)<20000))).antitoneOn
  have ht (d s : ℝ) (h : Rectangle d s) : scaledThreshold d s ∈
      Ioo (GrowthLimit.freeGrowth (Real.log 20000)) (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<20000)] using robustness_rectangle_admissible h.1 h.2
  exact ⟨hm (ht _ _ hR) (ht _ _ corner_rectangles.1) hlow,
    hm (ht _ _ corner_rectangles.2) (ht _ _ hR) hhigh⟩

theorem common_positive_window {d s lam : ℝ} (hR : Rectangle d s)
    (hl : lam ∈ Icc 0 minimumEndpoint) : gate d s lam :=
  (gate_iff_window hR lam).mpr
    ⟨by linarith [hl.1],hl.2.trans (endpoint_corner_bounds hR).1⟩

theorem ratio_density_readout (d s lam : ℝ) (j : Fin 12) :
    ratio d s j lam=|lam|/((time d s j lam)^3)⁻¹ := by simp only [ratio,div_inv_eq_mul]

theorem ratio_nonnegative {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (j : Fin 12) : 0≤ratio d s j lam :=
  mul_nonneg (abs_nonneg _) (pow_nonneg (time_positive hR hg j).le _)

theorem ratio_positive {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (hne : lam≠0) (j : Fin 12) : 0<ratio d s j lam :=
  mul_pos (abs_pos.mpr hne) (pow_pos (time_positive hR hg j) 3)

theorem ratio_zero (d s : ℝ) (j : Fin 12) : ratio d s j 0=0 := by simp [ratio]

theorem ratio_nonnegative_upper {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (hl : 0≤lam) (j : Fin 12) : ratio d s j lam≤8000*lam := by
  have hs := time_spec hR hg j
  have hp := pow_le_pow_left₀ (time_positive hR hg j).le hs.1.2 3
  have hm := mul_le_mul_of_nonneg_left hp hl
  simpa only [ratio,abs_of_nonneg hl] using (by nlinarith : lam*(time d s j lam)^3≤8000*lam)

theorem ratio_nonpositive_small {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam)
    (hl : lam≤0) (j : Fin 12) : ratio d s j lam<(1:ℝ)/125 := by
  have htime : time d s j lam≤4 := by
    have h := time_nonpositive_upper hR hg hl j
    linarith [(threshold_bounds hR j).2]
  have hp := pow_le_pow_left₀ (time_positive hR hg j).le htime 3
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg lam)
  have ha : |lam|<(1:ℝ)/8000 := by
    rw [abs_of_nonpos hl]
    linarith [((gate_iff_window hR lam).mp hg).1]
  unfold ratio
  have hupper : |lam| *(time d s j lam)^3≤64*|lam| := by nlinarith
  exact hupper.trans_lt (by linarith)

/-- One finite bound valid for every signed admitted parameter and every seed. -/
theorem full_window_ratios {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    0≤ratio d s j lam ∧ ratio d s j lam≤max (8000*maximumEndpoint) (1/125) := by
  refine ⟨ratio_nonnegative hR hg j,?_⟩
  by_cases hl : 0≤lam
  · have hbound := ((gate_iff_window hR lam).mp hg).2.trans (endpoint_corner_bounds hR).2
    exact (ratio_nonnegative_upper hR hg hl j).trans
      ((mul_le_mul_of_nonneg_left hbound (by norm_num)).trans (le_max_left _ _))
  · exact (ratio_nonpositive_small hR hg (le_of_not_ge hl) j).le.trans (le_max_right _ _)

/-- Uniform endpoint bounds; their actual root constants are not numerical order-unity evidence. -/
theorem endpoint_ratios {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    minimumEndpoint/1000<ratio d s j (scaledEndpoint d s) ∧
      ratio d s j (scaledEndpoint d s)≤8000*maximumEndpoint := by
  have he := endpoint_spec hR
  have hg : gate d s (scaledEndpoint d s) :=
    (gate_iff_window hR _).mpr ⟨by linarith [he.1],le_rfl⟩
  have ht : (1:ℝ)/10<time d s j (scaledEndpoint d s) := by
    have h := time_nonnegative_lower hR hg he.1.le j
    linarith [(threshold_bounds hR j).1]
  have hp := pow_lt_pow_left₀ ht (by norm_num : (0:ℝ)≤1/10) (by norm_num : 3≠0)
  have hc := endpoint_corner_bounds hR
  have hmul := mul_lt_mul_of_pos_left hp he.1
  rw [ratio,abs_of_pos he.1]
  constructor
  · have hcorner := mul_le_mul_of_nonneg_right hc.1 (by norm_num : (0:ℝ)≤(1/10)^3)
    nlinarith
  · have h := ratio_nonnegative_upper hR hg he.1.le j
    rw [ratio,abs_of_pos he.1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hc.2 (by norm_num))

/-- A single positive lambda works simultaneously for every rectangle point and seed. -/
theorem ratios_uniformly_arbitrarily_small {epsilon : ℝ} (he : 0<epsilon) :
    ∃ lam : ℝ, 0<lam ∧ lam≤minimumEndpoint ∧
      ∀ d s : ℝ, Rectangle d s → gate d s lam ∧
        ∀ j : Fin 12, 0<ratio d s j lam ∧ ratio d s j lam<epsilon := by
  let lam : ℝ := min minimumEndpoint (epsilon/16000)
  have hl : 0<lam := lt_min corner_endpoints_positive.1 (div_pos he (by norm_num))
  have hmax : lam≤minimumEndpoint := min_le_left _ _
  have hsmall : lam≤epsilon/16000 := min_le_right _ _
  refine ⟨lam,hl,hmax,?_⟩
  intro d s hR
  have hg := common_positive_window hR ⟨hl.le,hmax⟩
  refine ⟨hg,?_⟩
  intro j
  refine ⟨ratio_positive hR hg hl.ne' j,?_⟩
  have h := ratio_nonnegative_upper hR hg hl.le j
  linarith

theorem ratio_strictMono_nonnegative {d s : ℝ} (hR : Rectangle d s) (j : Fin 12) :
    StrictMonoOn (ratio d s j) (Icc 0 (scaledEndpoint d s)) := by
  intro l1 h1 l2 h2 h12
  have hg1 := (gate_iff_window hR l1).mpr ⟨by linarith [h1.1],h1.2⟩
  have hg2 := (gate_iff_window hR l2).mpr ⟨by linarith [h2.1],h2.2⟩
  have ht := (time_strictMono hR j ⟨by linarith [h1.1],h1.2⟩
    ⟨by linarith [h2.1],h2.2⟩ h12).le
  have hb := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (time_positive hR hg1 j).le ht 3) h1.1
  have hs := mul_lt_mul_of_pos_right h12 (pow_pos (time_positive hR hg2 j) 3)
  simpa only [ratio,abs_of_nonneg h1.1,abs_of_nonneg h2.1] using hb.trans_lt hs

/-- Compensating threshold/amplitude changes preserve these actual readouts exactly. -/
theorem equal_factor_return {d1 s1 d2 s2 : ℝ} (h : factor d1 s1=factor d2 s2)
    (j : Fin 12) (lam : ℝ) :
    scaledEndpoint d1 s1=scaledEndpoint d2 s2 ∧ time d1 s1 j lam=time d2 s2 j lam ∧
      ratio d1 s1 j lam=ratio d2 s2 j lam := by
  have ht : threshold d1 s1 j=threshold d2 s2 j := by unfold threshold; rw [h]
  have he : scaledThreshold d1 s1=scaledThreshold d2 s2 := congrArg (fun c => c*WindowSample.aggregateThreshold) h
  have htime : time d1 s1 j lam=time d2 s2 j lam := by unfold time; rw [ht]
  exact ⟨congrArg (GrowthEndpointSensitivity.endpoint (1/1000) (Real.log 20000)) he,
    htime,congrArg (fun a => |lam| * a^3) htime⟩

theorem original_ratio_return (j : Fin 12) (lam : ℝ) :
    ratio WindowSample.delta 1 j lam=WindowSignedRecord.ratio j lam := by
  unfold ratio WindowSignedRecord.ratio
  rw [original_time_return]

/-- Both knobs change inside the rectangle, while the original readouts persist. -/
theorem compensated_original_return :
    Rectangle (3*WindowSample.delta/4) (3/4) ∧
      ∀ (j : Fin 12) (lam : ℝ),
        time (3*WindowSample.delta/4) (3/4) j lam=WindowSignedRecord.time j lam ∧
        ratio (3*WindowSample.delta/4) (3/4) j lam=WindowSignedRecord.ratio j lam := by
  refine ⟨by norm_num [Rectangle,WindowSample.sampled_delta_exact],?_⟩
  intro j lam
  have h := equal_factor_return (d1 := 3*WindowSample.delta/4) (s1 := 3/4)
    (d2 := WindowSample.delta) (s2 := 1)
    (by norm_num [factor,WindowSample.sampled_delta_exact]) j lam
  exact ⟨h.2.1.trans (original_time_return j lam),h.2.2.trans (original_ratio_return j lam)⟩

end
end SbtCosmo.Derivation.WindowRobustRatio
