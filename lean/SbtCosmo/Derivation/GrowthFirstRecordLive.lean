import SbtCosmo.Derivation.GrowthFirstRecord

/-! First-threshold construction on the full live native parameter domain. -/
namespace SbtCosmo.Derivation.GrowthFirstRecordLive
noncomputable section
open Set GrowthComparison GrowthExistence GrowthScaleReturn
attribute [local instance] Classical.propDecidable

theorem native_initial {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) : nativeGrowth a0 lam a0 = 1 := by
  have hL := horizon_log_nonneg ha0 hA
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le hA)) hlam
  have hs := constructed_growthSolution hL hl
  simpa [nativeGrowth, logScale] using hs.growth_initial

theorem exists_unique_first_time {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A) :
    ∃! a : ℝ, a ∈ Icc a0 A ∧ nativeGrowth a0 lam a = T := by
  have hc : ContinuousOn (nativeGrowth a0 lam) (Icc a0 A) :=
    fun _ hx => (native_growth_derivative ha0 hA hlam hx).continuousAt.continuousWithinAt
  have hi : T ∈ Icc (nativeGrowth a0 lam a0) (nativeGrowth a0 lam A) :=
    ⟨(native_initial ha0 hA hlam) ▸ hT.le, hfinal⟩
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc hA hc hi
  refine ⟨a, ⟨ha, he⟩, ?_⟩
  intro b hb
  exact (GrowthFirstRecord.native_strictMonoOn ha0 hA hlam).injOn hb.1 ha (hb.2.trans he.symm)

def firstTime (a0 A T lam : ℝ) : ℝ :=
  if h : 0 < a0 ∧ a0 ≤ A ∧ -(1 / A^3) < lam ∧ 1 < T ∧ T ≤ nativeGrowth a0 lam A then
    (exists_unique_first_time h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose
  else a0

theorem firstTime_spec {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A) :
    firstTime a0 A T lam ∈ Icc a0 A ∧ nativeGrowth a0 lam (firstTime a0 A T lam) = T := by
  have h : 0 < a0 ∧ a0 ≤ A ∧ -(1 / A^3) < lam ∧ 1 < T ∧ T ≤ nativeGrowth a0 lam A :=
    ⟨ha0, hA, hlam, hT, hfinal⟩
  simp only [firstTime, dif_pos h]
  exact (exists_unique_first_time ha0 hA hlam hT hfinal).choose_spec.1

theorem firstTime_iff_threshold {a0 A lam T a : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A)
    (ha : a ∈ Icc a0 A) : T ≤ nativeGrowth a0 lam a ↔ firstTime a0 A T lam ≤ a := by
  have hs := firstTime_spec ha0 hA hlam hT hfinal
  have h := (GrowthFirstRecord.native_strictMonoOn ha0 hA hlam).le_iff_le hs.1 ha
  rw [hs.2] at h
  exact h

theorem firstTime_eq_nonnegative {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A) :
    firstTime a0 A T lam = GrowthFirstRecord.firstTime a0 A T lam := by
  have hcut : -(1 / A^3) < lam :=
    (neg_neg_of_pos (div_pos (by norm_num) (pow_pos (ha0.trans_le hA) 3))).trans_le hlam
  have hs := firstTime_spec ha0 hA hcut hT hfinal
  have ho := GrowthFirstRecord.firstTime_spec ha0 hA hlam hT hfinal
  exact (GrowthFirstRecord.native_strictMonoOn ha0 hA hcut).injOn hs.1 ho.1 (hs.2.trans ho.2.symm)

theorem native_matter_at_zero {a0 a : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a) :
    nativeGrowth a0 0 a = a / a0 := by
  have h := finalGrowth_at_zero a0 (horizon_log_nonneg ha0 ha)
  simpa [nativeGrowth, finalGrowth, logScale, Real.exp_log (div_pos (ha0.trans_le ha) ha0)] using h

/-- Nonpositive live lambda grows at least as much as the finite-start matter IVP. -/
theorem native_matter_lower {a0 A lam a : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hnonpos : lam ≤ 0) (ha : a ∈ Icc a0 A) :
    a / a0 ≤ nativeGrowth a0 lam a := by
  by_cases he : a = a0
  · subst a
    rw [native_initial ha0 hA hlam, div_self ha0.ne']
  have hap : a0 < a := lt_of_le_of_ne ha.1 (Ne.symm he)
  have hcut : -(1 / a^3) < lam :=
    (WindowRecords.negative_horizon_tightens (ha0.trans hap) ha.2).trans_lt hlam
  have hzero : -(1 / a^3) < (0 : ℝ) :=
    neg_neg_of_pos (div_pos (by norm_num) (pow_pos (ha0.trans hap) 3))
  have hg := (native_endpoint_strictAntiOn ha0 hap).antitoneOn hcut hzero hnonpos
  rw [native_matter_at_zero ha0 ha.1] at hg
  exact hg

theorem firstTime_nonpositive_upper {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hnonpos : lam ≤ 0) (hT : 1 < T)
    (hfinal : T ≤ nativeGrowth a0 lam A) : firstTime a0 A T lam ≤ a0 * T := by
  have hs := firstTime_spec ha0 hA hlam hT hfinal
  have hm := native_matter_lower ha0 hA hlam hnonpos hs.1
  rw [hs.2] at hm
  have h := (div_le_iff₀ ha0).mp hm
  simpa [mul_comm] using h

theorem firstTime_at_zero {a0 A T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 0 A) : firstTime a0 A T 0 = a0 * T := by
  have hcut : -(1 / A^3) < (0 : ℝ) :=
    neg_neg_of_pos (div_pos (by norm_num) (pow_pos (ha0.trans_le hA) 3))
  have hs := firstTime_spec ha0 hA hcut hT hfinal
  rw [native_matter_at_zero ha0 hA] at hfinal
  have ht : a0 * T ∈ Icc a0 A := ⟨by nlinarith, by
    have h := (le_div_iff₀ ha0).mp hfinal
    nlinarith⟩
  have he : nativeGrowth a0 0 (a0 * T) = T := by
    rw [native_matter_at_zero ha0 ht.1]
    field_simp
  exact (GrowthFirstRecord.native_strictMonoOn ha0 hA hcut).injOn hs.1 ht (hs.2.trans he.symm)

theorem firstTime_strict_parameter {a0 A T lam1 lam2 : ℝ} (ha0 : 0 < a0)
    (hA : a0 < A) (h1 : -(1 / A^3) < lam1) (h12 : lam1 < lam2) (hT : 1 < T)
    (hf1 : T ≤ nativeGrowth a0 lam1 A) (hf2 : T ≤ nativeGrowth a0 lam2 A) :
    firstTime a0 A T lam1 < firstTime a0 A T lam2 := by
  have h2 := h1.trans h12
  have hs1 := firstTime_spec ha0 hA.le h1 hT hf1
  have hs2 := firstTime_spec ha0 hA.le h2 hT hf2
  have ha2 : a0 < firstTime a0 A T lam2 := by
    by_contra hn
    have he := le_antisymm (le_of_not_gt hn) hs2.1.1
    rw [he, native_initial ha0 hA.le h2] at hs2
    linarith [hs2.2]
  have hc1 : -(1 / (firstTime a0 A T lam2)^3) < lam1 :=
    (WindowRecords.negative_horizon_tightens (ha0.trans ha2) hs2.1.2).trans_lt h1
  have hc2 := hc1.trans h12
  have hg := native_endpoint_strictAntiOn ha0 ha2 hc1 hc2 h12
  dsimp only at hg
  rw [hs2.2] at hg
  have hg' : nativeGrowth a0 lam1 (firstTime a0 A T lam1) <
      nativeGrowth a0 lam1 (firstTime a0 A T lam2) := by rw [hs1.2]; exact hg
  exact (GrowthFirstRecord.native_strictMonoOn ha0 hA.le h1).lt_iff_lt hs1.1 hs2.1 |>.mp hg'

end
end SbtCosmo.Derivation.GrowthFirstRecordLive
