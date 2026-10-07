import SbtCosmo.Derivation.GrowthWindow

/-! Constructed first-threshold times in the original native scale interval. -/
namespace SbtCosmo.Derivation.GrowthFirstRecord
noncomputable section
open Set GrowthComparison GrowthExistence GrowthScaleReturn GrowthLimit
attribute [local instance] Classical.propDecidable

theorem native_strictMonoOn {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) : StrictMonoOn (nativeGrowth a0 lam) (Icc a0 A) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a0 A)
    (fun a hx => (native_growth_derivative ha0 hA hlam hx).continuousAt.continuousWithinAt)
  intro a ha
  rw [(native_growth_derivative ha0 hA hlam (interior_subset ha)).deriv]
  exact (native_positive ha0 hA hlam a (interior_subset ha)).2

theorem native_initial {a0 lam : ℝ} (ha0 : 0 < a0) (hlam : 0 ≤ lam) :
    nativeGrowth a0 lam a0 = 1 := by
  have hp : 0 < rootSquared (lam * a0^3) 0 := by unfold rootSquared; positivity
  simpa [nativeGrowth, logScale] using growth_initial hp

theorem native_matter_upper {a0 lam a : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a)
    (hlam : 0 ≤ lam) : nativeGrowth a0 lam a ≤ a / a0 := by
  have hL := horizon_log_nonneg ha0 ha
  have hg := (growth_matter_bound ha0 hL hlam (logScale a0 a) ⟨hL, le_rfl⟩).1
  simpa only [logScale, Real.exp_log (div_pos (ha0.trans_le ha) ha0)] using hg

theorem exists_unique_first_time {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A) :
    ∃! a : ℝ, a ∈ Icc a0 A ∧ nativeGrowth a0 lam a = T := by
  have hcut : -(1 / A^3) < lam := by
    have hAp : 0 < A^3 := pow_pos (ha0.trans_le hA) 3
    exact (neg_neg_of_pos (div_pos (by norm_num) hAp)).trans_le hlam
  have hc : ContinuousOn (nativeGrowth a0 lam) (Icc a0 A) :=
    fun _ hx => (native_growth_derivative ha0 hA hcut hx).continuousAt.continuousWithinAt
  have hi : T ∈ Icc (nativeGrowth a0 lam a0) (nativeGrowth a0 lam A) :=
    ⟨(native_initial ha0 hlam) ▸ hT.le, hfinal⟩
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc hA hc hi
  refine ⟨a, ⟨ha, he⟩, ?_⟩
  intro b hb
  exact (native_strictMonoOn ha0 hA hcut).injOn hb.1 ha (hb.2.trans he.symm)

def firstTime (a0 A T lam : ℝ) : ℝ :=
  if h : 0 < a0 ∧ a0 ≤ A ∧ 0 ≤ lam ∧ 1 < T ∧ T ≤ nativeGrowth a0 lam A then
    (exists_unique_first_time h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose
  else a0

theorem firstTime_spec {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A) :
    firstTime a0 A T lam ∈ Icc a0 A ∧ nativeGrowth a0 lam (firstTime a0 A T lam) = T := by
  have h : 0 < a0 ∧ a0 ≤ A ∧ 0 ≤ lam ∧ 1 < T ∧ T ≤ nativeGrowth a0 lam A :=
    ⟨ha0, hA, hlam, hT, hfinal⟩
  simp only [firstTime, dif_pos h]
  exact (exists_unique_first_time ha0 hA hlam hT hfinal).choose_spec.1

theorem firstTime_iff_threshold {a0 A lam T a : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A)
    (ha : a ∈ Icc a0 A) :
    T ≤ nativeGrowth a0 lam a ↔ firstTime a0 A T lam ≤ a := by
  have hs := firstTime_spec ha0 hA hlam hT hfinal
  have hcut : -(1 / A^3) < lam := by
    have hAp : 0 < A^3 := pow_pos (ha0.trans_le hA) 3
    exact (neg_neg_of_pos (div_pos (by norm_num) hAp)).trans_le hlam
  have h := (native_strictMonoOn ha0 hA hcut).le_iff_le hs.1 ha
  rw [hs.2] at h
  exact h

theorem any_patch_collapse_iff {ι : Type*} {amp : ι → ℝ} {m δ D : ℝ}
    (hm : 0 < m) (hD : 0 ≤ D)
    (hbound : ∀ i, amp i ≤ m) (hattain : ∃ i, amp i = m) :
    (∃ i, δ ≤ amp i * D) ↔ δ / m ≤ D := by
  constructor
  · rintro ⟨i, hi⟩
    exact (div_le_iff₀ hm).mpr (by nlinarith [mul_le_mul_of_nonneg_right (hbound i) hD])
  · intro h
    obtain ⟨i, hi⟩ := hattain
    exact ⟨i, by rw [hi]; simpa [mul_comm] using (div_le_iff₀ hm).mp h⟩

theorem firstTime_lower_matter {a0 A lam T : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) (hT : 1 < T) (hfinal : T ≤ nativeGrowth a0 lam A) :
    a0 * T ≤ firstTime a0 A T lam := by
  have hs := firstTime_spec ha0 hA hlam hT hfinal
  have hb := native_matter_upper ha0 hs.1.1 hlam
  rw [hs.2] at hb
  simpa [mul_comm] using (le_div_iff₀ ha0).mp hb

theorem firstTime_strict_parameter {a0 A T lam1 lam2 : ℝ} (ha0 : 0 < a0)
    (hA : a0 < A) (h1 : 0 ≤ lam1) (h12 : lam1 < lam2) (hT : 1 < T)
    (hf1 : T ≤ nativeGrowth a0 lam1 A) (hf2 : T ≤ nativeGrowth a0 lam2 A) :
    firstTime a0 A T lam1 < firstTime a0 A T lam2 := by
  have h2 := h1.trans h12.le
  have hs1 := firstTime_spec ha0 hA.le h1 hT hf1
  have hs2 := firstTime_spec ha0 hA.le h2 hT hf2
  have ha2 : a0 < firstTime a0 A T lam2 := by
    by_contra hn
    have he := le_antisymm (le_of_not_gt hn) hs2.1.1
    rw [he, native_initial ha0 h2] at hs2
    linarith [hs2.2]
  have hcut1 : -(1 / A^3) < lam1 := by
    have hp : 0 < A^3 := pow_pos (ha0.trans hA) 3
    exact (neg_neg_of_pos (div_pos (by norm_num) hp)).trans_le h1
  have hg := (native_endpoint_strictAntiOn ha0 ha2)
    (show lam1 ∈ Ioi (-(1 / (firstTime a0 A T lam2)^3)) from
      (neg_neg_of_pos (div_pos (by norm_num) (pow_pos (ha0.trans ha2) 3))).trans_le h1)
    (show lam2 ∈ Ioi (-(1 / (firstTime a0 A T lam2)^3)) from
      (neg_neg_of_pos (div_pos (by norm_num) (pow_pos (ha0.trans ha2) 3))).trans_le h2) h12
  dsimp only at hg
  rw [hs2.2] at hg
  have hg' : nativeGrowth a0 lam1 (firstTime a0 A T lam1) <
      nativeGrowth a0 lam1 (firstTime a0 A T lam2) := by rw [hs1.2]; exact hg
  exact (native_strictMonoOn ha0 hA.le hcut1).lt_iff_lt hs1.1 hs2.1 |>.mp hg'

end
end SbtCosmo.Derivation.GrowthFirstRecord
