import SbtCosmo.Derivation.GrowthLimit
import Mathlib.Topology.Order.IntermediateValue

/-! The actual finite-start growth IVP has a unique positive threshold endpoint. -/
namespace SbtCosmo.Derivation.GrowthWindow
noncomputable section
open Set Filter GrowthComparison GrowthExistence GrowthLimit GrowthScaleReturn
open scoped Topology

/-- An endpoint is constructed by the IVT using the proved infinity limit. -/
theorem exists_unique_positive_endpoint {a0 L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hTinf : freeGrowth L < T) (hTzero : T < Real.exp L) :
    ∃! upper : ℝ, 0 < upper ∧ finalGrowth a0 L upper = T := by
  have ht := (finalGrowth_tendsto_atTop ha hL.le).eventually_lt_const hTinf
  obtain ⟨b, hbT, hb⟩ := (ht.and (eventually_gt_atTop (0 : ℝ))).exists
  have hc : ContinuousOn (finalGrowth a0 L) (Icc 0 b) := by
    intro lam hlam
    exact (finalGrowth_continuousAt hL.le (live_nonnegative ha.le hlam.1)).continuousWithinAt
  obtain ⟨upper, hu, he⟩ := intermediate_value_Icc' hb.le hc
    (show T ∈ Icc (finalGrowth a0 L b) (finalGrowth a0 L 0) from
      ⟨hbT.le, (finalGrowth_at_zero a0 hL.le) ▸ hTzero.le⟩)
  have hup : 0 < upper := by
    by_contra hn
    have hu0 : upper = 0 := le_antisymm (le_of_not_gt hn) hu.1
    rw [hu0, finalGrowth_at_zero a0 hL.le] at he
    exact hTzero.ne he.symm
  refine ⟨upper, ⟨hup, he⟩, ?_⟩
  intro other ho
  exact ((finalGrowth_strictAntiOn ha hL).eq_iff_eq
    (live_nonnegative ha.le hup.le) (live_nonnegative ha.le ho.1.le)).mp (he.trans ho.2.symm)

/-- The complete log-interval live predicate is equivalent to the original horizon cutoff. -/
theorem live_iff_horizon {a0 A lam L : ℝ} (ha : 0 < a0) (hL : 0 ≤ L)
    (hA : scale a0 L = A) : Live a0 lam L ↔ -(1 / A^3) < lam := by
  refine ⟨?_, live_of_horizon ha hA⟩
  intro hl
  have hAp : 0 < A^3 := pow_pos (hA ▸ mul_pos ha (Real.exp_pos L)) 3
  have hd := hl L ⟨hL, le_rfl⟩
  rw [hA] at hd
  have h : -(1 : ℝ) / A^3 < lam := (div_lt_iff₀ hAp).mpr (by linarith)
  simpa only [neg_div] using h

/-- Exact half-open window, including threshold equality and excluding turnaround. -/
theorem exists_unique_threshold_window {a0 A L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hA : scale a0 L = A) (hTinf : freeGrowth L < T) (hTzero : T < Real.exp L) :
    ∃! upper : ℝ, 0 < upper ∧ finalGrowth a0 L upper = T ∧
      ∀ lam : ℝ, (Live a0 lam L ∧ T ≤ finalGrowth a0 L lam) ↔
        (-(1 / A^3) < lam ∧ lam ≤ upper) := by
  obtain ⟨upper, hu, hunique⟩ := exists_unique_positive_endpoint ha hL hTinf hTzero
  refine ⟨upper, ⟨hu.1, hu.2, ?_⟩, ?_⟩
  · intro lam
    constructor
    · rintro ⟨hl, hT⟩
      refine ⟨(live_iff_horizon ha hL.le hA).mp hl, ?_⟩
      exact ((finalGrowth_strictAntiOn ha hL).le_iff_ge
        (live_nonnegative ha.le hu.1.le) hl).mp (hu.2 ▸ hT)
    · rintro ⟨hl, hupper⟩
      have hlive := (live_iff_horizon ha hL.le hA).mpr hl
      refine ⟨hlive, ?_⟩
      have h := ((finalGrowth_strictAntiOn ha hL).le_iff_ge
        (live_nonnegative ha.le hu.1.le) hlive).mpr hupper
      simpa only [hu.2] using h
  · intro other ho
    exact hunique other ⟨ho.1, ho.2.1⟩

/-- Return the window to the constructed original scale-factor solution. -/
theorem exists_unique_native_threshold_window {a0 A T : ℝ} (ha : 0 < a0) (hA : a0 < A)
    (hTinf : freeGrowth (Real.log (A / a0)) < T) (hTzero : T < A / a0) :
    ∃! upper : ℝ, 0 < upper ∧ nativeGrowth a0 upper A = T ∧
      ∀ lam : ℝ, (-(1 / A^3) < lam ∧ T ≤ nativeGrowth a0 lam A) ↔
        (-(1 / A^3) < lam ∧ lam ≤ upper) := by
  have hAp := ha.trans hA
  have hL : 0 < Real.log (A / a0) := Real.log_pos ((one_lt_div ha).mpr hA)
  have hs := scale_log_horizon ha hAp
  have ht : T < Real.exp (Real.log (A / a0)) := by rwa [Real.exp_log (div_pos hAp ha)]
  obtain ⟨upper, hu, huniq⟩ := exists_unique_threshold_window ha hL hs hTinf ht
  refine ⟨upper, ⟨hu.1, hu.2.1, ?_⟩, ?_⟩
  · intro lam
    simpa only [live_iff_horizon ha hL.le hs, nativeGrowth, logScale, finalGrowth] using hu.2.2 lam
  · intro other ho
    apply huniq other
    refine ⟨ho.1, ho.2.1, ?_⟩
    intro lam
    simpa only [live_iff_horizon ha hL.le hs, nativeGrowth, logScale, finalGrowth] using ho.2.2 lam

/-- Actual continuous native-scale collapse history is equivalent to the final contrast. -/
theorem native_ever_collapse_iff_final {a0 A lam amplitude threshold : ℝ}
    (ha : 0 < a0) (hA : a0 ≤ A) (hlam : -(1 / A^3) < lam) (hp : 0 ≤ amplitude) :
    (∃ a ∈ Icc a0 A, threshold ≤ amplitude * nativeGrowth a0 lam a) ↔
      threshold ≤ amplitude * nativeGrowth a0 lam A := by
  have hL := horizon_log_nonneg ha hA
  have hl := live_of_horizon ha (scale_log_horizon ha (ha.trans_le hA)) hlam
  have hs := constructed_growthSolution hL hl
  have hm := (growth_strict_in_time hL hl hs).monotoneOn
  constructor
  · rintro ⟨a, hx, hc⟩
    have hlog := logScale_mem ha hx
    exact hc.trans (mul_le_mul_of_nonneg_left
      (hm hlog ⟨hL, le_rfl⟩ hlog.2) hp)
  · intro hc
    exact ⟨A, ⟨hA, le_rfl⟩, hc⟩

/-- The original two-tag predicate is evaluated over the full scale-factor history. -/
theorem native_record_history_iff_threshold {ι : Type*} {amplitude : ι → ℝ} {tag : ι → Bool}
    {a0 A lam m0 m1 threshold : ℝ} (ha : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hp : ∀ i, 0 ≤ amplitude i)
    (h0 : WindowRecords.TagMaximum amplitude tag false m0)
    (h1 : WindowRecords.TagMaximum amplitude tag true m1) (hm0 : 0 < m0) (hm1 : 0 < m1) :
    WindowRecords.RecordBearing
      (fun i => ∃ a ∈ Icc a0 A, threshold ≤ amplitude i * nativeGrowth a0 lam a) tag ↔
      max (threshold / m0) (threshold / m1) ≤ nativeGrowth a0 lam A := by
  have heq : (fun i => ∃ a ∈ Icc a0 A, threshold ≤ amplitude i * nativeGrowth a0 lam a) =
      (fun i => threshold ≤ amplitude i * nativeGrowth a0 lam A) := by
    funext i
    exact propext (native_ever_collapse_iff_final ha hA hlam (hp i))
  rw [heq]
  exact WindowRecords.record_iff_threshold h0 h1 hm0 hm1
    (native_positive ha hA hlam A ⟨hA, le_rfl⟩).1.le

/-- Exact two-sided native record window; maxima are explicit fixed-realization premises. -/
theorem exists_unique_native_record_window {ι : Type*} {amplitude : ι → ℝ} {tag : ι → Bool}
    {a0 A m0 m1 threshold : ℝ} (ha : 0 < a0) (hA : a0 < A)
    (hp : ∀ i, 0 ≤ amplitude i)
    (h0 : WindowRecords.TagMaximum amplitude tag false m0)
    (h1 : WindowRecords.TagMaximum amplitude tag true m1) (hm0 : 0 < m0) (hm1 : 0 < m1)
    (hTinf : freeGrowth (Real.log (A / a0)) < max (threshold / m0) (threshold / m1))
    (hTzero : max (threshold / m0) (threshold / m1) < A / a0) :
    ∃! upper : ℝ, 0 < upper ∧
      nativeGrowth a0 upper A = max (threshold / m0) (threshold / m1) ∧
      ∀ lam : ℝ, (-(1 / A^3) < lam ∧ WindowRecords.RecordBearing
        (fun i => ∃ a ∈ Icc a0 A, threshold ≤ amplitude i * nativeGrowth a0 lam a) tag) ↔
        (-(1 / A^3) < lam ∧ lam ≤ upper) := by
  obtain ⟨upper, hu, _⟩ := exists_unique_native_threshold_window ha hA hTinf hTzero
  refine ⟨upper, ⟨hu.1, hu.2.1, ?_⟩, ?_⟩
  · intro lam
    constructor
    · rintro ⟨hl, hr⟩
      exact (hu.2.2 lam).mp ⟨hl,
        (native_record_history_iff_threshold ha hA.le hl hp h0 h1 hm0 hm1).mp hr⟩
    · intro hw
      obtain ⟨hl, ht⟩ := (hu.2.2 lam).mpr hw
      exact ⟨hl, (native_record_history_iff_threshold ha hA.le hl hp h0 h1 hm0 hm1).mpr ht⟩
  · intro other ho
    exact ((native_endpoint_strictAntiOn ha hA).eq_iff_eq
      (show upper ∈ Ioi (-(1 / A^3)) by
        have hAp : 0 < A^3 := pow_pos (ha.trans hA) 3
        have hn : -(1 / A^3) < 0 := neg_neg_of_pos (one_div_pos.mpr hAp)
        exact hn.trans hu.1)
      (show other ∈ Ioi (-(1 / A^3)) by
        have hAp : 0 < A^3 := pow_pos (ha.trans hA) 3
        have hn : -(1 / A^3) < 0 := neg_neg_of_pos (one_div_pos.mpr hAp)
        exact hn.trans ho.1)).mp (hu.2.1.trans ho.2.1.symm)

end
end SbtCosmo.Derivation.GrowthWindow
