import SbtCosmo.Derivation.WindowPatchCounts
import SbtCosmo.Derivation.WindowEternalRecords

/-! Eternal returns for the actual N=32 and N=128 robustness populations.
These separately realized populations have ordered thresholds; no inclusion or tag coupling is assumed. -/
namespace SbtCosmo.Derivation.WindowEternalPatchCounts
noncomputable section
open Set GrowthInfinite GrowthEternalWindow GrowthScaleReturn GrowthPopulation WindowPatchCounts
attribute [local instance] Classical.propDecidable

def upper (v : Bool) : ℝ := infiniteEndpoint (1 / 1000) (aggregateThreshold v)

theorem upper_spec (v : Bool) : 0 < upper v ∧ nativeInfinite (1 / 1000) (upper v) = aggregateThreshold v :=
  infiniteEndpoint_spec (by norm_num) (sampled_threshold_bounds v).1

theorem gate_at_horizon_iff (v : Bool) {A : ℝ} (hA : (1 / 1000 : ℝ) ≤ A) (lam : ℝ) :
    nativeAggregate (amplitude v) (WindowPatchCountData.tag v) (1 / 1000) A delta 10 lam ↔
      -(1 / A^3) < lam ∧ aggregateThreshold v ≤ nativeGrowth (1 / 1000) lam A := by
  have hbelow : (Finset.univ.filter
      (fun j => max (delta / maximumFalse v j) (delta / maximumTrue v j) < aggregateThreshold v)).card < 10 := by
    simpa only [← seedThreshold_eq, (sampled_rank_counts v).1] using (show 9 < 10 by decide)
  have hat : 10 ≤ passingCount
      (fun j => max (delta / maximumFalse v j) (delta / maximumTrue v j)) (aggregateThreshold v) := by
    simpa only [← seedThreshold_eq] using (sampled_rank_counts v).2.ge
  exact native_aggregate_iff_threshold (by norm_num) hA
    (fun j => (sampled_maxima v j).1) (fun j => (sampled_maxima v j).2.2.2.1)
    (fun j => (sampled_maxima v j).2.2.2.2) (fun j => (sampled_maxima v j).2.1)
    (fun j => (sampled_maxima v j).2.2.1) hbelow hat lam

def eternalGate (v : Bool) (lam : ℝ) : Prop := perpetualHorizon (1 / 1000) lam ∧
  ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧
    nativeAggregate (amplitude v) (WindowPatchCountData.tag v) (1 / 1000) A delta 10 lam

theorem eternal_gate_iff (v : Bool) (lam : ℝ) : eternalGate v lam ↔ 0 ≤ lam ∧ lam < upper v := by
  have hr : eternalGate v lam ↔ perpetualHorizon (1 / 1000) lam ∧
      ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧ aggregateThreshold v ≤ nativeGrowth (1 / 1000) lam A := by
    constructor
    · rintro ⟨hp, A, hA, hg⟩
      exact ⟨hp, A, hA, ((gate_at_horizon_iff v hA lam).mp hg).2⟩
    · rintro ⟨hp, A, hA, hT⟩
      exact ⟨hp, A, hA, (gate_at_horizon_iff v hA lam).mpr ⟨hp A hA, hT⟩⟩
  exact hr.trans (perpetual_threshold_window (by norm_num) (sampled_threshold_bounds v).1)

def eventualRecord (v : Bool) (j : Fin 12) (lam : ℝ) : Prop := ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧
  nativeRecord (amplitude v j) (WindowPatchCountData.tag v j) (1 / 1000) A delta lam

theorem eventual_record_iff (v : Bool) {lam : ℝ} (hlam : 0 < lam) (j : Fin 12) :
    eventualRecord v j lam ↔ seedThreshold v j < nativeInfinite (1 / 1000) lam := by
  have hper := (perpetual_horizon_iff (by norm_num : (0 : ℝ) < 1 / 1000)).mpr hlam.le
  have he : eventualRecord v j lam ↔ ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧
      seedThreshold v j ≤ nativeGrowth (1 / 1000) lam A := by
    have hr : ∀ A : ℝ, (1 / 1000 : ℝ) ≤ A →
        (nativeRecord (amplitude v j) (WindowPatchCountData.tag v j) (1 / 1000) A delta lam ↔
          seedThreshold v j ≤ nativeGrowth (1 / 1000) lam A) := by
      intro A hA
      rw [seedThreshold_eq]
      exact GrowthWindow.native_record_history_iff_threshold (by norm_num) hA (hper A hA)
        (sampled_maxima v j).1 (sampled_maxima v j).2.2.2.1 (sampled_maxima v j).2.2.2.2
        (sampled_maxima v j).2.1 (sampled_maxima v j).2.2.1
    constructor
    · rintro ⟨A, hA, hR⟩
      exact ⟨A, hA, (hr A hA).mp hR⟩
    · rintro ⟨A, hA, hT⟩
      exact ⟨A, hA, (hr A hA).mpr hT⟩
  exact he.trans (native_eventual_threshold_iff (by norm_num) hlam)

theorem endpoint_eventual_count (v : Bool) :
    (Finset.univ.filter (fun j => eventualRecord v j (upper v))).card = 9 := by
  simp_rw [eventual_record_iff v (upper_spec v).1, (upper_spec v).2]
  exact (sampled_rank_counts v).1

theorem zero_passes (v : Bool) : eternalGate v 0 := (eternal_gate_iff v 0).mpr ⟨le_rfl, (upper_spec v).1⟩

theorem endpoint_excluded (v : Bool) : ¬ eternalGate v (upper v) := by
  rw [eternal_gate_iff]
  exact fun h => (lt_irrefl (upper v)) h.2

theorem negative_excluded (v : Bool) {lam : ℝ} (hlam : lam < 0) : ¬ eternalGate v lam := by
  rw [eternal_gate_iff]
  exact fun h => hlam.not_ge h.1

theorem finite_upper_lt_eternal (v : Bool) : WindowPatchCounts.upper v < upper v :=
  finite_endpoint_lt_infinite (by norm_num) (sampled_threshold_bounds v).1
    (WindowPatchCounts.upper_spec v).1 (by norm_num) (WindowPatchCounts.upper_spec v).2.1

/-- Strict ordering is derived from the actual distinct-population thresholds. -/
theorem upper_order : upper false < WindowEternalRecords.upper ∧ WindowEternalRecords.upper < upper true := by
  have hm := native_infinite_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
  constructor
  · apply (hm.lt_iff_gt WindowEternalRecords.upper_spec.1 (upper_spec false).1).mp
    rw [WindowEternalRecords.upper_spec.2, (upper_spec false).2]
    exact threshold_order.2
  · apply (hm.lt_iff_gt (upper_spec true).1 WindowEternalRecords.upper_spec.1).mp
    rw [(upper_spec true).2, WindowEternalRecords.upper_spec.2]
    exact threshold_order.1

theorem gate_inclusions (lam : ℝ) :
    (eternalGate false lam → WindowEternalRecords.eternalGate lam) ∧
      (WindowEternalRecords.eternalGate lam → eternalGate true lam) := by
  rw [eternal_gate_iff false, WindowEternalRecords.eternal_gate_iff, eternal_gate_iff true]
  exact ⟨fun h => ⟨h.1, h.2.trans upper_order.1⟩, fun h => ⟨h.1, h.2.trans upper_order.2⟩⟩

/-- Open windows require witnesses at the smaller endpoints, rather than a pass at their own upper edge. -/
theorem strict_gate_witnesses :
    (WindowEternalRecords.eternalGate (upper false) ∧ ¬ eternalGate false (upper false)) ∧
      (eternalGate true WindowEternalRecords.upper ∧ ¬ WindowEternalRecords.eternalGate WindowEternalRecords.upper) := by
  exact ⟨⟨(WindowEternalRecords.eternal_gate_iff _).mpr ⟨(upper_spec false).1.le, upper_order.1⟩,
    endpoint_excluded false⟩,
    ⟨(eternal_gate_iff true _).mpr ⟨WindowEternalRecords.upper_spec.1.le, upper_order.2⟩,
      WindowEternalRecords.endpoint_excluded⟩⟩

def fixedDeadlineGate (v : Bool) (lam : ℝ) : Prop := perpetualHorizon (1 / 1000) lam ∧ realizedGate v lam

theorem fixed_deadline_gate_iff (v : Bool) (lam : ℝ) :
    fixedDeadlineGate v lam ↔ 0 ≤ lam ∧ lam ≤ WindowPatchCounts.upper v := by
  unfold fixedDeadlineGate
  rw [perpetual_horizon_iff (by norm_num), (WindowPatchCounts.upper_spec v).2.2]
  constructor
  · rintro ⟨hn, _, hu⟩
    exact ⟨hn, hu⟩
  · rintro ⟨hn, hu⟩
    exact ⟨hn, by linarith, hu⟩

theorem rational_starvation_margin (v : Bool) (j : Fin 12) :
    3 * max (WindowPatchCountData.maximumFalseRat v j) (WindowPatchCountData.maximumTrueRat v j) <
      WindowSampleData.deltaRat := by
  revert v j
  decide +kernel

theorem amplitude_starvation_margin (v : Bool) (j : Fin 12) (i : Fin (WindowPatchCountData.patchCount v)) :
    3 * amplitude v j i < delta := by
  have hb : amplitude v j i ≤ max (maximumFalse v j) (maximumTrue v j) := by
    cases ht : WindowPatchCountData.tag v j i
    · exact ((sampled_maxima v j).2.2.2.1.2 i ht).trans (le_max_left _ _)
    · exact ((sampled_maxima v j).2.2.2.2.2 i ht).trans (le_max_right _ _)
  have hm : 3 * max (maximumFalse v j) (maximumTrue v j) < delta := by
    dsimp only [maximumFalse, maximumTrue, delta]
    exact_mod_cast rational_starvation_margin v j
  exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_lt hm

theorem no_records_ever (v : Bool) {lam : ℝ} (hlam : (1000000000 : ℝ) ≤ lam)
    (j : Fin 12) (i : Fin (WindowPatchCountData.patchCount v)) :
    ¬ ∃ a : ℝ, (1 / 1000 : ℝ) ≤ a ∧ delta ≤ amplitude v j i * nativeGrowth (1 / 1000) lam a := by
  rintro ⟨a, ha, hT⟩
  have hc : 1 ≤ lam * (1 / 1000 : ℝ)^3 := by norm_num; linarith
  have hD := native_global_bound (by norm_num : (0 : ℝ) < 1 / 1000) ha hc
  have hp := (sampled_maxima v j).1 i
  have hb := mul_le_mul_of_nonneg_left hD.le hp
  have hs := amplitude_starvation_margin v j i
  nlinarith

end
end SbtCosmo.Derivation.WindowEternalPatchCounts
