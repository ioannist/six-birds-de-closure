import SbtCosmo.Derivation.GrowthEternalWindow
import SbtCosmo.Derivation.WindowEdgeCertified

/-! Actual original twelve-seed records with finite formation and perpetual horizon retention.
The fixed formation deadline and arbitrary finite formation predicates are kept distinct. -/
namespace SbtCosmo.Derivation.WindowEternalRecords
noncomputable section
open Set GrowthInfinite GrowthEternalWindow GrowthScaleReturn GrowthPopulation WindowSample
attribute [local instance] Classical.propDecidable

def upper : ℝ := infiniteEndpoint (1 / 1000) aggregateThreshold

theorem upper_spec : 0 < upper ∧ nativeInfinite (1 / 1000) upper = aggregateThreshold :=
  infiniteEndpoint_spec (by norm_num) sampled_threshold_bounds.1

/-- The original population/rank return applies to any finite horizon A, not just twenty. -/
theorem gate_at_horizon_iff {A : ℝ} (hA : (1 / 1000 : ℝ) ≤ A) (lam : ℝ) :
    nativeAggregate amplitude WindowSampleData.tag (1 / 1000) A delta 10 lam ↔
      -(1 / A^3) < lam ∧ aggregateThreshold ≤ nativeGrowth (1 / 1000) lam A := by
  have hbelow : (Finset.univ.filter
      (fun j => max (delta / maximumFalse j) (delta / maximumTrue j) < aggregateThreshold)).card < 10 := by
    simpa only [← seedThreshold_eq, sampled_rank_counts.1] using (show 9 < 10 by decide)
  have hat : 10 ≤ passingCount
      (fun j => max (delta / maximumFalse j) (delta / maximumTrue j)) aggregateThreshold := by
    simpa only [← seedThreshold_eq] using sampled_rank_counts.2.ge
  exact native_aggregate_iff_threshold (by norm_num) hA
    (fun j => (sampled_maxima j).1) (fun j => (sampled_maxima j).2.2.2.1)
    (fun j => (sampled_maxima j).2.2.2.2) (fun j => (sampled_maxima j).2.1)
    (fun j => (sampled_maxima j).2.2.1) hbelow hat lam

def eternalGate (lam : ℝ) : Prop := perpetualHorizon (1 / 1000) lam ∧
  ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧
    nativeAggregate amplitude WindowSampleData.tag (1 / 1000) A delta 10 lam

theorem eternal_gate_iff (lam : ℝ) : eternalGate lam ↔ 0 ≤ lam ∧ lam < upper := by
  have hr : eternalGate lam ↔ perpetualHorizon (1 / 1000) lam ∧
      ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧ aggregateThreshold ≤ nativeGrowth (1 / 1000) lam A := by
    constructor
    · rintro ⟨hp, A, hA, hg⟩
      exact ⟨hp, A, hA, ((gate_at_horizon_iff hA lam).mp hg).2⟩
    · rintro ⟨hp, A, hA, hT⟩
      exact ⟨hp, A, hA, (gate_at_horizon_iff hA lam).mpr ⟨hp A hA, hT⟩⟩
  exact hr.trans (perpetual_threshold_window (by norm_num) sampled_threshold_bounds.1)

theorem zero_passes : eternalGate 0 := (eternal_gate_iff 0).mpr ⟨le_rfl, upper_spec.1⟩

theorem endpoint_excluded : ¬ eternalGate upper := by
  rw [eternal_gate_iff]
  exact fun h => (lt_irrefl upper) h.2

theorem negative_excluded {lam : ℝ} (hlam : lam < 0) : ¬ eternalGate lam := by
  rw [eternal_gate_iff]
  exact fun h => hlam.not_ge h.1

theorem finite_upper_lt_eternal : WindowEdgeCertified.upper < upper :=
  finite_endpoint_lt_infinite (by norm_num) sampled_threshold_bounds.1
    WindowEdgeCertified.upper_spec.1 (by norm_num) WindowEdgeCertified.upper_spec.2.1

/-- An individual original seed forms both tag records by some actual finite epoch. -/
def eventualRecord (j : Fin 12) (lam : ℝ) : Prop := ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧
  nativeRecord (amplitude j) (WindowSampleData.tag j) (1 / 1000) A delta lam

theorem eventual_record_iff {lam : ℝ} (hlam : 0 < lam) (j : Fin 12) :
    eventualRecord j lam ↔ seedThreshold j < nativeInfinite (1 / 1000) lam := by
  have hper := (perpetual_horizon_iff (by norm_num : (0 : ℝ) < 1 / 1000)).mpr hlam.le
  have he : eventualRecord j lam ↔ ∃ A : ℝ, (1 / 1000 : ℝ) ≤ A ∧
      seedThreshold j ≤ nativeGrowth (1 / 1000) lam A := by
    have hr : ∀ A : ℝ, (1 / 1000 : ℝ) ≤ A →
        (nativeRecord (amplitude j) (WindowSampleData.tag j) (1 / 1000) A delta lam ↔
          seedThreshold j ≤ nativeGrowth (1 / 1000) lam A) := by
      intro A hA
      rw [seedThreshold_eq]
      exact GrowthWindow.native_record_history_iff_threshold (by norm_num) hA (hper A hA)
        (sampled_maxima j).1 (sampled_maxima j).2.2.2.1 (sampled_maxima j).2.2.2.2
        (sampled_maxima j).2.1 (sampled_maxima j).2.2.1
    constructor
    · rintro ⟨A, hA, hR⟩
      exact ⟨A, hA, (hr A hA).mp hR⟩
    · rintro ⟨A, hA, hT⟩
      exact ⟨A, hA, (hr A hA).mpr hT⟩
  exact he.trans (native_eventual_threshold_iff (by norm_num) hlam)

/-- Nine seeds eventually form both tags at the limiting endpoint; the required ten do not. -/
theorem endpoint_eventual_count :
    (Finset.univ.filter (fun j => eventualRecord j upper)).card = 9 := by
  simp_rw [eventual_record_iff upper_spec.1, upper_spec.2]
  exact sampled_rank_counts.1

/-- Keeping the original formation deadline, with perpetual retention, is a different predicate. -/
def fixedDeadlineGate (lam : ℝ) : Prop := perpetualHorizon (1 / 1000) lam ∧ realizedGate lam

theorem fixed_deadline_gate_iff (lam : ℝ) :
    fixedDeadlineGate lam ↔ 0 ≤ lam ∧ lam ≤ WindowEdgeCertified.upper := by
  unfold fixedDeadlineGate
  rw [perpetual_horizon_iff (by norm_num), WindowEdgeCertified.upper_spec.2.2]
  constructor
  · rintro ⟨hn, _, hu⟩
    exact ⟨hn, hu⟩
  · rintro ⟨hn, hu⟩
    exact ⟨hn, by linarith, hu⟩

/-- A small kernel computation checks a global starvation margin for the unchanged realization. -/
theorem rational_starvation_margin (j : Fin 12) :
    3 * max (WindowSampleData.maximumFalseRat j) (WindowSampleData.maximumTrueRat j) <
      WindowSampleData.deltaRat := by
  revert j
  decide +kernel

theorem amplitude_starvation_margin (j : Fin 12) (i : Fin 64) : 3 * amplitude j i < delta := by
  have hb : amplitude j i ≤ max (maximumFalse j) (maximumTrue j) := by
    cases ht : WindowSampleData.tag j i
    · exact ((sampled_maxima j).2.2.2.1.2 i ht).trans (le_max_left _ _)
    · exact ((sampled_maxima j).2.2.2.2.2 i ht).trans (le_max_right _ _)
  have hm : 3 * max (maximumFalse j) (maximumTrue j) < delta := by
    dsimp only [maximumFalse, maximumTrue, delta]
    exact_mod_cast rational_starvation_margin j
  exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_lt hm

/-- No original patch reaches collapse at any finite scale factor above this coarse lambda cutoff. -/
theorem no_records_ever {lam : ℝ} (hlam : (1000000000 : ℝ) ≤ lam)
    (j : Fin 12) (i : Fin 64) :
    ¬ ∃ a : ℝ, (1 / 1000 : ℝ) ≤ a ∧ delta ≤ amplitude j i * nativeGrowth (1 / 1000) lam a := by
  rintro ⟨a, ha, hT⟩
  have hc : 1 ≤ lam * (1 / 1000 : ℝ)^3 := by norm_num; linarith
  have hD := native_global_bound (by norm_num : (0 : ℝ) < 1 / 1000) ha hc
  have hp := (sampled_maxima j).1 i
  have hb := mul_le_mul_of_nonneg_left hD.le hp
  have hs := amplitude_starvation_margin j i
  nlinarith

end
end SbtCosmo.Derivation.WindowEternalRecords
