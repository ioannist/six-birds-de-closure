import SbtCosmo.Derivation.GrowthInfiniteTail
import SbtCosmo.Derivation.GrowthHorizonLimit
import SbtCosmo.Derivation.WindowEternalRecords
import Mathlib.Topology.Order.DenselyOrdered

/-! Quantitative limiting bounds and actual horizon convergence for the original population. -/
namespace SbtCosmo.Derivation.WindowEternalBounds
noncomputable section
open Set Filter GrowthInfinite GrowthInfiniteTail GrowthHorizonLimit GrowthEternalWindow
  GrowthScaleReturn GrowthExistence WindowSample
open scoped Topology

theorem limiting_growth_at_four_upper : nativeInfinite (1 / 1000) 4 < (937 : ℝ) := by
  have ht := native_tail_bound (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (1 / 1000 : ℝ) ≤ 20)
  norm_num at ht
  linarith [WindowEdgeCertified.native_growth_at_four_upper]

theorem infinite_upper_bracket : (3 : ℝ) < WindowEternalRecords.upper ∧
    WindowEternalRecords.upper < 4 := by
  have hlow := WindowEdgeCertified.upper_certified_bounds.1.trans WindowEternalRecords.finite_upper_lt_eternal
  have hu := WindowEternalRecords.upper_spec
  have hb : nativeInfinite (1 / 1000) 4 < nativeInfinite (1 / 1000) WindowEternalRecords.upper := by
    rw [hu.2]
    linarith [limiting_growth_at_four_upper, WindowEdgeCertified.sampled_threshold_tight_bounds.1]
  exact ⟨hlow, ((native_infinite_strictAntiOn (by norm_num)).lt_iff_gt
    (by norm_num : (0 : ℝ) < 4) hu.1).mp hb⟩

def formationUpper (A : ℝ) : ℝ := finiteEndpoint (1 / 1000) aggregateThreshold A

theorem formationUpper_spec {A : ℝ} (hA : aggregateThreshold / 1000 < A) :
    0 < formationUpper A ∧ nativeGrowth (1 / 1000) (formationUpper A) A = aggregateThreshold := by
  apply finiteEndpoint_spec (by norm_num) sampled_threshold_bounds.1
  simpa only [one_div_mul_eq_div] using hA

theorem finite_horizon_gate_iff {A : ℝ} (hA : aggregateThreshold / 1000 < A) (lam : ℝ) :
    GrowthPopulation.nativeAggregate amplitude WindowSampleData.tag (1 / 1000) A delta 10 lam ↔
      -(1 / A^3) < lam ∧ lam ≤ formationUpper A := by
  have hA' : (1 / 1000 : ℝ) * aggregateThreshold < A := by
    simpa only [one_div_mul_eq_div] using hA
  have hv := finite_horizon_admissible (by norm_num : (0 : ℝ) < 1 / 1000) sampled_threshold_bounds.1 hA'
  have hs := formationUpper_spec hA
  have hm := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000) hv.1
  have hcut : -(1 / A^3) < formationUpper A := by
    have ha : 0 < A := by linarith [hv.1]
    exact (neg_neg_of_pos (one_div_pos.mpr (pow_pos ha 3))).trans hs.1
  rw [WindowEternalRecords.gate_at_horizon_iff hv.1.le]
  constructor
  · rintro ⟨hc, hT⟩
    exact ⟨hc, (hm.le_iff_ge hcut hc).mp (by simpa only [hs.2] using hT)⟩
  · rintro ⟨hc, hu⟩
    exact ⟨hc, by simpa only [hs.2] using (hm.le_iff_ge hcut hc).mpr hu⟩

theorem formationUpper_at_twenty : formationUpper 20 = WindowEdgeCertified.upper := by
  have hA : aggregateThreshold / 1000 < (20 : ℝ) := by
    linarith [sampled_threshold_bounds.2]
  have hs := formationUpper_spec hA
  have hu := WindowEdgeCertified.upper_spec
  have hm := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20)
  apply (hm.eq_iff_eq (by norm_num; linarith [hs.1]) (by norm_num; linarith [hu.1])).mp
  exact hu.2.1.trans hs.2.symm

theorem formationUpper_strictMonoOn : StrictMonoOn formationUpper (Ioi (aggregateThreshold / 1000)) := by
  simpa only [formationUpper, one_div_mul_eq_div] using
    finiteEndpoint_strictMonoOn (by norm_num : (0 : ℝ) < 1 / 1000) sampled_threshold_bounds.1

theorem formationUpper_tendsto : Tendsto formationUpper atTop (𝓝 WindowEternalRecords.upper) :=
  finiteEndpoint_tendsto (by norm_num) sampled_threshold_bounds.1

/-- The closed interval is the closure of actual eventual-record parameters, not finite attainment at the endpoint. -/
theorem eternal_window_closure : closure {lam : ℝ | WindowEternalRecords.eternalGate lam} =
    Icc 0 WindowEternalRecords.upper := by
  have he : {lam : ℝ | WindowEternalRecords.eternalGate lam} = Ico 0 WindowEternalRecords.upper := by
    ext lam
    exact WindowEternalRecords.eternal_gate_iff lam
  rw [he, closure_Ico WindowEternalRecords.upper_spec.1.ne]

end
end SbtCosmo.Derivation.WindowEternalBounds
