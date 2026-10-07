import SbtCosmo.Derivation.GrowthPopulation
import SbtCosmo.Derivation.WindowPatchCountData
import SbtCosmo.Derivation.WindowEdgeCertified

/-! Exact continuum windows for the actual separately realized N=32 and N=128
robustness populations. No inclusion or tag coupling is assumed. -/
namespace SbtCosmo.Derivation.WindowPatchCounts
noncomputable section
open Set GrowthPopulation GrowthScaleReturn GrowthLimit WindowPatchCountData
attribute [local instance] Classical.propDecidable

def amplitude (v : Bool) (j : Fin 12) (i : Fin (patchCount v)) : ℝ := amplitudeRat v j i
def maximumFalse (v : Bool) (j : Fin 12) : ℝ := maximumFalseRat v j
def maximumTrue (v : Bool) (j : Fin 12) : ℝ := maximumTrueRat v j
def seedThreshold (v : Bool) (j : Fin 12) : ℝ := thresholdRat v j
def delta : ℝ := WindowSampleData.deltaRat
def aggregateThreshold (v : Bool) : ℝ := aggregateRat v

theorem sampled_maxima (v : Bool) (j : Fin 12) :
    (∀ i, 0 ≤ amplitude v j i) ∧ 0 < maximumFalse v j ∧ 0 < maximumTrue v j ∧
      WindowRecords.TagMaximum (amplitude v j) (tag v j) false (maximumFalse v j) ∧
      WindowRecords.TagMaximum (amplitude v j) (tag v j) true (maximumTrue v j) := by
  dsimp only [amplitude, maximumFalse, maximumTrue]
  obtain ⟨hm0, hm1, hf, haf, ht, hat, hb⟩ := rational_maxima_certificate v j
  refine ⟨?_, ?_, ?_, ⟨⟨falseIndex v j, hf, ?_⟩, ?_⟩, ⟨⟨trueIndex v j, ht, ?_⟩, ?_⟩⟩
  · intro i
    exact_mod_cast (hb i).1
  · exact_mod_cast hm0
  · exact_mod_cast hm1
  · dsimp only [amplitude]
    exact_mod_cast haf
  · intro i hi
    dsimp only [amplitude]
    exact_mod_cast (hb i).2.1 hi
  · dsimp only [amplitude]
    exact_mod_cast hat
  · intro i hi
    dsimp only [amplitude]
    exact_mod_cast (hb i).2.2 hi

theorem seedThreshold_eq (v : Bool) (j : Fin 12) :
    seedThreshold v j = max (delta / maximumFalse v j) (delta / maximumTrue v j) := by
  dsimp only [seedThreshold, delta, maximumFalse, maximumTrue]
  exact_mod_cast rational_threshold_certificate v j

theorem sampled_rank_counts (v : Bool) :
    (Finset.univ.filter (fun j => seedThreshold v j < aggregateThreshold v)).card = 9 ∧
      passingCount (seedThreshold v) (aggregateThreshold v) = 10 := by
  simpa only [seedThreshold, aggregateThreshold, passingCount, Rat.cast_lt, Rat.cast_le]
    using rational_rank_certificate v

theorem sampled_count_iff_threshold (v : Bool) (x : ℝ) :
    10 ≤ passingCount (seedThreshold v) x ↔ aggregateThreshold v ≤ x := by
  apply passingCount_iff_rank
  · rw [(sampled_rank_counts v).1]
    norm_num
  · exact (sampled_rank_counts v).2.ge

theorem sampled_threshold_bounds (v : Bool) : (3 : ℝ) / 2 < aggregateThreshold v ∧
    aggregateThreshold v < 20000 := by
  constructor
  · change (3 : ℝ) / 2 < (aggregateRat v : ℝ)
    have h : (((3 : ℚ) / 2 : ℚ) : ℝ) < (aggregateRat v : ℝ) :=
      Rat.cast_lt.mpr (rational_window_bounds v).1
    convert h using 1
    norm_num
  · change (aggregateRat v : ℝ) < 20000
    exact_mod_cast (rational_window_bounds v).2

theorem threshold_exact_32 : aggregateThreshold false =
    (971912828383572000768 : ℝ) / 776048084276875375 := by
  norm_num [aggregateThreshold, aggregateRat]

theorem threshold_exact_128 : aggregateThreshold true =
    (161985471397262000128 : ℝ) / 201471766463730375 := by
  norm_num [aggregateThreshold, aggregateRat]

def realizedGate (v : Bool) (lam : ℝ) : Prop := nativeAggregate (amplitude v) (tag v) (1 / 1000) 20 delta 10 lam

theorem realized_gate_iff_seed_fraction (v : Bool) (lam : ℝ) :
    realizedGate v lam ↔ -(1 / (20 : ℝ)^3) < lam ∧
      (4 / 5 : ℝ) ≤ ((Finset.univ.filter
        (fun j => nativeRecord (amplitude v j) (tag v j) (1 / 1000) 20 delta lam)).card : ℝ) / 12 := by
  unfold realizedGate nativeAggregate
  rw [WindowSample.seed_fraction_iff]

theorem realized_gate_iff_threshold (v : Bool) (lam : ℝ) :
    realizedGate v lam ↔ -(1 / 8000 : ℝ) < lam ∧
      aggregateThreshold v ≤ nativeGrowth (1 / 1000) lam 20 := by
  have hbelow : (Finset.univ.filter
      (fun j => max (delta / maximumFalse v j) (delta / maximumTrue v j) < aggregateThreshold v)).card < 10 := by
    simpa only [← seedThreshold_eq, (sampled_rank_counts v).1] using (show 9 < 10 by decide)
  have hat : 10 ≤ passingCount
      (fun j => max (delta / maximumFalse v j) (delta / maximumTrue v j)) (aggregateThreshold v) := by
    simpa only [← seedThreshold_eq] using (sampled_rank_counts v).2.ge
  have h := native_aggregate_iff_threshold (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 20)
    (fun j => (sampled_maxima v j).1) (fun j => (sampled_maxima v j).2.2.2.1)
    (fun j => (sampled_maxima v j).2.2.2.2) (fun j => (sampled_maxima v j).2.1)
    (fun j => (sampled_maxima v j).2.2.1) hbelow hat lam
  norm_num [realizedGate] at h ⊢
  exact h

/-- Original twelve-seed continuum window, with every population/rank premise discharged. -/
theorem exists_unique_realized_window (v : Bool) :
    ∃! upper : ℝ, 0 < upper ∧ nativeGrowth (1 / 1000) upper 20 = aggregateThreshold v ∧
      ∀ lam : ℝ, realizedGate v lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ upper := by
  have hTinf : freeGrowth (Real.log ((20 : ℝ) / (1 / 1000))) < aggregateThreshold v := by
    unfold freeGrowth
    have he := Real.exp_pos (-2 * Real.log ((20 : ℝ) / (1 / 1000)))
    linarith [(sampled_threshold_bounds v).1]
  have hTzero : aggregateThreshold v < (20 : ℝ) / (1 / 1000) := by
    norm_num
    exact (sampled_threshold_bounds v).2
  obtain ⟨upper, hu, huniq⟩ := GrowthWindow.exists_unique_native_threshold_window
    (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num : (1 / 1000 : ℝ) < 20) hTinf hTzero
  refine ⟨upper, ⟨hu.1, hu.2.1, ?_⟩, ?_⟩
  · intro lam
    have hw := hu.2.2 lam
    have hcut : -(1 / (20 : ℝ)^3) = -(1 / 8000 : ℝ) := by norm_num
    rw [hcut] at hw
    exact (realized_gate_iff_threshold v lam).trans hw
  · intro other ho
    apply huniq other
    refine ⟨ho.1, ho.2.1, ?_⟩
    intro lam
    have hw := (realized_gate_iff_threshold v lam).symm.trans (ho.2.2 lam)
    have hcut : -(1 / (20 : ℝ)^3) = -(1 / 8000 : ℝ) := by norm_num
    rw [hcut]
    exact hw

def upper (v : Bool) : ℝ := (exists_unique_realized_window v).choose

theorem upper_spec (v : Bool) : 0 < upper v ∧
    nativeGrowth (1 / 1000) (upper v) 20 = aggregateThreshold v ∧
      ∀ lam : ℝ, realizedGate v lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ upper v :=
  (exists_unique_realized_window v).choose_spec.1

theorem threshold_order : aggregateThreshold true < WindowSample.aggregateThreshold ∧
    WindowSample.aggregateThreshold < aggregateThreshold false := by
  dsimp only [aggregateThreshold, WindowSample.aggregateThreshold]
  exact_mod_cast rational_threshold_order

/-- Ordering for the actual separately realized populations, not an assumed inclusion. -/
theorem upper_order : upper false < WindowEdgeCertified.upper ∧
    WindowEdgeCertified.upper < upper true := by
  have hm := native_endpoint_strictAntiOn (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) < 20)
  have h32 : upper false ∈ Ioi (-(1 / (20 : ℝ)^3)) := by
    change -(1 / (20 : ℝ)^3) < upper false
    linarith [(upper_spec false).1]
  have h64 : WindowEdgeCertified.upper ∈ Ioi (-(1 / (20 : ℝ)^3)) := by
    change -(1 / (20 : ℝ)^3) < WindowEdgeCertified.upper
    linarith [WindowEdgeCertified.upper_spec.1]
  have h128 : upper true ∈ Ioi (-(1 / (20 : ℝ)^3)) := by
    change -(1 / (20 : ℝ)^3) < upper true
    linarith [(upper_spec true).1]
  constructor
  · apply (hm.lt_iff_gt h64 h32).mp
    rw [WindowEdgeCertified.upper_spec.2.1, (upper_spec false).2.1]
    exact threshold_order.2
  · apply (hm.lt_iff_gt h128 h64).mp
    rw [(upper_spec true).2.1, WindowEdgeCertified.upper_spec.2.1]
    exact threshold_order.1

theorem gate_inclusions (lam : ℝ) :
    (realizedGate false lam → WindowSample.realizedGate lam) ∧
      (WindowSample.realizedGate lam → realizedGate true lam) := by
  rw [(upper_spec false).2.2 lam, WindowEdgeCertified.upper_spec.2.2 lam,
    (upper_spec true).2.2 lam]
  exact ⟨fun h => ⟨h.1, h.2.trans upper_order.1.le⟩,
    fun h => ⟨h.1, h.2.trans upper_order.2.le⟩⟩

/-- The two set inclusions are strict, witnessed at actual endpoint parameters. -/
theorem strict_gate_witnesses :
    (WindowSample.realizedGate WindowEdgeCertified.upper ∧
      ¬ realizedGate false WindowEdgeCertified.upper) ∧
    (realizedGate true (upper true) ∧ ¬ WindowSample.realizedGate (upper true)) := by
  rw [WindowEdgeCertified.upper_spec.2.2 WindowEdgeCertified.upper,
    (upper_spec false).2.2 WindowEdgeCertified.upper,
    (upper_spec true).2.2 (upper true), WindowEdgeCertified.upper_spec.2.2 (upper true)]
  refine ⟨⟨⟨by linarith [WindowEdgeCertified.upper_spec.1], le_rfl⟩,
    fun h => upper_order.1.not_ge h.2⟩, ⟨⟨by linarith [(upper_spec true).1], le_rfl⟩,
    fun h => upper_order.2.not_ge h.2⟩⟩

theorem zero_passes (v : Bool) : realizedGate v 0 := by
  rw [(upper_spec v).2.2]
  exact ⟨by norm_num, (upper_spec v).1.le⟩

theorem cutoff_fails (v : Bool) : ¬ realizedGate v (-(1 / 8000)) := by
  rw [(upper_spec v).2.2]
  exact fun h => lt_irrefl _ h.1

end
end SbtCosmo.Derivation.WindowPatchCounts
