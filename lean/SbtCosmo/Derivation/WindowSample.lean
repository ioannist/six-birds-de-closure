import SbtCosmo.Derivation.GrowthPopulation
import SbtCosmo.Derivation.WindowSampleData

/-! The original realized 12×64 population has an exact two-sided continuum window.
The input realization is kernel-checked; its deterministic NumPy provenance is separate. -/
namespace SbtCosmo.Derivation.WindowSample
noncomputable section
open Set GrowthPopulation GrowthScaleReturn GrowthLimit WindowSampleData
attribute [local instance] Classical.propDecidable

def amplitude (j : Fin 12) (i : Fin 64) : ℝ := amplitudeRat j i
def maximumFalse (j : Fin 12) : ℝ := maximumFalseRat j
def maximumTrue (j : Fin 12) : ℝ := maximumTrueRat j
def seedThreshold (j : Fin 12) : ℝ := thresholdRat j
def delta : ℝ := deltaRat
def aggregateThreshold : ℝ := aggregateRat

theorem sampled_maxima (j : Fin 12) :
    (∀ i, 0 ≤ amplitude j i) ∧ 0 < maximumFalse j ∧ 0 < maximumTrue j ∧
      WindowRecords.TagMaximum (amplitude j) (tag j) false (maximumFalse j) ∧
      WindowRecords.TagMaximum (amplitude j) (tag j) true (maximumTrue j) := by
  dsimp only [amplitude, maximumFalse, maximumTrue]
  obtain ⟨hm0, hm1, hf, haf, ht, hat, hb⟩ := rational_maxima_certificate j
  refine ⟨?_, ?_, ?_, ⟨⟨falseIndex j, hf, ?_⟩, ?_⟩, ⟨⟨trueIndex j, ht, ?_⟩, ?_⟩⟩
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

theorem seedThreshold_eq (j : Fin 12) :
    seedThreshold j = max (delta / maximumFalse j) (delta / maximumTrue j) := by
  dsimp only [seedThreshold, delta, maximumFalse, maximumTrue]
  exact_mod_cast rational_threshold_certificate j

theorem sampled_rank_counts :
    (Finset.univ.filter (fun j => seedThreshold j < aggregateThreshold)).card = 9 ∧
      passingCount seedThreshold aggregateThreshold = 10 := by
  simpa only [seedThreshold, aggregateThreshold, passingCount, Rat.cast_lt, Rat.cast_le]
    using rational_rank_certificate

theorem sampled_count_iff_threshold (x : ℝ) :
    10 ≤ passingCount seedThreshold x ↔ aggregateThreshold ≤ x := by
  apply passingCount_iff_rank
  · rw [sampled_rank_counts.1]
    norm_num
  · exact sampled_rank_counts.2.ge

theorem sampled_threshold_bounds : (3 : ℝ) / 2 < aggregateThreshold ∧
    aggregateThreshold < 20000 := by
  constructor
  · change (3 : ℝ) / 2 < (aggregateRat : ℝ)
    have h : (((3 : ℚ) / 2 : ℚ) : ℝ) < (aggregateRat : ℝ) :=
      Rat.cast_lt.mpr rational_window_bounds.1
    convert h using 1
    norm_num
  · change (aggregateRat : ℝ) < 20000
    exact_mod_cast rational_window_bounds.2

theorem sampled_threshold_exact :
    aggregateThreshold = (971912828383572000768 : ℝ) / 1012057850670495125 := by
  norm_num [aggregateThreshold, aggregateRat]

theorem sampled_delta_exact : delta = (843 : ℝ) / 500 := by
  norm_num [delta, deltaRat]

/-- The declared 80% of twelve seeds means at least ten passes, including equality. -/
theorem seed_fraction_iff (passing : ℕ) :
    (4 / 5 : ℝ) ≤ (passing : ℝ) / 12 ↔ 10 ≤ passing := by
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
  constructor
  · intro h
    by_contra hn
    have hn9 : passing ≤ 9 := by omega
    have hn9r : (passing : ℝ) ≤ 9 := by exact_mod_cast hn9
    norm_num at h
    linarith
  · intro h
    have hr : (10 : ℝ) ≤ passing := by exact_mod_cast h
    norm_num
    linarith

def realizedGate (lam : ℝ) : Prop := nativeAggregate amplitude tag (1 / 1000) 20 delta 10 lam

theorem realized_gate_iff_seed_fraction (lam : ℝ) :
    realizedGate lam ↔ -(1 / (20 : ℝ)^3) < lam ∧
      (4 / 5 : ℝ) ≤ ((Finset.univ.filter
        (fun j => nativeRecord (amplitude j) (tag j) (1 / 1000) 20 delta lam)).card : ℝ) / 12 := by
  unfold realizedGate nativeAggregate
  rw [seed_fraction_iff]

theorem realized_gate_iff_threshold (lam : ℝ) :
    realizedGate lam ↔ -(1 / 8000 : ℝ) < lam ∧
      aggregateThreshold ≤ nativeGrowth (1 / 1000) lam 20 := by
  have hbelow : (Finset.univ.filter
      (fun j => max (delta / maximumFalse j) (delta / maximumTrue j) < aggregateThreshold)).card < 10 := by
    simpa only [← seedThreshold_eq, sampled_rank_counts.1] using (show 9 < 10 by decide)
  have hat : 10 ≤ passingCount
      (fun j => max (delta / maximumFalse j) (delta / maximumTrue j)) aggregateThreshold := by
    simpa only [← seedThreshold_eq] using sampled_rank_counts.2.ge
  have h := native_aggregate_iff_threshold (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (1 / 1000 : ℝ) ≤ 20)
    (fun j => (sampled_maxima j).1) (fun j => (sampled_maxima j).2.2.2.1)
    (fun j => (sampled_maxima j).2.2.2.2) (fun j => (sampled_maxima j).2.1)
    (fun j => (sampled_maxima j).2.2.1) hbelow hat lam
  norm_num [realizedGate] at h ⊢
  exact h

/-- Original twelve-seed continuum window, with every population/rank premise discharged. -/
theorem exists_unique_realized_window :
    ∃! upper : ℝ, 0 < upper ∧ nativeGrowth (1 / 1000) upper 20 = aggregateThreshold ∧
      ∀ lam : ℝ, realizedGate lam ↔ -(1 / 8000 : ℝ) < lam ∧ lam ≤ upper := by
  have hTinf : freeGrowth (Real.log ((20 : ℝ) / (1 / 1000))) < aggregateThreshold := by
    unfold freeGrowth
    have he := Real.exp_pos (-2 * Real.log ((20 : ℝ) / (1 / 1000)))
    linarith [sampled_threshold_bounds.1]
  have hTzero : aggregateThreshold < (20 : ℝ) / (1 / 1000) := by
    norm_num
    exact sampled_threshold_bounds.2
  obtain ⟨upper, hu, huniq⟩ := GrowthWindow.exists_unique_native_threshold_window
    (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num : (1 / 1000 : ℝ) < 20) hTinf hTzero
  refine ⟨upper, ⟨hu.1, hu.2.1, ?_⟩, ?_⟩
  · intro lam
    have hw := hu.2.2 lam
    have hcut : -(1 / (20 : ℝ)^3) = -(1 / 8000 : ℝ) := by norm_num
    rw [hcut] at hw
    exact (realized_gate_iff_threshold lam).trans hw
  · intro other ho
    apply huniq other
    refine ⟨ho.1, ho.2.1, ?_⟩
    intro lam
    have hw := (realized_gate_iff_threshold lam).symm.trans (ho.2.2 lam)
    have hcut : -(1 / (20 : ℝ)^3) = -(1 / 8000 : ℝ) := by norm_num
    rw [hcut]
    exact hw

end
end SbtCosmo.Derivation.WindowSample
