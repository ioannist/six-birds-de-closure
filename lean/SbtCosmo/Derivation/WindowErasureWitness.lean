import SbtCosmo.Derivation.GrowthNegativeLower
import SbtCosmo.Derivation.WindowSample
import SbtCosmo.Derivation.WindowErasureData

/-! The negative outside witness: actual original IVP collapse histories,
followed by the explicitly declared toy erasure at turnaround. -/
namespace SbtCosmo.Derivation.WindowErasureWitness
noncomputable section
open Set GrowthComparison GrowthScaleReturn GrowthNegativeBounds GrowthNegativeLower
open WindowSample WindowSampleData WindowErasureData
attribute [local instance] Classical.propDecidable

/-- Exact IEEE-754 outside parameter from the original full-precision readout. -/
def outside : ℝ := -(1245155224975395 / 4611686018427387904)

theorem exists_unique_turnaround :
    ∃! t : ℝ, t ∈ Icc (77 / 5) (31 / 2) ∧ t^3 = 4611686018427387904 / 1245155224975395 := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (a := (77 : ℝ) / 5) (b := 31 / 2)
    (f := fun t : ℝ => t^3) (by norm_num) (by fun_prop)
    (show (4611686018427387904 : ℝ) / 1245155224975395 ∈ Icc ((77 / 5)^3) ((31 / 2)^3) by norm_num)
  refine ⟨t, ⟨ht, he⟩, ?_⟩
  intro b hb
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hb0 : 0 ≤ b := by linarith [hb.1.1]
  exact (pow_left_inj₀ hb0 ht0 (by decide : (3 : ℕ) ≠ 0)).mp (hb.2.trans he.symm)

def turnaround : ℝ := exists_unique_turnaround.choose

theorem turnaround_spec : 77 / 5 < turnaround ∧ turnaround < 31 / 2 ∧
    turnaround^3 = 4611686018427387904 / 1245155224975395 := by
  have hs : turnaround ∈ Icc (77 / 5) (31 / 2) ∧ turnaround^3 = 4611686018427387904 / 1245155224975395 :=
    exists_unique_turnaround.choose_spec.1
  have hlo : turnaround ≠ 77 / 5 := by intro h; rw [h] at hs; norm_num at hs
  have hhi : turnaround ≠ 31 / 2 := by intro h; rw [h] at hs; norm_num at hs
  exact ⟨lt_of_le_of_ne hs.1.1 (Ne.symm hlo), lt_of_le_of_ne hs.1.2 hhi, hs.2⟩

theorem live_before_turnaround {a : ℝ} (ha : 0 < a) (ht : a < turnaround) :
    -(1 / a^3) < outside := by
  have ht0 : 0 < turnaround := by linarith [turnaround_spec.1]
  have hp := pow_lt_pow_left₀ ht ha.le (by decide : (3 : ℕ) ≠ 0)
  rw [turnaround_spec.2.2] at hp
  unfold outside
  rw [neg_lt_neg_iff]
  apply (lt_div_iff₀ (pow_pos ha 3)).mpr
  nlinarith

theorem growth_at_fifteen : 17000 < nativeGrowth (1 / 1000) outside 15 := by
  have hl := native_lower (a0 := (1 : ℝ) / 1000) (a := 15) (lam := outside)
    (by norm_num) (by norm_num)
    (by norm_num [outside]) (by norm_num [outside])
  have he : Real.exp (Real.log (15000 : ℝ)) = 15000 := Real.exp_log (by norm_num)
  have h4 : Real.exp (4 * Real.log (15000 : ℝ)) = 15000^4 := by
    simpa only [Nat.cast_ofNat, he] using Real.exp_nat_mul (Real.log (15000 : ℝ)) 4
  have hlog : Real.log (15000 : ℝ) ≤ 14999 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 15000) using 1
    norm_num
  norm_num [logScale, outside, lowerGrowth, he, h4] at hl
  unfold outside
  nlinarith

theorem growth_before_turnaround {a : ℝ} (ha : (1 : ℝ) / 1000 ≤ a)
    (ht : a < turnaround) : nativeGrowth (1 / 1000) outside a < 26000 := by
  have hap : 0 < a := by linarith
  have hg := native_linear_upper (by norm_num : (0 : ℝ) < 1 / 1000) ha
    (live_before_turnaround hap ht) (by norm_num [outside])
  have hat : a < 31 / 2 := ht.trans turnaround_spec.2.1
  norm_num at hg
  linarith

def preCollapsed (i : Fin 64) : Prop :=
  ∃ a ∈ Ico ((1 : ℝ) / 1000) turnaround,
    delta ≤ amplitude 0 i * nativeGrowth (1 / 1000) outside a

theorem collapse_gap (i : Fin 64) :
    delta ≤ amplitude 0 i * 17000 ↔ delta ≤ amplitude 0 i * 26000 := by
  have h := gap_certificate i
  dsimp only [collapsedRat] at h
  dsimp only [delta, amplitude]
  exact_mod_cast h

theorem preCollapsed_iff (i : Fin 64) : preCollapsed i ↔ delta ≤ amplitude 0 i * 17000 := by
  have ha := (sampled_maxima 0).1 i
  constructor
  · rintro ⟨a, hmem, hc⟩
    apply (collapse_gap i).mpr
    exact hc.trans (mul_le_mul_of_nonneg_left (growth_before_turnaround hmem.1 hmem.2).le ha)
  · intro hc
    refine ⟨15, ⟨by norm_num, by linarith [turnaround_spec.1]⟩, ?_⟩
    exact hc.trans (mul_le_mul_of_nonneg_left growth_at_fifteen.le ha)

theorem pre_count : (Finset.univ.filter preCollapsed).card = 58 := by
  have hf : Finset.univ.filter preCollapsed = Finset.univ.filter (collapsedRat 17000) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, preCollapsed_iff]
    dsimp only [collapsedRat, delta, amplitude]
    exact_mod_cast (Iff.rfl : deltaRat ≤ amplitudeRat 0 i * 17000 ↔ deltaRat ≤ amplitudeRat 0 i * 17000)
  rw [hf]
  exact count_at_lower

theorem pre_both_tags : WindowRecords.RecordBearing preCollapsed (tag 0) := by
  have h := tags_at_lower
  refine ⟨54, 58, (preCollapsed_iff 54).mpr ?_, (preCollapsed_iff 58).mpr ?_, ?_⟩
  · dsimp only [delta, amplitude]
    have hc := h.2.1
    dsimp only [collapsedRat] at hc
    exact_mod_cast hc
  · dsimp only [delta, amplitude]
    have hc := h.2.2.2
    dsimp only [collapsedRat] at hc
    exact_mod_cast hc
  · rw [h.1, h.2.2.1]
    decide

/-- Exact mathematical counterpart of the original 1e-8 turnaround buffer. -/
def stopScale : ℝ := min 20 (turnaround * (1 - 1 / 100000000))

theorem stopScale_bounds : 15 < stopScale ∧ stopScale < turnaround := by
  have h := turnaround_spec
  have ht0 : 0 < turnaround := by linarith
  unfold stopScale
  constructor
  · exact lt_min (by norm_num) (by nlinarith [h.1])
  · exact (min_le_right _ _).trans_lt (by nlinarith)

def stoppedCollapsed (i : Fin 64) : Prop :=
  ∃ a ∈ Icc ((1 : ℝ) / 1000) stopScale,
    delta ≤ amplitude 0 i * nativeGrowth (1 / 1000) outside a

theorem stoppedCollapsed_iff (i : Fin 64) : stoppedCollapsed i ↔ preCollapsed i := by
  constructor
  · rintro ⟨a, ha, hc⟩
    exact ⟨a, ⟨ha.1, ha.2.trans_lt stopScale_bounds.2⟩, hc⟩
  · intro h
    refine ⟨15, ⟨by norm_num, stopScale_bounds.1.le⟩, ?_⟩
    exact ((preCollapsed_iff i).mp h).trans
      (mul_le_mul_of_nonneg_left growth_at_fifteen.le ((sampled_maxima 0).1 i))

theorem stopped_count : (Finset.univ.filter stoppedCollapsed).card = 58 := by
  have hf : Finset.univ.filter stoppedCollapsed = Finset.univ.filter preCollapsed := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, stoppedCollapsed_iff]
  rw [hf]
  exact pre_count

theorem stopped_both_tags : WindowRecords.RecordBearing stoppedCollapsed (tag 0) := by
  simpa only [WindowRecords.RecordBearing, stoppedCollapsed_iff] using pre_both_tags

theorem turnaround_before_horizon : turnaround < 20 := by linarith [turnaround_spec.2.1]

theorem turnaround_zero : 1 / turnaround^3 + outside = 0 := by
  rw [turnaround_spec.2.2]
  norm_num [outside]

theorem outside_excluded : ¬ realizedGate outside := by
  intro h
  have hc := h.1
  norm_num [outside] at hc

/-- The carrier's stipulated erasure law: records persist iff no turnaround by a_max.
This is a toy policy, not a theorem of physical evolution through a big crunch. -/
def retained (i : Fin 64) : Prop := stoppedCollapsed i ∧ 20 < turnaround

theorem no_retained (i : Fin 64) : ¬ retained i := by
  rintro ⟨_, ht⟩
  linarith [turnaround_before_horizon]

theorem final_count : (Finset.univ.filter retained).card = 0 := by
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact no_retained i

theorem final_not_bearing : ¬ WindowRecords.RecordBearing retained (tag 0) := by
  rintro ⟨i, _, hi, _, _⟩
  exact no_retained i hi

end
end SbtCosmo.Derivation.WindowErasureWitness
