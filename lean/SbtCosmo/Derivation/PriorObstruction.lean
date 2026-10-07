import Mathlib.Tactic

/-!
Exact mixture obstruction for the frozen, equal-seed base measure.
The 44 reified count pairs concern the original full-support top-decade band.
They are checked against the decimal CSV by the construction receipt script.
This does not certify the accuracy of the upstream ODE computations.
-/
namespace SbtCosmo.Derivation.PriorObstruction

noncomputable section
open Finset

theorem weighted_ratio_bound {n : Type*} [Fintype n]
    (weight numerator denominator : n → ℝ) (bound : ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hb : ∀ i, numerator i ≤ bound * denominator i)
    (htotal : 0 < ∑ i, weight i * denominator i) :
    (∑ i, weight i * numerator i) / (∑ i, weight i * denominator i) ≤ bound := by
  apply (div_le_iff₀ htotal).2
  calc
    ∑ i, weight i * numerator i ≤ ∑ i, weight i * (bound * denominator i) :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i)
    _ = bound * ∑ i, weight i * denominator i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring

/-- Increasing lambda order: forty zero-top groups, then 2/12, 4/12,
7/12, 8/11. Counts use the full retained RS-passing seed distribution. -/
def baseCounts (i : Fin 44) : ℝ × ℝ :=
  if i.val < 40 then (0, 12)
  else if i.val = 40 then (2, 12)
  else if i.val = 41 then (4, 12)
  else if i.val = 42 then (7, 12)
  else (8, 11)

theorem base_counts_bound (i : Fin 44) :
    (baseCounts i).1 ≤ (8 / 11 : ℝ) * (baseCounts i).2 := by
  unfold baseCounts
  split_ifs <;> norm_num

/-- No prior reweighting of lambda alone reaches 80% in this fixed band.
Strictly positive priors preserve the original maximum and hence this band. -/
theorem base_prior_cannot_collapse (weight : Fin 44 → ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (htotal : 0 < ∑ i, weight i * (baseCounts i).2) :
    (∑ i, weight i * (baseCounts i).1) /
        (∑ i, weight i * (baseCounts i).2) ≤ (8 / 11 : ℝ) ∧
      (∑ i, weight i * (baseCounts i).1) /
        (∑ i, weight i * (baseCounts i).2) < (4 / 5 : ℝ) := by
  have h := weighted_ratio_bound weight (fun i => (baseCounts i).1)
    (fun i => (baseCounts i).2) (8 / 11) hw base_counts_bound htotal
  exact ⟨h, lt_of_le_of_lt h (by norm_num)⟩

end
end SbtCosmo.Derivation.PriorObstruction
