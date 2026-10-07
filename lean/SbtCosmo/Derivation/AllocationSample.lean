import SbtCosmo.Derivation.AllocationSampleData
import SbtCosmo.Derivation.AllocationScreening

/-! Exact returns to the original 32-patch IEEE allocation inputs and budgets.
Numerical optimizer outputs and finite-difference accuracy are not premises. -/
namespace SbtCosmo.Derivation.AllocationSample
noncomputable section
open AllocationPrice AllocationSensitivity AllocationScreening Set

def weights (i : Fin 32) : ℝ := AllocationSampleData.weight i
def curvatures (i : Fin 32) : ℝ := AllocationSampleData.curvature i
def budget : ℝ := AllocationSampleData.budget
def budgets (j : Fin 10) : ℝ := AllocationSampleData.budgets j
def offsets (j : Fin 3) : ℝ := AllocationSampleData.offsets j

theorem weights_positive (i : Fin 32) : 0 < weights i := by
  have h : (7/10:ℝ) < weights i := by
    dsimp [weights]
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr (AllocationSampleData.parameter_bounds i).1
  linarith
theorem curvatures_positive (i : Fin 32) : 0 < curvatures i := by
  have h : (1/5:ℝ) < curvatures i := by
    dsimp [curvatures]
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr (AllocationSampleData.parameter_bounds i).2.2.1
  linarith
theorem budget_bounds : (22:ℝ) < budget ∧ budget < 23 := by
  dsimp [budget]
  exact_mod_cast AllocationSampleData.budget_bounds.2
theorem budgets_positive (j : Fin 10) : 0 < budgets j := by
  dsimp [budgets]
  exact_mod_cast AllocationSampleData.budget_bounds.1 j

def price (s : ℝ) : ℝ := selectedPrice weights curvatures (fun _ => s)
  weights_positive curvatures_positive budget
def allocation (s : ℝ) : Fin 32 → ℝ := selectedAllocation weights curvatures (fun _ => s)
  weights_positive curvatures_positive budget
def value (s B : ℝ) : ℝ := costValue weights curvatures (fun _ => s)
  weights_positive curvatures_positive B
def response (q : Fin 5) (i : Fin 32) : ℝ :=
  demand (weights i) (curvatures i) 0 (AllocationSampleData.price q)

theorem response_cells (q : Fin 5) (i : Fin 32) :
    (AllocationSampleData.lower q i:ℝ) ≤ response q i ∧ response q i ≤ (AllocationSampleData.upper q i:ℝ) := by
  have h : 0 < (AllocationSampleData.lower q i:ℝ) ∧ (AllocationSampleData.lower q i:ℝ) ≤ (AllocationSampleData.upper q i:ℝ) ∧
      (AllocationSampleData.price q:ℝ) ≤ weights i/(1+(AllocationSampleData.lower q i:ℝ))-curvatures i*(AllocationSampleData.lower q i:ℝ) ∧
      weights i/(1+(AllocationSampleData.upper q i:ℝ))-curvatures i*(AllocationSampleData.upper q i:ℝ) ≤ (AllocationSampleData.price q:ℝ) := by
    dsimp [weights,curvatures]
    exact_mod_cast AllocationSampleData.cells q i
  exact demand_margin_bounds (weights_positive i) (curvatures_positive i) h.1.le
    (h.1.le.trans h.2.1) (by simpa only [marginal,add_zero] using h.2.2.1)
    (by simpa only [marginal,add_zero] using h.2.2.2)

theorem response_mass_bounds (q : Fin 5) :
    (∑ i, (AllocationSampleData.lower q i:ℝ)) ≤ mass (response q) ∧
      mass (response q) ≤ ∑ i, (AllocationSampleData.upper q i:ℝ) := by
  exact ⟨Finset.sum_le_sum (fun i _ => (response_cells q i).1),
    Finset.sum_le_sum (fun i _ => (response_cells q i).2)⟩

theorem original_price_bounds : (46112:ℝ)/100000 < price 0 ∧ price 0 < 46113/100000 := by
  have hd : budget < (∑ i, (AllocationSampleData.lower 1 i:ℝ)) ∧
      (∑ i, (AllocationSampleData.upper 2 i:ℝ)) < budget := by
    dsimp [budget]
    exact_mod_cast AllocationSampleData.price_mass_bounds
  have hl := hd.1.trans_le (response_mass_bounds 1).1
  have hh := (response_mass_bounds 2).2.trans_lt hd.2
  apply selected_price_response_bounds weights_positive curvatures_positive
    (by linarith [budget_bounds.1]) (by norm_num)
  · have hp1 : (AllocationSampleData.price 1:ℝ) = 46112/100000 := by
      norm_num [AllocationSampleData.price]
    simpa only [mass,response,hp1] using hl
  · have hp2 : (AllocationSampleData.price 2:ℝ) = 46113/100000 := by
      norm_num [AllocationSampleData.price,Matrix.cons_val_two]
    simpa only [mass,response,hp2] using hh

theorem actual_kkt (s : ℝ) : AllocationKKT weights curvatures (fun _ => s)
    (allocation s) budget (price s) :=
  selected_kkt weights_positive curvatures_positive (by linarith [budget_bounds.1])

theorem actual_global_optimal (s : ℝ) {x : Fin 32 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hb : mass x ≤ budget) :
    utility weights curvatures (fun _ => s) x ≤
      utility weights curvatures (fun _ => s) (allocation s)-penalty curvatures (allocation s) x :=
  kkt_global_optimal (fun i => (weights_positive i).le) (actual_kkt s) hx hb

theorem actual_unique_optimizer (s : ℝ) {x : Fin 32 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hb : mass x ≤ budget)
    (hu : utility weights curvatures (fun _ => s) (allocation s) ≤ utility weights curvatures (fun _ => s) x) :
    allocation s = x :=
  kkt_unique_optimizer (fun i => (weights_positive i).le) curvatures_positive (actual_kkt s) hx hb hu

theorem original_active : mass (allocation 0) = budget := by
  have hk := actual_kkt 0
  have hp : 0 < price 0 := by linarith [original_price_bounds.1]
  have hz := (mul_eq_zero.mp hk.budget_complementarity).resolve_left hp.ne'
  linarith

theorem original_allocations_positive (i : Fin 32) : 0 < allocation 0 i := by
  apply demand_positive (weights_positive i) (curvatures_positive i)
  have hw : (7/10:ℝ) < weights i := by
    dsimp [weights]
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr (AllocationSampleData.parameter_bounds i).1
  have hp : price 0 < weights i+0 := by linarith [original_price_bounds.2]
  exact hp

theorem original_stationarity (i : Fin 32) :
    marginal (weights i) (curvatures i) 0 (allocation 0 i) = price 0 :=
  marginal_eq_price_at_positive (actual_kkt 0) (original_allocations_positive i)

theorem original_heterogeneity : allocation 0 0 < allocation 0 1 := by
  have hd : weights 0 < weights 1 ∧ curvatures 1 < curvatures 0 := by
    dsimp [weights,curvatures]
    exact_mod_cast AllocationSampleData.heterogeneity_order
  have hx := (actual_kkt 0).nonnegative 0
  have hy := (actual_kkt 0).nonnegative 1
  have hw := div_lt_div_of_pos_right hd.1 (by linarith : 0 < 1+allocation 0 0)
  have hc := mul_le_mul_of_nonneg_right hd.2.le hx
  have hm : marginal (weights 0) (curvatures 0) 0 (allocation 0 0) <
      marginal (weights 1) (curvatures 1) 0 (allocation 0 0) := by
    unfold marginal
    linarith
  by_contra hn
  have hs := (marginal_strictAntiOn (b := (0:ℝ)) (weights_positive 1).le
    (curvatures_positive 1)).antitoneOn hy hx (le_of_not_gt hn)
  rw [original_stationarity 0] at hm
  rw [original_stationarity 1] at hs
  linarith

theorem screening {s : ℝ} (hs : s ∈ Icc (-(1/4)) (1/4)) :
    allocation s = allocation 0 ∧ price s = price 0+s := by
  have hp : 0 ≤ price 0+s := by linarith [original_price_bounds.1,hs.1]
  simpa only [price,allocation,zero_add] using selected_offset_screened
    weights_positive curvatures_positive (by linarith [budget_bounds.1]) original_active hp

theorem screened_positive_price {s : ℝ} (hs : s ∈ Icc (-(1/4)) (1/4)) : 0 < price s := by
  rw [(screening hs).2]
  linarith [original_price_bounds.1,hs.1]

theorem screened_active {s : ℝ} (hs : s ∈ Icc (-(1/4)) (1/4)) : mass (allocation s) = budget := by
  rw [(screening hs).1,original_active]

theorem screened_stationarity {s : ℝ} (hs : s ∈ Icc (-(1/4)) (1/4)) (i : Fin 32) :
    marginal (weights i) (curvatures i) s (allocation s i) = price s := by
  apply marginal_eq_price_at_positive (actual_kkt s)
  rw [(screening hs).1]
  exact original_allocations_positive i

theorem screened_value {s : ℝ} (hs : s ∈ Icc (-(1/4)) (1/4)) :
    value s budget = value 0 budget-s*budget := by
  have hp : 0 ≤ price 0+s := by linarith [original_price_bounds.1,hs.1]
  simpa only [value,zero_add] using selected_cost_offset_return
    weights_positive curvatures_positive (by linarith [budget_bounds.1]) original_active hp

theorem original_offsets_return (j : Fin 3) :
    allocation (offsets j) = allocation 0 ∧ price (offsets j) = price 0+offsets j := by
  have hs : offsets j ∈ Icc (-(1/4)) (1/4) := by
    change -(1/4:ℝ) ≤ (AllocationSampleData.offsets j:ℝ) ∧ (AllocationSampleData.offsets j:ℝ) ≤ 1/4
    have h := AllocationSampleData.original_offsets.1 j
    constructor
    · simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h.1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h.2
  exact screening hs

theorem actual_value_derivative {B : ℝ} (hB : 0 < B) (s : ℝ) :
    HasDerivAt (value s) (-selectedPrice weights curvatures (fun _ => s)
      weights_positive curvatures_positive B) B :=
  cost_value_hasDerivAt weights_positive curvatures_positive hB

theorem original_negative_value_derivative : deriv (value 0) budget = -price 0 ∧
    deriv (value 0) budget < 0 := by
  have he : deriv (value 0) budget = -price 0 := (actual_value_derivative (by linarith [budget_bounds.1]) 0).deriv
  exact ⟨he,by rw [he]; linarith [original_price_bounds.1]⟩

theorem sweep_active {j : Fin 10} (hj : j.val < 7) :
    0 < selectedPrice weights curvatures (fun _ => 0) weights_positive curvatures_positive (budgets j) ∧
      mass (selectedAllocation weights curvatures (fun _ => 0)
        weights_positive curvatures_positive (budgets j)) = budgets j := by
  have hd : budgets j < ∑ i, (AllocationSampleData.lower 0 i:ℝ) := by
    have hq : AllocationSampleData.budgets j < ∑ i, AllocationSampleData.lower 0 i := by
      simpa only [if_pos hj] using AllocationSampleData.sweep_mass_bounds j
    dsimp [budgets]
    exact_mod_cast hq
  have hm : budgets j < mass (fun i => demand (weights i) (curvatures i) 0 0) := by
    have hb := hd.trans_le (response_mass_bounds 0).1
    have hp0 : (AllocationSampleData.price 0:ℝ) = 0 := by norm_num [AllocationSampleData.price]
    simpa only [mass,response,hp0] using hb
  exact ⟨below_unconstrained_price_positive weights_positive curvatures_positive
    (budgets_positive j).le hm,below_unconstrained_budget_active weights_positive
      curvatures_positive (budgets_positive j).le hm⟩

theorem sweep_slack {j : Fin 10} (hj : 7 ≤ j.val) :
    selectedPrice weights curvatures (fun _ => 0) weights_positive curvatures_positive (budgets j) = 0 ∧
      mass (selectedAllocation weights curvatures (fun _ => 0)
        weights_positive curvatures_positive (budgets j)) < budgets j := by
  have hd : (∑ i, (AllocationSampleData.upper 0 i:ℝ)) < budgets j := by
    have hq : (∑ i, AllocationSampleData.upper 0 i) < AllocationSampleData.budgets j := by
      simpa only [if_neg (by omega : ¬j.val < 7)] using AllocationSampleData.sweep_mass_bounds j
    dsimp [budgets]
    exact_mod_cast hq
  have hm : mass (fun i => demand (weights i) (curvatures i) 0 0) < budgets j := by
    have hb := (response_mass_bounds 0).2.trans_lt hd
    have hp0 : (AllocationSampleData.price 0:ℝ) = 0 := by norm_num [AllocationSampleData.price]
    simpa only [mass,response,hp0] using hb
  have hp := above_unconstrained_price_zero weights_positive curvatures_positive (budgets_positive j) hm.le
  refine ⟨hp,?_⟩
  unfold selectedAllocation
  rw [hp]
  exact hm

end
end SbtCosmo.Derivation.AllocationSample
