import SbtCosmo.Derivation.AllocationSensitivity

/-! Actual selected-allocation screening and response certificates.
The original objective and KKT selector remain unchanged. -/
namespace SbtCosmo.Derivation.AllocationScreening
noncomputable section
open AllocationPrice AllocationSensitivity Set

theorem demand_margin_bounds {w c b p lo hi : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hml : p ≤ marginal w c b lo) (hmh : marginal w c b hi ≤ p) :
    lo ≤ demand w c b p ∧ demand w c b p ≤ hi := by
  have hd := demand_nonnegative w c b p
  have hm := marginal_strictAntiOn (b := b) hw.le hc
  constructor
  · by_contra hn
    have hlt := hm hd hlo (lt_of_not_ge hn)
    have hbound := (demand_certificate (b := b) (p := p) hw hc).1
    linarith
  · by_contra hn
    have hlt : hi < demand w c b p := lt_of_not_ge hn
    have he := demand_stationary_of_positive hw hc (hhi.trans_lt hlt)
    have hstrict := hm hhi hd hlt
    rw [he] at hstrict
    linarith

theorem demand_strict_parameter {w c b p q : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hpq : p < q) (hq : q < w+b) : demand w c b q < demand w c b p := by
  have hle := demand_antitone (b := b) hw hc hpq.le
  have hs := demand_stationary hw hc hq
  have ht := demand_stationary hw hc (hpq.trans hq)
  apply lt_of_le_of_ne hle
  intro he
  rw [he] at hs
  linarith

theorem demand_offset_return (w c s : ℝ) : demand w c s 0 = demand w c 0 (-s) := by
  simp only [demand,sub_zero,zero_sub]

variable {ι : Type*} [Fintype ι]

theorem selected_price_response_bounds {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B lo hi : ℝ}
    (hB : 0 < B) (hlo : 0 < lo)
    (hl : B < mass (fun i => demand (w i) (c i) (b i) lo))
    (hh : mass (fun i => demand (w i) (c i) (b i) hi) < B) :
    lo < selectedPrice w c b hw hc B ∧ selectedPrice w c b hw hc B < hi := by
  have hk := selected_kkt (b := b) hw hc hB.le
  have hlow : lo < selectedPrice w c b hw hc B := by
    by_contra hn
    have hm : mass (fun i => demand (w i) (c i) (b i) lo) ≤
        mass (selectedAllocation w c b hw hc B) :=
      Finset.sum_le_sum (fun i _ => demand_antitone (hw i) (hc i) (le_of_not_gt hn))
    linarith [hk.feasible]
  have hp : 0 < selectedPrice w c b hw hc B := hlo.trans hlow
  have hactive : mass (selectedAllocation w c b hw hc B) = B := by
    have he := (mul_eq_zero.mp hk.budget_complementarity).resolve_left hp.ne'
    linarith
  refine ⟨hlow,?_⟩
  by_contra hn
  have hm : mass (selectedAllocation w c b hw hc B) ≤
      mass (fun i => demand (w i) (c i) (b i) hi) :=
    Finset.sum_le_sum (fun i _ => demand_antitone (hw i) (hc i) (le_of_not_gt hn))
  linarith

theorem selected_offset_screened {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B s : ℝ} (hB : 0 < B)
    (ha : mass (selectedAllocation w c b hw hc B) = B)
    (hp : 0 ≤ selectedPrice w c b hw hc B+s) :
    selectedAllocation w c (fun i => b i+s) hw hc B = selectedAllocation w c b hw hc B ∧
      selectedPrice w c (fun i => b i+s) hw hc B = selectedPrice w c b hw hc B+s :=
  kkt_unique (fun i => (hw i).le) hc (selected_kkt hw hc hB.le)
    (active_offset_kkt (selected_kkt hw hc hB.le) ha s hp) hB

theorem utility_offset_return (w c b x : ι → ℝ) (s : ℝ) :
    utility w c (fun i => b i+s) x = utility w c b x+s*mass x := by
  unfold utility localUtility mass
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem selected_cost_offset_return {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B s : ℝ} (hB : 0 < B)
    (ha : mass (selectedAllocation w c b hw hc B) = B)
    (hp : 0 ≤ selectedPrice w c b hw hc B+s) :
    costValue w c (fun i => b i+s) hw hc B = costValue w c b hw hc B-s*B := by
  unfold costValue
  rw [(selected_offset_screened hw hc hB ha hp).1,utility_offset_return,ha]
  ring

end
end SbtCosmo.Derivation.AllocationScreening
