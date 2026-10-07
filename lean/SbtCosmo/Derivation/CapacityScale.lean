import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
Finite cut objective versus prices, and a constructed common-capacity-scale
price. A fixed capacity shape and a scale coordinate are explicitly supplied;
the optional throughput ceiling is an added constraint. None is a physical
Lambda or continuum RT identification.
-/
namespace SbtCosmo.Derivation.CapacityScale

noncomputable section
open scoped BigOperators Topology

section Cuts

variable {K E : Type*} [Fintype E]

def cutCost (weights : K → E → ℝ) (capacity : E → ℝ) (cut : K) : ℝ :=
  ∑ e, capacity e * weights cut e

theorem cutCost_scale (weights : K → E → ℝ) (capacity : E → ℝ) (cut : K) (B : ℝ) :
    cutCost weights (fun e => B*capacity e) cut = B*cutCost weights capacity cut := by
  unfold cutCost
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

variable [Fintype K] [Nonempty K]

def area (weights : K → E → ℝ) (capacity : E → ℝ) : ℝ :=
  (Finset.univ.image (fun cut => cutCost weights capacity cut)).min'
    (Finset.univ_nonempty.image _)

theorem area_attained (weights : K → E → ℝ) (capacity : E → ℝ) :
    ∃ cut, cutCost weights capacity cut = area weights capacity := by
  classical
  have h := Finset.min'_mem (Finset.univ.image (fun cut => cutCost weights capacity cut))
    (Finset.univ_nonempty.image _)
  obtain ⟨cut, _, he⟩ := Finset.mem_image.mp h
  exact ⟨cut, he⟩

theorem area_le_cut (weights : K → E → ℝ) (capacity : E → ℝ) (cut : K) :
    area weights capacity ≤ cutCost weights capacity cut := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨cut, Finset.mem_univ cut, rfl⟩)

theorem area_nonnegative {weights : K → E → ℝ} {capacity : E → ℝ}
    (hw : ∀ cut e, 0 ≤ weights cut e) (hc : ∀ e, 0 ≤ capacity e) :
    0 ≤ area weights capacity := by
  obtain ⟨cut, he⟩ := area_attained weights capacity
  rw [← he]
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (hc e) (hw cut e))

/-- The minimizing incidence vector supports the concave area function.
The scalar area is its capacity-weighted value, not that vector itself. -/
theorem area_supergradient (weights : K → E → ℝ) (capacity alternative : E → ℝ) :
    ∃ cut, cutCost weights capacity cut = area weights capacity ∧
      area weights alternative ≤ area weights capacity +
        ∑ e, weights cut e*(alternative e-capacity e) := by
  obtain ⟨cut, he⟩ := area_attained weights capacity
  refine ⟨cut, he, ?_⟩
  have hi : cutCost weights alternative cut = cutCost weights capacity cut +
      ∑ e, weights cut e*(alternative e-capacity e) := by
    unfold cutCost
    simp_rw [mul_sub, mul_comm (weights cut _)]
    rw [Finset.sum_sub_distrib]
    ring
  rw [← he, ← hi]
  exact area_le_cut weights alternative cut

/-- Positive homogeneity constructs a scalar scale-price route without
equating a dual objective to an individual capacity multiplier. -/
theorem area_scale (weights : K → E → ℝ) (capacity : E → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    area weights (fun e => B*capacity e) = B*area weights capacity := by
  obtain ⟨cut, he⟩ := area_attained weights capacity
  obtain ⟨scaledCut, hs⟩ := area_attained weights (fun e => B*capacity e)
  apply le_antisymm
  · calc
      _ ≤ cutCost weights (fun e => B*capacity e) cut := area_le_cut _ _ _
      _ = _ := by rw [cutCost_scale, he]
  · calc
      _ ≥ B*cutCost weights capacity scaledCut := by rw [← hs, cutCost_scale]
      _ ≥ B*area weights capacity := mul_le_mul_of_nonneg_left (area_le_cut _ _ _) hB

theorem area_scale_hasDerivAt (weights : K → E → ℝ) (capacity : E → ℝ)
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun b => area weights (fun e => b*capacity e)) (area weights capacity) B := by
  have he : (fun b => area weights (fun e => b*capacity e)) =ᶠ[𝓝 B]
      (fun b => b*area weights capacity) := by
    filter_upwards [isOpen_Ioi.mem_nhds hB] with b hb
    exact area_scale weights capacity (le_of_lt hb)
  simpa using ((hasDerivAt_id B).mul_const (area weights capacity)).congr_of_eventuallyEq he

theorem area_reparameterized_hasDerivAt (weights : K → E → ℝ) (capacity : E → ℝ)
    {unit B : ℝ} (hu : 0 < unit) (hB : 0 < B) :
    HasDerivAt (fun b => area weights (fun e => (b/unit)*capacity e))
      (area weights capacity/unit) B := by
  have h := (area_scale_hasDerivAt weights capacity (div_pos hB hu)).comp B
    ((hasDerivAt_id B).div_const unit)
  simpa [Function.comp_def, div_eq_mul_inv] using h

end Cuts

section FlowCut

variable {N E K : Type*} [Fintype N] [DecidableEq N] [Fintype E]

def flowBalance (tail head : E → N) (flow : E → ℝ) (n : N) : ℝ :=
  (∑ e, if tail e = n then flow e else 0) - (∑ e, if head e = n then flow e else 0)

def flowConserves (tail head : E → N) (flow : E → ℝ) (source sink : N) : Prop :=
  ∀ n, n ≠ source → n ≠ sink → flowBalance tail head flow n = 0

/-- Finite summation by parts derives the flow/potential ledger pairing. -/
theorem flow_potential_identity (tail head : E → N) (flow : E → ℝ) (potential : N → ℝ) :
    ∑ n, potential n*flowBalance tail head flow n =
      ∑ e, (potential (tail e)-potential (head e))*flow e := by
  have hs (endpoint : E → N) :
      (∑ n, potential n*(∑ e, if endpoint e = n then flow e else 0)) =
        ∑ e, potential (endpoint e)*flow e := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [mul_ite]
  simp_rw [flowBalance, mul_sub]
  rw [Finset.sum_sub_distrib, hs tail, hs head, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem terminal_flow_pairing (tail head : E → N) (flow : E → ℝ)
    (potential : N → ℝ) (source sink : N)
    (hc : flowConserves tail head flow source sink)
    (hs : potential source = 1) (ht : potential sink = 0) :
    (∑ e, (potential (tail e)-potential (head e))*flow e) =
      flowBalance tail head flow source := by
  rw [← flow_potential_identity]
  classical
  have he : (∑ n, potential n*flowBalance tail head flow n) =
      potential source*flowBalance tail head flow source := by
    apply Finset.sum_eq_single source
    · intro n _ hn
      by_cases ht' : n = sink
      · rw [ht', ht, zero_mul]
      · rw [hc n hn ht', mul_zero]
    · simp
  rw [he, hs, one_mul]

/-- Weak duality: edge capacities, conservation and a lawful potential give a cut bound. -/
theorem flow_cut_weak_duality (tail head : E → N) (flow capacity weights : E → ℝ)
    (potential : N → ℝ) (source sink : N)
    (hc : flowConserves tail head flow source sink)
    (hs : potential source = 1) (ht : potential sink = 0)
    (hf : ∀ e, |flow e| ≤ capacity e)
    (hw : ∀ e, |potential (tail e)-potential (head e)| ≤ weights e) :
    flowBalance tail head flow source ≤ ∑ e, capacity e*weights e := by
  rw [← terminal_flow_pairing tail head flow potential source sink hc hs ht]
  apply Finset.sum_le_sum
  intro e _
  calc
    _ ≤ |(potential (tail e)-potential (head e))*flow e| := le_abs_self _
    _ = |potential (tail e)-potential (head e)| * |flow e| := abs_mul _ _
    _ ≤ weights e*capacity e :=
      mul_le_mul (hw e) (hf e) (abs_nonneg _) (le_trans (abs_nonneg _) (hw e))
    _ = _ := mul_comm _ _

variable [Fintype K] [Nonempty K]

theorem flow_value_le_area (tail head : E → N) (flow capacity : E → ℝ)
    (weights : K → E → ℝ) (potential : K → N → ℝ) (source sink : N)
    (hc : flowConserves tail head flow source sink)
    (hs : ∀ k, potential k source = 1) (ht : ∀ k, potential k sink = 0)
    (hf : ∀ e, |flow e| ≤ capacity e)
    (hw : ∀ k e, |potential k (tail e)-potential k (head e)| ≤ weights k e) :
    flowBalance tail head flow source ≤ area weights capacity := by
  obtain ⟨k, he⟩ := area_attained weights capacity
  rw [← he]
  exact flow_cut_weak_duality tail head flow capacity (weights k) (potential k) source sink
    hc (hs k) (ht k) hf (hw k)

/-- A tight feasible flow certificate returns an actual global optimizer.
Tightness must be constructed separately; it is not hidden as an existence theorem. -/
theorem tight_flow_optimal (tail head : E → N) (flow alternative capacity : E → ℝ)
    (weights : K → E → ℝ) (potential : K → N → ℝ) (source sink : N)
    (hs : ∀ k, potential k source = 1) (ht : ∀ k, potential k sink = 0)
    (hw : ∀ k e, |potential k (tail e)-potential k (head e)| ≤ weights k e)
    (hc : flowConserves tail head alternative source sink)
    (hf : ∀ e, |alternative e| ≤ capacity e)
    (hfc : flowConserves tail head flow source sink)
    (hff : ∀ e, |flow e| ≤ capacity e)
    (hflow : flowBalance tail head flow source = area weights capacity) :
    flowConserves tail head flow source sink ∧ (∀ e, |flow e| ≤ capacity e) ∧
      flowBalance tail head alternative source ≤ flowBalance tail head flow source := by
  refine ⟨hfc, hff, ?_⟩
  rw [hflow]
  exact flow_value_le_area tail head alternative capacity weights potential source sink hc hs ht hf hw

end FlowCut

/-- Maximum throughput under an explicit common scale budget and ceiling. -/
def scaleValue (A Q B : ℝ) : ℝ := min (A*B) Q

structure ScaleFeasible (A Q B scale flow : ℝ) : Prop where
  scale_nonnegative : 0 ≤ scale
  flow_nonnegative : 0 ≤ flow
  budget : scale ≤ B
  capacity : flow ≤ A*scale
  ceiling : flow ≤ Q

theorem scale_value_upper {A Q B scale flow : ℝ} (hA : 0 ≤ A)
    (h : ScaleFeasible A Q B scale flow) : flow ≤ scaleValue A Q B := by
  exact le_min (le_trans h.capacity (mul_le_mul_of_nonneg_left h.budget hA)) h.ceiling

theorem scale_value_attained {A Q B : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q) (hB : 0 ≤ B) :
    ScaleFeasible A Q B (min B (Q/A)) (scaleValue A Q B) := by
  have hx : 0 ≤ min B (Q/A) := le_min hB (div_nonneg hQ hA.le)
  have hf : 0 ≤ scaleValue A Q B := le_min (mul_nonneg hA.le hB) hQ
  refine ⟨hx, hf, min_le_left _ _, ?_, min_le_right _ _⟩
  unfold scaleValue
  rw [mul_min_of_nonneg _ _ hA.le]
  rw [mul_div_cancel₀ Q hA.ne']

theorem scale_value_derivative_active {A Q B : ℝ} (hactive : A*B < Q) :
    HasDerivAt (scaleValue A Q) A B := by
  have he : scaleValue A Q =ᶠ[𝓝 B] (fun b => A*b) := by
    have hn : {b : ℝ | A*b < Q} ∈ 𝓝 B :=
      isOpen_lt (continuous_const.mul continuous_id) continuous_const |>.mem_nhds hactive
    filter_upwards [hn] with b hb
    exact min_eq_left (le_of_lt hb)
  simpa using ((hasDerivAt_id B).const_mul A).congr_of_eventuallyEq he

theorem scale_value_derivative_slack {A Q B : ℝ} (hslack : Q < A*B) :
    HasDerivAt (scaleValue A Q) 0 B := by
  have he : scaleValue A Q =ᶠ[𝓝 B] (fun _ => Q) := by
    have hn : {b : ℝ | Q < A*b} ∈ 𝓝 B :=
      isOpen_lt continuous_const (continuous_const.mul continuous_id) |>.mem_nhds hslack
    filter_upwards [hn] with b hb
    exact min_eq_right (le_of_lt hb)
  exact (hasDerivAt_const B Q).congr_of_eventuallyEq he

/-- KKT multipliers for budget, capacity coupling and independent ceiling.
The lower-bound multipliers are set to zero in this sufficient certificate.
It has no assumed optimum or value-derivative fields. -/
structure ScaleKKT (A Q B scale flow price capacityPrice ceilingPrice : ℝ) : Prop where
  feasible : ScaleFeasible A Q B scale flow
  price_nonnegative : 0 ≤ price
  capacityPrice_nonnegative : 0 ≤ capacityPrice
  ceilingPrice_nonnegative : 0 ≤ ceilingPrice
  scale_stationarity : price-capacityPrice*A = 0
  flow_stationarity : -1+capacityPrice+ceilingPrice = 0
  budget_complementarity : price*(B-scale) = 0
  capacity_complementarity : capacityPrice*(A*scale-flow) = 0
  ceiling_complementarity : ceilingPrice*(Q-flow) = 0

theorem scale_kkt_active {A Q B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : A*B ≤ Q) :
    ScaleKKT A Q B B (A*B) A 1 0 := by
  refine ⟨⟨hB, mul_nonneg hA hB, le_refl _, le_refl _, hq⟩,
    hA, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- Explicit return from the constructed cut area to the common-scale controller. -/
theorem area_scale_controller_active {K E : Type*} [Fintype K] [Nonempty K] [Fintype E]
    (weights : K → E → ℝ) (capacity : E → ℝ) {Q B : ℝ}
    (hA : 0 ≤ area weights capacity) (hB : 0 ≤ B) (hQ : area weights capacity*B ≤ Q) :
    ScaleKKT (area weights capacity) Q B B (area weights (fun e => B*capacity e))
      (area weights capacity) 1 0 := by
  rw [area_scale weights capacity hB, mul_comm B]
  exact scale_kkt_active hA hB hQ

theorem scale_kkt_slack {A Q B : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q) (hq : Q ≤ A*B) :
    ScaleKKT A Q B (Q/A) Q 0 0 1 := by
  have hx : Q/A ≤ B := (div_le_iff₀ hA).mpr (by simpa [mul_comm] using hq)
  have he : A*(Q/A) = Q := mul_div_cancel₀ Q hA.ne'
  refine ⟨⟨div_nonneg hQ hA.le, hQ, hx, he.ge, le_refl _⟩,
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem scale_kkt_optimal {A Q B scale flow price capacityPrice ceilingPrice : ℝ}
    (h : ScaleKKT A Q B scale flow price capacityPrice ceilingPrice)
    {alternativeScale alternativeFlow : ℝ}
    (hy : ScaleFeasible A Q B alternativeScale alternativeFlow) : alternativeFlow ≤ flow := by
  have hb := mul_nonneg h.price_nonnegative (sub_nonneg.mpr hy.budget)
  have hc := mul_nonneg h.capacityPrice_nonnegative (sub_nonneg.mpr hy.capacity)
  have hq := mul_nonneg h.ceilingPrice_nonnegative (sub_nonneg.mpr hy.ceiling)
  have hs : price = capacityPrice*A := sub_eq_zero.mp h.scale_stationarity
  have hf : capacityPrice+ceilingPrice = 1 := by linarith [h.flow_stationarity]
  have hv : price*B+ceilingPrice*Q = flow := by
    calc
      _ = price*scale-capacityPrice*(A*scale-flow)+ceilingPrice*flow := by
        nlinarith [h.budget_complementarity, h.capacity_complementarity,
          h.ceiling_complementarity]
      _ = (capacityPrice+ceilingPrice)*flow := by rw [hs]; ring
      _ = flow := by rw [hf, one_mul]
  have he : price*(B-alternativeScale)+capacityPrice*(A*alternativeScale-alternativeFlow)+
      ceilingPrice*(Q-alternativeFlow) = flow-alternativeFlow := by
    calc
      _ = price*B+ceilingPrice*Q-(capacityPrice+ceilingPrice)*alternativeFlow+
          (capacityPrice*A-price)*alternativeScale := by ring
      _ = flow-alternativeFlow := by rw [← hs, sub_self, zero_mul, add_zero, hf, one_mul, hv]
  have hn := add_nonneg (add_nonneg hb hc) hq
  rw [he] at hn
  exact sub_nonneg.mp hn

/-- At the ceiling kink every budget price in [0,A] has a certificate. -/
theorem scale_kkt_boundary {A B price : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hp : 0 ≤ price) (hpA : price ≤ A) :
    ScaleKKT A (A*B) B B (A*B) price (price/A) (1-price/A) := by
  have he : price/A*A = price := div_mul_cancel₀ price hA.ne'
  have hp1 : price/A ≤ 1 := (div_le_one hA).mpr hpA
  refine ⟨⟨hB, mul_nonneg hA.le hB, le_refl _, le_refl _, le_refl _⟩,
    hp, div_nonneg hp hA.le, sub_nonneg.mpr hp1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he, sub_self]
  all_goals ring

theorem scale_value_attained_zero {Q B : ℝ} (hQ : 0 ≤ Q) (hB : 0 ≤ B) :
    ScaleFeasible 0 Q B 0 (scaleValue 0 Q B) := by
  simp only [scaleValue, zero_mul, min_eq_left hQ]
  exact ⟨le_refl _, le_refl _, hB, by simp, hQ⟩

theorem unit_scale_price_matches_area : ScaleKKT 3 10 1 1 3 3 1 0 := by
  simpa using scale_kkt_active (A := 3) (Q := 10) (B := 1)
    (by norm_num) (by norm_num) (by norm_num)

theorem scaled_budget_units_change_price : ScaleKKT (3/2) 10 2 2 3 (3/2) 1 0 := by
  have h := scale_kkt_active (A := 3/2) (Q := 10) (B := 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The cut objective of the one-edge graph, with its only legal cut. -/
theorem single_edge_area (c : ℝ) :
    area (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun _ => c) = c := by
  obtain ⟨cut, he⟩ := area_attained (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun _ => c)
  simpa [cutCost] using he.symm

/-- The two cuts of a two-edge path: one edge on either side of the interface. -/
def seriesWeights (cut edge : Fin 2) : ℝ := if cut = edge then 1 else 0

theorem series_path_area (a b : ℝ) : area seriesWeights ![a,b] = min a b := by
  have hcost (k : Fin 2) : cutCost seriesWeights ![a,b] k = (![a,b] : Fin 2 → ℝ) k := by
    fin_cases k <;> norm_num [cutCost, seriesWeights, Fin.sum_univ_two]
  apply le_antisymm
  · apply le_min
    · simpa only [hcost] using area_le_cut seriesWeights ![a,b] 0
    · simpa only [hcost] using area_le_cut seriesWeights ![a,b] 1
  · obtain ⟨k, he⟩ := area_attained seriesWeights ![a,b]
    rw [← he, hcost]
    fin_cases k
    · exact min_le_left a b
    · exact min_le_right a b

/-- A single edge of capacity 3 has area 3 and capacity price 1. -/
theorem area_not_individual_price :
    area (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun _ => (3 : ℝ)) = 3 ∧
    HasDerivAt (fun c : ℝ => area (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun _ => c)) 1 3 ∧
    (3 : ℝ) ≠ 1 := by
  refine ⟨single_edge_area 3, ?_, by norm_num⟩
  simpa only [single_edge_area] using hasDerivAt_id (3 : ℝ)

end

end SbtCosmo.Derivation.CapacityScale
