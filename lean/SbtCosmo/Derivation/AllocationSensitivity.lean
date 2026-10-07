import SbtCosmo.Derivation.AllocationPrice
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Derived regularity of the original allocation carrier, including active-set switches.
No differentiability or regularity of the selected optimizer or value is assumed. -/
namespace SbtCosmo.Derivation.AllocationSensitivity
noncomputable section
open AllocationPrice Set Filter
open scoped Topology

theorem marginal_sub_identity {w c b x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    marginal w c b x - marginal w c b y = w*(y-x)/((1+x)*(1+y)) + c*(y-x) := by
  unfold marginal
  have h1 : 1+x ≠ 0 := by linarith
  have h2 : 1+y ≠ 0 := by linarith
  field_simp
  ring

theorem marginal_sub_bounds {w c b x y : ℝ} (hw : 0 ≤ w)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    c*(y-x) ≤ marginal w c b x - marginal w c b y ∧
      marginal w c b x - marginal w c b y ≤ (w+c)*(y-x) := by
  rw [marginal_sub_identity hx (hx.trans hxy)]
  have hd : (1 : ℝ) ≤ (1+x)*(1+y) := by nlinarith
  have hn : 0 ≤ w*(y-x) := mul_nonneg hw (sub_nonneg.mpr hxy)
  have hp : 0 < (1+x)*(1+y) := lt_of_lt_of_le (by norm_num) hd
  have hl := div_nonneg hn hp.le
  have hu : w*(y-x)/((1+x)*(1+y)) ≤ w*(y-x) := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  constructor <;> nlinarith

theorem marginal_strictAntiOn {w c b : ℝ} (hw : 0 ≤ w) (hc : 0 < c) :
    StrictAntiOn (marginal w c b) (Ici 0) := by
  intro x hx y hy hxy
  have h := (marginal_sub_bounds (c := c) (b := b) hw hx hxy.le).1
  have hp := mul_pos hc (sub_pos.mpr hxy)
  linarith

theorem demand_stationary_of_positive {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hp : 0 < demand w c b p) : marginal w c b (demand w c b p) = p := by
  apply demand_stationary hw hc
  by_contra hn
  rw [demand_zero hw hc (le_of_not_gt hn)] at hp
  exact (lt_irrefl 0) hp

theorem demand_antitone {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) : Antitone (demand w c b) := by
  intro p q hpq
  by_contra hn
  have hxy : demand w c b p < demand w c b q := lt_of_not_ge hn
  have hy : 0 < demand w c b q := (demand_nonnegative _ _ _ _).trans_lt hxy
  have hm := marginal_strictAntiOn (b := b) hw.le hc
    (demand_nonnegative _ _ _ _) (demand_nonnegative _ _ _ _) hxy
  rw [demand_stationary_of_positive hw hc hy] at hm
  have hb := (demand_certificate (b := b) (p := p) hw hc).1
  linarith

variable {ι : Type*} [Fintype ι]

def priceModulus (w c : ι → ℝ) : ℝ := ∑ i, (w i+c i)

theorem priceModulus_nonnegative {w c : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) :
    0 ≤ priceModulus w c := Finset.sum_nonneg (fun i _ => (add_pos (hw i) (hc i)).le)

theorem selected_price_antitoneOn {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) :
    AntitoneOn (selectedPrice w c b hw hc) (Ioi 0) := by
  intro B hB C hC hBC
  rcases hBC.eq_or_lt with he | he
  · subst C
    exact le_rfl
  · exact price_antitone (fun i => (hw i).le) (fun i => (hc i).le)
      (selected_kkt hw hc hB.le) (selected_kkt hw hc hC.le) he

/-- An active positive patch controls the price difference; no fixed active set is required. -/
theorem price_difference_bound {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B C : ℝ} (hB : 0 < B) (hBC : B < C) :
    selectedPrice w c b hw hc B - selectedPrice w c b hw hc C ≤ priceModulus w c * (C-B) := by
  let x := selectedAllocation w c b hw hc B
  let y := selectedAllocation w c b hw hc C
  let p := selectedPrice w c b hw hc B
  let q := selectedPrice w c b hw hc C
  have hx : AllocationKKT w c b x B p := selected_kkt hw hc hB.le
  have hy : AllocationKKT w c b y C q := selected_kkt hw hc (hB.trans hBC).le
  have hqp : q ≤ p := selected_price_antitoneOn hw hc hB (hB.trans hBC) hBC.le
  have hK := priceModulus_nonnegative hw hc
  change p-q ≤ priceModulus w c * (C-B)
  by_cases hpq : p ≤ q
  · have hz : p-q = 0 := by linarith
    rw [hz]
    exact mul_nonneg hK (sub_nonneg.mpr hBC.le)
  have hpp : 0 < p := lt_of_le_of_lt hy.price_nonnegative (lt_of_not_ge hpq)
  have hm : mass x = B := by
    have he := (mul_eq_zero.mp hx.budget_complementarity).resolve_left hpp.ne'
    linarith
  have hxy : ∀ i, x i ≤ y i := fun i => demand_antitone (b := b i) (hw i) (hc i) hqp
  have hsum : 0 < ∑ i, x i := by change 0 < mass x; rw [hm]; exact hB
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hx.nonnegative i)).mp hsum
  have hgrad := (marginal_sub_bounds (c := c i) (b := b i) (hw i).le (hx.nonnegative i) (hxy i)).2
  rw [marginal_eq_price_at_positive hx hi, marginal_eq_price_at_positive hy (hi.trans_le (hxy i))] at hgrad
  have hd : y i-x i ≤ C-B := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hxy j)) (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hs
    change y i-x i ≤ mass y-mass x at hs
    linarith [hy.feasible]
  have hk : w i+c i ≤ priceModulus w c :=
    Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (add_pos (hw j) (hc j)).le) (Finset.mem_univ i)
  exact hgrad.trans ((mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr (hxy i))).trans
    (mul_le_mul_of_nonneg_left hd hK))

theorem price_abs_difference_bound {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    |selectedPrice w c b hw hc B - selectedPrice w c b hw hc C| ≤ priceModulus w c * |B-C| := by
  rcases lt_trichotomy B C with hBC | hBC | hBC
  · rw [abs_of_nonneg (sub_nonneg.mpr (selected_price_antitoneOn hw hc hB hC hBC.le)),
      abs_of_neg (sub_neg.mpr hBC)]
    simpa only [neg_sub] using price_difference_bound hw hc hB hBC
  · subst C
    simp
  · rw [abs_sub_comm (selectedPrice w c b hw hc B), abs_sub_comm B]
    rw [abs_of_nonneg (sub_nonneg.mpr (selected_price_antitoneOn hw hc hC hB hBC.le)),
      abs_of_neg (sub_neg.mpr hBC)]
    simpa only [neg_sub] using price_difference_bound hw hc hC hBC

theorem selected_price_lipschitzOn {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) :
    LipschitzOnWith (Real.toNNReal (priceModulus w c)) (selectedPrice w c b hw hc) (Ioi 0) := by
  apply LipschitzOnWith.of_dist_le'
  intro B hB C hC
  simpa only [Real.dist_eq] using price_abs_difference_bound (b := b) hw hc hB hC

theorem selected_price_continuousOn {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) :
    ContinuousOn (selectedPrice w c b hw hc) (Ioi 0) := (selected_price_lipschitzOn hw hc).continuousOn

/-- A uniform quadratic remainder through all active-set and active/slack switches. -/
theorem cost_remainder_bounds {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    0 ≤ costValue w c b hw hc C - costValue w c b hw hc B + selectedPrice w c b hw hc B*(C-B) ∧
      costValue w c b hw hc C - costValue w c b hw hc B + selectedPrice w c b hw hc B*(C-B) ≤
        priceModulus w c * |C-B|^2 := by
  have hs := cost_value_support (b := b) hw hc hB.le hC.le
  have ht := cost_value_support (b := b) hw hc hC.le hB.le
  have hp := price_abs_difference_bound (b := b) hw hc hB hC
  rw [abs_sub_comm B] at hp
  have hm := mul_le_mul_of_nonneg_right hp (abs_nonneg (C-B))
  have ha : (selectedPrice w c b hw hc B - selectedPrice w c b hw hc C)*(C-B) ≤
      |selectedPrice w c b hw hc B - selectedPrice w c b hw hc C| * |C-B| := by
    rw [← abs_mul]
    exact le_abs_self _
  constructor <;> nlinarith

/-- The original value derivative is constructed, rather than supplied as an input. -/
theorem cost_value_hasDerivAt {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt (costValue w c b hw hc) (-selectedPrice w c b hw hc B) B := by
  rw [hasDerivAt_iff_isLittleO]
  apply Asymptotics.IsBigO.trans_isLittleO ?_
    (Asymptotics.isLittleO_pow_sub_sub B (m := 2) (by norm_num))
  rw [Asymptotics.isBigO_iff]
  refine ⟨priceModulus w c, ?_⟩
  filter_upwards [isOpen_Ioi.mem_nhds hB] with C hC
  have h := cost_remainder_bounds (b := b) hw hc hB hC
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_pow, abs_abs]
  have he : costValue w c b hw hc C - costValue w c b hw hc B -
      (C-B)*(-selectedPrice w c b hw hc B) =
      costValue w c b hw hc C - costValue w c b hw hc B + selectedPrice w c b hw hc B*(C-B) := by ring
  rw [he, abs_of_nonneg h.1]
  exact h.2

theorem cost_value_deriv {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B : ℝ} (hB : 0 < B) :
    deriv (costValue w c b hw hc) B = -selectedPrice w c b hw hc B :=
  (cost_value_hasDerivAt hw hc hB).deriv

theorem cost_value_deriv_lipschitzOn {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) :
    LipschitzOnWith (Real.toNNReal (priceModulus w c)) (deriv (costValue w c b hw hc)) (Ioi 0) := by
  apply LipschitzOnWith.of_dist_le'
  intro B hB C hC
  rw [Real.dist_eq, cost_value_deriv hw hc hB, cost_value_deriv hw hc hC]
  rw [show -selectedPrice w c b hw hc B - -selectedPrice w c b hw hc C =
    -(selectedPrice w c b hw hc B - selectedPrice w c b hw hc C) by ring, abs_neg]
  simpa only [Real.dist_eq] using price_abs_difference_bound (b := b) hw hc hB hC

theorem cost_value_contDiffOn_one {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) :
    ContDiffOn ℝ 1 (costValue w c b hw hc) (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun B hB => (cost_value_hasDerivAt hw hc hB).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · norm_num
  · exact contDiffOn_zero.mpr (cost_value_deriv_lipschitzOn hw hc).continuousOn

/-- Below the unconstrained budget the actual cost is strictly sensitive. -/
theorem actual_strict_sensitivity_iff {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B : ℝ} (hB : 0 < B) :
    deriv (costValue w c b hw hc) B < 0 ↔ B < mass (fun i => demand (w i) (c i) (b i) 0) := by
  rw [cost_value_deriv hw hc hB]
  constructor
  · intro hs
    by_contra hn
    rw [above_unconstrained_price_zero hw hc hB (le_of_not_gt hn)] at hs
    norm_num at hs
  · intro hs
    have hp := below_unconstrained_price_positive hw hc hB.le hs
    linarith

/-- Certified exact-real central finite difference, including switch points. -/
theorem central_difference_price_error {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B h : ℝ} (hh : 0 < h) (hB : h < B) :
    |(costValue w c b hw hc (B+h) - costValue w c b hw hc (B-h))/(2*h) +
      selectedPrice w c b hw hc B| ≤ priceModulus w c * h/2 := by
  have hBp : 0 < B := hh.trans hB
  have hp := cost_remainder_bounds (b := b) hw hc hBp (by linarith : 0 < B+h)
  have hm := cost_remainder_bounds (b := b) hw hc hBp (by linarith : 0 < B-h)
  rw [show B+h-B = h by ring, abs_of_pos hh] at hp
  rw [show B-h-B = -h by ring, abs_neg, abs_of_pos hh] at hm
  have he : (costValue w c b hw hc (B+h) - costValue w c b hw hc (B-h))/(2*h) +
      selectedPrice w c b hw hc B =
      (costValue w c b hw hc (B+h) - costValue w c b hw hc (B-h) +
        2*h*selectedPrice w c b hw hc B)/(2*h) := by
    field_simp
  have ha : |costValue w c b hw hc (B+h) - costValue w c b hw hc (B-h) +
        2*h*selectedPrice w c b hw hc B| ≤ priceModulus w c * h^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2*h)]
  apply (div_le_iff₀ (by positivity : 0 < 2*h)).mpr
  nlinarith

/-- The existing heterogeneous exact carrier fixes the derivative's negative-price sign. -/
theorem demo_actual_derivative :
    HasDerivAt (costValue demoWeights (fun _ => 1) (fun _ => 0)
      (by intro i; fin_cases i <;> norm_num [demoWeights]) (fun _ => by norm_num)) (-1) 3 := by
  let hw : ∀ i : Fin 2, 0 < demoWeights i := by intro i; fin_cases i <;> norm_num [demoWeights]
  let hc : ∀ _ : Fin 2, (0 : ℝ) < 1 := fun _ => by norm_num
  have hp := (kkt_unique (fun i => (hw i).le) hc (selected_kkt hw hc (by norm_num)) demo_kkt (by norm_num)).2
  convert cost_value_hasDerivAt (b := fun _ => 0) hw hc (by norm_num : (0 : ℝ) < 3) using 1
  rw [hp]

/-- The same allocation/budget with changed local weights has a different actual derivative. -/
theorem changed_weights_actual_derivative :
    HasDerivAt (costValue changedWeights (fun _ => 1) (fun _ => 0)
      (by intro i; fin_cases i <;> norm_num [changedWeights]) (fun _ => by norm_num)) (-2) 3 := by
  let hw : ∀ i : Fin 2, 0 < changedWeights i := by intro i; fin_cases i <;> norm_num [changedWeights]
  let hc : ∀ _ : Fin 2, (0 : ℝ) < 1 := fun _ => by norm_num
  have hp := (kkt_unique (fun i => (hw i).le) hc (selected_kkt hw hc (by norm_num)) changed_weights_kkt (by norm_num)).2
  convert cost_value_hasDerivAt (b := fun _ => 0) hw hc (by norm_num : (0 : ℝ) < 3) using 1
  rw [hp]

/-- Active budget with zero price and a derived zero value derivative: binding alone is insufficient. -/
theorem active_zero_derivative_control :
    AllocationKKT (fun _ : Fin 1 => 2) (fun _ => 1) (fun _ => 0) (fun _ => 1) 1 0 ∧
      mass (fun _ : Fin 1 => (1 : ℝ)) = 1 ∧
      HasDerivAt (costValue (fun _ : Fin 1 => 2) (fun _ => 1) (fun _ => 0)
        (fun _ => by norm_num) (fun _ => by norm_num)) 0 1 := by
  have hk : AllocationKKT (fun _ : Fin 1 => 2) (fun _ => 1) (fun _ => 0) (fun _ => 1) 1 0 := by
    constructor
    · intro i; norm_num
    · norm_num [mass]
    · norm_num
    · intro i; norm_num [marginal]
    · intro i; norm_num [marginal]
    · norm_num
  refine ⟨hk, by norm_num [mass], ?_⟩
  let hw : ∀ _ : Fin 1, (0 : ℝ) < 2 := fun _ => by norm_num
  let hc : ∀ _ : Fin 1, (0 : ℝ) < 1 := fun _ => by norm_num
  have hp := (kkt_unique (fun i => (hw i).le) hc (selected_kkt hw hc (by norm_num)) hk (by norm_num)).2
  convert cost_value_hasDerivAt (b := fun _ => 0) hw hc (by norm_num : (0 : ℝ) < 1) using 1
  rw [hp]
  norm_num

end
end SbtCosmo.Derivation.AllocationSensitivity
