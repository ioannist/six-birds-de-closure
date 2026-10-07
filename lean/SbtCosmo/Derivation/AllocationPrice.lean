import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
The original finite allocation objective in `scripts/de_dual_carrier.py`.
KKT certificates contain feasibility and stationarity, not an assumed optimal
value. A direct logarithmic tangent bound derives global optimality, uniqueness
and budget-price support. No physical Lambda or equation-of-state bridge.
-/
namespace SbtCosmo.Derivation.AllocationPrice

noncomputable section

def localUtility (w c b x : ℝ) : ℝ :=
  w * Real.log (1+x) - c/2*x^2 + b*x

def marginal (w c b x : ℝ) : ℝ := w/(1+x) - c*x + b

theorem localUtility_hasDerivAt (w c b : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (localUtility w c b) (marginal w c b x) x := by
  have hn : 1+x ≠ 0 := by linarith
  have hi : HasDerivAt (fun t : ℝ => 1+t) 1 x := (hasDerivAt_id x).const_add 1
  convert (((hi.log hn).const_mul w).sub
    (((hasDerivAt_id x).pow 2).const_mul (c/2))).add
    ((hasDerivAt_id x).const_mul b) using 1
  simp only [marginal, div_eq_mul_inv, id_eq]
  ring

theorem log_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.log (1+y) ≤ Real.log (1+x) + (y-x)/(1+x) := by
  have hp : 0 < 1+x := by linarith
  have hq : 0 < 1+y := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at h
  have he : (1+y)/(1+x)-1 = (y-x)/(1+x) := by
    field_simp
    ring
  rw [he] at h
  linarith

/-- Strong tangent inequality for the exact log/quadratic utility. -/
theorem local_strong_tangent {w c b x y : ℝ} (hw : 0 ≤ w)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    localUtility w c b y ≤ localUtility w c b x +
      marginal w c b x * (y-x) - c/2*(y-x)^2 := by
  have hl := mul_le_mul_of_nonneg_left (log_tangent hx hy) hw
  have he : w * ((y-x)/(1+x)) = (w/(1+x)) * (y-x) := by ring
  unfold localUtility marginal
  rw [mul_add, he] at hl
  nlinarith [hl]

/-- Exact nonnegative patch response used by the numerical water-filling solver.
The numerical implementation rationalizes this positive root for conditioning. -/
def demand (w c b p : ℝ) : ℝ :=
  max 0 ((Real.sqrt ((c-(p-b))^2+4*c*w) - (c+(p-b)))/(2*c))

theorem demand_nonnegative (w c b p : ℝ) : 0 ≤ demand w c b p := le_max_left _ _

theorem demand_zero {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hp : w+b ≤ p) : demand w c b p = 0 := by
  have hs : Real.sqrt ((c-(p-b))^2+4*c*w) ≤ c+(p-b) := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  unfold demand
  rw [max_eq_left]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem demand_positive {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hp : p < w+b) : 0 < demand w c b p := by
  have hd : 0 ≤ (c-(p-b))^2+4*c*w := by positivity
  have hs := Real.sq_sqrt hd
  have hr := Real.sqrt_nonneg ((c-(p-b))^2+4*c*w)
  have ht : c+(p-b) < Real.sqrt ((c-(p-b))^2+4*c*w) := by
    by_contra hn
    have he : Real.sqrt ((c-(p-b))^2+4*c*w) ≤ c+(p-b) := le_of_not_gt hn
    nlinarith [sq_nonneg (Real.sqrt ((c-(p-b))^2+4*c*w) - (c+(p-b)))]
  have ha : 0 < (Real.sqrt ((c-(p-b))^2+4*c*w) - (c+(p-b)))/(2*c) :=
    div_pos (sub_pos.mpr ht) (by linarith)
  exact lt_of_lt_of_le ha (le_max_right _ _)

theorem demand_eq_root {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hp : p < w+b) : demand w c b p =
      (Real.sqrt ((c-(p-b))^2+4*c*w) - (c+(p-b)))/(2*c) := by
  have hx := demand_positive hw hc hp
  unfold demand at hx ⊢
  rcases lt_max_iff.mp hx with hz | hr
  · exact False.elim (lt_irrefl _ hz)
  · exact max_eq_right hr.le

/-- Exact algebraic bridge to the rationalized positive-root branch in Python.
Numerical conditioning and floating arithmetic are separate checks. -/
theorem demand_rationalized {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hp : p < w+b) : demand w c b p =
      2*(w-(p-b))/(Real.sqrt ((c-(p-b))^2+4*c*w)+(c+(p-b))) := by
  have hd : 0 ≤ (c-(p-b))^2+4*c*w := by positivity
  have hs := Real.sq_sqrt hd
  have hr := Real.sqrt_nonneg ((c-(p-b))^2+4*c*w)
  have hn : 0 < Real.sqrt ((c-(p-b))^2+4*c*w)+(c+(p-b)) := by
    by_contra he
    have hle := le_of_not_gt he
    nlinarith [sq_nonneg (Real.sqrt ((c-(p-b))^2+4*c*w)+(c+(p-b)))]
  rw [demand_eq_root hw hc hp]
  apply (div_eq_div_iff (by positivity : 2*c ≠ 0) hn.ne').mpr
  nlinarith [hs]

/-- Positive root solves stationarity in the actual unmodified objective. -/
theorem demand_stationary {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hp : p < w+b) : marginal w c b (demand w c b p) = p := by
  have hx := demand_positive hw hc hp
  have hd : 0 ≤ (c-(p-b))^2+4*c*w := by positivity
  have hs := Real.sq_sqrt hd
  have ha := demand_eq_root hw hc hp
  have he : 2*c*demand w c b p + (c+(p-b)) =
      Real.sqrt ((c-(p-b))^2+4*c*w) := by
    rw [ha]
    field_simp
    ring
  have hpoly : c*(c*(demand w c b p)^2 +
      (c+(p-b))*demand w c b p + (p-b)-w) = 0 := by
    have he2 := congrArg (fun t : ℝ => t^2) he
    nlinarith [he2, hs]
  have hz := (mul_eq_zero.mp hpoly).resolve_left hc.ne'
  have hn : 1+demand w c b p ≠ 0 := by linarith
  have heq : w/(1+demand w c b p) = p+c*demand w c b p-b := by
    apply (div_eq_iff hn).mpr
    nlinarith [hz]
  unfold marginal
  linarith

theorem demand_certificate {w c b p : ℝ} (hw : 0 < w) (hc : 0 < c) :
    marginal w c b (demand w c b p) ≤ p ∧
    (p-marginal w c b (demand w c b p))*demand w c b p = 0 := by
  by_cases hp : p < w+b
  · rw [demand_stationary hw hc hp]
    exact ⟨le_refl _, by ring⟩
  · rw [demand_zero hw hc (le_of_not_gt hp)]
    constructor
    · simpa [marginal] using le_of_not_gt hp
    · simp

theorem demand_continuous (w c b : ℝ) : Continuous (demand w c b) := by
  unfold demand
  fun_prop

variable {ι : Type*} [Fintype ι]

def utility (w c b x : ι → ℝ) : ℝ := ∑ i, localUtility (w i) (c i) (b i) (x i)

def mass (x : ι → ℝ) : ℝ := ∑ i, x i

def penalty (c x y : ι → ℝ) : ℝ := ∑ i, c i/2 * (y i-x i)^2

structure AllocationKKT (w c b x : ι → ℝ) (budget price : ℝ) : Prop where
  nonnegative : ∀ i, 0 ≤ x i
  feasible : mass x ≤ budget
  price_nonnegative : 0 ≤ price
  gradient_bound : ∀ i, marginal (w i) (c i) (b i) (x i) ≤ price
  lower_complementarity : ∀ i,
    (price - marginal (w i) (c i) (b i) (x i)) * x i = 0
  budget_complementarity : price * (budget - mass x) = 0

theorem marginal_eq_price_at_positive {w c b x : ι → ℝ} {budget price : ℝ}
    (h : AllocationKKT w c b x budget price) {i : ι} (hi : 0 < x i) :
    marginal (w i) (c i) (b i) (x i) = price := by
  have hc := h.lower_complementarity i
  rcases mul_eq_zero.mp hc with he | he
  · linarith
  · linarith

theorem slack_price_zero {w c b x : ι → ℝ} {budget price : ℝ}
    (h : AllocationKKT w c b x budget price) (hs : mass x < budget) : price = 0 := by
  rcases mul_eq_zero.mp h.budget_complementarity with hp | hb
  · exact hp
  · linarith

theorem penalty_nonnegative {c x y : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    0 ≤ penalty c x y := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg (hc i) (by norm_num)) (sq_nonneg _))

theorem penalty_zero_iff {c x y : ι → ℝ} (hc : ∀ i, 0 < c i) :
    penalty c x y = 0 ↔ x = y := by
  unfold penalty
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (div_nonneg (hc i).le (by norm_num)) (sq_nonneg _))]
  constructor
  · intro h
    funext i
    have hi := h i (Finset.mem_univ i)
    have hp : 0 < c i/2 := div_pos (hc i) (by norm_num)
    have hz : (y i-x i)^2 = 0 := (mul_eq_zero.mp hi).resolve_left hp.ne'
    nlinarith [hz]
  · intro h
    subst y
    simp

/-- A global price support bound for every nonnegative alternative, including
alternatives with a different budget. This is derived from stationarity. -/
theorem kkt_strong_support {w c b x : ι → ℝ} {budget price : ℝ}
    (hw : ∀ i, 0 ≤ w i) (h : AllocationKKT w c b x budget price)
    {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) :
    utility w c b y ≤ utility w c b x + price * (mass y-budget) - penalty c x y := by
  have hi : ∀ i, localUtility (w i) (c i) (b i) (y i) ≤
      localUtility (w i) (c i) (b i) (x i) + price*(y i-x i) -
        c i/2*(y i-x i)^2 := by
    intro i
    have ht := local_strong_tangent (c := c i) (b := b i) (hw i) (h.nonnegative i) (hy i)
    have hn := mul_nonneg (sub_nonneg.mpr (h.gradient_bound i)) (hy i)
    have hz := h.lower_complementarity i
    nlinarith [ht, hn, hz]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hc := h.budget_complementarity
  have hs' : utility w c b y ≤ utility w c b x +
      price*(mass y-mass x) - penalty c x y := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      utility, mass, penalty] using hs
  nlinarith [hs', hc]


/-- The complete original parameter family has a KKT solution, including
zero budgets, slack budgets, arbitrary offsets, and empty finite patch sets. -/
theorem kkt_exists {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ p : ℝ, AllocationKKT w c b (fun i => demand (w i) (c i) (b i) p) B p := by
  classical
  let S : ℝ → ℝ := fun p => ∑ i, demand (w i) (c i) (b i) p
  have hcert : ∀ p i, marginal (w i) (c i) (b i) (demand (w i) (c i) (b i) p) ≤ p ∧
      (p-marginal (w i) (c i) (b i) (demand (w i) (c i) (b i) p))*
        demand (w i) (c i) (b i) p = 0 :=
    fun p i => demand_certificate (hw i) (hc i)
  by_cases hs : S 0 ≤ B
  · refine ⟨0, ?_⟩
    exact ⟨fun i => demand_nonnegative _ _ _ _, hs, le_refl _,
      fun i => (hcert 0 i).1, fun i => (hcert 0 i).2, by ring⟩
  · let M : ℝ := 1+∑ i, max 0 (w i+b i)
    have hM : 0 ≤ M := by
      dsimp [M]
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => le_max_left _ _)))
    have hcap : ∀ i, w i+b i ≤ M := by
      intro i
      have hi := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => le_max_left (0 : ℝ) (w j+b j))
        (Finset.mem_univ i)
      have hj := le_max_right (0 : ℝ) (w i+b i)
      dsimp [M]
      linarith
    have hz : S M = 0 := by
      dsimp [S]
      apply Finset.sum_eq_zero
      intro i _
      exact demand_zero (hw i) (hc i) (hcap i)
    have hcont : Continuous S := by
      dsimp [S]
      exact continuous_finset_sum Finset.univ (fun i _ => demand_continuous _ _ _)
    obtain ⟨p, hp, he⟩ := intermediate_value_Icc' hM hcont.continuousOn
      (show B ∈ Set.Icc (S M) (S 0) from ⟨by simpa [hz] using hB, (lt_of_not_ge hs).le⟩)
    refine ⟨p, fun i => demand_nonnegative _ _ _ _, ?_, hp.1,
      fun i => (hcert p i).1, fun i => (hcert p i).2, ?_⟩
    · exact he.le
    · change p*(B-S p) = 0
      rw [he]
      ring

/-- A realized solution rather than a certificate-valued hypothesis. -/
def selectedPrice (w c b : ι → ℝ) (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    (B : ℝ) : ℝ :=
  if hB : 0 ≤ B then Classical.choose (kkt_exists (b := b) hw hc hB) else 0

def selectedAllocation (w c b : ι → ℝ) (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    (B : ℝ) : ι → ℝ := fun i => demand (w i) (c i) (b i) (selectedPrice w c b hw hc B)

theorem selected_kkt {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B : ℝ} (hB : 0 ≤ B) :
    AllocationKKT w c b (selectedAllocation w c b hw hc B) B (selectedPrice w c b hw hc B) := by
  unfold selectedAllocation selectedPrice
  rw [dif_pos hB]
  exact Classical.choose_spec (kkt_exists (b := b) hw hc hB)

/-- Every feasible alternative loses at least the explicit quadratic penalty. -/
theorem kkt_global_optimal {w c b x : ι → ℝ} {budget price : ℝ}
    (hw : ∀ i, 0 ≤ w i) (h : AllocationKKT w c b x budget price)
    {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) (hb : mass y ≤ budget) :
    utility w c b y ≤ utility w c b x - penalty c x y := by
  have hs := kkt_strong_support hw h hy
  have hp := mul_nonpos_of_nonneg_of_nonpos h.price_nonnegative (sub_nonpos.mpr hb)
  linarith

theorem kkt_unique_optimizer {w c b x : ι → ℝ} {budget price : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 < c i)
    (h : AllocationKKT w c b x budget price)
    {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) (hb : mass y ≤ budget)
    (hu : utility w c b x ≤ utility w c b y) : x = y := by
  have hs := kkt_global_optimal hw h hy hb
  have hp := penalty_nonnegative (fun i => (hc i).le) (x := x) (y := y)
  exact (penalty_zero_iff hc).mp (by linarith)

theorem price_unique_at_positive_budget {w c b x : ι → ℝ} {B p q : ℝ}
    (hp : AllocationKKT w c b x B p) (hq : AllocationKKT w c b x B q)
    (hB : 0 < B) : p = q := by
  by_cases hm : 0 < mass x
  · obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => hp.nonnegative i)).mp hm
    have he := marginal_eq_price_at_positive hp hi
    have hf := marginal_eq_price_at_positive hq hi
    linarith
  · have hs : mass x < B := lt_of_le_of_lt (le_of_not_gt hm) hB
    rw [slack_price_zero hp hs, slack_price_zero hq hs]

/-- The constructed optimum and price are intrinsic at a positive budget;
classical choice in existence cannot alter them. -/
theorem kkt_unique {w c b x y : ι → ℝ} {B p q : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 < c i)
    (hx : AllocationKKT w c b x B p) (hy : AllocationKKT w c b y B q)
    (hB : 0 < B) : x = y ∧ p = q := by
  have he := kkt_global_optimal hw hy hx.nonnegative hx.feasible
  have hn := penalty_nonnegative (fun i => (hc i).le) (x := y) (y := x)
  have hu : utility w c b x ≤ utility w c b y := by linarith
  have heq := kkt_unique_optimizer hw hc hx hy.nonnegative hy.feasible hu
  subst y
  exact ⟨rfl, price_unique_at_positive_budget hx hy hB⟩

theorem below_unconstrained_price_positive {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B : ℝ} (hB : 0 ≤ B)
    (hs : B < mass (fun i => demand (w i) (c i) (b i) 0)) :
    0 < selectedPrice w c b hw hc B := by
  have hx := selected_kkt (b := b) hw hc hB
  have hn := hx.price_nonnegative
  apply lt_of_le_of_ne hn
  intro hp
  have he : selectedPrice w c b hw hc B = 0 := hp.symm
  have hf := hx.feasible
  unfold selectedAllocation at hf
  rw [he] at hf
  linarith

theorem below_unconstrained_budget_active {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B : ℝ} (hB : 0 ≤ B)
    (hs : B < mass (fun i => demand (w i) (c i) (b i) 0)) :
    mass (selectedAllocation w c b hw hc B) = B := by
  have hx := selected_kkt (b := b) hw hc hB
  have hp := below_unconstrained_price_positive hw hc hB hs
  have he := (mul_eq_zero.mp hx.budget_complementarity).resolve_left hp.ne'
  linarith

theorem above_unconstrained_price_zero {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B : ℝ} (hB : 0 < B)
    (hs : mass (fun i => demand (w i) (c i) (b i) 0) ≤ B) :
    selectedPrice w c b hw hc B = 0 := by
  have hx := selected_kkt (b := b) hw hc hB.le
  have hz : AllocationKKT w c b (fun i => demand (w i) (c i) (b i) 0) B 0 :=
    ⟨fun i => demand_nonnegative _ _ _ _, hs, le_refl _,
      fun i => (demand_certificate (hw i) (hc i)).1,
      fun i => (demand_certificate (hw i) (hc i)).2, by ring⟩
  exact (kkt_unique (fun i => (hw i).le) hc hx hz hB).2

/-- The cost value of the constructed optimizer, matching the original
script's cost_value=-utility convention. The negative-budget extension is unused. -/
def costValue (w c b : ι → ℝ) (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) (B : ℝ) : ℝ :=
  -utility w c b (selectedAllocation w c b hw hc B)

theorem cost_value_support {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    costValue w c b hw hc B - selectedPrice w c b hw hc B*(T-B) ≤
      costValue w c b hw hc T := by
  have hx := selected_kkt (b := b) hw hc hB
  have hy := selected_kkt (b := b) hw hc hT
  have hs := kkt_strong_support (fun i => (hw i).le) hx hy.nonnegative
  have hp := penalty_nonnegative (fun i => (hc i).le)
    (x := selectedAllocation w c b hw hc B) (y := selectedAllocation w c b hw hc T)
  have hm := mul_le_mul_of_nonneg_left hy.feasible hx.price_nonnegative
  unfold costValue
  nlinarith

/-- At an interior budget, differentiability of the actual optimal cost value
identifies its derivative with the negative KKT price. No finite difference is
used as a proof of the derivative. -/
theorem cost_value_derivative {w c b : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i)
    {B d : ℝ} (hB : 0 < B) (hd : HasDerivAt (costValue w c b hw hc) d B) :
    d = -selectedPrice w c b hw hc B := by
  let p := selectedPrice w c b hw hc B
  have hm : IsMinOn (fun T => costValue w c b hw hc T+p*T) (Set.Ioi 0) B := by
    intro T hT
    have hs := cost_value_support (b := b) hw hc hB.le (le_of_lt hT)
    dsimp [p] at *
    linarith
  have hlocal := hm.isLocalMin (isOpen_Ioi.mem_nhds hB)
  have hz := hlocal.hasDerivAt_eq_zero (hd.add ((hasDerivAt_id B).const_mul p))
  dsimp [p] at hz
  linarith

theorem strictly_sensitive_price_positive {w c b : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 < c i) {B d : ℝ}
    (hB : 0 < B) (hd : HasDerivAt (costValue w c b hw hc) d B) (hs : d < 0) :
    0 < selectedPrice w c b hw hc B := by
  have he := cost_value_derivative hw hc hB hd
  linarith

/-- Comparing two certified budgets gives the correct monotonicity direction. -/
theorem price_antitone {w c b x y : ι → ℝ} {B C p q : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 ≤ c i)
    (hx : AllocationKKT w c b x B p) (hy : AllocationKKT w c b y C q)
    (hBC : B < C) : q ≤ p := by
  have hs := kkt_strong_support hw hx hy.nonnegative
  have ht := kkt_strong_support hw hy hx.nonnegative
  have hp := penalty_nonnegative hc (x := x) (y := y)
  have hq := penalty_nonnegative hc (x := y) (y := x)
  have hm := mul_le_mul_of_nonneg_left hy.feasible hx.price_nonnegative
  have hn := mul_le_mul_of_nonneg_left hx.feasible hy.price_nonnegative
  nlinarith

/-- A uniform offset preserves an active allocation precisely when the
rebased inequality price remains admissible. -/
theorem active_offset_kkt {w c b x : ι → ℝ} {B p : ℝ}
    (h : AllocationKKT w c b x B p) (ha : mass x = B)
    (s : ℝ) (hp : 0 ≤ p+s) :
    AllocationKKT w c (fun i => b i+s) x B (p+s) := by
  refine ⟨h.nonnegative, h.feasible, hp, ?_, ?_, ?_⟩
  · intro i
    have hi := h.gradient_bound i
    unfold marginal at *
    linarith
  · intro i
    have hi := h.lower_complementarity i
    unfold marginal at *
    nlinarith [hi]
  · rw [ha]
    ring

/-- At a positive allocation all active patch prices agree; a zero allocation
only has the upper bound already present in the certificate. -/
theorem positive_patch_prices_equal {w c b x : ι → ℝ} {B p : ℝ}
    (h : AllocationKKT w c b x B p) {i j : ι} (hi : 0 < x i) (hj : 0 < x j) :
    marginal (w i) (c i) (b i) (x i) = marginal (w j) (c j) (b j) (x j) := by
  rw [marginal_eq_price_at_positive h hi, marginal_eq_price_at_positive h hj]

def demoAllocation (i : Fin 2) : ℝ := if i.val = 0 then 1 else 2

def demoWeights (i : Fin 2) : ℝ := if i.val = 0 then 4 else 9

def changedWeights (i : Fin 2) : ℝ := if i.val = 0 then 6 else 12

theorem demo_kkt : AllocationKKT demoWeights (fun _ => 1) (fun _ => 0)
    demoAllocation 3 1 := by
  constructor
  · intro i; fin_cases i <;> norm_num [demoAllocation]
  · norm_num [mass, demoAllocation, Fin.sum_univ_succ]
  · norm_num
  · intro i; fin_cases i <;> norm_num [marginal, demoWeights, demoAllocation]
  · intro i; fin_cases i <;> norm_num [marginal, demoWeights, demoAllocation]
  · norm_num [mass, demoAllocation, Fin.sum_univ_succ]

theorem changed_weights_kkt : AllocationKKT changedWeights (fun _ => 1) (fun _ => 0)
    demoAllocation 3 2 := by
  constructor
  · intro i; fin_cases i <;> norm_num [demoAllocation]
  · norm_num [mass, demoAllocation, Fin.sum_univ_succ]
  · norm_num
  · intro i; fin_cases i <;> norm_num [marginal, changedWeights, demoAllocation]
  · intro i; fin_cases i <;> norm_num [marginal, changedWeights, demoAllocation]
  · norm_num [mass, demoAllocation, Fin.sum_univ_succ]

theorem demo_unique_optimizer {y : Fin 2 → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hB : mass y ≤ 3)
    (hu : utility demoWeights (fun _ => 1) (fun _ => 0) demoAllocation ≤
      utility demoWeights (fun _ => 1) (fun _ => 0) y) : demoAllocation = y := by
  apply kkt_unique_optimizer (fun i => ?_) (fun _ => by norm_num) demo_kkt hy hB hu
  fin_cases i <;> norm_num [demoWeights]

/-- Same budget and same optimizer, different local weights and different price.
Spatial uniformity of a global price is not invariance of its value. -/
theorem price_depends_on_weights :
    AllocationKKT demoWeights (fun _ => 1) (fun _ => 0) demoAllocation 3 1 ∧
    AllocationKKT changedWeights (fun _ => 1) (fun _ => 0) demoAllocation 3 2 ∧
    (1 : ℝ) ≠ 2 := by
  exact ⟨demo_kkt, changed_weights_kkt, by norm_num⟩

theorem negative_offset_slack :
    AllocationKKT demoWeights (fun _ => 1) (fun _ => -10) (fun _ => 0) 3 0 := by
  constructor
  · intro i; norm_num
  · norm_num [mass]
  · norm_num
  · intro i; fin_cases i <;> norm_num [marginal, demoWeights]
  · intro i; simp
  · simp [mass]

/-- At the zero budget there may be many inequality multipliers. -/
theorem zero_budget_price_nonunique :
    AllocationKKT demoWeights (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 9 ∧
    AllocationKKT demoWeights (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 10 ∧
    (9 : ℝ) ≠ 10 := by
  have h : ∀ p : ℝ, 9 ≤ p → AllocationKKT demoWeights (fun _ => 1)
      (fun _ => 0) (fun _ => 0) 0 p := by
    intro p hp
    constructor
    · intro i; norm_num
    · simp [mass]
    · linarith
    · intro i; fin_cases i <;> norm_num [marginal, demoWeights] <;> linarith
    · intro i; simp
    · simp [mass]
  exact ⟨h 9 (by norm_num), h 10 (by norm_num), by norm_num⟩

end

end SbtCosmo.Derivation.AllocationPrice
