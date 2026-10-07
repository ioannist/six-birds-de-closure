import SbtCosmo.Derivation.BackgroundSelection
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
An additional equality-ledger carrier, not a theorem about unchanged Step26.
The nonlinear ledger retains its background-feedback coefficient. A joint
background/dual-price shift preserves the full relative presentation. Absolute
price does not descend through that gauge quotient. A constant chosen gauge
representative is possible; it is not an equivariant absolute-value law.
-/
namespace SbtCosmo.Derivation.GaugeClosure

noncomputable section
open Finset

def ledgerTerm (kappa density : ℝ) : ℝ := density + kappa / 2 * density ^ 2

theorem ledgerTerm_hasDerivAt (kappa density : ℝ) :
    HasDerivAt (ledgerTerm kappa) (1 + kappa * density) density := by
  convert (hasDerivAt_id density).add
    (((hasDerivAt_id density).pow 2).const_mul (kappa / 2)) using 1
  simp
  ring

theorem ledgerTerm_nonnegative {kappa density : ℝ}
    (hk : 0 ≤ kappa) (hd : 0 ≤ density) : 0 ≤ ledgerTerm kappa density := by
  unfold ledgerTerm
  positivity

theorem ledgerTerm_dominates_density {kappa density : ℝ} (hk : 0 ≤ kappa) :
    density ≤ ledgerTerm kappa density := by
  unfold ledgerTerm
  have : 0 ≤ kappa / 2 * density ^ 2 := by positivity
  linarith

/-- Matching Step26's shift coefficient fixes this quadratic ledger. -/
theorem quadratic_ledger_unique (a b kappa : ℝ)
    (h : ∀ density : ℝ, a + 2 * b * density = 1 + kappa * density) :
    a = 1 ∧ b = kappa / 2 := by
  have h0 := h 0
  have h1 := h 1
  constructor <;> nlinarith

theorem annihilating_projection_shift {V : Type*} [AddCommGroup V] [Module ℝ V]
    (project : V →ₗ[ℝ] V) (force normal : V) (shift : ℝ)
    (h : project normal = 0) : project (force + shift • normal) = project force := by
  simp only [map_add, map_smul, h, smul_zero, add_zero]

section FiniteLedger
variable {n : Type*} [Fintype n]

def ledger (kappa : ℝ) (density : n → ℝ) : ℝ :=
  ∑ i, ledgerTerm kappa (density i)

def objective (base : (n → ℝ) → ℝ) (kappa : ℝ)
    (background density : n → ℝ) : ℝ :=
  base density + ∑ i, background i * ledgerTerm kappa (density i)

def feedbackForce (background density gradientEnergy field : n → ℝ) (kappa : ℝ) : n → ℝ :=
  fun i => BackgroundSelection.potential (background i) kappa (density i) (gradientEnergy i) * field i

def feedbackNormal (density field : n → ℝ) (kappa : ℝ) : n → ℝ :=
  fun i => (1 + kappa * density i) * field i

omit [Fintype n] in
theorem feedbackForce_shift (background density gradientEnergy field : n → ℝ) (kappa shift : ℝ) :
    feedbackForce (fun i => background i + shift) density gradientEnergy field kappa =
      feedbackForce background density gradientEnergy field kappa +
        shift • feedbackNormal density field kappa := by
  funext i
  simp only [feedbackForce, feedbackNormal, BackgroundSelection.potential,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype n] in
/-- Tangent projection removes precisely the added ledger-normal force. The
background-independent force can include the original kinetic operator. The
same real identity applies to real and imaginary coordinates of a field. -/
theorem projected_feedback_blind (background density gradientEnergy field baseForce : n → ℝ)
    (kappa shift : ℝ) (project : (n → ℝ) →ₗ[ℝ] (n → ℝ))
    (h : project (feedbackNormal density field kappa) = 0) :
    project (baseForce + feedbackForce (fun i => background i + shift) density gradientEnergy field kappa) =
      project (baseForce + feedbackForce background density gradientEnergy field kappa) := by
  rw [feedbackForce_shift, ← add_assoc]
  exact annihilating_projection_shift project
    (baseForce + feedbackForce background density gradientEnergy field kappa)
    (feedbackNormal density field kappa) shift h

theorem objective_shift (base : (n → ℝ) → ℝ) (kappa shift : ℝ)
    (background density : n → ℝ) :
    objective base kappa (fun i => background i + shift) density =
      objective base kappa background density + shift * ledger kappa density := by
  simp only [objective, ledger, add_mul, sum_add_distrib, mul_sum]
  ring

/-- Whole objective order, not merely stationarity, is preserved on the ledger. -/
theorem objective_order_on_ledger (base : (n → ℝ) → ℝ)
    (kappa shift budget : ℝ) (background x y : n → ℝ)
    (hx : ledger kappa x = budget) (hy : ledger kappa y = budget) :
    objective base kappa (fun i => background i + shift) x ≤
        objective base kappa (fun i => background i + shift) y ↔
      objective base kappa background x ≤ objective base kappa background y := by
  rw [objective_shift, objective_shift, hx, hy]
  constructor <;> intro h <;> linarith

def IsOptimalOnLedger (allowed : (n → ℝ) → Prop) (base : (n → ℝ) → ℝ)
    (kappa budget : ℝ) (background x : n → ℝ) : Prop :=
  allowed x ∧ ledger kappa x = budget ∧ ∀ y, allowed y → ledger kappa y = budget →
    objective base kappa background y ≤ objective base kappa background x

theorem optimizer_shift_iff (allowed : (n → ℝ) → Prop) (base : (n → ℝ) → ℝ)
    (kappa budget shift : ℝ) (background x : n → ℝ) :
    IsOptimalOnLedger allowed base kappa budget (fun i => background i + shift) x ↔
      IsOptimalOnLedger allowed base kappa budget background x := by
  constructor
  · rintro ⟨ha, hx, h⟩
    refine ⟨ha, hx, ?_⟩
    intro y hay hy
    exact (objective_order_on_ledger base kappa shift budget background y x hy hx).1 (h y hay hy)
  · rintro ⟨ha, hx, h⟩
    refine ⟨ha, hx, ?_⟩
    intro y hay hy
    exact (objective_order_on_ledger base kappa shift budget background y x hy hx).2 (h y hay hy)

/-- Finite simplex projection characterized by its water level. -/
def IsSimplexProjection (vector x : n → ℝ) (budget level : ℝ) : Prop :=
  (∑ i, x i) = budget ∧ ∀ i, x i = max (vector i - level) 0

theorem simplex_projection_shift (vector x : n → ℝ) (budget level shift : ℝ)
    (h : IsSimplexProjection vector x budget level) :
    IsSimplexProjection (fun i => vector i + shift) x budget (level + shift) := by
  refine ⟨h.1, ?_⟩
  intro i
  have heq : vector i + shift - (level + shift) = vector i - level := by ring
  rw [heq]
  exact h.2 i

theorem max_sub_firm (v t u : ℝ) :
    (max (v - t) 0 - max (v - u) 0) ^ 2 ≤
      (u - t) * (max (v - t) 0 - max (v - u) 0) := by
  by_cases ht : 0 ≤ v - t
  · by_cases hu : 0 ≤ v - u
    · rw [max_eq_left ht, max_eq_left hu]
      nlinarith
    · have hu' : v - u ≤ 0 := le_of_lt (lt_of_not_ge hu)
      rw [max_eq_left ht, max_eq_right hu']
      nlinarith [mul_nonneg ht (show 0 ≤ u - v by linarith)]
  · have ht' : v - t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    by_cases hu : 0 ≤ v - u
    · rw [max_eq_right ht', max_eq_left hu]
      nlinarith [mul_nonneg hu (show 0 ≤ t - v by linarith)]
    · have hu' : v - u ≤ 0 := le_of_lt (lt_of_not_ge hu)
      rw [max_eq_right ht', max_eq_right hu']
      norm_num

/-- The projected state is unique even when the water-level representation is not. -/
theorem simplex_projection_unique (vector x y : n → ℝ) (budget t u : ℝ)
    (hx : IsSimplexProjection vector x budget t)
    (hy : IsSimplexProjection vector y budget u) : x = y := by
  have hpoint : ∀ i, (x i - y i)^2 ≤ (u - t) * (x i - y i) := by
    intro i
    rw [hx.2 i, hy.2 i]
    exact max_sub_firm (vector i) t u
  have hs : (∑ i, (x i - y i)^2) ≤ 0 := by
    calc
      ∑ i, (x i - y i)^2 ≤ ∑ i, (u - t) * (x i - y i) :=
        sum_le_sum fun i _ => hpoint i
      _ = 0 := by rw [← mul_sum, sum_sub_distrib, hx.1, hy.1]; ring
  have hz : (∑ i, (x i - y i)^2) = 0 :=
    le_antisymm hs (sum_nonneg fun i _ => sq_nonneg (x i - y i))
  funext i
  have hi : (x i - y i)^2 = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - y j))).1 hz i (mem_univ i)
  nlinarith [sq_nonneg (x i - y i)]

def gradientVector (weight curvature background x : n → ℝ) (rate : ℝ) : n → ℝ :=
  fun i => x i + rate * (weight i / (1 + x i) - curvature i * x i + background i)

/-- Signed equality multiplier and lower-bound KKT conditions of the concrete
strictly concave allocation problem, in ledger coordinates. -/
def AllocationKKT (weight curvature background x : n → ℝ) (budget price : ℝ) : Prop :=
  (∑ i, x i) = budget ∧ ∀ i, 0 ≤ x i ∧
    (x i = 0 → weight i + background i ≤ price) ∧
    (0 < x i → weight i / (1 + x i) - curvature i * x i + background i = price)

theorem allocationKKT_shift (weight curvature background x : n → ℝ) (budget price shift : ℝ)
    (h : AllocationKKT weight curvature background x budget price) :
    AllocationKKT weight curvature (fun i => background i + shift) x budget (price + shift) := by
  refine ⟨h.1, ?_⟩
  intro i
  refine ⟨(h.2 i).1, ?_, ?_⟩
  · intro hx
    have hi := (h.2 i).2.1 hx
    linarith
  · intro hx
    have hi := (h.2 i).2.2 hx
    linarith

/-- Actual projected-gradient updates commute with background shifts. No
pre-assumed quotient update is needed for this implementation. -/
theorem projected_gradient_state_shift (weight curvature background x y z : n → ℝ)
    (rate budget t u shift : ℝ)
    (hy : IsSimplexProjection (gradientVector weight curvature background x rate) y budget t)
    (hz : IsSimplexProjection
      (gradientVector weight curvature (fun i => background i + shift) x rate) z budget u) :
    y = z := by
  have hv : gradientVector weight curvature (fun i => background i + shift) x rate =
      fun i => gradientVector weight curvature background x rate i + rate * shift := by
    funext i
    unfold gradientVector
    ring
  rw [hv] at hz
  exact simplex_projection_unique _ y z budget (t + rate * shift) u
    (simplex_projection_shift _ y budget t (rate * shift) hy) hz

theorem full_projected_histories (weight curvature background : n → ℝ)
    (left right : ℕ → n → ℝ) (leftLevel rightLevel : ℕ → ℝ)
    (rate budget shift : ℝ) (hinit : left 0 = right 0)
    (hl : ∀ k, IsSimplexProjection
      (gradientVector weight curvature background (left k) rate) (left (k + 1)) budget (leftLevel k))
    (hr : ∀ k, IsSimplexProjection
      (gradientVector weight curvature (fun i => background i + shift) (right k) rate)
      (right (k + 1)) budget (rightLevel k)) : ∀ k, left k = right k := by
  intro k
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have hright := hr k
    rw [← ih] at hright
    exact projected_gradient_state_shift weight curvature background (left k)
      (left (k + 1)) (right (k + 1)) rate budget (leftLevel k) (rightLevel k) shift
      (hl k) hright

end FiniteLedger
variable {n : Type*}

def screenedPotential (background price kappa density gradientEnergy : ℝ) : ℝ :=
  BackgroundSelection.potential background kappa density gradientEnergy -
    price * (1 + kappa * density)

theorem screenedPotential_eq_relative (background price kappa density gradientEnergy : ℝ) :
    screenedPotential background price kappa density gradientEnergy =
      (background - price) * (1 + kappa * density) + kappa * gradientEnergy := by
  unfold screenedPotential BackgroundSelection.potential
  ring

theorem screenedPotential_shift (background price kappa density gradientEnergy shift : ℝ) :
    screenedPotential (background + shift) (price + shift) kappa density gradientEnergy =
      screenedPotential background price kappa density gradientEnergy := by
  simp only [screenedPotential_eq_relative]
  ring

structure Presentation (S : Type*) (n : Type*) where
  state : S
  background : n → ℝ
  price : ℝ

variable {S : Type*}

def shiftPresentation (p : Presentation S n) (c : ℝ) : Presentation S n :=
  ⟨p.state, fun i => p.background i + c, p.price + c⟩

/-- Full state plus every relative background coordinate. The state may include
the entire retained history. Absolute chart origins are declared gauge data. -/
def record (p : Presentation S n) : S × (n → ℝ) :=
  (p.state, fun i => p.background i - p.price)

theorem record_shift (p : Presentation S n) (c : ℝ) :
    record (shiftPresentation p c) = record p := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [record, shiftPresentation]
    ring

/-- No extra loss: equal records are exactly joint additive gauge orbits. -/
theorem record_eq_iff_shift (p q : Presentation S n) :
    record p = record q ↔ ∃ c, q = shiftPresentation p c := by
  constructor
  · intro h
    have hs : p.state = q.state := congrArg Prod.fst h
    have hb : ∀ i, p.background i - p.price = q.background i - q.price :=
      fun i => congrFun (congrArg Prod.snd h) i
    refine ⟨q.price - p.price, ?_⟩
    cases p with
    | mk s b t =>
      cases q with
      | mk s' b' t' =>
        simp only [shiftPresentation, Presentation.mk.injEq]
        refine ⟨hs.symm, ?_, ?_⟩
        · funext i
          have hi := hb i
          dsimp at hi
          linarith
        · ring
  · rintro ⟨c, rfl⟩
    exact (record_shift p c).symm

theorem absolute_price_not_descend (p : Presentation S n) :
    ¬ ∃ f : S × (n → ℝ) → ℝ, ∀ q : Presentation S n, f (record q) = q.price := by
  apply BackgroundSelection.same_record_different_value_no_factor record
    Presentation.price (x := p) (y := shiftPresentation p 1)
  · exact (record_shift p 1).symm
  · simp only [shiftPresentation]
    linarith

/-- Only two admitted realizations are needed; unrestricted ambient states
are not used to smuggle a physical-domain witness into the conclusion. -/
theorem admitted_absolute_price_not_descend (admitted : Presentation S n → Prop)
    (p : Presentation S n) (hp : admitted p) (hshift : admitted (shiftPresentation p 1)) :
    ¬ ∃ f : S × (n → ℝ) → ℝ, ∀ q : Presentation S n, admitted q → f (record q) = q.price := by
  rintro ⟨f, hf⟩
  have h0 := hf p hp
  have h1 := hf (shiftPresentation p 1) hshift
  rw [record_shift] at h1
  simp only [shiftPresentation] at h1
  linarith

/-- An explicit heterogeneous, nonlinear, positive-price realization. -/
def realizedPresentation : Presentation (Fin 2 → ℝ) (Fin 2) :=
  ⟨![1 / 2, 1], ![0, 1 / 2], 3 / 2⟩

theorem realized_pair :
    AllocationKKT ![63 / 16, 9] ![1, 1] realizedPresentation.background
      (fun i => ledgerTerm 2 (realizedPresentation.state i)) (11 / 4) realizedPresentation.price ∧
    AllocationKKT ![63 / 16, 9] ![1, 1] (shiftPresentation realizedPresentation 1).background
      (fun i => ledgerTerm 2 ((shiftPresentation realizedPresentation 1).state i))
      (11 / 4) (shiftPresentation realizedPresentation 1).price ∧
    record (shiftPresentation realizedPresentation 1) = record realizedPresentation ∧
    0 < realizedPresentation.price ∧
    realizedPresentation.price ≠ (shiftPresentation realizedPresentation 1).price := by
  have h : AllocationKKT ![63 / 16, 9] ![1, 1] realizedPresentation.background
      (fun i => ledgerTerm 2 (realizedPresentation.state i)) (11 / 4) realizedPresentation.price := by
    constructor
    · norm_num [realizedPresentation, ledgerTerm, Fin.sum_univ_two]
    · intro i
      fin_cases i <;> norm_num [realizedPresentation, ledgerTerm]
  refine ⟨h, allocationKKT_shift _ _ _ _ _ _ 1 h, record_shift _ _, ?_, ?_⟩ <;>
    norm_num [realizedPresentation, shiftPresentation]

theorem realized_admitted_prices_not_descend :
    ¬ ∃ f : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ,
      ∀ q : Presentation (Fin 2 → ℝ) (Fin 2),
        ((∀ i, 0 ≤ q.state i) ∧ AllocationKKT ![63 / 16, 9] ![1, 1] q.background
          (fun i => ledgerTerm 2 (q.state i)) (11 / 4) q.price) → f (record q) = q.price := by
  apply admitted_absolute_price_not_descend
    (fun q : Presentation (Fin 2 → ℝ) (Fin 2) =>
      (∀ i, 0 ≤ q.state i) ∧ AllocationKKT ![63 / 16, 9] ![1, 1] q.background
      (fun i => ledgerTerm 2 (q.state i)) (11 / 4) q.price) realizedPresentation
  · refine ⟨?_, realized_pair.1⟩
    intro i
    fin_cases i <;> norm_num [realizedPresentation]
  · refine ⟨?_, realized_pair.2.1⟩
    intro i
    fin_cases i <;> norm_num [realizedPresentation, shiftPresentation]

theorem no_equivariant_absolute_selector (p : Presentation S n) :
    ¬ ∃ f : S × (n → ℝ) → ℝ, ∀ q : Presentation S n, ∀ c : ℝ,
      f (record (shiftPresentation q c)) = f (record q) + c := by
  rintro ⟨f, hf⟩
  have h := hf p 1
  rw [record_shift] at h
  linarith

/-- Any deterministic update using this full quotient, at every finite time.
The screened feedback potential above has exactly this dependence. -/
def history (step : (n → ℝ) → S → S) (p : Presentation S n) : ℕ → S
  | 0 => p.state
  | k + 1 => step (record p).2 (history step p k)

theorem history_shift (step : (n → ℝ) → S → S)
    (p : Presentation S n) (c : ℝ) (k : ℕ) :
    history step (shiftPresentation p c) k = history step p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [history, record_shift, ih]

end
end SbtCosmo.Derivation.GaugeClosure
