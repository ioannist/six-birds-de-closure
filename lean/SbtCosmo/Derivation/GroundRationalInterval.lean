import SbtCosmo.Derivation.GroundParameterTube

/-! Exact rational interval arithmetic and expression evaluation. Soundness
concerns real values, while certificate comparisons compute over rationals in
the kernel. No external arithmetic checker is part of these soundness proofs. -/
namespace SbtCosmo.Derivation.GroundRationalInterval
open scoped BigOperators

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def Interval.Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ a.hi
def Interval.point (q : ℚ) : Interval := ⟨q, q⟩
def Interval.add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Interval.neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩
def Interval.mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def Interval.bound (a : Interval) : ℚ := max |a.lo| |a.hi|

theorem Interval.point_sound (q : ℚ) : (Interval.point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem Interval.add_sound {a b : Interval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  simpa only [Interval.Contains, Interval.add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem Interval.neg_sound {a : Interval} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := by
  simpa only [Interval.Contains, Interval.neg, Rat.cast_neg] using
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

/-- Each endpoint case is selected from signs; no positivity of the intervals
is assumed, so boxes crossing zero and negative coefficients are covered. -/
theorem mul_rectangle_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hlow : ∀ u, u*c ≤ u*y ∧ u*y ≤ u*d ∨ u*d ≤ u*y ∧ u*y ≤ u*c := by
    intro u
    by_cases hu : 0 ≤ u
    · exact Or.inl ⟨mul_le_mul_of_nonneg_left hy.1 hu, mul_le_mul_of_nonneg_left hy.2 hu⟩
    · exact Or.inr ⟨mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hu),
        mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hu)⟩
  have houter : a*y ≤ x*y ∧ x*y ≤ b*y ∨ b*y ≤ x*y ∧ x*y ≤ a*y := by
    by_cases hy0 : 0 ≤ y
    · exact Or.inl ⟨mul_le_mul_of_nonneg_right hx.1 hy0, mul_le_mul_of_nonneg_right hx.2 hy0⟩
    · exact Or.inr ⟨mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0),
        mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)⟩
  rcases hlow a with ha | ha <;> rcases hlow b with hb | hb <;>
    rcases houter with ho | ho
  all_goals constructor
  all_goals first
    | exact (min_le_of_left_le (min_le_left _ _)).trans (ha.1.trans ho.1)
    | exact (min_le_of_left_le (min_le_right _ _)).trans (ha.1.trans ho.1)
    | exact (min_le_of_right_le (min_le_left _ _)).trans (hb.1.trans ho.1)
    | exact (min_le_of_right_le (min_le_right _ _)).trans (hb.1.trans ho.1)
    | exact ho.2.trans (hb.2.trans (le_max_of_le_right (le_max_right _ _)))
    | exact ho.2.trans (hb.2.trans (le_max_of_le_right (le_max_left _ _)))
    | exact ho.2.trans (ha.2.trans (le_max_of_le_left (le_max_right _ _)))
    | exact ho.2.trans (ha.2.trans (le_max_of_le_left (le_max_left _ _)))

theorem Interval.mul_sound {a b : Interval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  simpa only [Interval.Contains, Interval.mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
    using mul_rectangle_bounds hx hy

theorem Interval.abs_le_bound {a : Interval} {x : ℝ} (hx : a.Contains x) :
    |x| ≤ (a.bound : ℝ) := by
  rw [Interval.bound, Rat.cast_max, Rat.cast_abs, Rat.cast_abs]
  apply abs_le.mpr
  constructor
  · have hlow := (neg_le_abs (a.lo : ℝ)).trans (le_max_left |(a.lo : ℝ)| |(a.hi : ℝ)|)
    linarith [hx.1]
  · exact hx.2.trans ((le_abs_self (a.hi : ℝ)).trans (le_max_right _ _))

inductive Expr (V : Type*) where
  | const : ℚ → Expr V
  | var : V → Expr V
  | add : Expr V → Expr V → Expr V
  | neg : Expr V → Expr V
  | mul : Expr V → Expr V → Expr V

variable {V : Type*}

def Expr.eval (σ : V → ℝ) : Expr V → ℝ
  | .const q => q
  | .var i => σ i
  | .add a b => a.eval σ + b.eval σ
  | .neg a => -a.eval σ
  | .mul a b => a.eval σ * b.eval σ

def Expr.enclose (B : V → Interval) : Expr V → Interval
  | .const q => Interval.point q
  | .var i => B i
  | .add a b => (a.enclose B).add (b.enclose B)
  | .neg a => (a.enclose B).neg
  | .mul a b => (a.enclose B).mul (b.enclose B)

theorem Expr.enclose_sound (e : Expr V) {B : V → Interval} {σ : V → ℝ}
    (h : ∀ i, (B i).Contains (σ i)) : (e.enclose B).Contains (e.eval σ) := by
  induction e with
  | const q => exact Interval.point_sound q
  | var i => exact h i
  | add a b ha hb => exact Interval.add_sound ha hb
  | neg a ha => exact Interval.neg_sound ha
  | mul a b ha hb => exact Interval.mul_sound ha hb

def Expr.sum {n : ℕ} (e : Fin n → Expr V) : Expr V :=
  (List.ofFn e).foldr Expr.add (.const 0)

theorem Expr.eval_sum {n : ℕ} (e : Fin n → Expr V) (σ : V → ℝ) :
    (Expr.sum e).eval σ = ∑ i, (e i).eval σ := by
  unfold Expr.sum
  have h : ∀ l : List (Expr V), (l.foldr Expr.add (.const 0)).eval σ =
      (l.map (Expr.eval σ)).sum := by
    intro l
    induction l with
    | nil => simp [Expr.eval]
    | cons i l ih => simp [Expr.eval, ih]
  rw [h, List.map_ofFn, List.sum_ofFn]
  rfl

end SbtCosmo.Derivation.GroundRationalInterval
