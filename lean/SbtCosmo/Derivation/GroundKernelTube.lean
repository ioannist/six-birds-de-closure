import SbtCosmo.Derivation.GroundResidualEnclosure

/-! Turn kernel-checked rational enclosures into actual uniform Newton tubes.
The only certificate hypotheses are explicit rational arithmetic comparisons;
the real operator, equation, positivity, and residual obligations are derived. -/
namespace SbtCosmo.Derivation.GroundKernelTube
noncomputable section
set_option maxHeartbeats 2000000
open Metric GroundState GroundBorder GroundRootCertificate GroundParameterTube
open GroundRationalInterval GroundPointCoordinates GroundResidualEnclosure
open scoped BigOperators

def background (β : Fin 8 → ℚ) : Field := fun i => β i
def center (z : Fin 9 → ℚ) : Point := fromCoord (fun j => (z j : ℝ))

def box (β : Fin 8 → ℚ) (a c : ℚ) (z : Fin 9 → ℚ) (r : ℚ) : Variable → Interval
  | .background i => .point (β i)
  | .coupling => ⟨a, c⟩
  | .state j => ⟨z j - r, z j + r⟩

theorem box_sound (β : Fin 8 → ℚ) (a c : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    {κ : ℝ} {x : Point} (hk : κ ∈ Set.Icc (a : ℝ) (c : ℝ))
    (hx : x ∈ closedBall (center z) (r : ℝ)) :
    ∀ v, (box β a c z r v).Contains (valuation (background β) κ x v) := by
  intro v
  cases v with
  | background i => exact Interval.point_sound (β i)
  | coupling => exact hk
  | state j =>
    have hn : ‖x - center z‖ ≤ (r : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hc := (coord_norm_le (x - center z) j).trans hn
    rw [coord_sub, center, coord_fromCoord] at hc
    have hh := abs_le.mp hc
    simp only [Interval.Contains, box, valuation, Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith

/-- Numerical input shape used for a concrete certificate. All comparisons are
over exact rationals and can be proved by kernel reduction. -/
structure Arithmetic (β : Fin 8 → ℚ) (a c : ℚ) (z : Fin 9 → ℚ) (r q y : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) : Prop where
  radius_pos : 0 < r
  rate_nonneg : 0 ≤ q
  rate_lt : q < 1
  residual_nonneg : 0 ≤ y
  strict_invariance : y + q*r < r
  positive : ∀ i : Fin 8, 0 < z i.castSucc - r
  defect_rows : ∀ i : Fin 9, (∑ j, ((defectExpr C i j).enclose (box β a c z r)).bound) ≤ q
  residual_rows : ∀ i : Fin 9, ((correctedResidualExpr C i).enclose (box β a c z 0)).bound ≤ y

def tube {β : Fin 8 → ℚ} {a c : ℚ} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic β a c z r q y C) :
    TubeCertificate (background β) where
  interval := Set.Icc (a : ℝ) (c : ℝ)
  center := center z
  radius := r
  preconditioner := preconditioner C
  rate := ⟨(q : ℝ), by exact_mod_cast h.rate_nonneg⟩
  radius_pos := by exact_mod_cast h.radius_pos
  rate_lt := by
    change (q : ℝ) < 1
    exact_mod_cast h.rate_lt
  defect := fun κ hk x hx =>
    defect_norm_bound C (box β a c z r) (background β) κ x h.rate_nonneg
      (box_sound β a c z r hk hx) h.defect_rows
  residual_strict := by
    intro κ hk
    have hb := corrected_residual_norm_bound C (box β a c z 0) (background β) κ (center z)
      h.residual_nonneg (box_sound β a c z 0 hk (mem_closedBall_self (by norm_num))) h.residual_rows
    have hh : (y : ℝ) + (q : ℝ)*(r : ℝ) < (r : ℝ) := by exact_mod_cast h.strict_invariance
    exact (add_le_add hb le_rfl).trans_lt hh
  field_positive := by
    intro x hx i
    have hb := abs_le.mp ((coord_norm_le (x - center z) i.castSucc).trans
      (show ‖x-center z‖ ≤ (r : ℝ) by simpa only [mem_closedBall, dist_eq_norm] using hx))
    rw [coord_sub, center, coord_fromCoord] at hb
    have hp : 0 < (z i.castSucc : ℝ) - (r : ℝ) := by exact_mod_cast h.positive i
    simp only [coord, Fin.lastCases_castSucc] at hb
    linarith

theorem certified_actual_root {β : Fin 8 → ℚ} {a c : ℚ} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic β a c z r q y C)
    {κ : ℝ} (hk : κ ∈ Set.Icc (a : ℝ) (c : ℝ)) :
    ∃ x ∈ closedBall (center z) (r : ℝ), residual (background β) κ x = 0 ∧
      IsGround (sourcePotential (background β) κ x.1) x.1 x.2 ∧
      GroundSourceJacobian.groundMap (background β) κ x.1 = x.1 ∧
      ∀ t ∈ closedBall (center z) (r : ℝ), residual (background β) κ t = 0 → t = x :=
  (tube h).positive_root_exists hk

end
end SbtCosmo.Derivation.GroundKernelTube
