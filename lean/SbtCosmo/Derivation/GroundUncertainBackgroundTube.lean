import SbtCosmo.Derivation.GroundKernelTube

/-! Kernel-certified Newton tubes uniform over a whole background interval box.
Exact and rounded shifted inputs can be covered together, without identifying
them. Every actual equation and selector return is derived for the supplied
background inside the box. -/
namespace SbtCosmo.Derivation.GroundUncertainBackgroundTube
noncomputable section
set_option maxHeartbeats 2000000
open Metric GroundState GroundBorder GroundRootCertificate GroundParameterTube
open GroundRationalInterval GroundPointCoordinates GroundResidualEnclosure
open scoped BigOperators

def box (B : Fin 8 → Interval) (a c : ℚ) (z : Fin 9 → ℚ) (r : ℚ) : Variable → Interval
  | .background i => B i
  | .coupling => ⟨a, c⟩
  | .state j => ⟨z j - r, z j + r⟩

theorem box_sound (B : Fin 8 → Interval) (a c : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    {b : Field} (hb : ∀ i, (B i).Contains (b i))
    {κ : ℝ} {x : Point} (hk : κ ∈ Set.Icc (a : ℝ) (c : ℝ))
    (hx : x ∈ closedBall (GroundKernelTube.center z) (r : ℝ)) :
    ∀ v, (box B a c z r v).Contains (valuation b κ x v) := by
  intro v
  cases v with
  | background i => exact hb i
  | coupling => exact hk
  | state j =>
    have hn : ‖x - GroundKernelTube.center z‖ ≤ (r : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hc := (coord_norm_le (x - GroundKernelTube.center z) j).trans hn
    rw [coord_sub, GroundKernelTube.center, coord_fromCoord] at hc
    have hh := abs_le.mp hc
    simp only [Interval.Contains, box, valuation, Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith

/-- Numerical input shape used for a concrete certificate. All comparisons are
over exact rationals and can be proved by kernel reduction. -/
structure Arithmetic (B : Fin 8 → Interval) (a c : ℚ) (z : Fin 9 → ℚ) (r q y : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) : Prop where
  radius_pos : 0 < r
  rate_nonneg : 0 ≤ q
  rate_lt : q < 1
  residual_nonneg : 0 ≤ y
  strict_invariance : y + q*r < r
  positive : ∀ i : Fin 8, 0 < z i.castSucc - r
  defect_rows : ∀ i : Fin 9, (∑ j, ((defectExpr C i j).enclose (box B a c z r)).bound) ≤ q
  residual_rows : ∀ i : Fin 9, ((correctedResidualExpr C i).enclose (box B a c z 0)).bound ≤ y

def tube {B : Fin 8 → Interval} {a c : ℚ} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic B a c z r q y C)
    {b : Field} (hb : ∀ i, (B i).Contains (b i)) :
    TubeCertificate b where
  interval := Set.Icc (a : ℝ) (c : ℝ)
  center := GroundKernelTube.center z
  radius := r
  preconditioner := preconditioner C
  rate := ⟨(q : ℝ), by exact_mod_cast h.rate_nonneg⟩
  radius_pos := by exact_mod_cast h.radius_pos
  rate_lt := by
    change (q : ℝ) < 1
    exact_mod_cast h.rate_lt
  defect := fun κ hk x hx =>
    defect_norm_bound C (box B a c z r) b κ x h.rate_nonneg
      (box_sound B a c z r hb hk hx) h.defect_rows
  residual_strict := by
    intro κ hk
    have hb := corrected_residual_norm_bound C (box B a c z 0) b κ (GroundKernelTube.center z)
      h.residual_nonneg (box_sound B a c z 0 hb hk (mem_closedBall_self (by norm_num))) h.residual_rows
    have hh : (y : ℝ) + (q : ℝ)*(r : ℝ) < (r : ℝ) := by exact_mod_cast h.strict_invariance
    exact (add_le_add hb le_rfl).trans_lt hh
  field_positive := by
    intro x hx i
    have hb := abs_le.mp ((coord_norm_le (x - GroundKernelTube.center z) i.castSucc).trans
      (show ‖x-GroundKernelTube.center z‖ ≤ (r : ℝ) by simpa only [mem_closedBall, dist_eq_norm] using hx))
    rw [coord_sub, GroundKernelTube.center, coord_fromCoord] at hb
    have hp : 0 < (z i.castSucc : ℝ) - (r : ℝ) := by exact_mod_cast h.positive i
    simp only [coord, Fin.lastCases_castSucc] at hb
    linarith

theorem certified_actual_root {B : Fin 8 → Interval} {a c : ℚ} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic B a c z r q y C)
    {b : Field} (hb : ∀ i, (B i).Contains (b i))
    {κ : ℝ} (hk : κ ∈ Set.Icc (a : ℝ) (c : ℝ)) :
    ∃ x ∈ closedBall (GroundKernelTube.center z) (r : ℝ), residual b κ x = 0 ∧
      IsGround (sourcePotential b κ x.1) x.1 x.2 ∧
      GroundSourceJacobian.groundMap b κ x.1 = x.1 ∧
      ∀ t ∈ closedBall (GroundKernelTube.center z) (r : ℝ), residual b κ t = 0 → t = x :=
  (tube h hb).positive_root_exists hk

end
end SbtCosmo.Derivation.GroundUncertainBackgroundTube
