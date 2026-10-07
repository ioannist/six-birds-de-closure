import SbtCosmo.Derivation.GroundKernelTube
import SbtCosmo.Derivation.GroundSmooth

/-! Uniform kernel Newton certificates over boxes of real potential entries.
At coupling zero these enclose the actual selected ground for every potential
in the box; the potential is not replaced by its midpoint. -/
namespace SbtCosmo.Derivation.GroundBackgroundKernel
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundBorder GroundSmooth GroundKernelTube GroundParameterTube
open GroundRationalInterval GroundResidualEnclosure GroundPointCoordinates
open Metric
open scoped BigOperators

def box (B : Fin 8 → Interval) (z : Fin 9 → ℚ) (r : ℚ) : Variable → Interval
  | .background i => B i
  | .coupling => Interval.point 0
  | .state j => ⟨z j-r, z j+r⟩

theorem box_sound (B : Fin 8 → Interval) (z : Fin 9 → ℚ) (r : ℚ) {b : Field} {x : Point}
    (hb : ∀ i, (B i).Contains (b i)) (hx : x ∈ closedBall (center z) (r : ℝ)) :
    ∀ v, (box B z r v).Contains (valuation b 0 x v) := by
  intro v
  cases v with
  | background i => exact hb i
  | coupling => simpa only [box, valuation, Rat.cast_zero] using Interval.point_sound 0
  | state j =>
    have hn : ‖x-center z‖ ≤ (r : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hh := abs_le.mp ((coord_norm_le (x-center z) j).trans hn)
    rw [coord_sub, center, coord_fromCoord] at hh
    simp only [Interval.Contains, box, valuation, Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith

structure Arithmetic (B : Fin 8 → Interval) (z : Fin 9 → ℚ) (r q y : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) : Prop where
  radius_pos : 0 < r
  rate_nonneg : 0 ≤ q
  rate_lt : q < 1
  residual_nonneg : 0 ≤ y
  strict_invariance : y+q*r < r
  positive : ∀ i : Fin 8, 0 < z i.castSucc-r
  defect_rows : ∀ i : Fin 9, (∑ j, ((defectExpr C i j).enclose (box B z r)).bound) ≤ q
  residual_rows : ∀ i : Fin 9, ((correctedResidualExpr C i).enclose (box B z 0)).bound ≤ y

def tube {B : Fin 8 → Interval} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic B z r q y C)
    (b : Field) (hb : ∀ i, (B i).Contains (b i)) : TubeCertificate b where
  interval := {0}
  center := center z
  radius := r
  preconditioner := preconditioner C
  rate := ⟨q, by exact_mod_cast h.rate_nonneg⟩
  radius_pos := by exact_mod_cast h.radius_pos
  rate_lt := by
    change (q : ℝ) < 1
    exact_mod_cast h.rate_lt
  defect := by
    intro κ hk x hx
    have he : κ = 0 := Set.mem_singleton_iff.mp hk
    subst κ
    exact defect_norm_bound C (box B z r) b 0 x h.rate_nonneg (box_sound B z r hb hx) h.defect_rows
  residual_strict := by
    intro κ hk
    have he : κ = 0 := Set.mem_singleton_iff.mp hk
    subst κ
    have hh := corrected_residual_norm_bound C (box B z 0) b 0 (center z) h.residual_nonneg
      (box_sound B z 0 hb (mem_closedBall_self (by norm_num))) h.residual_rows
    have hs : (y : ℝ)+(q : ℝ)*(r : ℝ) < (r : ℝ) := by exact_mod_cast h.strict_invariance
    exact (add_le_add hh le_rfl).trans_lt hs
  field_positive := by
    intro x hx i
    have hn : ‖x-center z‖ ≤ (r : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hh := abs_le.mp ((coord_norm_le (x-center z) i.castSucc).trans hn)
    rw [coord_sub, center, coord_fromCoord] at hh
    have hp : 0 < (z i.castSucc : ℝ)-(r : ℝ) := by exact_mod_cast h.positive i
    simp only [coord, Fin.lastCases_castSucc] at hh
    linarith

theorem actual_ground_pair_enclosed {B : Fin 8 → Interval} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic B z r q y C)
    {b : Field} (hb : ∀ i, (B i).Contains (b i)) :
    groundPair b ∈ closedBall (center z) (r : ℝ) := by
  obtain ⟨x, hx, _, hg, hf, _⟩ := (tube h b hb).positive_root_exists (by change (0 : ℝ) ∈ ({0} : Set ℝ); exact Set.mem_singleton 0)
  rw [GroundNormalizedJacobian.zero_coupling_groundMap] at hf
  have hv : sourcePotential b 0 x.1 = b := by funext i; simp [sourcePotential, BackgroundSelection.potential]
  rw [hv] at hg
  have he := ground_energy hg
  have hp : groundPair b = x := by
    apply Prod.ext
    · exact hf
    · change energy b (positiveGround b) = x.2
      rw [hf]; exact he
  rw [hp]; exact hx

def fieldBox (z : Fin 9 → ℚ) (r : ℚ) (i : Fin 8) : Interval := ⟨z i.castSucc-r, z i.castSucc+r⟩

theorem actual_selected_enclosed {B : Fin 8 → Interval} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : Arithmetic B z r q y C)
    {b : Field} (hb : ∀ i, (B i).Contains (b i)) (i : Fin 8) :
    (fieldBox z r i).Contains (positiveGround b i) := by
  have hx := actual_ground_pair_enclosed h hb
  have hn : ‖groundPair b-center z‖ ≤ (r : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hh := abs_le.mp ((coord_norm_le (groundPair b-center z) i.castSucc).trans hn)
  rw [coord_sub, center, coord_fromCoord] at hh
  simp only [Interval.Contains, fieldBox, Rat.cast_sub, Rat.cast_add]
  simp only [coord, Fin.lastCases_castSucc] at hh
  change -(r : ℝ) ≤ positiveGround b i-(z i.castSucc : ℝ) ∧
    positiveGround b i-(z i.castSucc : ℝ) ≤ (r : ℝ) at hh
  constructor <;> linarith

end
end SbtCosmo.Derivation.GroundBackgroundKernel
