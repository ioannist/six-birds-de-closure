import SbtCosmo.Derivation.GroundBackgroundKernel
import SbtCosmo.Derivation.GroundBorderResponse
import SbtCosmo.Derivation.GroundNativeBox

/-! Uniform response control for the actual selector on a whole potential box.
The border inverse error is earned from the same zero-coupling Newton defect;
source perturbations can have all real/imaginary contributions. -/
namespace SbtCosmo.Derivation.GroundBackgroundResponse
noncomputable section
set_option maxHeartbeats 3000000
open GroundState GroundBorder GroundSmooth GroundSourceJacobian GroundRootCertificate
open GroundRationalInterval GroundResidualEnclosure GroundPointCoordinates GroundKernelTube
open GroundNativeBox
open scoped BigOperators

theorem residualDerivative_zero (b : Field) (x : Point) :
    residualDerivative b 0 x = border b x.1 x.2 := by
  apply ContinuousLinearMap.ext
  intro h
  have hv : sourcePotential b 0 x.1 = b := by
    funext i; simp [sourcePotential, BackgroundSelection.potential]
  rw [residualDerivative_apply, hv, border_apply]
  simp [sourceDerivative_apply]

theorem actual_border_defect {B : Fin 8 → Interval} {z : Fin 9 → ℚ} {r q y : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} (h : GroundBackgroundKernel.Arithmetic B z r q y C)
    {b : Field} (hb : ∀ i, (B i).Contains (b i)) :
    ‖ContinuousLinearMap.id ℝ Point - (preconditioner C).comp
      (border b (groundPair b).1 (groundPair b).2)‖ ≤ (q : ℝ) := by
  have hg := GroundBackgroundKernel.actual_ground_pair_enclosed h hb
  have he := defect_norm_bound C (GroundBackgroundKernel.box B z r) b 0 (groundPair b)
    h.rate_nonneg (GroundBackgroundKernel.box_sound B z r hb hg) h.defect_rows
  unfold correctionDerivative at he
  rw [residualDerivative_zero] at he
  exact he

def rhs (b v : Field) : Point := (fun i => -v i * positiveGround b i, 0)
def rhsBox (G V : Fin 8 → Interval) : Fin 9 → Interval :=
  Fin.lastCases (Interval.point 0) (fun i => (V i).neg.mul (G i))
def correctedBox (C : Matrix (Fin 9) (Fin 9) ℚ) (G V : Fin 8 → Interval) (i : Fin 9) : Interval :=
  sumBox (fun j => (Interval.point (C i j)).mul (rhsBox G V j))

theorem rhsBox_sound {G V : Fin 8 → Interval} {b v : Field}
    (hg : ∀ i, (G i).Contains (positiveGround b i)) (hv : ∀ i, (V i).Contains (v i)) (j : Fin 9) :
    (rhsBox G V j).Contains (coord (rhs b v) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [rhsBox, rhs, coord, Fin.lastCases_last, Rat.cast_zero] using Interval.point_sound 0
  · simpa only [rhsBox, rhs, coord, Fin.lastCases_castSucc] using
      Interval.mul_sound (Interval.neg_sound (hv i)) (hg i)

theorem correctedBox_sound (C : Matrix (Fin 9) (Fin 9) ℚ) {G V : Fin 8 → Interval} {b v : Field}
    (hg : ∀ i, (G i).Contains (positiveGround b i)) (hv : ∀ i, (V i).Contains (v i)) (i : Fin 9) :
    (correctedBox C G V i).Contains (coord (preconditioner C (rhs b v)) i) := by
  have h := sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound (C i j)) (rhsBox_sound hg hv j))
  simpa only [correctedBox, preconditioner, matrixMap_apply] using h

structure ResponseArithmetic (C : Matrix (Fin 9) (Fin 9) ℚ) (G V : Fin 8 → Interval)
    (q y e : ℚ) : Prop where
  rhs_nonneg : 0 ≤ y
  error_nonneg : 0 ≤ e
  budget : q*y ≤ e*(1-q)
  rhs_rows : ∀ i, (correctedBox C G V i).bound ≤ y

theorem actual_response_error {B : Fin 8 → Interval} {z : Fin 9 → ℚ} {r q a y e : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} {V : Fin 8 → Interval}
    (h : GroundBackgroundKernel.Arithmetic B z r q a C)
    (hv : ResponseArithmetic C (GroundBackgroundKernel.fieldBox z r) V q y e)
    {b v : Field} (hb : ∀ i, (B i).Contains (b i)) (hV : ∀ i, (V i).Contains (v i)) :
    ‖pairDerivative b v-preconditioner C (rhs b v)‖ ≤ (e : ℝ) := by
  have hq : 0 ≤ (q : ℝ) := by exact_mod_cast h.rate_nonneg
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast h.rate_lt
  have hh := GroundBorderResponse.linear_response_error_mul _ (preconditioner C)
    (pairDerivative_equation b v) hq (actual_border_defect h hb)
  change (1-(q : ℝ))*‖pairDerivative b v-preconditioner C (rhs b v)‖ ≤
    (q : ℝ)*‖preconditioner C (rhs b v)‖ at hh
  have hc := correctedBox_sound C (GroundBackgroundKernel.actual_selected_enclosed h hb) hV
  have hr : ‖preconditioner C (rhs b v)‖ ≤ (y : ℝ) := by
    apply norm_le_coordinates (by exact_mod_cast hv.rhs_nonneg)
    intro i
    exact (Interval.abs_le_bound (hc i)).trans (by exact_mod_cast hv.rhs_rows i)
  have budget : (q : ℝ)*(y : ℝ) ≤ (e : ℝ)*(1-(q : ℝ)) := by exact_mod_cast hv.budget
  have hn := mul_le_mul_of_nonneg_left hr hq
  nlinarith

def responseInterval (C : Matrix (Fin 9) (Fin 9) ℚ) (G V : Fin 8 → Interval) (e : ℚ) (i : Fin 8) : Interval :=
  (correctedBox C G V i.castSucc).add ⟨-e,e⟩

theorem actual_selector_response_enclosed {B : Fin 8 → Interval} {z : Fin 9 → ℚ} {r q a y e : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} {V : Fin 8 → Interval}
    (h : GroundBackgroundKernel.Arithmetic B z r q a C)
    (hv : ResponseArithmetic C (GroundBackgroundKernel.fieldBox z r) V q y e)
    {b v : Field} (hb : ∀ i, (B i).Contains (b i)) (hV : ∀ i, (V i).Contains (v i)) (i : Fin 8) :
    (responseInterval C (GroundBackgroundKernel.fieldBox z r) V e i).Contains (selectorDerivative b v i) := by
  have he := (coord_norm_le (pairDerivative b v-preconditioner C (rhs b v)) i.castSucc).trans
    (actual_response_error h hv hb hV)
  rw [coord_sub] at he
  simp only [coord, Fin.lastCases_castSucc] at he
  have hx : (⟨-e,e⟩ : Interval).Contains
      ((pairDerivative b v).1 i-(preconditioner C (rhs b v)).1 i) := by
    simpa only [Interval.Contains, Rat.cast_neg] using abs_le.mp he
  have hc := correctedBox_sound C (GroundBackgroundKernel.actual_selected_enclosed h hb) hV i.castSucc
  have hs := Interval.add_sound hc hx
  simpa only [responseInterval, coord, Fin.lastCases_castSucc, add_sub_cancel,
    selectorDerivative, ContinuousLinearMap.comp_apply] using hs


end
end SbtCosmo.Derivation.GroundBackgroundResponse
