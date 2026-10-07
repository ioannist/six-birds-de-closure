import SbtCosmo.Derivation.GroundUncertainBackgroundTube
import SbtCosmo.Derivation.GroundBorderResponse
import SbtCosmo.Derivation.GroundMatrixCoordinates

/-! Actual bordered-selector responses on a whole background box. The saved
border preconditioner differs from the nonlinear root preconditioner, and the
quantitative inverse error is retained before normalized/native derivatives. -/
namespace SbtCosmo.Derivation.GroundUncertainBorderResponse
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
open GroundState GroundBorder GroundSourceJacobian GroundRationalInterval
open GroundResidualEnclosure GroundPointCoordinates GroundBorderResponse
open scoped BigOperators

/-- Exact rational obligations for one full root box and all eight source
responses. `C` approximates the selector border inverse, not the nonlinear
residual derivative inverse. -/
structure Arithmetic (B : Fin 8 → Interval) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) (q : ℚ) (y e : Fin 8 → ℚ) : Prop where
  rate_nonneg : 0 ≤ q
  rate_lt : q < 1
  rhs_nonneg : ∀ j, 0 ≤ y j
  error_nonneg : ∀ j, 0 ≤ e j
  budget : ∀ j, q*y j ≤ e j*(1-q)
  defect_rows : ∀ i, (∑ j, ((borderDefectExpr C i j).enclose (GroundUncertainBackgroundTube.box B a a z r)).bound) ≤ q
  rhs_rows : ∀ j i, ((correctedRhsExpr C j i).enclose (GroundUncertainBackgroundTube.box B a a z r)).bound ≤ y j

theorem arithmetic_response_error {B : Fin 8 → Interval} {a : ℚ} {z : Fin 9 → ℚ} {r q : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} {y e : Fin 8 → ℚ}
    (h : Arithmetic B a z r C q y e) {b : Field}
    (hb : ∀ i, (B i).Contains (b i)) {x : Point}
    (hx : x ∈ Metric.closedBall (GroundKernelTube.center z) (r : ℝ))
    (hg : groundPair (sourcePotential b a x.1) = x) (j : Fin 8) :
    ‖response b a x j - preconditioner C (rhs b a x j)‖ ≤ (e j : ℝ) :=
  response_error C (GroundUncertainBackgroundTube.box B a a z r) b a x j
    h.rate_nonneg h.rate_lt (h.rhs_nonneg j) (h.budget j) hg
    (GroundUncertainBackgroundTube.box_sound B a a z r hb ⟨le_rfl, le_rfl⟩ hx) h.defect_rows (h.rhs_rows j)

def halfInterval (B : Fin 8 → Interval) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) (e : Fin 8 → ℚ) (i j : Fin 8) : Interval :=
  ((halfNominalExpr C i j).enclose (GroundUncertainBackgroundTube.box B a a z r)).add ⟨-(e j)/2, (e j)/2⟩

theorem halfInterval_sound {B : Fin 8 → Interval} {a : ℚ} {z : Fin 9 → ℚ} {r q : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} {y e : Fin 8 → ℚ}
    (h : Arithmetic B a z r C q y e) {b : Field}
    (hb : ∀ i, (B i).Contains (b i)) {x : Point}
    (hx : x ∈ Metric.closedBall (GroundKernelTube.center z) (r : ℝ))
    (hg : groundPair (sourcePotential b a x.1) = x)
    (hf : groundMap b a x.1 = x.1) (i j : Fin 8) :
    (halfInterval B a z r C e i j).Contains
      (GroundNormalizedJacobian.normalizedJacobian b a (1/2) x.1 (GroundLocalDynamics.column j) i) := by
  let v := valuation b (a : ℝ) x
  have hbox := GroundUncertainBackgroundTube.box_sound B a a z r hb (κ := (a : ℝ)) ⟨le_rfl, le_rfl⟩ hx
  have hn := (halfNominalExpr C i j).enclose_sound hbox
  have he := arithmetic_response_error h hb hx hg j
  have hc := (coord_norm_le (response b a x j - preconditioner C (rhs b a x j)) i.castSucc).trans he
  rw [coord_sub] at hc
  have hcf : coord (response b a x j) i.castSucc =
      jacobian b a x.1 (GroundLocalDynamics.column j) i := by
    simp only [coord, Fin.lastCases_castSucc, response_field]
  rw [hcf] at hc
  have hd : dot x.1 (GroundLocalDynamics.column j) = x.1 j := by
    simp [dot, GroundLocalDynamics.column, Pi.single_apply]
  have ha := GroundRootCertificate.half_mixing_jacobian_apply hf (GroundLocalDynamics.column j) i
  rw [hd] at ha
  have hnom := halfNominalExpr_return C b a x i j
  have hdiff : |GroundNormalizedJacobian.normalizedJacobian b a (1/2) x.1
      (GroundLocalDynamics.column j) i - (halfNominalExpr C i j).eval v| ≤ (e j : ℝ)/2 := by
    rw [ha]
    change |((GroundLocalDynamics.column j i - x.1 j * x.1 i + jacobian b a x.1
      (GroundLocalDynamics.column j) i)/2) - (halfNominalExpr C i j).eval (valuation b a x)| ≤ _
    rw [hnom]
    have hcol : GroundLocalDynamics.column j i = if i = j then 1 else 0 := by
      simp [GroundLocalDynamics.column, Pi.single_apply]
    rw [hcol]
    have hid : ((if i = j then 1 else 0) - x.1 j * x.1 i + jacobian b a x.1
        (GroundLocalDynamics.column j) i)/2 -
        ((if i = j then 1 else 0) - x.1 i * x.1 j + coord (preconditioner C (rhs b a x j)) i.castSucc)/2 =
      (jacobian b a x.1 (GroundLocalDynamics.column j) i -
        coord (preconditioner C (rhs b a x j)) i.castSucc)/2 := by ring
    rw [hid, abs_div]
    rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact div_le_div_of_nonneg_right hc (by norm_num)
  have hdelta : (⟨-(e j)/2, (e j)/2⟩ : Interval).Contains
      (GroundNormalizedJacobian.normalizedJacobian b a (1/2) x.1 (GroundLocalDynamics.column j) i -
        (halfNominalExpr C i j).eval v) := by
    have hb := abs_le.mp hdiff
    simpa only [Interval.Contains, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using hb
  have hs := Interval.add_sound hn hdelta
  simpa only [halfInterval, v, add_sub_cancel] using hs

def imaginaryIntervals (B : Fin 8 → Interval) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    (i j : Fin 8) : Interval :=
  (GroundMatrixCoordinates.imaginaryExpr i j).enclose
    (GroundUncertainBackgroundTube.box B a a z r)

theorem imaginaryIntervals_sound (B : Fin 8 → Interval) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    {b : Field} (hb : ∀ i, (B i).Contains (b i)) {x : Point}
    (hx : x ∈ Metric.closedBall (GroundKernelTube.center z) (r : ℝ)) (i j : Fin 8) :
    (imaginaryIntervals B a z r i j).Contains
      (GroundMatrixCoordinates.entries (GroundNativeJacobian.imaginaryDerivative (1/2) x.1) i j) := by
  rw [← GroundMatrixCoordinates.imaginaryExpr_return b (a : ℝ) x i j]
  exact Expr.enclose_sound _ (GroundUncertainBackgroundTube.box_sound B a a z r hb ⟨le_rfl, le_rfl⟩ hx)

def Included (A D : Matrix (Fin 8) (Fin 8) Interval) : Prop :=
  ∀ i j, (D i j).lo ≤ (A i j).lo ∧ (A i j).hi ≤ (D i j).hi

theorem included_sound {A D : Matrix (Fin 8) (Fin 8) Interval}
    (h : Included A D) {i j : Fin 8} {x : ℝ} (hx : (A i j).Contains x) :
    (D i j).Contains x :=
  ⟨(Rat.cast_le.mpr (h i j).1).trans hx.1, hx.2.trans (Rat.cast_le.mpr (h i j).2)⟩

end
end SbtCosmo.Derivation.GroundUncertainBorderResponse
