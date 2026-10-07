import SbtCosmo.Derivation.GroundKernelTube
import SbtCosmo.Derivation.GroundNativeLocal

/-! Polynomial border/response enclosures returned to the actual sourced
selector derivative. A near-inverse defect controls actual response error;
no derivative inverse or interval matrix is supplied as a proof oracle. -/
namespace SbtCosmo.Derivation.GroundBorderResponse
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSmooth GroundSourceJacobian
open GroundRationalInterval GroundPointCoordinates GroundResidualEnclosure
open GroundKernelTube
open scoped BigOperators

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_response_error_mul (L C : E →L[ℝ] E) {y r : E} {q : ℝ}
    (hy : L y = r) (hq : 0 ≤ q)
    (hdefect : ‖ContinuousLinearMap.id ℝ E - C.comp L‖ ≤ q) :
    (1-q)*‖y-C r‖ ≤ q*‖C r‖ := by
  have hd : ‖y-C r‖ ≤ q*‖y‖ := by
    have hb := ((ContinuousLinearMap.id ℝ E - C.comp L).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hdefect (norm_nonneg y))
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, hy] using hb
  have ht : ‖y‖ ≤ ‖y-C r‖ + ‖C r‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y-C r) (C r)
  have hb := mul_le_mul_of_nonneg_left ht hq
  nlinarith

theorem linear_response_error (L C : E →L[ℝ] E) {y r : E} {q : ℝ}
    (hy : L y = r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hdefect : ‖ContinuousLinearMap.id ℝ E - C.comp L‖ ≤ q) :
    ‖y-C r‖ ≤ q/(1-q)*‖C r‖ := by
  have hb := linear_response_error_mul L C hy hq hdefect
  have hd : 0 < 1-q := sub_pos.mpr hq1
  have he : ‖y-C r‖ ≤ (q*‖C r‖)/(1-q) := (le_div_iff₀ hd).mpr (by nlinarith [hb])
  simpa only [div_mul_eq_mul_div] using he

end Linear

def borderOperator (b : Field) (κ : ℝ) (x : Point) : Point →L[ℝ] Point :=
  border (sourcePotential b κ x.1) x.1 x.2

def borderExpr (j : Fin 9) : Fin 9 → Expression := Fin.lastCases
  (Expr.sum (fun i : Fin 8 => uExpr i * .const (basisField j i)))
  (fun i => (1 + sourceExpr i - energyExpr) * .const (basisField j i) -
    .const ((basisField j (prev i) + basisField j (next i))/2) -
    .const (basisEnergy j) * uExpr i)

def borderDefectExpr (C : Matrix (Fin 9) (Fin 9) ℚ) (i j : Fin 9) : Expression :=
  .const (if i = j then 1 else 0) - Expr.sum (fun a => .const (C i a) * borderExpr j a)

def rhs (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) : Point :=
  (fun i => -(sourceDerivative b κ x.1 (GroundLocalDynamics.column j) i)*x.1 i, 0)

def rhsExpr (j : Fin 8) : Fin 9 → Expression := Fin.lastCases 0
  (fun i => -(sourceColumnExpr i j.castSucc) * uExpr i)

def correctedRhsExpr (C : Matrix (Fin 9) (Fin 9) ℚ) (j : Fin 8) (i : Fin 9) : Expression :=
  Expr.sum (fun a => .const (C i a) * rhsExpr j a)

def response (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) : Point :=
  pairDerivative (sourcePotential b κ x.1)
    (sourceDerivative b κ x.1 (GroundLocalDynamics.column j))

theorem borderExpr_return (b : Field) (κ : ℝ) (x : Point) (j i : Fin 9) :
    (borderExpr j i).eval (valuation b κ x) = coord (borderOperator b κ x (column j)) i := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [borderExpr, coord, Fin.lastCases_last]
    simp [Expr.eval_sum, Expr.eval, eval_uExpr, basisField_return,
      borderOperator, border_apply, dot]
  · simp only [borderExpr, coord, Fin.lastCases_castSucc]
    simp [Expr.eval, eval_uExpr, eval_sourceExpr, eval_energyExpr,
      basisField_return, basisEnergy_return, borderOperator, border_apply, shifted, hamiltonian]
    ring

theorem field_column_return (j : Fin 8) : (column j.castSucc).1 = GroundLocalDynamics.column j := by
  funext i
  simp [column, fromCoord, GroundLocalDynamics.column, Pi.single_apply]

theorem rhsExpr_return (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) (i : Fin 9) :
    (rhsExpr j i).eval (valuation b κ x) = coord (rhs b κ x j) i := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [rhsExpr, coord, Fin.lastCases_last, Expr.eval, rhs]
    norm_num
  · simp only [rhsExpr, coord, Fin.lastCases_castSucc]
    simp [Expr.eval, sourceColumnExpr, valuation, eval_uExpr, eval_gradExpr,
      basisField_return, field_column_return, rhs, sourceDerivative_apply, GroundState.gradient]

theorem correctedRhsExpr_return (C : Matrix (Fin 9) (Fin 9) ℚ)
    (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) (i : Fin 9) :
    (correctedRhsExpr C j i).eval (valuation b κ x) = coord (preconditioner C (rhs b κ x j)) i := by
  simp [correctedRhsExpr, Expr.eval_sum, Expr.eval, rhsExpr_return, preconditioner, matrixMap_apply]

theorem borderDefectExpr_return (C : Matrix (Fin 9) (Fin 9) ℚ)
    (b : Field) (κ : ℝ) (x : Point) (i j : Fin 9) :
    (borderDefectExpr C i j).eval (valuation b κ x) =
      coord ((ContinuousLinearMap.id ℝ Point - (preconditioner C).comp (borderOperator b κ x)) (column j)) i := by
  change _ = coord (column j - preconditioner C (borderOperator b κ x (column j))) i
  rw [coord_sub, coord_column]
  simp only [preconditioner, matrixMap_apply]
  by_cases hij : i = j <;>
    simp [borderDefectExpr, Expr.eval_sum, Expr.eval, borderExpr_return, hij, sub_eq_add_neg]

theorem response_equation (b : Field) (κ : ℝ) (x : Point) (j : Fin 8)
    (hg : groundPair (sourcePotential b κ x.1) = x) :
    borderOperator b κ x (response b κ x j) = rhs b κ x j := by
  have hu : positiveGround (sourcePotential b κ x.1) = x.1 := congrArg Prod.fst hg
  have he := pairDerivative_equation (sourcePotential b κ x.1)
    (sourceDerivative b κ x.1 (GroundLocalDynamics.column j))
  rw [hg, hu] at he
  simpa only [borderOperator, response, rhs] using he

theorem response_field (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) :
    (response b κ x j).1 = jacobian b κ x.1 (GroundLocalDynamics.column j) := rfl

theorem border_defect_norm (C : Matrix (Fin 9) (Fin 9) ℚ) (B : Variable → Interval)
    (b : Field) (κ : ℝ) (x : Point) {q : ℚ} (hq : 0 ≤ q)
    (hB : ∀ v, (B v).Contains (valuation b κ x v))
    (hrows : ∀ i, (∑ j, ((borderDefectExpr C i j).enclose B).bound) ≤ q) :
    ‖ContinuousLinearMap.id ℝ Point - (preconditioner C).comp (borderOperator b κ x)‖ ≤ (q : ℝ) := by
  apply operator_norm_le_rows _ (by exact_mod_cast hq)
  intro i
  calc
    (∑ j, |coord ((ContinuousLinearMap.id ℝ Point - (preconditioner C).comp (borderOperator b κ x)) (column j)) i|) ≤
        ∑ j, (((borderDefectExpr C i j).enclose B).bound : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← borderDefectExpr_return]
      exact Interval.abs_le_bound ((borderDefectExpr C i j).enclose_sound hB)
    _ ≤ q := by exact_mod_cast hrows i

theorem corrected_rhs_norm (C : Matrix (Fin 9) (Fin 9) ℚ) (B : Variable → Interval)
    (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) {y : ℚ} (hy : 0 ≤ y)
    (hB : ∀ v, (B v).Contains (valuation b κ x v))
    (hrows : ∀ i, ((correctedRhsExpr C j i).enclose B).bound ≤ y) :
    ‖preconditioner C (rhs b κ x j)‖ ≤ (y : ℝ) := by
  apply norm_le_coordinates (by exact_mod_cast hy)
  intro i
  rw [← correctedRhsExpr_return]
  exact (Interval.abs_le_bound ((correctedRhsExpr C j i).enclose_sound hB)).trans
    (by exact_mod_cast hrows i)

theorem response_error (C : Matrix (Fin 9) (Fin 9) ℚ) (B : Variable → Interval)
    (b : Field) (κ : ℝ) (x : Point) (j : Fin 8) {q y e : ℚ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hy : 0 ≤ y) (hbudget : q*y ≤ e*(1-q))
    (hg : groundPair (sourcePotential b κ x.1) = x)
    (hB : ∀ v, (B v).Contains (valuation b κ x v))
    (hdefect : ∀ i, (∑ k, ((borderDefectExpr C i k).enclose B).bound) ≤ q)
    (hrows : ∀ i, ((correctedRhsExpr C j i).enclose B).bound ≤ y) :
    ‖response b κ x j - preconditioner C (rhs b κ x j)‖ ≤ (e : ℝ) := by
  have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hb := linear_response_error_mul (borderOperator b κ x) (preconditioner C)
    (response_equation b κ x j hg) hq' (border_defect_norm C B b κ x hq hB hdefect)
  have hr := corrected_rhs_norm C B b κ x j hy hB hrows
  have hbudget' : (q : ℝ)*(y : ℝ) ≤ (e : ℝ)*(1-(q : ℝ)) := by exact_mod_cast hbudget
  have hn := mul_le_mul_of_nonneg_left hr hq'
  nlinarith

/-- Exact rational obligations for one full root box and all eight source
responses. `C` approximates the selector border inverse, not the nonlinear
residual derivative inverse. -/
structure Arithmetic (β : Fin 8 → ℚ) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) (q : ℚ) (y e : Fin 8 → ℚ) : Prop where
  rate_nonneg : 0 ≤ q
  rate_lt : q < 1
  rhs_nonneg : ∀ j, 0 ≤ y j
  error_nonneg : ∀ j, 0 ≤ e j
  budget : ∀ j, q*y j ≤ e j*(1-q)
  defect_rows : ∀ i, (∑ j, ((borderDefectExpr C i j).enclose (box β a a z r)).bound) ≤ q
  rhs_rows : ∀ j i, ((correctedRhsExpr C j i).enclose (box β a a z r)).bound ≤ y j

theorem arithmetic_response_error {β : Fin 8 → ℚ} {a : ℚ} {z : Fin 9 → ℚ} {r q : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} {y e : Fin 8 → ℚ}
    (h : Arithmetic β a z r C q y e) {x : Point}
    (hx : x ∈ Metric.closedBall (center z) (r : ℝ))
    (hg : groundPair (sourcePotential (background β) a x.1) = x) (j : Fin 8) :
    ‖response (background β) a x j - preconditioner C (rhs (background β) a x j)‖ ≤ (e j : ℝ) :=
  response_error C (box β a a z r) (background β) a x j
    h.rate_nonneg h.rate_lt (h.rhs_nonneg j) (h.budget j) hg
    (box_sound β a a z r ⟨le_rfl, le_rfl⟩ hx) h.defect_rows (h.rhs_rows j)

def halfNominalExpr (C : Matrix (Fin 9) (Fin 9) ℚ) (i j : Fin 8) : Expression :=
  (.const (if i = j then 1 else 0) - uExpr i * uExpr j + correctedRhsExpr C j i.castSucc) * .const (1/2)

def halfInterval (β : Fin 8 → ℚ) (a : ℚ) (z : Fin 9 → ℚ) (r : ℚ)
    (C : Matrix (Fin 9) (Fin 9) ℚ) (e : Fin 8 → ℚ) (i j : Fin 8) : Interval :=
  ((halfNominalExpr C i j).enclose (box β a a z r)).add ⟨-(e j)/2, (e j)/2⟩

theorem halfNominalExpr_return (C : Matrix (Fin 9) (Fin 9) ℚ)
    (b : Field) (κ : ℝ) (x : Point) (i j : Fin 8) :
    (halfNominalExpr C i j).eval (valuation b κ x) =
      ((if i = j then 1 else 0) - x.1 i * x.1 j + coord (preconditioner C (rhs b κ x j)) i.castSucc)/2 := by
  by_cases hij : i = j <;>
    simp [halfNominalExpr, Expr.eval, eval_uExpr, correctedRhsExpr_return, hij]
  all_goals ring

theorem halfInterval_sound {β : Fin 8 → ℚ} {a : ℚ} {z : Fin 9 → ℚ} {r q : ℚ}
    {C : Matrix (Fin 9) (Fin 9) ℚ} {y e : Fin 8 → ℚ}
    (h : Arithmetic β a z r C q y e) {x : Point}
    (hx : x ∈ Metric.closedBall (center z) (r : ℝ))
    (hg : groundPair (sourcePotential (background β) a x.1) = x)
    (hf : groundMap (background β) a x.1 = x.1) (i j : Fin 8) :
    (halfInterval β a z r C e i j).Contains
      (GroundNormalizedJacobian.normalizedJacobian (background β) a (1/2) x.1 (GroundLocalDynamics.column j) i) := by
  let v := valuation (background β) (a : ℝ) x
  have hbox := box_sound β a a z r (κ := (a : ℝ)) ⟨le_rfl, le_rfl⟩ hx
  have hn := (halfNominalExpr C i j).enclose_sound hbox
  have he := arithmetic_response_error h hx hg j
  have hc := (coord_norm_le (response (background β) a x j - preconditioner C (rhs (background β) a x j)) i.castSucc).trans he
  rw [coord_sub] at hc
  have hcf : coord (response (background β) a x j) i.castSucc =
      jacobian (background β) a x.1 (GroundLocalDynamics.column j) i := by
    simp only [coord, Fin.lastCases_castSucc, response_field]
  rw [hcf] at hc
  have hd : dot x.1 (GroundLocalDynamics.column j) = x.1 j := by
    simp [dot, GroundLocalDynamics.column, Pi.single_apply]
  have ha := GroundRootCertificate.half_mixing_jacobian_apply hf (GroundLocalDynamics.column j) i
  rw [hd] at ha
  have hnom := halfNominalExpr_return C (background β) a x i j
  have hdiff : |GroundNormalizedJacobian.normalizedJacobian (background β) a (1/2) x.1
      (GroundLocalDynamics.column j) i - (halfNominalExpr C i j).eval v| ≤ (e j : ℝ)/2 := by
    rw [ha]
    change |((GroundLocalDynamics.column j i - x.1 j * x.1 i + jacobian (background β) a x.1
      (GroundLocalDynamics.column j) i)/2) - (halfNominalExpr C i j).eval (valuation (background β) a x)| ≤ _
    rw [hnom]
    have hcol : GroundLocalDynamics.column j i = if i = j then 1 else 0 := by
      simp [GroundLocalDynamics.column, Pi.single_apply]
    rw [hcol]
    have hid : ((if i = j then 1 else 0) - x.1 j * x.1 i + jacobian (background β) a x.1
        (GroundLocalDynamics.column j) i)/2 -
        ((if i = j then 1 else 0) - x.1 i * x.1 j + coord (preconditioner C (rhs (background β) a x j)) i.castSucc)/2 =
      (jacobian (background β) a x.1 (GroundLocalDynamics.column j) i -
        coord (preconditioner C (rhs (background β) a x j)) i.castSucc)/2 := by ring
    rw [hid, abs_div]
    rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact div_le_div_of_nonneg_right hc (by norm_num)
  have hdelta : (⟨-(e j)/2, (e j)/2⟩ : Interval).Contains
      (GroundNormalizedJacobian.normalizedJacobian (background β) a (1/2) x.1 (GroundLocalDynamics.column j) i -
        (halfNominalExpr C i j).eval v) := by
    have hb := abs_le.mp hdiff
    simpa only [Interval.Contains, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using hb
  have hs := Interval.add_sound hn hdelta
  simpa only [halfInterval, v, add_sub_cancel] using hs

end
end SbtCosmo.Derivation.GroundBorderResponse
