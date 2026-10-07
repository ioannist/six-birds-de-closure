import SbtCosmo.Derivation.MatrixSensitivityStationarity
import SbtCosmo.Derivation.GeneralMatrixExamples
import SbtCosmo.Derivation.ExtendedMatrixClosurePriceExamples

/-! Actual extended Schur sensitivity/stationarity, whole-price uniqueness and
controls distinguishing whole matrix derivatives from partial readouts. -/
namespace SbtCosmo.Derivation.MatrixSensitivityExamples
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice GeneralMatrixPrice MatrixPriceSensitivity
open ExtendedClosurePrice ConvexSubgradient SchurDifferential
open MatrixClosurePriceExamples (budget coordinate energy)
open GeneralMatrixExamples (matrixScalar)
open scoped Matrix Topology Matrix.Norms.Elementwise

theorem actual_optimizer : ExtendedConeClosurePrice.PrimalOptimum univ
    ExtendedClosurePriceExamples.objective energy positive (budget 1) 1 := by
  have hp : PrimalOptimum univ ExtendedClosurePriceExamples.objective SchurClosurePriceExamples.energy 1 1 := by
    simpa using ExtendedClosurePriceExamples.sqrt_primal_optimum
      (by norm_num : (0 : ℝ)<1) (by norm_num : (1 : ℝ)<4)
  refine ⟨hp.member,hp.finite,(MatrixClosurePriceExamples.feasible_iff _ _).mpr hp.feasible,?_⟩
  intro x hx he
  exact hp.optimal x hx ((MatrixClosurePriceExamples.feasible_iff _ _).mp he)

theorem actual_slater : ((budget 1 : Matrix (Fin 1) (Fin 1) ℝ)-(energy 0 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  rw [MatrixClosurePriceExamples.energy_eq]
  have he : ((budget 1 : Matrix (Fin 1) (Fin 1) ℝ)-(budget (0^2) : Matrix (Fin 1) (Fin 1) ℝ))=1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
  rw [he]
  exact Matrix.PosDef.one

theorem actual_schur_derivative : HasFDerivAt (fun x => (energy x : Matrix (Fin 1) (Fin 1) ℝ))
    ((2 : ℝ) • matrixScalar) 1 := by
  have he : (fun x => (energy x : Matrix (Fin 1) (Fin 1) ℝ))=(fun x => matrixScalar (x^2)) := by
    funext x
    rw [MatrixClosurePriceExamples.energy_eq]
    rfl
  rw [he]
  have hh := matrixScalar.hasFDerivAt.comp (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).pow 2).hasFDerivAt
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  ext i j
  fin_cases i
  fin_cases j
  simp [matrixScalar]
  ring

theorem tracePrice_one : tracePrice (1 : Matrix (Fin 1) (Fin 1) ℝ)=coordinate := by
  apply ContinuousLinearMap.ext
  intro H
  simp [tracePrice_apply,coordinate,Matrix.trace]
  rfl

/-- No local value guard is supplied: the actual finite PD Slater point earns it. -/
theorem actual_price_identified {P : Matrix (Fin 1) (Fin 1) ℝ} {star : ℝ}
    (hP : P.PosSemidef)
    (hc : ExtendedConeClosurePrice.DualCertificate univ ExtendedClosurePriceExamples.objective
      energy positive (budget 1) (tracePrice P) star) : P=1 := by
  have hXi : LoewnerConvexOn univ energy := fun x _ y _ a b ha hb hab =>
    affine_residual_loewner_convex (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe x y ha hb hab
  have heq := slater_price_identification (fun x _ => ExtendedClosurePriceExamples.objective_no_bottom x)
    ExtendedClosurePriceExamples.objective_epigraph_convex hXi hc (mem_univ 0)
    (by norm_num [ExtendedClosurePriceExamples.objective]) actual_slater
    ExtendedMatrixClosurePriceExamples.actual_value_derivative
  have heq' : tracePrice P=coordinate := by
    apply ContinuousLinearMap.ext
    intro H
    have hh := congrArg (fun p : Symmetric (Fin 1) →L[ℝ] ℝ => p H) heq
    simpa only [ContinuousLinearMap.neg_apply,neg_neg] using hh
  exact tracePrice_injective hP.1 Matrix.isHermitian_one (heq'.trans tracePrice_one.symm)

/-- All actual original Schur derivatives, optimizer, Slater and RI witnesses
are proved before the generic same-price endpoint. It returns canonical P=1. -/
theorem actual_same_price_stationarity : ∃ q η : ℝ →L[ℝ] ℝ,
    Subgradient ExtendedClosurePriceExamples.objective 1 q ∧ NormalCone univ 1 η ∧
      q+traceAdjoint ((2 : ℝ) • matrixScalar) (1 : Matrix (Fin 1) (Fin 1) ℝ)+η=0 ∧
      ExtendedConeClosurePrice.DualCertificate univ ExtendedClosurePriceExamples.objective energy positive
        (budget 1) (tracePrice (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1 ∧
      ExtendedConeClosurePrice.dualValue univ ExtendedClosurePriceExamples.objective energy (budget 1)
        (tracePrice (1 : Matrix (Fin 1) (Fin 1) ℝ))=1 := by
  have hXi : LoewnerConvexOn univ energy := fun x _ y _ a b ha hb hab =>
    affine_residual_loewner_convex (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe x y ha hb hab
  have hAr : (1 : ℝ) ∈ intrinsicInterior ℝ (univ : Set ℝ) := interior_subset_intrinsicInterior (by simp)
  have hstrict : ∃ H : Symmetric (Fin 1), positive H ∧ (-coordinate) H < 0 :=
    ⟨budget 1,(MatrixClosurePriceExamples.budget_positive_iff 1).mpr (by norm_num),
      by norm_num [MatrixClosurePriceExamples.coordinate_budget]⟩
  obtain ⟨P,q,η,hP,_,_,_,_,hq,hη,hs,_,hc,hdual,_⟩ := MatrixSensitivityStationarity.matrix_stationarity
    ExtendedClosurePriceExamples.objective_no_bottom ExtendedClosurePriceExamples.objective_epigraph_convex
    convex_univ ScalarStationarityExamples.extended_relative_interior hAr hXi actual_schur_derivative
    actual_optimizer (mem_univ 0) (by norm_num [ExtendedClosurePriceExamples.objective]) actual_slater
    ExtendedMatrixClosurePriceExamples.actual_value_derivative hstrict
  have heq := actual_price_identified hP hc
  rw [heq] at hs hc hdual
  refine ⟨q,η,hq,hη,hs,hc,?_⟩
  rw [hdual,ExtendedMatrixClosurePriceExamples.value_return,MatrixClosurePriceExamples.coordinate_budget]
  exact ExtendedClosurePriceExamples.actual_positive_certificate.2.2

/-- Symmetric budgets cannot see a nonzero antisymmetric price component. -/
theorem antisymmetric_price_control :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;-1,0]
    A ≠ 0 ∧ tracePrice A=0 := by
  dsimp
  constructor
  · intro hz
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hz
    norm_num at hh
  · apply ContinuousLinearMap.ext
    intro H
    have hsym : (H : Matrix (Fin 2) (Fin 2) ℝ) 1 0=(H : Matrix (Fin 2) (Fin 2) ℝ) 0 1 :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) H.property
    simp only [tracePrice_apply,ContinuousLinearMap.zero_apply,Matrix.trace,Matrix.diag_apply,
      Matrix.mul_apply,Fin.sum_univ_succ]
    norm_num
    linarith

/-- A single positive budget direction does not identify a PSD matrix price. -/
theorem one_direction_control :
    let P : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
    let Q : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,1]
    let H : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
    P.PosSemidef ∧ Q.PosSemidef ∧ H.PosSemidef ∧ P ≠ Q ∧ trace (P*H)=trace (Q*H) := by
  dsimp
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  · intro hz
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hz
    norm_num at hh
  · norm_num [Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ]

theorem kink_matrix_feasible (B : Symmetric (Fin 1)) (x : ℝ × ℝ) :
    positive (B-GeneralMatrixExamples.kinkMatrix x) ↔ ScalarStationarityExamples.kinkEnergy x ≤ coordinate B := by
  have he : B-GeneralMatrixExamples.kinkMatrix x=budget (coordinate B-ScalarStationarityExamples.kinkEnergy x) := by
    rw [← MatrixClosurePriceExamples.budget_coordinate B]
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [he,MatrixClosurePriceExamples.budget_positive_iff,sub_nonneg]

/-- Full symmetric-budget value of the genuinely nonsmooth matrix program. -/
theorem kink_actual_value (B : Symmetric (Fin 1)) :
    ExtendedConeClosurePrice.value univ ScalarStationarityExamples.kinkObjective
      GeneralMatrixExamples.kinkMatrix positive B=(-coordinate B : ℝ) := by
  have hp := ScalarStationarityExamples.kink_primal_optimum (coordinate B)
  have hs : ExtendedConeClosurePrice.PrimalOptimum univ ScalarStationarityExamples.kinkObjective
      GeneralMatrixExamples.kinkMatrix positive B (coordinate B,0) :=
    ⟨hp.member,hp.finite,(kink_matrix_feasible B _).mpr hp.feasible,
      fun x hx he => hp.optimal x hx ((kink_matrix_feasible B x).mp he)⟩
  exact ExtendedConeClosurePrice.optimum_value hs

theorem kink_value_derivative (B : Symmetric (Fin 1)) :
    HasFDerivAt (fun T => (ExtendedConeClosurePrice.value univ ScalarStationarityExamples.kinkObjective
      GeneralMatrixExamples.kinkMatrix positive T).toReal) (-coordinate) B := by
  have he : (fun T => (ExtendedConeClosurePrice.value univ ScalarStationarityExamples.kinkObjective
      GeneralMatrixExamples.kinkMatrix positive T).toReal)=(fun T => -coordinate T) := by
    funext T
    rw [kink_actual_value,EReal.toReal_coe]
  rw [he]
  simpa only [ContinuousLinearMap.neg_apply] using coordinate.hasFDerivAt.neg

/-- Actual full value sensitivity identifies P=1 in a program whose matrix map
has no derivative at the optimizer. Trace-energy support and stationarity remain
earned outputs. Final statement has zero premises. -/
theorem actual_nonsmooth_same_price_stationarity : ∃ q k η : (ℝ × ℝ) →L[ℝ] ℝ,
    Subgradient ScalarStationarityExamples.kinkObjective (0,0) q ∧
      RealSubgradient (fun x => trace ((1 : Matrix (Fin 1) (Fin 1) ℝ)*
        (GeneralMatrixExamples.kinkMatrix x : Matrix (Fin 1) (Fin 1) ℝ))) (0,0) k ∧
      NormalCone univ (0,0) η ∧ q+k+η=0 ∧
      ExtendedConeClosurePrice.DualCertificate univ ScalarStationarityExamples.kinkObjective
        GeneralMatrixExamples.kinkMatrix positive (budget 0) (tracePrice (1 : Matrix (Fin 1) (Fin 1) ℝ)) (0,0) ∧
      ExtendedConeClosurePrice.dualValue univ ScalarStationarityExamples.kinkObjective
        GeneralMatrixExamples.kinkMatrix (budget 0) (tracePrice (1 : Matrix (Fin 1) (Fin 1) ℝ))=0 := by
  have hXi : LoewnerConvexOn univ GeneralMatrixExamples.kinkMatrix := by
    intro x hx y hy a b ha hb hab
    rw [GeneralMatrixExamples.kinkMatrix,GeneralMatrixExamples.kinkMatrix,GeneralMatrixExamples.kinkMatrix,
      GeneralMatrixExamples.budget_combination,MatrixClosurePriceExamples.budget_positive_iff]
    exact sub_nonneg.mpr (ScalarStationarityExamples.kink_energy_convex.2 hx hy ha hb hab)
  have hp := ScalarStationarityExamples.kink_primal_optimum 0
  have hstar : ExtendedConeClosurePrice.PrimalOptimum univ ScalarStationarityExamples.kinkObjective
      GeneralMatrixExamples.kinkMatrix positive (budget 0) (0,0) :=
    ⟨hp.member,hp.finite,(kink_matrix_feasible _ _).mpr hp.feasible,
      fun x hx he => hp.optimal x hx ((kink_matrix_feasible _ x).mp he)⟩
  have hdom : finiteDomain univ ScalarStationarityExamples.kinkObjective=univ := by
    ext x
    simp [finiteDomain,ScalarStationarityExamples.kinkObjective]
  have hC : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (finiteDomain univ ScalarStationarityExamples.kinkObjective) := by
    rw [hdom]; exact interior_subset_intrinsicInterior (by simp)
  have hAr : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (univ : Set (ℝ × ℝ)) := interior_subset_intrinsicInterior (by simp)
  have hslater : ((budget 0 : Matrix (Fin 1) (Fin 1) ℝ)-
      (GeneralMatrixExamples.kinkMatrix (-1,0) : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
    have he : ((budget 0 : Matrix (Fin 1) (Fin 1) ℝ)-
        (GeneralMatrixExamples.kinkMatrix (-1,0) : Matrix (Fin 1) (Fin 1) ℝ))=1 := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [GeneralMatrixExamples.kinkMatrix,ScalarStationarityExamples.kinkEnergy,
        budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
    rw [he]
    exact Matrix.PosDef.one
  have hstrict : ∃ H : Symmetric (Fin 1), positive H ∧ (-coordinate) H < 0 :=
    ⟨budget 1,(MatrixClosurePriceExamples.budget_positive_iff 1).mpr (by norm_num),
      by norm_num [MatrixClosurePriceExamples.coordinate_budget]⟩
  have hbottom : ∀ x, ScalarStationarityExamples.kinkObjective x ≠ ⊥ := fun x => EReal.coe_ne_bot _
  obtain ⟨P,q,k,η,hP,_,hprice,_,_,hq,hk,hη,hs,_,hc,hdual⟩ := MatrixSensitivityStationarity.matrix_nonsmooth_stationarity
    hbottom ScalarStationarityExamples.kink_objective_convex convex_univ hC hAr hXi hstar
    (mem_univ (-1,0)) (EReal.coe_ne_top _) hslater (kink_value_derivative _) hstrict
  have heq : tracePrice P=coordinate := by
    apply ContinuousLinearMap.ext
    intro H
    have hh := congrArg (fun p : Symmetric (Fin 1) →L[ℝ] ℝ => p H) hprice
    simpa only [ContinuousLinearMap.neg_apply,neg_neg] using hh
  have hPone : P=1 := tracePrice_injective hP.1 Matrix.isHermitian_one (heq.trans tracePrice_one.symm)
  rw [hPone] at hk hc hdual
  refine ⟨q,k,η,hq,hk,hη,hs,hc,?_⟩
  rw [hdual,kink_actual_value,MatrixClosurePriceExamples.coordinate_budget]
  norm_num

end
end SbtCosmo.Derivation.MatrixSensitivityExamples
