import SbtCosmo.Derivation.GeneralMatrixStationarity
import SbtCosmo.Derivation.ScalarStationarityExamples
import SbtCosmo.Derivation.MatrixClosurePriceExamples
import Mathlib.Analysis.Convex.Mul

/-! Nonquadratic and genuinely nonsmooth matrix-map instances of the general
Slater stationarity theorem. Final constructions have zero premises. -/
namespace SbtCosmo.Derivation.GeneralMatrixExamples
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice GeneralMatrixPrice
open ExtendedClosurePrice ConvexSubgradient SchurDifferential
open MatrixClosurePriceExamples (budget budget_positive_iff)
open scoped Matrix Topology Matrix.Norms.Elementwise

theorem budget_combination (a b r s t : ℝ) :
    a • budget r+b • budget s-budget t=budget (a*r+b*s-t) := by
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  rfl

def quartic (x : ℝ) : Symmetric (Fin 1) := budget (x^4)
def matrixScalar : ℝ →L[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
  (show ℝ →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℝ from
    {toFun := fun r => fun _ _ => r
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl}).toContinuousLinearMap

/-- The nonquadratic example is an actual Schur residual with a nonlinear probe,
not merely an abstract symmetric matrix map. -/
theorem quartic_actual_schur (x : ℝ) :
    quartic x=MatrixClosurePrice.residual (0 : Matrix (Fin 1) (Fin 1) ℝ) (matrixScalar (x^2)) := by
  apply Subtype.ext
  change (budget (x^4) : Matrix (Fin 1) (Fin 1) ℝ)=
    SbtCosmo.Adequacy.Support.residual (0 : Matrix (Fin 1) (Fin 1) ℝ) (matrixScalar (x^2))
  rw [SbtCosmo.Adequacy.Support.residual_zero_native]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [budget,matrixScalar,SbtCosmo.Adequacy.Reconciliation.oneByOne,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ]
  ring

theorem quartic_loewner_convex : LoewnerConvexOn univ quartic := by
  intro x hx y hy a b ha hb hab
  rw [quartic,quartic,quartic,budget_combination,budget_positive_iff]
  exact sub_nonneg.mpr ((show Even (4 : ℕ) from ⟨2,rfl⟩).convexOn_pow.2 hx hy ha hb hab)

theorem quartic_derivative (x : ℝ) :
    HasFDerivAt (fun z => (quartic z : Matrix (Fin 1) (Fin 1) ℝ))
      ((4*x^3) • matrixScalar) x := by
  have hd := (hasDerivAt_id x).pow 4
  have hh := matrixScalar.hasFDerivAt.comp x hd.hasFDerivAt
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  ext i j
  fin_cases i
  fin_cases j
  simp [matrixScalar]
  ring

theorem quartic_primal_one :
    ExtendedConeClosurePrice.PrimalOptimum univ ExtendedClosurePriceExamples.objective
      quartic positive (budget 1) 1 := by
  refine ⟨mem_univ _,by norm_num [ExtendedClosurePriceExamples.objective],?_,?_⟩
  · change positive (budget 1-budget (1^4))
    have he : budget 1-budget (1^4)=0 := by
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      norm_num [budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
    rw [he]
    exact Matrix.PosSemidef.zero
  · intro x _ hx
    by_cases hxp : 0 ≤ x
    · have he : budget 1-quartic x=budget (1-x^4) := by simpa [quartic] using budget_combination 1 0 1 0 (x^4)
      rw [he,budget_positive_iff] at hx
      have hfour : (x^2)^2 ≤ 1 := by nlinarith only [hx]
      have hs : x^2 ≤ 1 := by nlinarith [sq_nonneg (x^2-1)]
      have hu : x ≤ 1 := by nlinarith [sq_nonneg (x-1)]
      simp only [ExtendedClosurePriceExamples.objective,if_pos hxp,
        if_pos (by norm_num : (0 : ℝ) ≤ 1),EReal.coe_le_coe_iff,SchurClosurePriceExamples.objective]
      nlinarith [sq_nonneg (x-1)]
    · simp [ExtendedClosurePriceExamples.objective,hxp]

theorem quartic_primal_sixteen :
    ExtendedConeClosurePrice.PrimalOptimum univ ExtendedClosurePriceExamples.objective
      quartic positive (budget 16) 2 := by
  refine ⟨mem_univ _,by norm_num [ExtendedClosurePriceExamples.objective],?_,?_⟩
  · change positive (budget 16-budget (2^4))
    have he : budget 16-budget (2^4)=0 := by
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      norm_num [budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
    rw [he]
    exact Matrix.PosSemidef.zero
  · intro x _ _
    by_cases hxp : 0 ≤ x
    · simp only [ExtendedClosurePriceExamples.objective,if_pos hxp,
        if_pos (by norm_num : (0 : ℝ) ≤ 2),EReal.coe_le_coe_iff,SchurClosurePriceExamples.objective]
      nlinarith [sq_nonneg (x-2)]
    · simp [ExtendedClosurePriceExamples.objective,hxp]

theorem quartic_actual_values :
    ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective quartic positive (budget 1)=1 ∧
    ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective quartic positive (budget 16)=0 := by
  rw [ExtendedConeClosurePrice.optimum_value quartic_primal_one,
    ExtendedConeClosurePrice.optimum_value quartic_primal_sixteen]
  norm_num [ExtendedClosurePriceExamples.objective,SchurClosurePriceExamples.objective]

theorem quartic_slater : ((budget 1 : Matrix (Fin 1) (Fin 1) ℝ)-(quartic 0 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  have he : ((budget 1 : Matrix (Fin 1) (Fin 1) ℝ)-(quartic 0 : Matrix (Fin 1) (Fin 1) ℝ))=1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [quartic,budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
  rw [he]
  exact Matrix.PosDef.one

theorem quartic_sensitive : ∃ H : Symmetric (Fin 1), positive H ∧
    ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective quartic positive (budget 1+H) <
      ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective quartic positive (budget 1) := by
  refine ⟨budget 15,(budget_positive_iff 15).mpr (by norm_num),?_⟩
  have he : budget 1+budget 15=budget 16 := by
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    norm_num [budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
  rw [he,quartic_actual_values.1,quartic_actual_values.2]
  norm_num

/-- The example's actual matrix entry cannot be replaced by a quadratic scalar
polynomial. This checks that the general construction sees a broader class. -/
theorem quartic_not_quadratic : ¬ ∃ a b c : ℝ,
    ∀ x : ℝ, (quartic x : Matrix (Fin 1) (Fin 1) ℝ) 0 0=a*x^2+b*x+c := by
  rintro ⟨a,b,c,h⟩
  have h0 := h 0
  have h1 := h 1
  have hn := h (-1)
  have h2 := h 2
  norm_num [quartic,budget,SbtCosmo.Adequacy.Reconciliation.oneByOne] at h0 h1 hn h2
  linarith

/-- All general-map, derivative, optimizer, Slater, RI and strict-value inputs
are independently proved; no final price/stationarity field is supplied. -/
theorem constructed_quartic_stationarity :
    ∃ (P : Matrix (Fin 1) (Fin 1) ℝ) (q η : ℝ →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      Subgradient ExtendedClosurePriceExamples.objective 1 q ∧ NormalCone univ 1 η ∧
      q+traceAdjoint ((4 : ℝ) • matrixScalar) P+η=0 ∧
      ExtendedConeClosurePrice.DualCertificate univ ExtendedClosurePriceExamples.objective
        quartic positive (budget 1) (tracePrice P) 1 ∧
      ExtendedConeClosurePrice.dualValue univ ExtendedClosurePriceExamples.objective
        quartic (budget 1) (tracePrice P)=1 := by
  have hAr : (1 : ℝ) ∈ intrinsicInterior ℝ (univ : Set ℝ) := interior_subset_intrinsicInterior (by simp)
  have hd : HasFDerivAt (fun x => (quartic x : Matrix (Fin 1) (Fin 1) ℝ)) ((4 : ℝ) • matrixScalar) 1 := by
    simpa using quartic_derivative 1
  obtain ⟨P,q,η,hP,hne,hq,hη,hs,_,hc,hdual,_⟩ := GeneralMatrixStationarity.matrix_stationarity_nonzero
    ExtendedClosurePriceExamples.objective_no_bottom ExtendedClosurePriceExamples.objective_epigraph_convex
    convex_univ ScalarStationarityExamples.extended_relative_interior hAr quartic_loewner_convex hd
    quartic_primal_one (mem_univ 0) (by norm_num [ExtendedClosurePriceExamples.objective]) quartic_slater quartic_sensitive
  exact ⟨P,q,η,hP,hne,hq,hη,hs,hc,hdual.trans quartic_actual_values.1⟩

def kinkMatrix (x : ℝ × ℝ) : Symmetric (Fin 1) := budget (ScalarStationarityExamples.kinkEnergy x)

/-- The actual matrix map itself is not differentiable at the optimum. -/
theorem kink_matrix_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x => (kinkMatrix x : Matrix (Fin 1) (Fin 1) ℝ)) (0,0) := by
  intro h
  have hh := (MatrixDifferential.entry (0 : Fin 1) (0 : Fin 1)).differentiableAt.comp (0,0) h
  exact ScalarStationarityExamples.kink_energy_not_differentiable hh

/-- The full nonsmooth matrix theorem still returns real trace-energy support
and qualified stationarity. It assumes no fictitious matrix derivative. -/
theorem constructed_kink_matrix_stationarity :
    ∃ (P : Matrix (Fin 1) (Fin 1) ℝ) (q k η : (ℝ × ℝ) →L[ℝ] ℝ), P.PosSemidef ∧
      Subgradient ScalarStationarityExamples.kinkObjective (0,0) q ∧
      RealSubgradient (fun x => trace (P*(kinkMatrix x : Matrix (Fin 1) (Fin 1) ℝ))) (0,0) k ∧
      NormalCone univ (0,0) η ∧ q+k+η=0 ∧
      ExtendedConeClosurePrice.DualCertificate univ ScalarStationarityExamples.kinkObjective
        kinkMatrix positive (budget 0) (tracePrice P) (0,0) := by
  have hXi : LoewnerConvexOn univ kinkMatrix := by
    intro x hx y hy a b ha hb hab
    rw [kinkMatrix,kinkMatrix,kinkMatrix,budget_combination,budget_positive_iff]
    exact sub_nonneg.mpr (ScalarStationarityExamples.kink_energy_convex.2 hx hy ha hb hab)
  have hstar : ExtendedConeClosurePrice.PrimalOptimum univ ScalarStationarityExamples.kinkObjective
      kinkMatrix positive (budget 0) (0,0) := by
    have hp := ScalarStationarityExamples.kink_primal_optimum 0
    refine ⟨hp.member,hp.finite,?_,?_⟩
    · simp only [kinkMatrix,ScalarStationarityExamples.kinkEnergy,zero_add,abs_zero,sub_self]
      exact Matrix.PosSemidef.zero
    · intro x hx he
      have hg : budget 0-kinkMatrix x=budget (-ScalarStationarityExamples.kinkEnergy x) := by
        simpa [kinkMatrix] using budget_combination 1 0 0 0 (ScalarStationarityExamples.kinkEnergy x)
      rw [hg,budget_positive_iff] at he
      exact hp.optimal x hx (by linarith)
  have hdom : finiteDomain univ ScalarStationarityExamples.kinkObjective=univ := by
    ext x
    simp [finiteDomain,ScalarStationarityExamples.kinkObjective]
  have hC : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (finiteDomain univ ScalarStationarityExamples.kinkObjective) := by
    rw [hdom]; exact interior_subset_intrinsicInterior (by simp)
  have hAr : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (univ : Set (ℝ × ℝ)) := interior_subset_intrinsicInterior (by simp)
  have hslater : ((budget 0 : Matrix (Fin 1) (Fin 1) ℝ)-(kinkMatrix (-1,0) : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
    have he : ((budget 0 : Matrix (Fin 1) (Fin 1) ℝ)-(kinkMatrix (-1,0) : Matrix (Fin 1) (Fin 1) ℝ))=1 := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [kinkMatrix,ScalarStationarityExamples.kinkEnergy,budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
    rw [he]
    exact Matrix.PosDef.one
  have hbottom : ∀ x, ScalarStationarityExamples.kinkObjective x ≠ ⊥ := fun x => EReal.coe_ne_bot _
  obtain ⟨P,q,k,η,hP,hq,hk,hη,hs,_,hc,_⟩ := GeneralMatrixStationarity.matrix_nonsmooth_stationarity
    hbottom ScalarStationarityExamples.kink_objective_convex convex_univ hC hAr hXi hstar
    (mem_univ (-1,0)) (EReal.coe_ne_top _) hslater
  exact ⟨P,q,k,η,hP,hq,hk,hη,hs,hc⟩

def restrictedEnergy (x : ℝ) : ℝ := if 0 ≤ x then x else -1
def restrictedMatrix (x : ℝ) : Symmetric (Fin 1) := budget (restrictedEnergy x)

/-- Convexity on A alone says nothing about an arbitrary off-A continuation. -/
theorem restricted_matrix_loewner_convex : LoewnerConvexOn (Ici 0) restrictedMatrix := by
  intro x hx y hy a b ha hb _
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hm : 0 ≤ a*x+b*y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  change positive (a • budget (restrictedEnergy x)+b • budget (restrictedEnergy y)-
    budget (restrictedEnergy (a*x+b*y)))
  simp only [restrictedEnergy,if_pos hx,if_pos hy,if_pos hm]
  rw [budget_combination]
  have he : a*x+b*y-(a*x+b*y)=0 := sub_self _
  rw [he,budget_positive_iff]

/-- Every positive scalar trace price fails to have an ambient support for this
off-A continuation, although the actual matrix map is Loewner-convex on A. -/
theorem missing_extension_no_trace_support {p : ℝ} (hp : 0 < p) :
    ¬ ∃ r : ℝ →L[ℝ] ℝ,
      RealSubgradient (fun x => trace ((p • (1 : Matrix (Fin 1) (Fin 1) ℝ))*
        (restrictedMatrix x : Matrix (Fin 1) (Fin 1) ℝ))) 1 r := by
  have he (x : ℝ) : trace ((p • (1 : Matrix (Fin 1) (Fin 1) ℝ))*
      (restrictedMatrix x : Matrix (Fin 1) (Fin 1) ℝ))=p*restrictedEnergy x := by
    norm_num [restrictedMatrix,budget,SbtCosmo.Adequacy.Reconciliation.oneByOne,
      Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ]
  rintro ⟨r,hr⟩
  have h0 := hr 0
  have h2 := hr 2
  have hn := hr (-1/2)
  have hrev (t : ℝ) : r t=t*r 1 := by
    nth_rw 1 [show t=t • (1 : ℝ) by simp]
    rw [map_smul,smul_eq_mul]
  simp only [he] at h0 h2 hn
  rw [hrev] at h0 h2 hn
  norm_num [restrictedEnergy] at h0 h2 hn
  linarith

end
end SbtCosmo.Derivation.GeneralMatrixExamples
