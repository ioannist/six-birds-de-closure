import SbtCosmo.Derivation.MatrixClosurePrice
import SbtCosmo.Derivation.SchurClosurePriceExamples

/-! An actual one-dimensional matrix budget and a partial-slack complementarity control. -/
namespace SbtCosmo.Derivation.MatrixClosurePriceExamples
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice
open scoped Matrix Topology Matrix.Norms.Elementwise

def budget (r : ℝ) : Symmetric (Fin 1) :=
  ⟨SbtCosmo.Adequacy.Reconciliation.oneByOne r, by
    ext i j
    fin_cases i
    fin_cases j
    rfl⟩

def coordinate : Symmetric (Fin 1) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.proj (0 : Fin 1)).comp (symmetricSubmodule (Fin 1)).subtypeL)

def energy (x : ℝ) : Symmetric (Fin 1) :=
  residual (0 : Matrix (Fin 1) (Fin 1) ℝ) (SchurClosurePriceExamples.probe x)

theorem coordinate_budget (r : ℝ) : coordinate (budget r) = r := rfl

theorem budget_coordinate (B : Symmetric (Fin 1)) : budget (coordinate B) = B := by
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  rfl

theorem energy_eq (x : ℝ) : energy x = budget (x^2) := by
  apply Subtype.ext
  simp only [energy, MatrixClosurePrice.residual, SbtCosmo.Adequacy.Support.residual_zero_native]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [SchurClosurePriceExamples.probe, budget,
    SbtCosmo.Adequacy.Reconciliation.oneByOne, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, pow_two]

theorem budget_positive_iff (r : ℝ) : positive (budget r) ↔ 0 ≤ r := by
  constructor
  · intro h
    exact h.diag_nonneg (i := (0 : Fin 1))
  · intro h
    have he : (budget r : Matrix (Fin 1) (Fin 1) ℝ) = r • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      fin_cases i
      fin_cases j
      simp [budget, SbtCosmo.Adequacy.Reconciliation.oneByOne]
    change (budget r : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef
    rw [he]
    exact Matrix.PosSemidef.one.smul h

theorem feasible_iff (B : Symmetric (Fin 1)) (x : ℝ) :
    positive (B-energy x) ↔ SchurClosurePriceExamples.energy x ≤ coordinate B := by
  have he : B-energy x = budget (coordinate B-x^2) := by
    rw [energy_eq, ← budget_coordinate B]
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [he, budget_positive_iff, sub_nonneg, SchurClosurePriceExamples.energy_eq]

theorem costs_return (B : Symmetric (Fin 1)) :
    ConeClosurePrice.feasibleCosts univ SchurClosurePriceExamples.objective energy positive B =
    ConvexClosurePrice.feasibleCosts univ SchurClosurePriceExamples.objective SchurClosurePriceExamples.energy (coordinate B) := by
  ext r
  constructor <;> rintro ⟨x,hx,he,hr⟩
  · exact ⟨x,hx,(feasible_iff B x).mp he,hr⟩
  · exact ⟨x,hx,(feasible_iff B x).mpr he,hr⟩

theorem value_return (B : Symmetric (Fin 1)) :
    ConeClosurePrice.value univ SchurClosurePriceExamples.objective energy positive B =
    ConvexClosurePrice.budgetValue univ SchurClosurePriceExamples.objective SchurClosurePriceExamples.energy (coordinate B) := by
  unfold ConeClosurePrice.value ConvexClosurePrice.budgetValue
  rw [costs_return]

theorem actual_value_derivative :
    HasFDerivAt (ConeClosurePrice.value univ SchurClosurePriceExamples.objective energy positive)
      (-coordinate) (budget 1) := by
  have h := SchurClosurePriceExamples.actual_value_derivative.hasFDerivAt.comp (budget 1) coordinate.hasFDerivAt
  have he : ConeClosurePrice.value univ SchurClosurePriceExamples.objective energy positive =
      (fun B => ConvexClosurePrice.budgetValue univ SchurClosurePriceExamples.objective
        SchurClosurePriceExamples.energy (coordinate B)) := funext value_return
  rw [he]
  convert h using 1
  ext B
  simp

theorem actual_matrix_price :
    ∃ P : Matrix (Fin 1) (Fin 1) ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      (∀ H : Symmetric (Fin 1), trace (P*(H : Matrix (Fin 1) (Fin 1) ℝ))=coordinate H) ∧
      trace (P*((energy 1 : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ)))=0 ∧
      (∀ x : ℝ, SchurClosurePriceExamples.objective 1 ≤ SchurClosurePriceExamples.objective x+
        trace (P*((energy x : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ)))) := by
  have hs : ConeClosurePrice.PrimalOptimum univ SchurClosurePriceExamples.objective energy positive (budget 1) 1 := by
    have hp := SchurClosurePriceExamples.actual_positive_schur_certificate.1
    refine ⟨mem_univ _, (feasible_iff _ _).mpr hp.feasible, ?_⟩
    intro x hx he
    exact (ConvexClosurePrice.certificate_primal_optimum hp).optimal x hx ((feasible_iff _ _).mp he)
  have hf : ∀ᶠ B in 𝓝 (budget 1),
      (ConeClosurePrice.feasibleCosts univ SchurClosurePriceExamples.objective energy positive B).Nonempty ∧
      BddBelow (ConeClosurePrice.feasibleCosts univ SchurClosurePriceExamples.objective energy positive B) := by
    have hn : ∀ᶠ B in 𝓝 (budget 1), coordinate B ∈ Ioo 0 4 :=
      coordinate.continuous.tendsto (budget 1) (isOpen_Ioo.mem_nhds (by norm_num [coordinate_budget]))
    filter_upwards [hn] with B hB
    rw [costs_return]
    exact SchurClosurePriceExamples.local_finiteness hB.1
  have hstrict : ∃ H : Symmetric (Fin 1), positive H ∧ (-coordinate) H < 0 :=
    ⟨budget 1,(budget_positive_iff 1).mpr (by norm_num),by norm_num [coordinate_budget]⟩
  obtain ⟨P,hP,hne,hrepr,hcomp,hglobal,_⟩ := matrix_price
    (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe
    SchurClosurePriceExamples.objective_convex hs hf actual_value_derivative hstrict
  exact ⟨P,hP,hne,by simpa using hrepr,hcomp,fun x => hglobal x (mem_univ _)⟩

/-- A nonzero PSD price may have zero pairing with nonzero PSD slack. -/
theorem partial_slack_control :
    let P : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
    let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0,1]
    P.PosSemidef ∧ S.PosSemidef ∧ P ≠ 0 ∧ S ≠ 0 ∧ trace (P*S)=0 := by
  dsimp
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  · intro h
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num at hh
  · intro h
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
    norm_num at hh
  · norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ]

end
end SbtCosmo.Derivation.MatrixClosurePriceExamples
