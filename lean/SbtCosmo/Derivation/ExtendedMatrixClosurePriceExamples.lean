import SbtCosmo.Derivation.ExtendedMatrixClosurePrice
import SbtCosmo.Derivation.MatrixClosurePriceExamples
import SbtCosmo.Derivation.ExtendedClosurePriceExamples

/-! Inhabited matrix price with infinite objective values, and a bad-conversion control. -/
namespace SbtCosmo.Derivation.ExtendedMatrixClosurePriceExamples
noncomputable section
open Set Matrix Filter MatrixPriceRepresentation MatrixClosurePrice
open MatrixClosurePriceExamples (coordinate budget energy)
open ExtendedClosurePriceExamples (objective)
open scoped Matrix Topology Matrix.Norms.Elementwise

theorem costs_return (B : Symmetric (Fin 1)) :
    ExtendedConeClosurePrice.costs univ objective energy positive B =
      ExtendedClosurePrice.costs univ objective SchurClosurePriceExamples.energy (coordinate B) := by
  ext r
  constructor <;> rintro ⟨x,hx,he,hr⟩
  · exact ⟨x,hx,(MatrixClosurePriceExamples.feasible_iff B x).mp he,hr⟩
  · exact ⟨x,hx,(MatrixClosurePriceExamples.feasible_iff B x).mpr he,hr⟩

theorem value_return (B : Symmetric (Fin 1)) :
    ExtendedConeClosurePrice.value univ objective energy positive B =
      ExtendedClosurePrice.value univ objective SchurClosurePriceExamples.energy (coordinate B) := by
  unfold ExtendedConeClosurePrice.value ExtendedClosurePrice.value
  rw [costs_return]

theorem actual_value_derivative :
    HasFDerivAt (fun B => (ExtendedConeClosurePrice.value univ objective energy positive B).toReal)
      (-coordinate) (budget 1) := by
  have h := ExtendedClosurePriceExamples.actual_value_derivative.hasFDerivAt.comp (budget 1) coordinate.hasFDerivAt
  have he : (fun B => (ExtendedConeClosurePrice.value univ objective energy positive B).toReal) =
      (fun B => (ExtendedClosurePrice.value univ objective SchurClosurePriceExamples.energy (coordinate B)).toReal) := by
    funext B
    rw [value_return]
  rw [he]
  convert h using 1
  ext B
  simp

/-- Optimizer, finite actual value and derivative are earned before applying the extended matrix theorem. -/
theorem actual_matrix_price :
    ∃ P : Matrix (Fin 1) (Fin 1) ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      (∀ H : Symmetric (Fin 1), trace (P*(H : Matrix (Fin 1) (Fin 1) ℝ))=coordinate H) ∧
      trace (P*((energy 1 : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ)))=0 ∧
      (∀ x : ℝ, objective 1 ≤ objective x+
        (trace (P*((energy x : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ))) : ℝ)) ∧
      sInf ((fun x => objective x+(trace (P*((energy x : Matrix (Fin 1) (Fin 1) ℝ)-
        (budget 1 : Matrix (Fin 1) (Fin 1) ℝ))) : ℝ)) '' univ) = (1 : EReal) ∧
      ExtendedConeClosurePrice.value univ objective energy positive (budget 1) = (1 : EReal) := by
  have hs : ExtendedConeClosurePrice.PrimalOptimum univ objective energy positive (budget 1) 1 := by
    have hp : ExtendedClosurePrice.PrimalOptimum univ objective SchurClosurePriceExamples.energy 1 1 := by
      simpa using ExtendedClosurePriceExamples.sqrt_primal_optimum
        (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 4)
    refine ⟨mem_univ _,hp.finite,(MatrixClosurePriceExamples.feasible_iff _ _).mpr hp.feasible,?_⟩
    intro x hx he
    exact hp.optimal x hx ((MatrixClosurePriceExamples.feasible_iff _ _).mp he)
  have hf : ∀ᶠ B in 𝓝 (budget 1),
      ExtendedConeClosurePrice.value univ objective energy positive B ≠ ⊤ ∧
      ExtendedConeClosurePrice.value univ objective energy positive B ≠ ⊥ := by
    have hn : ∀ᶠ B in 𝓝 (budget 1), coordinate B ∈ Ioo 0 4 :=
      coordinate.continuous.tendsto (budget 1)
        (isOpen_Ioo.mem_nhds (by norm_num [MatrixClosurePriceExamples.coordinate_budget]))
    filter_upwards [hn] with B hB
    rw [value_return]
    exact ExtendedClosurePriceExamples.local_finiteness hB.1 hB.2
  have hstrict : ∃ H : Symmetric (Fin 1), positive H ∧ (-coordinate) H < 0 :=
    ⟨budget 1,(MatrixClosurePriceExamples.budget_positive_iff 1).mpr (by norm_num),
      by norm_num [MatrixClosurePriceExamples.coordinate_budget]⟩
  have hv : ExtendedConeClosurePrice.value univ objective energy positive (budget 1) = (1 : EReal) := by
    rw [value_return,MatrixClosurePriceExamples.coordinate_budget]
    exact ExtendedClosurePriceExamples.actual_positive_certificate.2.2
  obtain ⟨P,hP,hne,hrepr,hcomp,hglobal,hdual,_,_⟩ := ExtendedMatrixClosurePrice.matrix_price
    (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe
    (fun x _ => ExtendedClosurePriceExamples.objective_no_bottom x)
    ExtendedClosurePriceExamples.objective_epigraph_convex hs hf actual_value_derivative hstrict
  exact ⟨P,hP,hne,by simpa using hrepr,hcomp,fun x => hglobal x (mem_univ _),hdual.trans hv,hv⟩

theorem converted_value_return (K : ℝ → ℝ) (B : Symmetric (Fin 1)) :
    ConeClosurePrice.value univ K energy positive B =
      ConvexClosurePrice.budgetValue univ K SchurClosurePriceExamples.energy (coordinate B) := by
  have hc : ConeClosurePrice.feasibleCosts univ K energy positive B =
      ConvexClosurePrice.feasibleCosts univ K SchurClosurePriceExamples.energy (coordinate B) := by
    ext r
    constructor <;> rintro ⟨x,hx,he,hr⟩
    · exact ⟨x,hx,(MatrixClosurePriceExamples.feasible_iff B x).mp he,hr⟩
    · exact ⟨x,hx,(MatrixClosurePriceExamples.feasible_iff B x).mpr he,hr⟩
  exact congrArg sInf hc

/-- Omitting the finite-domain restriction changes the actual matrix-budget value from one to zero. -/
theorem unrestricted_toReal_false_value :
    ConeClosurePrice.value univ (ExtendedClosurePrice.realObjective objective) energy positive (budget 1) = 0 ∧
    ExtendedConeClosurePrice.value univ objective energy positive (budget 1) = (1 : EReal) ∧ objective (-1) = ⊤ := by
  rw [converted_value_return,MatrixClosurePriceExamples.coordinate_budget,value_return,
    MatrixClosurePriceExamples.coordinate_budget]
  exact ExtendedClosurePriceExamples.unrestricted_toReal_false_value

end
end SbtCosmo.Derivation.ExtendedMatrixClosurePriceExamples
