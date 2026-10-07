import SbtCosmo.Derivation.NonsmoothMatrixPrice
import SbtCosmo.Derivation.ExtendedMatrixClosurePriceExamples
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Genuine kink in the actual value, and an original extended Schur matrix return
using Slater without a value derivative. -/
namespace SbtCosmo.Derivation.NonsmoothPriceExamples
noncomputable section
open Set Filter Matrix ConeClosurePrice
open scoped Topology Matrix Matrix.Norms.Elementwise

def objective (x : ℝ) : ℝ := max (-x) (-2*x)

theorem objective_convex : ConvexOn ℝ univ objective := by
  have h1 : ConvexOn ℝ univ (fun x : ℝ => -x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [smul_eq_mul]
    linarith
  have h2 : ConvexOn ℝ univ (fun x : ℝ => -2*x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [smul_eq_mul]
    linarith
  exact h1.sup h2

theorem objective_antitone : Antitone objective := by
  intro x y hxy
  exact max_le_max (neg_le_neg hxy) (by linarith)

theorem primal_optimum (B : ℝ) : PrimalOptimum univ objective id (fun H => 0 ≤ H) B B := by
  refine ⟨mem_univ _, by simp, ?_⟩
  intro x _ hx
  exact objective_antitone (by simpa using sub_nonneg.mp hx)

theorem actual_value (B : ℝ) : value univ objective id (fun H => 0 ≤ H) B=objective B :=
  optimum_value (primal_optimum B)

/-- The actual value has a genuine kink at budget zero. -/
theorem actual_value_not_differentiable :
    ¬ DifferentiableAt ℝ (value univ objective id (fun H => 0 ≤ H)) 0 := by
  have hf : value univ objective id (fun H => 0 ≤ H)=objective := funext actual_value
  rw [hf]
  intro h
  have hh := (h.mul_const 2).add ((differentiableAt_id (x := (0 : ℝ))).const_mul 3)
  have habs : (fun x : ℝ => objective x*2+3*x)=abs := by
    funext x
    dsimp [objective]
    by_cases hx : 0 ≤ x
    · rw [max_eq_left (by linarith),abs_of_nonneg hx]
      ring
    · rw [max_eq_right (by linarith),abs_of_neg (lt_of_not_ge hx)]
      ring
  change DifferentiableAt ℝ (fun x => objective x*2+3*x) 0 at hh
  rw [habs] at hh
  exact not_differentiableAt_abs_zero hh

/-- The generic Slater theorem constructs a nonzero price at this nondifferentiable value. -/
theorem actual_nonsmooth_price :
    ∃ price : ℝ →L[ℝ] ℝ, DualCertificate univ objective id (fun H => 0 ≤ H) 0 price 0 ∧
      price ≠ 0 ∧ dualValue univ objective id 0 price=0 := by
  have hc : ConeLaws (fun H : ℝ => 0 ≤ H) :=
    ⟨le_rfl,fun hx hy => add_nonneg hx hy, fun ha hx => mul_nonneg ha hx⟩
  have he : ∀ x ∈ (univ : Set ℝ), ∀ y ∈ univ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      0 ≤ a • id x+b • id y-id (a • x+b • y) := by
    intros
    simp
  have hs : (0 : ℝ)-id (-1) ∈ interior {H : ℝ | 0 ≤ H} := by
    change (0 : ℝ)-(-1) ∈ interior (Ici 0)
    rw [interior_Ici]
    norm_num
  obtain ⟨price,hprice⟩ := NonsmoothConePrice.slater_price_certificate hc objective_convex he
    (primal_optimum 0) (mem_univ (-1)) hs
  have hn : (feasibleCosts univ objective id (fun H => 0 ≤ H) 1).Nonempty :=
    ⟨objective 1,1,mem_univ _,by norm_num,rfl⟩
  have hd : value univ objective id (fun H => 0 ≤ H) 1 < value univ objective id (fun H => 0 ≤ H) 0 := by
    rw [actual_value,actual_value]
    norm_num [objective]
  refine ⟨price,hprice,NonsmoothConePrice.certificate_nonzero hprice hn hd,?_⟩
  rw [certificate_strong_duality hprice,actual_value]
  norm_num [objective]

open MatrixPriceRepresentation MatrixClosurePrice
open MatrixClosurePriceExamples (budget energy)

/-- The original infinite-objective Schur example returns through Slater alone. -/
theorem actual_extended_matrix_price :
    ∃ P : Matrix (Fin 1) (Fin 1) ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      trace (P*((energy 1 : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ)))=0 ∧
      (∀ x : ℝ, ExtendedClosurePriceExamples.objective 1 ≤ ExtendedClosurePriceExamples.objective x+
        (trace (P*((energy x : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ))) : ℝ)) ∧
      sInf ((fun x => ExtendedClosurePriceExamples.objective x+
        (trace (P*((energy x : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ))) : ℝ)) '' univ)=(1 : EReal) := by
  have hstar : ExtendedConeClosurePrice.PrimalOptimum univ ExtendedClosurePriceExamples.objective energy positive (budget 1) 1 := by
    have hp : ExtendedClosurePrice.PrimalOptimum univ ExtendedClosurePriceExamples.objective
        SchurClosurePriceExamples.energy 1 1 := by
      simpa using ExtendedClosurePriceExamples.sqrt_primal_optimum
        (by norm_num : (0 : ℝ)<1) (by norm_num : (1 : ℝ)<4)
    refine ⟨mem_univ _,hp.finite,(MatrixClosurePriceExamples.feasible_iff _ _).mpr hp.feasible,?_⟩
    intro x hx he
    exact hp.optimal x hx ((MatrixClosurePriceExamples.feasible_iff _ _).mp he)
  have hslater : ((budget 1 : Matrix (Fin 1) (Fin 1) ℝ)-(energy 0 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
    have heq : ((budget 1 : Matrix (Fin 1) (Fin 1) ℝ)-(energy 0 : Matrix (Fin 1) (Fin 1) ℝ))=1 := by
      rw [MatrixClosurePriceExamples.energy_eq]
      ext i j
      fin_cases i
      fin_cases j
      norm_num [budget,SbtCosmo.Adequacy.Reconciliation.oneByOne]
    rw [heq]
    exact Matrix.PosDef.one
  have hstrict : ∃ H : Symmetric (Fin 1), positive H ∧
      ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective energy positive (budget 1+H) <
        ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective energy positive (budget 1) := by
    refine ⟨budget 3,(MatrixClosurePriceExamples.budget_positive_iff 3).mpr (by norm_num),?_⟩
    have hfeas : positive (budget 1+budget 3-energy 2) := by
      apply (MatrixClosurePriceExamples.feasible_iff _ _).mpr
      norm_num [SchurClosurePriceExamples.energy_eq,MatrixClosurePriceExamples.coordinate_budget]
    have hc : ExtendedClosurePriceExamples.objective 2 ∈
        ExtendedConeClosurePrice.costs univ ExtendedClosurePriceExamples.objective energy positive (budget 1+budget 3) :=
      ⟨2,mem_univ _,hfeas,rfl⟩
    have hv : ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective energy positive (budget 1+budget 3) ≤
        ExtendedClosurePriceExamples.objective 2 := sInf_le hc
    apply hv.trans_lt
    rw [ExtendedConeClosurePrice.optimum_value hstar]
    norm_num [ExtendedClosurePriceExamples.objective,SchurClosurePriceExamples.objective]
  obtain ⟨P,hP,hne,hcomp,hglob,hdual⟩ := NonsmoothMatrixPrice.matrix_price_nonzero
    (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe
    (fun x _ => ExtendedClosurePriceExamples.objective_no_bottom x)
    ExtendedClosurePriceExamples.objective_epigraph_convex hstar (mem_univ 0)
    (by norm_num [ExtendedClosurePriceExamples.objective]) hslater hstrict
  refine ⟨P,hP,hne,hcomp,fun x => hglob x (mem_univ _),?_⟩
  have hv : ExtendedConeClosurePrice.value univ ExtendedClosurePriceExamples.objective energy positive (budget 1)=(1 : EReal) := by
    rw [ExtendedConeClosurePrice.optimum_value hstar]
    norm_num [ExtendedClosurePriceExamples.objective,SchurClosurePriceExamples.objective]
  exact hdual.trans hv

end
end SbtCosmo.Derivation.NonsmoothPriceExamples
