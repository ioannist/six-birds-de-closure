import SbtCosmo.Derivation.SchurStationarity
import SbtCosmo.Derivation.NonsmoothPriceExamples
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Complete stationarity examples and a genuine missing-domain-qualification control. -/
namespace SbtCosmo.Derivation.StationarityExamples
noncomputable section
open Set Matrix ConvexSubgradient MatrixPriceRepresentation MatrixClosurePrice
open MatrixClosurePriceExamples (energy budget)
open scoped Topology Matrix Matrix.Norms.Elementwise

/-- A nonsmooth finite ambient objective has its own subgradient in the full split. -/
theorem actual_nonsmooth_stationarity :
    ∃ price q : ℝ →L[ℝ] ℝ, price ≠ 0 ∧
      RealSubgradient NonsmoothPriceExamples.objective 0 q ∧ q+price=0 := by
  obtain ⟨price,hp,hne,_⟩ := NonsmoothPriceExamples.actual_nonsmooth_price
  have hg : ConvexOn ℝ univ price := by
    have hh := (convexOn_id (𝕜 := ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))).comp_linearMap price.toLinearMap
    simpa only [preimage_univ,Function.comp_def,id_eq] using hh
  have hm : ∀ x ∈ (univ : Set ℝ), NonsmoothPriceExamples.objective 0+price 0 ≤
      NonsmoothPriceExamples.objective x+price x := by
    simpa only [map_zero,id_eq,sub_zero,add_zero] using hp.global_minimum
  obtain ⟨q,n,hq,hn,heq⟩ := ConvexSumSplit.finite_objective_stationarity convex_univ
    NonsmoothPriceExamples.objective_convex hg (mem_univ 0) hm price.hasFDerivAt
  rw [normal_univ_iff.mp hn,add_zero] at heq
  exact ⟨price,q,hne,hq,heq⟩

/-- Actual Schur-budget program earns a nonzero price, ambient objective support,
admissibility normal and actual constraint derivative, with no stationarity premises. -/
theorem actual_schur_stationarity :
    ∃ (P : Matrix (Fin 1) (Fin 1) ℝ) (q n : ℝ →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      RealSubgradient SchurClosurePriceExamples.objective 1 q ∧ NormalCone univ 1 n ∧
      q+fderiv ℝ (fun x => trace (P*((energy x : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ)))) 1+n=0 ∧
      trace (P*((energy 1 : Matrix (Fin 1) (Fin 1) ℝ)-(budget 1 : Matrix (Fin 1) (Fin 1) ℝ)))=0 := by
  have hstar : ConeClosurePrice.PrimalOptimum univ SchurClosurePriceExamples.objective energy positive (budget 1) 1 := by
    have hp := ConvexClosurePrice.certificate_primal_optimum SchurClosurePriceExamples.actual_positive_schur_certificate.1
    refine ⟨mem_univ _,(MatrixClosurePriceExamples.feasible_iff _ _).mpr hp.feasible,?_⟩
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
      ExtendedConeClosurePrice.value univ (fun x => (SchurClosurePriceExamples.objective x : EReal)) energy positive (budget 1+H) <
        ExtendedConeClosurePrice.value univ (fun x => (SchurClosurePriceExamples.objective x : EReal)) energy positive (budget 1) := by
    refine ⟨budget 3,(MatrixClosurePriceExamples.budget_positive_iff 3).mpr (by norm_num),?_⟩
    have hf : positive (budget 1+budget 3-energy 2) := by
      apply (MatrixClosurePriceExamples.feasible_iff _ _).mpr
      norm_num [SchurClosurePriceExamples.energy_eq,MatrixClosurePriceExamples.coordinate_budget]
    have hc : (SchurClosurePriceExamples.objective 2 : EReal) ∈
        ExtendedConeClosurePrice.costs univ (fun x => (SchurClosurePriceExamples.objective x : EReal)) energy positive (budget 1+budget 3) :=
      ⟨2,mem_univ _,hf,rfl⟩
    have he : ExtendedConeClosurePrice.PrimalOptimum univ (fun x => (SchurClosurePriceExamples.objective x : EReal))
        energy positive (budget 1) 1 :=
      ⟨hstar.member,EReal.coe_ne_top _,hstar.feasible,fun x hx hf => EReal.coe_le_coe_iff.mpr (hstar.optimal x hx hf)⟩
    apply (sInf_le hc).trans_lt
    rw [ExtendedConeClosurePrice.optimum_value he]
    norm_num [SchurClosurePriceExamples.objective]
  exact SchurStationarity.matrix_stationarity_nonzero (0 : Matrix (Fin 1) (Fin 1) ℝ)
    SchurClosurePriceExamples.probe convex_univ SchurClosurePriceExamples.objective_convex hstar (mem_univ 0) hslater hstrict

def boundaryObjective (x : ℝ) : EReal := if 0 ≤ x then (-Real.sqrt x : ℝ) else ⊤

theorem boundary_no_bottom (x : ℝ) : boundaryObjective x ≠ ⊥ := by
  unfold boundaryObjective
  split <;> simp

/-- The control objective is convex on its true effective domain and genuinely extended. -/
theorem boundary_epigraph_convex : Convex ℝ (ExtendedClosurePrice.epigraph univ boundaryObjective) := by
  have he : ExtendedClosurePrice.epigraph univ boundaryObjective =
      {z : ℝ × ℝ | z.1 ∈ Ici 0 ∧ -Real.sqrt z.1 ≤ z.2} := by
    ext z
    by_cases hz : 0 ≤ z.1
    · simp only [ExtendedClosurePrice.epigraph,mem_setOf_eq,mem_univ,true_and,boundaryObjective,mem_Ici,hz,ite_true,EReal.coe_le_coe_iff]
    · simp [ExtendedClosurePrice.epigraph,boundaryObjective,hz,top_le_iff]
  rw [he]
  exact Real.strictConcaveOn_sqrt.concaveOn.neg.convex_epigraph

/-- The constrained minimizer has restricted zero support. -/
theorem boundary_restricted_support : SubgradientOn {0} boundaryObjective 0 0 := by
  refine ⟨mem_singleton _,by norm_num [boundaryObjective],by norm_num [boundaryObjective],?_⟩
  intro x hx
  have he : x=0 := hx
  subst x
  simp

/-- No finite ambient objective support exists at the endpoint: the right slope is unbounded. -/
theorem boundary_no_ambient_support : ¬ ∃ p : ℝ →L[ℝ] ℝ, Subgradient boundaryObjective 0 p := by
  rintro ⟨p,hp⟩
  let t : ℝ := 1/(|p 1|+1)
  have hden : 0 < |p 1|+1 := by positivity
  have ht : 0 < t := div_pos zero_lt_one hden
  have hcancel : t*(|p 1|+1)=1 := div_mul_cancel₀ 1 hden.ne'
  have hpval : p (t^2)=t^2*p 1 := by
    have he : (t^2 : ℝ)=(t^2) • (1 : ℝ) := by simp
    rw [he,map_smul]
    simp only [smul_eq_mul,mul_one]
  have hh := hp.2.2.2 (t^2) (mem_univ _)
  have heval : boundaryObjective (t^2)=(-t : ℝ) := by
    simp only [boundaryObjective,if_pos (sq_nonneg t),Real.sqrt_sq_eq_abs,abs_of_pos ht]
  simp only [sub_zero] at hh
  rw [heval,hpval] at hh
  have hz : boundaryObjective 0=0 := by norm_num [boundaryObjective]
  rw [hz,zero_add] at hh
  have hreal := EReal.coe_le_coe_iff.mp hh
  have hpos : 0 ≤ p 1+|p 1| := by linarith [neg_abs_le (p 1)]
  have hproduct : t^2*|p 1|+t^2=t := by
    have hm := congrArg (fun r : ℝ => t*r) hcancel
    nlinarith only [hm]
  nlinarith [mul_nonneg (sq_nonneg t) hpos,sq_pos_of_pos ht]

/-- Restricted stationarity cannot be relabeled as the ambient objective/normal split
without a domain qualification: even allowing every admissibility normal cannot fix it. -/
theorem missing_qualification_no_split :
    ¬ ∃ q n : ℝ →L[ℝ] ℝ, Subgradient boundaryObjective 0 q ∧ NormalCone {0} 0 n ∧ q+n=0 := by
  rintro ⟨q,_,hq,_,_⟩
  exact boundary_no_ambient_support ⟨q,hq⟩

end
end SbtCosmo.Derivation.StationarityExamples
