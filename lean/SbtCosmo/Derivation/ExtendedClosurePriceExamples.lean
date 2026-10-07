import SbtCosmo.Derivation.ExtendedSchurClosurePrice
import SbtCosmo.Derivation.SchurClosurePriceExamples

/-! A genuinely extended objective, with its actual Schur budget and infinity control. -/
namespace SbtCosmo.Derivation.ExtendedClosurePriceExamples
noncomputable section
open Set Filter ExtendedClosurePrice
open scoped Topology

def objective (x : ℝ) : EReal :=
  if 0 ≤ x then (SchurClosurePriceExamples.objective x : EReal) else ⊤

theorem objective_no_bottom (x : ℝ) : objective x ≠ ⊥ := by
  unfold objective
  split <;> simp

theorem objective_domain : finiteDomain univ objective = Ici 0 := by
  ext x
  by_cases hx : 0 ≤ x <;> simp [finiteDomain, objective, hx]

theorem epigraph_eq : epigraph univ objective =
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ SchurClosurePriceExamples.objective p.1 ≤ p.2} := by
  ext p
  by_cases hp : 0 ≤ p.1
  · simp [epigraph, objective, hp]
  · simp [epigraph, objective, hp, top_le_iff]

theorem objective_epigraph_convex : Convex ℝ (epigraph univ objective) := by
  rw [epigraph_eq]
  intro p hp q hq a b ha hb hab
  constructor
  · exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
  · have h := SchurClosurePriceExamples.objective_convex.2 (mem_univ p.1) (mem_univ q.1) ha hb hab
    have hpa := mul_le_mul_of_nonneg_left hp.2 ha
    have hqb := mul_le_mul_of_nonneg_left hq.2 hb
    exact h.trans (add_le_add hpa hqb)

theorem sqrt_primal_optimum {B : ℝ} (hB : 0 < B) (hu : B < 4) :
    PrimalOptimum univ objective SchurClosurePriceExamples.energy B (Real.sqrt B) := by
  have h := SchurClosurePriceExamples.sqrt_primal_optimum hB hu
  refine ⟨mem_univ _, ?_, h.feasible, ?_⟩
  · simp [objective, Real.sqrt_nonneg]
  · intro x hx he
    by_cases hp : 0 ≤ x
    · simpa only [objective, if_pos (Real.sqrt_nonneg B), if_pos hp, EReal.coe_le_coe_iff]
        using h.optimal x hx he
    · simp [objective, hp]

theorem actual_value_formula {B : ℝ} (hB : 0 < B) (hu : B < 4) :
    value univ objective SchurClosurePriceExamples.energy B = ((Real.sqrt B-2)^2 : ℝ) := by
  rw [optimum_value (sqrt_primal_optimum hB hu)]
  simp [objective, Real.sqrt_nonneg, SchurClosurePriceExamples.objective]

theorem local_finiteness {B : ℝ} (hB : 0 < B) (hu : B < 4) :
    value univ objective SchurClosurePriceExamples.energy B ≠ ⊤ ∧
    value univ objective SchurClosurePriceExamples.energy B ≠ ⊥ := by
  rw [actual_value_formula hB hu]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

theorem actual_value_derivative :
    HasDerivAt (fun B => (value univ objective SchurClosurePriceExamples.energy B).toReal) (-1) 1 := by
  have h : (fun B => (value univ objective SchurClosurePriceExamples.energy B).toReal) =ᶠ[𝓝 (1 : ℝ)]
      ConvexClosurePrice.budgetValue univ SchurClosurePriceExamples.objective SchurClosurePriceExamples.energy := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioo 0 4)] with B hB
    rw [actual_value_formula hB.1 hB.2, SchurClosurePriceExamples.actual_value_formula hB.1 hB.2]
    rfl
  exact SchurClosurePriceExamples.actual_value_derivative.congr_of_eventuallyEq h

/-- All optimizer, domain, finite-value and derivative inputs are independently supplied by proofs. -/
theorem actual_positive_certificate :
    DualCertificate univ objective SchurClosurePriceExamples.energy 1 1 1 ∧
    dualValue univ objective SchurClosurePriceExamples.energy 1 1 =
      value univ objective SchurClosurePriceExamples.energy 1 ∧
    value univ objective SchurClosurePriceExamples.energy 1 = (1 : EReal) := by
  have hp : PrimalOptimum univ objective SchurClosurePriceExamples.energy 1 1 := by
    simpa using sqrt_primal_optimum (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 4)
  obtain ⟨p, hpval, _, _, hc, hdual⟩ := ExtendedSchurClosurePrice.positive_schur_price
    Matrix.PosSemidef.one (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe
    convex_univ (fun x _ => objective_no_bottom x) objective_epigraph_convex hp
    (by norm_num : (1 : ℝ) ∈ Ioo 0 4)
    (fun T hT => local_finiteness hT.1 hT.2) actual_value_derivative (by norm_num : (-1 : ℝ) < 0)
  norm_num at hpval
  subst p
  refine ⟨hc, hdual, ?_⟩
  rw [actual_value_formula (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 4)]
  norm_num

/-- Blindly taking toReal on the whole domain admits a forbidden point with zero cost. -/
theorem unrestricted_toReal_false_value :
    ConvexClosurePrice.budgetValue univ (realObjective objective) SchurClosurePriceExamples.energy 1 = 0 ∧
    value univ objective SchurClosurePriceExamples.energy 1 = (1 : EReal) ∧ objective (-1) = ⊤ := by
  have hp : ConvexClosurePrice.PrimalOptimum univ (realObjective objective)
      SchurClosurePriceExamples.energy 1 (-1) := by
    refine ⟨mem_univ _, by norm_num [SchurClosurePriceExamples.energy_eq], ?_⟩
    intro x _ _
    simp only [realObjective, objective]
    rw [if_neg (by norm_num : ¬ (0 : ℝ) ≤ -1)]
    by_cases hx : 0 ≤ x
    · simpa [hx, SchurClosurePriceExamples.objective] using sq_nonneg (x-2)
    · simp [hx]
  refine ⟨?_, actual_positive_certificate.2.2, by norm_num [objective]⟩
  rw [ConvexClosurePrice.optimum_value hp]
  norm_num [realObjective, objective]

end
end SbtCosmo.Derivation.ExtendedClosurePriceExamples
