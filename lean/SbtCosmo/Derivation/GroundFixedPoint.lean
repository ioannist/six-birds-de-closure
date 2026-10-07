import SbtCosmo.Derivation.GroundSelector
import Gametheory.Brouwer

/-!
All-parameter self-consistent ground states for the original eight-site source
potential. The ground selector is constructed and proved continuous before the
audited simplex Brouwer theorem is applied. No fixed-point witness is a premise.
-/
namespace SbtCosmo.Derivation.GroundState

noncomputable section
open scoped BigOperators

abbrev Probability := stdSimplex ℝ (Fin 8)

def sqrtField (p : Probability) : Field := fun i => Real.sqrt (p.val i)

theorem sqrtField_normalized (p : Probability) : normSq (sqrtField p) = 1 := by
  calc
    _ = ∑ i, p.val i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Real.sq_sqrt (p.property.1 i)
    _ = 1 := p.property.2

theorem continuous_sqrtField : Continuous sqrtField := by
  exact continuous_pi fun i => Real.continuous_sqrt.comp
    ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_sourcePotential (b : Field) (κ : ℝ) : Continuous (sourcePotential b κ) := by
  unfold sourcePotential BackgroundSelection.potential gradient
  fun_prop

def probabilityMap (b : Field) (κ : ℝ) (p : Probability) : Probability :=
  let g := positiveGround (sourcePotential b κ (sqrtField p))
  ⟨fun i => (g i) ^ 2, fun i => sq_nonneg (g i),
    (positiveGround_spec (sourcePotential b κ (sqrtField p))).2.1⟩

theorem continuous_probabilityMap (b : Field) (κ : ℝ) : Continuous (probabilityMap b κ) := by
  apply Continuous.subtype_mk
  have hg := continuous_positiveGround.comp
    ((continuous_sourcePotential b κ).comp continuous_sqrtField)
  exact continuous_pi fun i => ((continuous_apply i).comp hg).pow 2

/-- Every finite real background and coupling admits an exact positive ground fixed point. -/
theorem exists_selfConsistent_ground (b : Field) (κ : ℝ) :
    ∃ u : Field, (∀ i, 0 < u i) ∧ IsSelfConsistentGround b κ u := by
  obtain ⟨p, hp⟩ := @Brouwer (8 : ℕ+) (probabilityMap b κ) (continuous_probabilityMap b κ)
  let u := sqrtField p
  let v := sourcePotential b κ u
  let g := positiveGround v
  have heq : u = g := by
    funext i
    have hi : (g i) ^ 2 = p.val i := congrArg (fun q : Probability => q.val i) hp
    change Real.sqrt (p.val i) = g i
    rw [← hi]
    exact Real.sqrt_sq ((positiveGround_spec v).1 i).le
  refine ⟨u, ?_, energy v g, ?_⟩
  · rw [heq]
    exact (positiveGround_spec v).1
  · change IsGround v u (energy v g)
    rw [heq]
    exact (positiveGround_spec v).2

theorem every_background_offset_admitted (base : Field) (κ offset : ℝ) :
    ∃ u : Field, IsSelfConsistentGround (fun i => base i + offset) κ u := by
  obtain ⟨u, _, hu⟩ := exists_selfConsistent_ground (fun i => base i + offset) κ
  exact ⟨u, hu⟩

/-- Returns to the declared audit on the original nonconstant template as well. -/
theorem background_offset_no_forced_value (base : Field) (κ : ℝ) :
    ¬ ∃ c : ℝ, BackgroundSelection.ForcesValue
      (fun offset : ℝ => ∃ u : Field,
        IsSelfConsistentGround (fun i => base i + offset) κ u) (fun offset => offset) c := by
  apply BackgroundSelection.two_admitted_values_not_forced
    (fun offset : ℝ => ∃ u : Field, IsSelfConsistentGround (fun i => base i + offset) κ u)
    (fun offset => offset)
    (every_background_offset_admitted base κ 0) (every_background_offset_admitted base κ 1)
  norm_num

/-- Existence alone cannot demarcate admissible and inadmissible couplings. -/
theorem coupling_no_forced_value (b : Field) :
    ¬ ∃ c : ℝ, BackgroundSelection.ForcesValue
      (fun κ : ℝ => ∃ u : Field, IsSelfConsistentGround b κ u) (fun κ => κ) c := by
  have h0 : ∃ u : Field, IsSelfConsistentGround b 0 u := by
    obtain ⟨u, _, hu⟩ := exists_selfConsistent_ground b 0
    exact ⟨u, hu⟩
  have h1 : ∃ u : Field, IsSelfConsistentGround b 1 u := by
    obtain ⟨u, _, hu⟩ := exists_selfConsistent_ground b 1
    exact ⟨u, hu⟩
  apply BackgroundSelection.two_admitted_values_not_forced
    (fun κ : ℝ => ∃ u : Field, IsSelfConsistentGround b κ u) (fun κ => κ) h0 h1
  norm_num

end
end SbtCosmo.Derivation.GroundState
