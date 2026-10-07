import SbtCosmo.Derivation.RelativeConvexContinuity
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Actual perturbation witnesses from intersecting relative interiors. The
budget space is the sum of the two affine-span directions, not ambient E. -/
namespace SbtCosmo.Derivation.RelativeDifference
noncomputable section
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual difference of two direction vectors, in their sum space. -/
def difference (P Q : Submodule ℝ E) : (P × Q) →ₗ[ℝ] ↥(P ⊔ Q) where
  toFun z := ⟨(z.1 : E) - (z.2 : E), Submodule.sub_mem_sup z.1.property z.2.property⟩
  map_add' z w := by ext; simp; abel
  map_smul' a z := by ext; simp [smul_sub]

/-- The difference map is onto its actual budget space. -/
theorem difference_surjective (P Q : Submodule ℝ E) : Function.Surjective (difference P Q) := by
  intro w
  obtain ⟨u,hu,v,hv,he⟩ := Submodule.mem_sup.mp w.property
  refine ⟨(⟨u,hu⟩,⟨-v,Q.neg_mem hv⟩), ?_⟩
  apply Subtype.ext
  simpa only [difference,LinearMap.coe_mk,AddHom.coe_mk,sub_neg_eq_add] using he

/-- Relative interiors earn actual feasible differences of bounded cost near zero.
No local feasible-value or support certificate is a premise. -/
theorem local_bounded_witnesses [FiniteDimensional ℝ E]
    {C A : Set E} {f : E → ℝ} {x₀ : E} (hf : ConvexOn ℝ C f)
    (hC : x₀ ∈ intrinsicInterior ℝ C) (hA : x₀ ∈ intrinsicInterior ℝ A) :
    ∀ᶠ w : ↥((affineSpan ℝ C).direction ⊔ (affineSpan ℝ A).direction) in 𝓝 0,
      ∃ x ∈ C, ∃ y ∈ A, x-y=(w : E) ∧ f x ≤ f x₀+1 := by
  let P := (affineSpan ℝ C).direction
  let Q := (affineSpan ℝ A).direction
  have hP := RelativeConvexContinuity.chart_bounded_above hf hC
  have hQ := RelativeConvexContinuity.chart_mem_nhds hA
  have hfirst : ∀ᶠ z : P × Q in 𝓝 0,
      x₀ + (z.1 : E) ∈ C ∧ f (x₀ + (z.1 : E)) ≤ f x₀+1 :=
    (continuous_fst.continuousAt (x := (0 : P × Q))).tendsto.eventually hP
  have hsecond : ∀ᶠ z : P × Q in 𝓝 0, x₀ + (z.2 : E) ∈ A :=
    (continuous_snd.continuousAt (x := (0 : P × Q))).tendsto.eventually hQ
  letI : IsModuleTopology ℝ ↥(P ⊔ Q) := isModuleTopologyOfFiniteDimensional
  have hopen : IsOpenMap (difference P Q) :=
    IsModuleTopology.isOpenMap_of_surjective (difference_surjective P Q)
  have hn := hopen.image_mem_nhds (hfirst.and hsecond)
  rw [map_zero] at hn
  filter_upwards [hn] with w hw
  obtain ⟨z,hz,he⟩ := hw
  refine ⟨x₀ + (z.1 : E),hz.1.1,x₀ + (z.2 : E),hz.2,?_,hz.1.2⟩
  have he' := congrArg (fun v : ↥(P ⊔ Q) => (v : E)) he
  change (z.1 : E)-(z.2 : E)=(w : E) at he'
  calc
    (x₀ + (z.1 : E))-(x₀ + (z.2 : E))=(z.1 : E)-(z.2 : E) := by abel
    _ = (w : E) := he'

end
end SbtCosmo.Derivation.RelativeDifference
