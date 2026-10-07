import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Intrinsic

/-! Earn relative-interior continuity by returning the intrinsic topology through
an actual affine-span origin and its normed direction space. -/
namespace SbtCosmo.Derivation.RelativeConvexContinuity
noncomputable section
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Finite convex values are continuous on the actual relative interior, including
lower-dimensional domains. No relative continuity field is supplied. -/
theorem continuousOn_intrinsicInterior {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f) :
    ContinuousOn f (intrinsicInterior ℝ C) := by
  obtain rfl | ⟨x₀,hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  let S : AffineSubspace ℝ E := affineSpan ℝ C
  have hxspan : x₀ ∈ S := subset_affineSpan ℝ C hx₀
  letI : Nonempty S := ⟨⟨x₀,hxspan⟩⟩
  let e : S.direction ≃ᵃⁱ[ℝ] S := AffineIsometryEquiv.vaddConst ℝ ⟨x₀,hxspan⟩
  let U : Set S := (fun x : S => (x : E)) ⁻¹' C
  have hcv := hf.comp_affineMap (S.subtype.comp e.toAffineMap)
  have hc : ContinuousOn ((fun x : S => f (x : E)) ∘ e) (interior (e ⁻¹' U)) :=
    hcv.continuousOn_interior
  have himage : e '' interior (e ⁻¹' U)=interior U := by
    change e.toHomeomorph '' interior (e.toHomeomorph ⁻¹' U) = interior U
    rw [e.toHomeomorph.image_interior]
    rw [e.toHomeomorph.surjective.image_preimage]
  have hs : ContinuousOn (fun x : S => f (x : E)) (e '' interior (e ⁻¹' U)) :=
    e.toHomeomorph.isInducing.continuousOn_image_iff.mpr hc
  rw [himage] at hs
  exact Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr hs

omit [FiniteDimensional ℝ E] in
/-- Relative-interior membership supplies an actual direction-space neighborhood. -/
theorem chart_mem_nhds {C : Set E} {x₀ : E} (hx₀ : x₀ ∈ intrinsicInterior ℝ C) :
    {u : (affineSpan ℝ C).direction | x₀ + (u : E) ∈ C} ∈ 𝓝 0 := by
  obtain ⟨p,hp,hpx⟩ := mem_intrinsicInterior.mp hx₀
  letI : Nonempty (affineSpan ℝ C) := ⟨p⟩
  let e := AffineIsometryEquiv.vaddConst ℝ p
  have he0 : e 0 = p := by simp [e]
  have hn : ∀ᶠ u in 𝓝 (0 : (affineSpan ℝ C).direction), (e u : E) ∈ C := by
    have ht : Tendsto e (𝓝 0) (𝓝 p) := he0 ▸ e.continuous.continuousAt.tendsto
    exact ht.eventually (mem_interior_iff_mem_nhds.mp hp)
  have he (u : (affineSpan ℝ C).direction) : (e u : E) = x₀ + (u : E) := by
    simp only [e,AffineIsometryEquiv.coe_vaddConst,AffineSubspace.coe_vadd,vadd_eq_add]
    rw [hpx,add_comm]
  simpa only [he] using hn

/-- Convexity and relative-interior membership earn continuity of the actual chart
at its origin, even when C has empty ambient interior. -/
theorem continuousAt_chart {C : Set E} {f : E → ℝ} {x₀ : E}
    (hf : ConvexOn ℝ C f) (hx₀ : x₀ ∈ intrinsicInterior ℝ C) :
    ContinuousAt (fun u : (affineSpan ℝ C).direction => f (x₀ + (u : E))) 0 := by
  obtain ⟨p,hp,hpx⟩ := mem_intrinsicInterior.mp hx₀
  letI : Nonempty (affineSpan ℝ C) := ⟨p⟩
  let e := AffineIsometryEquiv.vaddConst ℝ p
  have he (u : (affineSpan ℝ C).direction) : (e u : E) = x₀ + (u : E) := by
    simp only [e,AffineIsometryEquiv.coe_vaddConst,AffineSubspace.coe_vadd,vadd_eq_add]
    rw [hpx,add_comm]
  have hcv := hf.comp_affineMap ((affineSpan ℝ C).subtype.comp e.toAffineMap)
  have hn : (0 : (affineSpan ℝ C).direction) ∈
      interior ((fun u => (e u : E)) ⁻¹' C) := by
    apply mem_interior_iff_mem_nhds.mpr
    simpa only [he] using chart_mem_nhds hx₀
  have hc := hcv.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hn)
  change ContinuousAt (fun u => f (e u : E)) 0 at hc
  simpa only [he] using hc

/-- A uniform finite upper bound is constructed from relative-interior continuity. -/
theorem chart_bounded_above {C : Set E} {f : E → ℝ} {x₀ : E}
    (hf : ConvexOn ℝ C f) (hx₀ : x₀ ∈ intrinsicInterior ℝ C) :
    ∀ᶠ u : (affineSpan ℝ C).direction in 𝓝 0,
      x₀ + (u : E) ∈ C ∧ f (x₀ + (u : E)) ≤ f x₀ + 1 := by
  have hlt := (continuousAt_chart hf hx₀).eventually_lt continuousAt_const
    (by simp : f (x₀ + ((0 : (affineSpan ℝ C).direction) : E)) < f x₀ + 1)
  filter_upwards [chart_mem_nhds hx₀,hlt] with u hu hfu
  exact ⟨hu,hfu.le⟩

end
end SbtCosmo.Derivation.RelativeConvexContinuity
