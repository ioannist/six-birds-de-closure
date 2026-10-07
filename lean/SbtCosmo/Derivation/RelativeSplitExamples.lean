import SbtCosmo.Derivation.RelativeSumSplit

/-! Actual lower-dimensional extended-domain return. The qualified construction
must produce a nonzero ambient support, despite empty ambient domain interior. -/
namespace SbtCosmo.Derivation.RelativeSplitExamples
noncomputable section
open Set Filter ConvexSubgradient ExtendedClosurePrice
open scoped Topology

theorem intrinsicInterior_affineSubspace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : AffineSubspace ℝ E) :
    intrinsicInterior ℝ (S : Set E)=(S : Set E) := by
  unfold intrinsicInterior
  rw [AffineSubspace.affineSpan_coe]
  have he : ((fun x : S => (x : E)) ⁻¹' (S : Set E))=univ := by ext x; simp
  rw [he,interior_univ]
  ext x
  simp

def line : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)
def objective (x : ℝ × ℝ) : EReal := if x.2=0 then (x.1 : ℝ) else ⊤

theorem objective_no_bottom (x : ℝ × ℝ) : objective x ≠ ⊥ := by
  unfold objective
  split <;> simp

theorem objective_epigraph_convex : Convex ℝ (epigraph univ objective) := by
  have he : epigraph univ objective = {z : (ℝ × ℝ) × ℝ | z.1 ∈ (line : Set (ℝ × ℝ)) ∧ z.1.1 ≤ z.2} := by
    ext z
    by_cases hz : z.1.2=0
    · simp [epigraph,objective,hz,line,LinearMap.mem_ker,EReal.coe_le_coe_iff]
    · simp [epigraph,objective,hz,line,LinearMap.mem_ker,top_le_iff]
  rw [he]
  exact ((LinearMap.fst ℝ ℝ ℝ).convexOn line.convex).convex_epigraph

theorem objective_domain : finiteDomain univ objective=(line : Set (ℝ × ℝ)) := by
  ext x
  by_cases hx : x.2=0 <;> simp [finiteDomain,objective,hx,line,LinearMap.mem_ker]

theorem objective_relative_interior : intrinsicInterior ℝ (finiteDomain univ objective)=(line : Set (ℝ × ℝ)) := by
  rw [objective_domain]
  exact intrinsicInterior_affineSubspace line.toAffineSubspace

/-- The example's domain really has empty ambient interior. -/
theorem objective_ambient_interior_empty : interior (finiteDomain univ objective)=∅ := by
  rw [objective_domain]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxline := interior_subset hx
  have hx₂ : x.2=0 := hxline
  have hn := mem_interior_iff_mem_nhds.mp hx
  have ht : Tendsto (fun t : ℝ => x+(0,t)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+(0,t)) := by fun_prop
    have ht' := (hc.continuousAt (x := (0 : ℝ))).tendsto
    have he : x+(0,(0 : ℝ))=x := by change x+(0 : ℝ × ℝ)=x; simp
    rw [he] at ht'
    exact ht'.mono_left nhdsWithin_le_nhds
  obtain ⟨t,htline,htpos⟩ := ((ht.eventually hn).and self_mem_nhdsWithin).exists
  have he : x.2+t=0 := htline
  linarith

theorem objective_restricted_support : SubgradientOn {(0 : ℝ × ℝ)} objective 0 0 := by
  refine ⟨mem_singleton _,by simp [objective],objective_no_bottom _,?_⟩
  intro x hx
  have he : x=0 := hx
  subst x
  simp

/-- Zero-premise application of the qualified extended split, with a forced
nonzero ambient objective support and an actual admissibility normal. -/
theorem constructed_lower_dimensional_split :
    ∃ q n : (ℝ × ℝ) →L[ℝ] ℝ, Subgradient objective 0 q ∧
      NormalCone {(0 : ℝ × ℝ)} 0 n ∧ q+n=0 ∧ q ≠ 0 := by
  have hC : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (finiteDomain univ objective) := by
    rw [objective_relative_interior]
    exact line.zero_mem
  have hA : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ {(0 : ℝ × ℝ)} := by simp
  obtain ⟨q,n,hq,hn,heq⟩ := RelativeSumSplit.split_subgradient objective_no_bottom
    objective_epigraph_convex (convex_singleton 0) hC hA objective_restricted_support
  refine ⟨q,n,hq,hn,heq,?_⟩
  intro hz
  have hh := hq.2.2.2 (-1,0) (mem_univ _)
  have hh' : ((0 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by simpa [hz,objective] using hh
  have hhreal := EReal.coe_le_coe_iff.mp hh'
  norm_num at hhreal

end
end SbtCosmo.Derivation.RelativeSplitExamples
