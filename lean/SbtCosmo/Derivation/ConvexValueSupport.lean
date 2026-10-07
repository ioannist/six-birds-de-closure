import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation

/-! Supporting linear functionals constructed by separating the actual strict epigraph.
Continuity is earned from convexity in finite-dimensional budget spaces. -/
namespace SbtCosmo.Derivation.ConvexValueSupport
noncomputable section
open Set Filter
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- The strict epigraph is open on an open domain of continuity. -/
theorem strict_epigraph_open {U : Set F} {f : F → ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) :
    IsOpen {z : F × ℝ | z.1 ∈ U ∧ f z.1 < z.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hcont : ContinuousAt (fun w : F × ℝ => f w.1) z :=
    (hf.continuousAt (hU.mem_nhds hz.1)).comp continuousAt_fst
  exact Filter.inter_mem ((hU.preimage continuous_fst).mem_nhds hz.1)
    (hcont.eventually_lt continuousAt_snd hz.2)

/-- Separation supplies and normalizes a price; the support is not a premise. -/
theorem supporting_functional_of_continuous {U : Set F} {f : F → ℝ} {B : F}
    (hU : IsOpen U) (hf : ConvexOn ℝ U f) (hcont : ContinuousOn f U) (hB : B ∈ U) :
    ∃ d : F →L[ℝ] ℝ, ∀ T ∈ U, f B + d (T-B) ≤ f T := by
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hf.convex_strict_epigraph
    (strict_epigraph_open hU hcont) (x := (B, f B)) (by simp)
  let c : ℝ := l (0, 1)
  let q : F →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ F ℝ)
  have hsplit (T : F) (r : ℝ) : l (T,r) = q T + c*r := by
    have heq : (T,r) = (T,(0 : ℝ)) + r • ((0 : F),1) := by simp
    rw [heq, map_add, map_smul]
    simp [q, c, smul_eq_mul, mul_comm]
  have hc : 0 < c := by
    have hh := hl (B, f B+1) ⟨hB, by linarith⟩
    rw [hsplit, hsplit] at hh
    linarith
  have hclosed (T : F) (hT : T ∈ U) : l (B,f B) ≤ l (T,f T) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hl (T, f T+ε/c) ⟨hT, by linarith [div_pos hε hc]⟩
    rw [hsplit, hsplit] at hh
    rw [hsplit, hsplit]
    have he : c*(ε/c)=ε := mul_div_cancel₀ ε hc.ne'
    nlinarith
  refine ⟨-(c⁻¹ • q), ?_⟩
  intro T hT
  have hh := hclosed T hT
  rw [hsplit, hsplit] at hh
  have hdiv : (q B-q T)/c ≤ f T-f B := (div_le_iff₀ hc).2 (by nlinarith only [hh])
  calc
    f B + (-(c⁻¹ • q)) (T-B) = f B + (q B-q T)/c := by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        map_sub, smul_eq_mul, div_eq_mul_inv]
      ring
    _ ≤ f B + (f T-f B) := add_le_add (le_refl _) hdiv
    _ = f T := by ring

/-- No differentiability is needed for support on an open finite-dimensional convex domain. -/
theorem supporting_functional [FiniteDimensional ℝ F] {U : Set F} {f : F → ℝ} {B : F}
    (hU : IsOpen U) (hf : ConvexOn ℝ U f) (hB : B ∈ U) :
    ∃ d : F →L[ℝ] ℝ, ∀ T ∈ U, f B + d (T-B) ≤ f T :=
  supporting_functional_of_continuous hU hf (hf.continuousOn hU) hB

end
end SbtCosmo.Derivation.ConvexValueSupport
