import SbtCosmo.Derivation.MatrixClosurePrice
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Compactness.Compact

/-! A positive-definite slack is interior in the actual symmetric PSD budget cone.
The topology is on symmetric matrices, not the full matrix space. -/
namespace SbtCosmo.Derivation.MatrixSlaterTopology
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice
open scoped Matrix Topology Matrix.Norms.Elementwise
variable {n : Type*} [Fintype n]

theorem quadratic_continuous :
    Continuous (fun z : Symmetric n × (n → ℝ) => z.2 ⬝ᵥ ((z.1 : Matrix n n ℝ) *ᵥ z.2)) := by
  simp only [dotProduct, Matrix.mulVec]
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul
  · exact (continuous_apply i).comp continuous_snd
  · apply continuous_finset_sum
    intro j _
    apply Continuous.mul
    · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))
    · exact (continuous_apply j).comp continuous_snd

/-- Compactness of the unit sphere earns uniform positivity under symmetric perturbations. -/
theorem posdef_mem_interior_positive {A : Symmetric n} (hA : (A : Matrix n n ℝ).PosDef) :
    A ∈ interior {M : Symmetric n | positive M} := by
  have hopen : IsOpen {z : Symmetric n × (n → ℝ) | 0 < z.2 ⬝ᵥ ((z.1 : Matrix n n ℝ) *ᵥ z.2)} :=
    isOpen_lt continuous_const quadratic_continuous
  have hsphere := isCompact_sphere (0 : n → ℝ) 1
  have hsub : ({A} : Set (Symmetric n)) ×ˢ Metric.sphere (0 : n → ℝ) 1 ⊆
      {z : Symmetric n × (n → ℝ) | 0 < z.2 ⬝ᵥ ((z.1 : Matrix n n ℝ) *ᵥ z.2)} := by
    rintro ⟨M,v⟩ ⟨hM,hv⟩
    have he : M=A := hM
    subst M
    have hv0 : v ≠ 0 := by
      intro hz
      simp [hz] at hv
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos hv0
  obtain ⟨U,V,hU,_,hAU,hSV,hUV⟩ := generalized_tube_lemma isCompact_singleton hsphere hopen hsub
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hU.mem_nhds (hAU (mem_singleton A)))
  intro M hM
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using M.property
  · intro v
    simp only [star_trivial]
    by_cases hv0 : v=0
    · simp [hv0]
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    let w : n → ℝ := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : n → ℝ) 1 := by
      simp only [Metric.mem_sphere, dist_zero_right, w, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']
    have hwpos : 0 < w ⬝ᵥ ((M : Matrix n n ℝ) *ᵥ w) := hUV (show (M,w) ∈ U ×ˢ V from ⟨hM,hSV hw⟩)
    have hvscale : ‖v‖ • w=v := by simp [w, smul_smul, hvnorm.ne']
    rw [← hvscale, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    positivity

end
end SbtCosmo.Derivation.MatrixSlaterTopology
