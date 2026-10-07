import SbtCosmo.Derivation.SchurClosurePrice
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Inhabited actual Schur-budget program: its optimum, finite value and derivative are constructed. -/
namespace SbtCosmo.Derivation.SchurClosurePriceExamples
noncomputable section
open Matrix Set ConvexClosurePrice SchurClosurePrice
open scoped Matrix Topology

def probe : ℝ →ᵃ[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
  (show ℝ →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℝ from
    { toFun := fun x => fun _ _ => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toAffineMap

def energy (x : ℝ) : ℝ := schurEnergy (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (probe x)
def objective (x : ℝ) : ℝ := (x-2)^2

theorem energy_eq (x : ℝ) : energy x = x^2 := by
  rw [energy, schurEnergy, SbtCosmo.Adequacy.Support.residual_zero_native]
  norm_num [probe, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Fin.sum_univ_succ, pow_two]

theorem objective_convex : ConvexOn ℝ univ objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [objective, smul_eq_mul]
  have he : (a*x+b*y-2)^2 = a*(x-2)^2+b*(y-2)^2-a*b*(x-y)^2 := by
    linear_combination (a*x^2+b*y^2-4)*hab
  have hn := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
  linarith

theorem local_finiteness {T : ℝ} (hT : 0 < T) :
    (feasibleCosts univ objective energy T).Nonempty ∧ BddBelow (feasibleCosts univ objective energy T) := by
  constructor
  · refine ⟨objective 0, 0, mem_univ _, ?_, rfl⟩
    rw [energy_eq]
    simpa using hT.le
  · refine ⟨0, ?_⟩
    rintro r ⟨x, _, _, rfl⟩
    exact sq_nonneg (x-2)

theorem sqrt_primal_optimum {B : ℝ} (hB : 0 < B) (hupper : B < 4) :
    PrimalOptimum univ objective energy B (Real.sqrt B) := by
  have hs := Real.sq_sqrt hB.le
  have hp := Real.sqrt_nonneg B
  have hu : Real.sqrt B < 2 := by nlinarith
  refine ⟨mem_univ _, ?_, ?_⟩
  · rw [energy_eq, hs]
  · intro x _ hx
    rw [energy_eq] at hx
    have hxs : x ≤ Real.sqrt B := by nlinarith
    dsimp [objective]
    nlinarith [sq_nonneg (x-Real.sqrt B)]

theorem actual_value_formula {B : ℝ} (hB : 0 < B) (hupper : B < 4) :
    budgetValue univ objective energy B = (Real.sqrt B-2)^2 :=
  optimum_value (sqrt_primal_optimum hB hupper)

theorem actual_value_derivative : HasDerivAt (budgetValue univ objective energy) (-1) 1 := by
  have hs := (Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)).sub_const 2
  have hd := hs.pow 2
  have he : budgetValue univ objective energy =ᶠ[𝓝 (1 : ℝ)] (fun B => (Real.sqrt B-2)^2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Ioo 0 4)] with B hB
    exact actual_value_formula hB.1 hB.2
  convert hd.congr_of_eventuallyEq he using 1
  norm_num

/-- No local-finiteness or derivative input is supplied in this actual singular-native instance. -/
theorem actual_positive_schur_certificate :
    DualCertificate univ objective energy 1 1 1 ∧ energy 1 = 1 ∧
      dualValue univ objective energy 1 1 = budgetValue univ objective energy 1 := by
  have hp : PrimalOptimum univ objective energy 1 1 := by
    simpa using sqrt_primal_optimum (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 4)
  have henergy : ConvexOn ℝ univ energy :=
    affine_schur_energy_convex Matrix.PosSemidef.one (0 : Matrix (Fin 1) (Fin 1) ℝ) probe convex_univ
  obtain ⟨p, heq, _, hc⟩ := positive_price_certificate objective_convex henergy hp
    (by norm_num : (1 : ℝ) ∈ Ioo 0 4) (fun T hT => local_finiteness hT.1)
    actual_value_derivative (by norm_num : (-1 : ℝ) < 0)
  norm_num at heq
  subst p
  exact ⟨hc, by norm_num [energy_eq], certificate_strong_duality hc⟩

/-- Slater is explicitly inhabited; the native Gram block is nevertheless singular. -/
theorem actual_slater_and_singular_native : energy 0 < (1 : ℝ) ∧
    ¬ IsUnit ((0 : Matrix (Fin 1) (Fin 1) ℝ) * (0 : Matrix (Fin 1) (Fin 1) ℝ)ᴴ) := by
  constructor
  · norm_num [energy_eq]
  · simp

def varyingNativeEnergy (x : ℝ) : ℝ := schurEnergy (1 : Matrix (Fin 1) (Fin 1) ℝ)
  (SbtCosmo.Adequacy.Reconciliation.oneByOne x) 1

/-- Varying the native family can destroy convexity even with affine probe entries. -/
theorem varying_native_values : varyingNativeEnergy 1 = 0 ∧ varyingNativeEnergy (-1) = 0 ∧
    varyingNativeEnergy 0 = 1 := by
  have h1 : SbtCosmo.Adequacy.Reconciliation.oneByOne 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j; fin_cases i; fin_cases j; norm_num [SbtCosmo.Adequacy.Reconciliation.oneByOne]
  have hn : SbtCosmo.Adequacy.Reconciliation.oneByOne (-1) = (-1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j; fin_cases i; fin_cases j; norm_num [SbtCosmo.Adequacy.Reconciliation.oneByOne]
  have h0 : SbtCosmo.Adequacy.Reconciliation.oneByOne 0 = (0 : Matrix (Fin 1) (Fin 1) ℝ) := rfl
  have hp := (SbtCosmo.Adequacy.Support.residual_zero_iff_factor
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)).mpr ⟨1, by simp⟩
  have hm := (SbtCosmo.Adequacy.Support.residual_zero_iff_factor
    (-1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)).mpr ⟨-1, by simp⟩
  simp only [varyingNativeEnergy, h1, hn, h0, schurEnergy, hp, hm,
    SbtCosmo.Adequacy.Support.residual_zero_native]
  norm_num [Matrix.trace, Fin.sum_univ_succ]

theorem varying_native_nonconvex : ¬ ConvexOn ℝ univ varyingNativeEnergy := by
  intro h
  have hm := h.2 (mem_univ (1 : ℝ)) (mem_univ (-1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+(1/2 : ℝ)=1)
  norm_num [smul_eq_mul, varying_native_values.1, varying_native_values.2.1, varying_native_values.2.2] at hm

end
end SbtCosmo.Derivation.SchurClosurePriceExamples
