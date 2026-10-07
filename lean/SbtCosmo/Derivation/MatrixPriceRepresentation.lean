import SbtCosmo.Adequacy.Support
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Construct the trace representative of a linear price on the real symmetric budget space. -/
namespace SbtCosmo.Derivation.MatrixPriceRepresentation
noncomputable section
open Matrix
open scoped Matrix

variable (n : Type*)

def symmetricSubmodule : Submodule ℝ (Matrix n n ℝ) where
  carrier := {M | M.transpose = M}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A.transpose = A at hA
    change B.transpose = B at hB
    change (A+B).transpose = A+B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' := by
    intro a A hA
    change A.transpose = A at hA
    change (a • A).transpose = a • A
    rw [Matrix.transpose_smul, hA]

abbrev Symmetric := symmetricSubmodule n

variable {n}

def symmetrize : Matrix n n ℝ →ₗ[ℝ] Symmetric n where
  toFun M := ⟨(1/2 : ℝ) • (M+M.transpose), by
    change ((1/2 : ℝ) • (M+M.transpose)).transpose = (1/2 : ℝ) • (M+M.transpose)
    simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
    rw [add_comm]⟩
  map_add' A B := by
    apply Subtype.ext
    change (1/2 : ℝ) • ((A+B)+(A+B).transpose) = (1/2 : ℝ) • (A+A.transpose)+(1/2 : ℝ) • (B+B.transpose)
    simp only [Matrix.transpose_add]
    module
  map_smul' a A := by
    apply Subtype.ext
    change (1/2 : ℝ) • (a • A+(a • A).transpose) = a • ((1/2 : ℝ) • (A+A.transpose))
    simp only [Matrix.transpose_smul]
    module

theorem symmetrize_symmetric (M : Symmetric n) : symmetrize (M : Matrix n n ℝ) = M := by
  apply Subtype.ext
  have hM : (M : Matrix n n ℝ).transpose = M := M.property
  simp only [symmetrize, LinearMap.coe_mk, AddHom.coe_mk, hM]
  module

theorem symmetrize_transpose (M : Matrix n n ℝ) : symmetrize M.transpose = symmetrize M := by
  apply Subtype.ext
  simp only [symmetrize, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_transpose]
  rw [add_comm]

variable [Fintype n] [DecidableEq n]

def priceMatrix (p : Symmetric n →ₗ[ℝ] ℝ) : Matrix n n ℝ :=
  fun i j => p (symmetrize (Matrix.single j i 1))

omit [Fintype n] in
theorem price_matrix_symmetric (p : Symmetric n →ₗ[ℝ] ℝ) :
    (priceMatrix p).IsHermitian := by
  change (priceMatrix p).conjTranspose = priceMatrix p
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, priceMatrix]
  rw [← Matrix.transpose_single, symmetrize_transpose]

theorem trace_representation (p : Symmetric n →ₗ[ℝ] ℝ) (M : Symmetric n) :
    trace (priceMatrix p * (M : Matrix n n ℝ)) = p M := by
  have hsingle (i j : n) (a : ℝ) : Matrix.single i j a = a • Matrix.single i j 1 := by
    ext k l
    simp [Matrix.single]
  have hsum : p M = ∑ i, ∑ j, (M : Matrix n n ℝ) i j * p (symmetrize (Matrix.single i j 1)) := by
    nth_rw 1 [← symmetrize_symmetric M]
    conv_lhs => rw [Matrix.matrix_eq_sum_single (M : Matrix n n ℝ)]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsingle, map_smul, map_smul, smul_eq_mul]
  rw [hsum]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, priceMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq n] in
theorem rank_one_pairing (P : Matrix n n ℝ) (v : n → ℝ) :
    trace (P * Matrix.vecMulVec v v) = v ⬝ᵥ (P *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity on actual PSD directions constructs a PSD trace representative. -/
theorem price_matrix_positive (p : Symmetric n →ₗ[ℝ] ℝ)
    (hpositive : ∀ M : Symmetric n, (M : Matrix n n ℝ).PosSemidef → 0 ≤ p M) :
    (priceMatrix p).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (price_matrix_symmetric p)
  intro v
  let M : Symmetric n := ⟨Matrix.vecMulVec v v, by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
    ring⟩
  have hM : (M : Matrix n n ℝ).PosSemidef := by
    simpa only [M, star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  have h := hpositive M hM
  rw [← trace_representation p M] at h
  simpa only [M, rank_one_pairing, star_trivial] using h

theorem price_matrix_nonzero (p : Symmetric n →ₗ[ℝ] ℝ) {M : Symmetric n}
    (hM : 0 < p M) : priceMatrix p ≠ 0 := by
  intro hzero
  have h := trace_representation p M
  rw [hzero, Matrix.zero_mul, Matrix.trace_zero] at h
  linarith

end
end SbtCosmo.Derivation.MatrixPriceRepresentation
