import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
An explicit Schmidt-diagonal two-qubit carrier and one-index tensor contraction.
Entropy is computed from the squared Schmidt coefficients of a normalized state.
The construction refutes a universal min-plus law for this entropy readout.
It is not a theorem about all quantum states or a continuum RT relation.
-/
namespace SbtCosmo.Derivation.TensorComposition
noncomputable section
open scoped BigOperators

/-- Coefficients of |00> and |11>; other coefficients are zero. -/
def pairTensor (amplitude : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal amplitude

/-- Squared norm of this diagonal bipartite state. -/
def pairMass (amplitude : Fin 2 → ℝ) : ℝ := ∑ i, amplitude i ^ 2

def pairWeight (amplitude : Fin 2 → ℝ) : ℝ := amplitude 0 ^ 2 / pairMass amplitude

/-- Entropy of the normalized squared Schmidt coefficients. -/
def pairEntropy (amplitude : Fin 2 → ℝ) : ℝ := Real.binEntropy (pairWeight amplitude)

def pairNormalize (amplitude : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => amplitude i / Real.sqrt (pairMass amplitude)

/-- This is actual contraction over the common index, not a prescribed readout. -/
theorem pair_tensor_contraction (left right : Fin 2 → ℝ) :
    pairTensor left * pairTensor right = pairTensor (fun i => left i * right i) := by
  exact Matrix.diagonal_mul_diagonal left right

/-- The reduced Gram operator really has the squared amplitudes on its diagonal. -/
theorem pair_reduced_gram (amplitude : Fin 2 → ℝ) :
    pairTensor amplitude * (pairTensor amplitude).transpose =
      Matrix.diagonal (fun i => amplitude i ^ 2) := by
  simp only [pairTensor, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, pow_two]

theorem pair_trace_mass (amplitude : Fin 2 → ℝ) :
    Matrix.trace (pairTensor amplitude * (pairTensor amplitude).transpose) = pairMass amplitude := by
  rw [pair_reduced_gram]
  simp [Matrix.trace, pairMass]

theorem pair_mass_nonnegative (amplitude : Fin 2 → ℝ) : 0 ≤ pairMass amplitude := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (amplitude i))

theorem pair_weight_mem_unit {amplitude : Fin 2 → ℝ} (hm : 0 < pairMass amplitude) :
    pairWeight amplitude ∈ Set.Icc (0 : ℝ) 1 := by
  have he : pairMass amplitude = amplitude 0 ^ 2 + amplitude 1 ^ 2 := by
    simp [pairMass, Fin.sum_univ_two]
  refine ⟨div_nonneg (sq_nonneg _) hm.le, (div_le_one hm).mpr ?_⟩
  rw [he]
  nlinarith [sq_nonneg (amplitude 1)]

theorem pair_normalize_mass {amplitude : Fin 2 → ℝ} (hm : 0 < pairMass amplitude) :
    pairMass (pairNormalize amplitude) = 1 := by
  have hs : Real.sqrt (pairMass amplitude) ^ 2 = pairMass amplitude := Real.sq_sqrt hm.le
  change (∑ i, (amplitude i / Real.sqrt (pairMass amplitude)) ^ 2) = 1
  simp only [div_pow]
  rw [hs, ← Finset.sum_div]
  exact div_self hm.ne'

theorem pair_normalize_weight {amplitude : Fin 2 → ℝ} (hm : 0 < pairMass amplitude) :
    pairWeight (pairNormalize amplitude) = pairWeight amplitude := by
  rw [pairWeight, pair_normalize_mass hm, div_one]
  simp only [pairNormalize, div_pow, Real.sq_sqrt hm.le, pairWeight]

/-- A unit-norm nonmaximally entangled pair, with squared Schmidt weights 3/4,1/4. -/
def inputAmplitude : Fin 2 → ℝ := ![Real.sqrt (3/4), Real.sqrt (1/4)]

def contractedAmplitude : Fin 2 → ℝ := ![(3/4), (1/4)]

theorem input_mass : pairMass inputAmplitude = 1 := by
  simp only [pairMass, Fin.sum_univ_two]
  change Real.sqrt (3/4) ^ 2 + Real.sqrt (1/4) ^ 2 = 1
  rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

theorem input_weight : pairWeight inputAmplitude = 3/4 := by
  rw [pairWeight, input_mass]
  change Real.sqrt (3/4) ^ 2 / 1 = 3/4
  rw [Real.sq_sqrt (by norm_num), div_one]

theorem input_reduced_gram :
    pairTensor inputAmplitude * (pairTensor inputAmplitude).transpose =
      Matrix.diagonal ![(3/4 : ℝ), (1/4)] := by
  rw [pair_reduced_gram]
  congr 1
  funext i
  fin_cases i
  · change Real.sqrt (3/4) ^ 2 = 3/4
    rw [Real.sq_sqrt (by norm_num)]
  · change Real.sqrt (1/4) ^ 2 = 1/4
    rw [Real.sq_sqrt (by norm_num)]

theorem input_self_contraction :
    pairTensor inputAmplitude * pairTensor inputAmplitude = pairTensor contractedAmplitude := by
  rw [pair_tensor_contraction]
  congr 1
  funext i
  fin_cases i
  · change Real.sqrt (3/4) * Real.sqrt (3/4) = 3/4
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  · change Real.sqrt (1/4) * Real.sqrt (1/4) = 1/4
    rw [← pow_two, Real.sq_sqrt (by norm_num)]

theorem contracted_mass : pairMass contractedAmplitude = 5/8 := by
  norm_num [pairMass, contractedAmplitude, Fin.sum_univ_two]

theorem contracted_weight : pairWeight contractedAmplitude = 9/10 := by
  rw [pairWeight, contracted_mass]
  norm_num [contractedAmplitude]

theorem normalized_contraction_is_unit : pairMass (pairNormalize contractedAmplitude) = 1 := by
  apply pair_normalize_mass
  rw [contracted_mass]
  norm_num

theorem normalized_contraction_gram :
    pairTensor (pairNormalize contractedAmplitude) *
      (pairTensor (pairNormalize contractedAmplitude)).transpose =
        Matrix.diagonal ![(9/10 : ℝ), (1/10)] := by
  rw [pair_reduced_gram]
  congr 1
  funext i
  simp only [pairNormalize, div_pow, contracted_mass, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/8)]
  fin_cases i <;> norm_num [contractedAmplitude]

theorem contraction_entropy_strictly_decreases :
    pairEntropy (pairNormalize contractedAmplitude) < pairEntropy inputAmplitude := by
  unfold pairEntropy
  rw [pair_normalize_weight (by rw [contracted_mass]; norm_num), contracted_weight, input_weight]
  apply Real.binEntropy_strictAntiOn (by norm_num) (by norm_num) (by norm_num)

/-- Identical-input min-plus would preserve the entropy, but actual contraction does not. -/
theorem entropy_not_minplus :
    pairEntropy (pairNormalize contractedAmplitude) ≠
      min (pairEntropy inputAmplitude) (pairEntropy inputAmplitude) := by
  rw [min_self]
  exact ne_of_lt contraction_entropy_strictly_decreases

/-- Whole/empty cuts of a pure pair have zero entropy; either split has this Schmidt entropy. -/
def boundaryEntropy (amplitude : Fin 2 → ℝ) (first second : Bool) : ℝ :=
  if first = second then 0 else pairEntropy amplitude

/-- Min-plus gluing minimizes over the two placements of the common boundary index. -/
def boundaryMinplus (left right : Fin 2 → ℝ) : ℝ :=
  min (boundaryEntropy left true false + boundaryEntropy right false false)
    (boundaryEntropy left true true + boundaryEntropy right true false)

theorem identical_boundary_minplus (amplitude : Fin 2 → ℝ) :
    boundaryMinplus amplitude amplitude = pairEntropy amplitude := by
  simp [boundaryMinplus, boundaryEntropy]

theorem entropy_not_boundary_minplus :
    pairEntropy (pairNormalize contractedAmplitude) ≠ boundaryMinplus inputAmplitude inputAmplitude := by
  rw [identical_boundary_minplus]
  exact ne_of_lt contraction_entropy_strictly_decreases

end
end SbtCosmo.Derivation.TensorComposition
