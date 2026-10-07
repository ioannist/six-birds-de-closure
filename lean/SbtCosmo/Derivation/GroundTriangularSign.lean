import SbtCosmo.Derivation.GroundMatrixCoordinates
import Mathlib.LinearAlgebra.Matrix.Block
namespace SbtCosmo.Derivation.GroundTriangularSign
noncomputable section
open GroundMatrixCoordinates OrderDual
open scoped BigOperators
structure Arithmetic (C L U : RMatrix) : Prop where
  product : L * U = C
  lower : L.BlockTriangular (@toDual (Fin 8))
  upper : U.BlockTriangular id
  diagonal : ∀ i, L i i = 1

theorem determinant_return {C L U : RMatrix} (h : Arithmetic C L U) :
    C.det = ∏ i, U i i := by
  rw [← h.product, Matrix.det_mul, Matrix.det_of_lowerTriangular L h.lower,
    Matrix.det_of_upperTriangular h.upper]
  have hl : (∏ i, L i i) = 1 := by simp [h.diagonal]
  rw [hl, one_mul]
end
end SbtCosmo.Derivation.GroundTriangularSign
