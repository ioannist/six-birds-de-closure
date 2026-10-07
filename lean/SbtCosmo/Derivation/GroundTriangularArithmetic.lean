import SbtCosmo.Derivation.GroundTriangularSign

/-! Integer product identities return to exact rational triangular factors.
Positive denominators are earned obligations, including before cancellation. -/
namespace SbtCosmo.Derivation.GroundTriangularArithmetic
noncomputable section
set_option maxHeartbeats 2000000
open GroundMatrixCoordinates OrderDual
open scoped BigOperators
abbrev ZMatrix := Matrix (Fin 8) (Fin 8) ℤ

def scaled (A : ZMatrix) (d : ℤ) : QMatrix := fun i j => (A i j : ℚ) / (d : ℚ)

structure Arithmetic (C L U : ZMatrix) (dC dL dU s : ℤ) : Prop where
  c_pos : 0 < dC
  l_pos : 0 < dL
  u_pos : 0 < dU
  product : dC • (L * U) = (dL * dU) • C
  lower : ∀ i j, i < j → L i j = 0
  upper : ∀ i j, j < i → U i j = 0
  diagonal : ∀ i, L i i = dL
  sign : 0 < s * (∏ i, U i i)

theorem scaled_product {C L U : ZMatrix} {dC dL dU s : ℤ}
    (h : Arithmetic C L U dC dL dU s) :
    scaled L dL * scaled U dU = scaled C dC := by
  have hc : (dC : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt h.c_pos
  have hl : (dL : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt h.l_pos
  have hu : (dU : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt h.u_pos
  ext i j
  have he := congrFun (congrFun h.product i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at he
  have heq : (dC : ℚ) * (∑ k, (L i k : ℚ) * (U k j : ℚ)) =
      (dL : ℚ) * (dU : ℚ) * (C i j : ℚ) := by exact_mod_cast he
  change (∑ k, ((L i k : ℚ) / (dL : ℚ)) * ((U k j : ℚ) / (dU : ℚ))) = (C i j : ℚ) / (dC : ℚ)
  calc
    _ = (∑ k, (L i k : ℚ) * (U k j : ℚ)) / ((dL : ℚ) * (dU : ℚ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    _ = _ := by
      apply (div_eq_div_iff (mul_ne_zero hl hu) hc).mpr
      calc
        _ = (dC : ℚ) * (∑ k, (L i k : ℚ) * (U k j : ℚ)) := mul_comm _ _
        _ = _ := heq
        _ = _ := mul_comm _ _

theorem triangular_return {C L U : ZMatrix} {dC dL dU s : ℤ}
    (h : Arithmetic C L U dC dL dU s) :
    GroundTriangularSign.Arithmetic (realMatrix (scaled C dC))
      (realMatrix (scaled L dL)) (realMatrix (scaled U dU)) := by
  have hl : (dL : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt h.l_pos
  constructor
  · rw [← realMatrix_mul, scaled_product h]
  · intro i j hij
    have hz := h.lower i j hij
    simp [realMatrix, scaled, hz]
  · intro i j hij
    have hz := h.upper i j hij
    simp [realMatrix, scaled, hz]
  · intro i
    simp [realMatrix, scaled, h.diagonal i, hl]

theorem determinant_sign {C L U : ZMatrix} {dC dL dU s : ℤ}
    (h : Arithmetic C L U dC dL dU s) :
    0 < (s : ℝ) * (realMatrix (scaled C dC)).det := by
  rw [GroundTriangularSign.determinant_return (triangular_return h)]
  have hp : 0 < (dU : ℝ) := by exact_mod_cast h.u_pos
  have hs : 0 < (s : ℝ) * (∏ i, (U i i : ℝ)) := by exact_mod_cast h.sign
  simpa only [realMatrix, scaled, Rat.cast_div, Rat.cast_intCast,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_div_assoc] using div_pos hs (pow_pos hp 8)
end
end SbtCosmo.Derivation.GroundTriangularArithmetic
