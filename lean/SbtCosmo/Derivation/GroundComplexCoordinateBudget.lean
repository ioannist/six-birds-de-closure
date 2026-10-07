import SbtCosmo.Derivation.GroundComplexEuclidean
namespace SbtCosmo.Derivation.GroundComplexCoordinateBudget
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
open GroundState GroundNativePhase GroundComplexEuclidean
open scoped BigOperators

theorem real_component_le_l2 (z : ComplexField) (i : Fin 8) : |(z i).re| ≤ l2 z := by
  have h := Finset.single_le_sum (fun (j : Fin 8) (_ : j ∈ Finset.univ) =>
    (show 0 ≤ Complex.normSq (z j) from Complex.normSq_nonneg _)) (Finset.mem_univ i)
  change Complex.normSq (z i) ≤ complexNormSq z at h
  rw [Complex.normSq_apply,← l2_sq] at h
  have hp := l2_nonneg z
  have ha := abs_nonneg (z i).re
  have he : |(z i).re|^2 = (z i).re^2 := sq_abs _
  nlinarith [sq_nonneg (z i).im]

theorem imag_component_le_l2 (z : ComplexField) (i : Fin 8) : |(z i).im| ≤ l2 z := by
  have h := Finset.single_le_sum (fun (j : Fin 8) (_ : j ∈ Finset.univ) =>
    (show 0 ≤ Complex.normSq (z j) from Complex.normSq_nonneg _)) (Finset.mem_univ i)
  change Complex.normSq (z i) ≤ complexNormSq z at h
  rw [Complex.normSq_apply,← l2_sq] at h
  have hp := l2_nonneg z
  have ha := abs_nonneg (z i).im
  have he : |(z i).im|^2 = (z i).im^2 := sq_abs _
  nlinarith [sq_nonneg (z i).re]

end
end SbtCosmo.Derivation.GroundComplexCoordinateBudget
