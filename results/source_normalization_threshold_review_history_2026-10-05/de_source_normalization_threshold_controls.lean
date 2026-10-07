import SbtCosmo.Derivation.GroundSourceNormalization

namespace SourceNormalizationThresholdReview
open SbtCosmo.Derivation.GroundState
open SbtCosmo.Derivation.GroundNativeIteration
open SbtCosmo.Derivation.GroundSourceNormalization
set_option warningAsError true

def basis : ComplexField := fun i => if i = 0 then 1 else 0

theorem basis_unit : complexNormSq basis = 1 := by
  norm_num [basis, complexNormSq, Fin.sum_univ_succ]

theorem negative_threshold_accepts_zero : attempt (-1) (0 : ComplexField) = some 0 := by
  simp [attempt, complexNormSq, complexNormalize]

theorem accepted_zero_is_not_unit : complexNormSq (0 : ComplexField) ≠ 1 := by
  simp [complexNormSq]

theorem zero_threshold_rejects_zero : attempt 0 (0 : ComplexField) = none :=
  zero_rejected le_rfl

theorem unit_at_threshold_one_is_rejected : attempt 1 basis = none := by
  simp [attempt, basis_unit]

#check negative_threshold_accepts_zero
#print axioms negative_threshold_accepts_zero
#check accepted_zero_is_not_unit
#print axioms accepted_zero_is_not_unit
#check zero_threshold_rejects_zero
#print axioms zero_threshold_rejects_zero
#check unit_at_threshold_one_is_rejected
#print axioms unit_at_threshold_one_is_rejected
end SourceNormalizationThresholdReview
