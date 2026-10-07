import SbtCosmo.Derivation.GroundCoordinates.Point009

/-! False-target controls for the actual basis and induced row tests. -/
namespace SbtCosmo.Derivation.GroundCoordinateControls
noncomputable section
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
open GroundMatrixCoordinates GroundCoordinates.Point009
open scoped BigOperators

theorem zero_inverse_rejected : ¬ InverseArithmetic S 0 := by
  intro h
  have he := congrFun (congrFun h.left 0) 0
  norm_num [Matrix.mul_apply, Matrix.one_apply] at he

theorem zero_row_budget_rejected : ¬ RowArithmetic S P realBox 0 := by
  intro h
  have hn : ¬ ((∑ j, (transformed S P realBox 0 j).bound) ≤ 0) := by
    decide +kernel
  exact hn (h.rows 0)

end
end SbtCosmo.Derivation.GroundCoordinateControls
