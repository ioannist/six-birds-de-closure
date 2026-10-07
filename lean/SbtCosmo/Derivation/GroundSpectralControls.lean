import SbtCosmo.Derivation.GroundSpectralTests.Test003

/-! False certificates exercise the actual determinant-sign mechanism. -/
namespace SbtCosmo.Derivation.GroundSpectralControls
noncomputable section
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
open GroundMatrixCoordinates GroundSpectralEnclosure GroundTriangularArithmetic
open GroundSpectralTests.Test003
open scoped BigOperators

theorem zero_preconditioner_rejected :
    ¬ GroundSpectralEnclosure.Arithmetic 0 (shifted B ell) (1/1000) := by
  intro h
  have hn : ¬ ((∑ j, (defects 0 (shifted B ell) 0 j).bound) ≤ (1/1000 : ℚ)) := by
    decide +kernel
  exact hn (h.rows 0)

theorem reversed_sign_rejected :
    ¬ GroundTriangularArithmetic.Arithmetic CI LI UI dc dl du (-sign) := by
  intro h
  have hp := factor_arithmetic.sign
  have hn := h.sign
  rw [neg_mul] at hn
  omega

end
end SbtCosmo.Derivation.GroundSpectralControls
