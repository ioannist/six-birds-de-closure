import SbtCosmo.Derivation.GroundResponses.Point010

/-! Substantive false-certificate controls on the original coupling20 response.
Zero preconditioning cannot earn the border defect; deleting its positive
response-error budget cannot satisfy the actual remainder comparison. -/
namespace SbtCosmo.Derivation.GroundResponseControls
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundBorderResponse GroundRationalInterval GroundKernelTube GroundOriginalFirstTube
open scoped BigOperators

theorem zero_border_preconditioner_rejected :
    ¬GroundBorderResponse.Arithmetic originalBackground GroundSamples.Point010.a GroundSamples.Point010.z
      GroundSamples.Point010.r (fun _ _ => 0) GroundResponses.Point010.q
      GroundResponses.Point010.y GroundResponses.Point010.error := by
  intro h
  have hb := h.defect_rows (0 : Fin 9)
  have hn : ¬(∑ j, ((borderDefectExpr (fun _ _ => 0) (0 : Fin 9) j).enclose
      (box originalBackground GroundSamples.Point010.a GroundSamples.Point010.a
        GroundSamples.Point010.z GroundSamples.Point010.r)).bound) ≤ GroundResponses.Point010.q := by
    decide +kernel
  exact hn hb

theorem zero_error_budget_rejected :
    ¬GroundBorderResponse.Arithmetic originalBackground GroundSamples.Point010.a GroundSamples.Point010.z
      GroundSamples.Point010.r GroundResponses.Point010.C GroundResponses.Point010.q
      GroundResponses.Point010.y (fun _ => 0) := by
  intro h
  have hb := h.budget (0 : Fin 8)
  have hn : ¬GroundResponses.Point010.q * GroundResponses.Point010.y 0 ≤
      (0 : ℚ)*(1-GroundResponses.Point010.q) := by
    decide +kernel
  exact hn hb

end
end SbtCosmo.Derivation.GroundResponseControls
