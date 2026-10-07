import SbtCosmo.Derivation.NativeCycleSeed20.Step000
import SbtCosmo.Derivation.GroundOffsetPrefixInitial
namespace SbtCosmo.Derivation.NativeCycleSeed20.Initial
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundNativeTransportGeometry GroundCertifiedNativeEntry Metric

def radius : ℚ := (1/1606938044258990275541962092341162602522202993782792835301376)

theorem initial_arithmetic : 0 ≤ radius ∧ ∀ i : Fin 8,
    ((Step000.certificate.coordinateBox (differenceBox GroundOffsetPrefixInitial.initialBox
      (around Step000.u Step000.v 0 0))).R i).bound ≤ radius ∧
    ((Step000.certificate.coordinateBox (differenceBox GroundOffsetPrefixInitial.initialBox
      (around Step000.u Step000.v 0 0))).I i).bound ≤ radius := by decide +kernel

/-- The actual original complex seed, with both source initial normalizations.
This is an earned enclosure, not an initial-state hypothesis. -/
theorem original_seed_enclosed : NativeCycleFrame20.T.symm (unpack GroundOriginalSeed.initial) ∈
    closedBall Step000.transport.center (Step000.ρ : ℝ) := by
  rw [mem_closedBall]
  exact coordinate_distance Step000.certificate initial_arithmetic.1
    GroundOffsetPrefixInitial.original_seed_enclosed
    (point_enclosed Step000.u Step000.v (by norm_num : (0 : ℚ) ≤ 0) (by norm_num : (0 : ℚ) ≤ 0))
    initial_arithmetic.2
end
end SbtCosmo.Derivation.NativeCycleSeed20.Initial
