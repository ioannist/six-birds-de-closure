import SbtCosmo.Derivation.NativeBoxUpdateGap
namespace SbtCosmo.Derivation.NativeBoxLastUpdateGap
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox
open GroundSourceDiagnostics NativeBoxUpdateGap

theorem last_update_gap_of_boxes {τ κ m : ℝ} {ε : ℚ} {b : Field}
    {P C : StateBox} {previous current : ComplexField}
    (hp : P.Contains (unpack previous)) (hc : C.Contains (unpack current))
    (imag positive : Bool) (i : Fin 8)
    (hgap : ε < gap P C imag positive i)
    (hstep : nativeUpdate τ b κ m previous = current) :
    (ε : ℝ) < lastUpdateResidual τ b κ m previous := by
  rw [lastUpdateResidual,hstep]
  have he : (ε : ℝ) < (gap P C imag positive i : ℝ) := by exact_mod_cast hgap
  exact he.trans_le (gap_le_update hp hc imag positive i)
end
end SbtCosmo.Derivation.NativeBoxLastUpdateGap
