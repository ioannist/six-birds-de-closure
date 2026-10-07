import SbtCosmo.Derivation.GroundComplexFiniteBudget
import SbtCosmo.Derivation.GroundComplexCoordinateBudget
namespace SbtCosmo.Derivation.NativeBoxUpdateGap
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean
open GroundNativeBox GroundRationalInterval GroundComplexCoordinateBudget GroundSourceDiagnostics

def component (z : ComplexField) (imag : Bool) (i : Fin 8) : ℝ :=
  if imag then (z i).im else (z i).re
def coordinateInterval (B : StateBox) (imag : Bool) (i : Fin 8) : Interval :=
  if imag then B.I i else B.R i
def gap (previous current : StateBox) (imag positive : Bool) (i : Fin 8) : ℚ :=
  if positive then (coordinateInterval current imag i).lo-(coordinateInterval previous imag i).hi
  else (coordinateInterval previous imag i).lo-(coordinateInterval current imag i).hi

theorem component_le (z : ComplexField) (imag : Bool) (i : Fin 8) :
    |component z imag i| ≤ l2 z := by
  cases imag
  · exact real_component_le_l2 z i
  · exact imag_component_le_l2 z i

theorem component_sub (current previous : ComplexField) (imag : Bool) (i : Fin 8) :
    component (current-previous) imag i = component current imag i-component previous imag i := by
  cases imag <;> simp [component]

theorem component_enclosed {B : StateBox} {z : ComplexField}
    (hz : B.Contains (unpack z)) (imag : Bool) (i : Fin 8) :
    (coordinateInterval B imag i).Contains (component z imag i) := by
  cases imag
  · exact (hz i).1
  · exact (hz i).2

/-- Both endpoint radii enter the interval gap, in either sign and either part. -/
theorem gap_le_update {P C : StateBox} {previous current : ComplexField}
    (hp : P.Contains (unpack previous)) (hc : C.Contains (unpack current))
    (imag positive : Bool) (i : Fin 8) :
    (gap P C imag positive i : ℝ) ≤ l2 (current-previous) := by
  have hprev := component_enclosed hp imag i
  have hcur := component_enclosed hc imag i
  have ha := component_le (current-previous) imag i
  rw [component_sub] at ha
  have hpos := le_abs_self (component current imag i-component previous imag i)
  have hneg := neg_le_abs (component current imag i-component previous imag i)
  cases positive <;> simp only [gap, Bool.false_eq_true, ↓reduceIte, Rat.cast_sub]
  · linarith [hprev.1,hcur.2]
  · linarith [hcur.1,hprev.2]

theorem tests_fail_of_gap {τ κ m : ℝ} {ε : ℚ} {b : Field}
    {P C : StateBox} {previous current : ComplexField}
    (hp : P.Contains (unpack previous)) (hc : C.Contains (unpack current))
    (imag positive : Bool) (i : Fin 8)
    (hgap : ε < gap P C imag positive i)
    (hstep : nativeUpdate τ b κ m previous = current) :
    ¬ MeetsConvergence τ (ε : ℝ) b κ m previous current := by
  apply GroundComplexFiniteBudget.fails_of_update hstep
  have he : (ε : ℝ) < (gap P C imag positive i : ℝ) := by exact_mod_cast hgap
  exact he.trans_le (gap_le_update hp hc imag positive i)
end
end SbtCosmo.Derivation.NativeBoxUpdateGap
