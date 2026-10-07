import SbtCosmo.Derivation.GroundOriginalSamples
import SbtCosmo.Derivation.GroundResponses.Point000
import SbtCosmo.Derivation.GroundResponses.Point001
import SbtCosmo.Derivation.GroundResponses.Point002
import SbtCosmo.Derivation.GroundResponses.Point003
import SbtCosmo.Derivation.GroundResponses.Point004
import SbtCosmo.Derivation.GroundResponses.Point005
import SbtCosmo.Derivation.GroundResponses.Point006
import SbtCosmo.Derivation.GroundResponses.Point007
import SbtCosmo.Derivation.GroundResponses.Point008
import SbtCosmo.Derivation.GroundResponses.Point009
import SbtCosmo.Derivation.GroundResponses.Point010
import SbtCosmo.Derivation.GroundResponses.Point011
import SbtCosmo.Derivation.GroundResponses.Point012
import SbtCosmo.Derivation.GroundResponses.Point013

/-! Actual original normalized half-mixing Jacobian entry enclosures from
closed response arithmetic, identified thin roots, and the actual derivative.
The final theorem has only finite indices, with no supplied spectral matrix. -/
namespace SbtCosmo.Derivation.GroundOriginalResponses
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundPointCoordinates GroundKernelTube GroundKernelChain
open GroundOriginalFirstTube GroundOriginalSamples

structure Certificate (d : Data originalBackground) where
  C : Matrix (Fin 9) (Fin 9) ℚ
  q : ℚ
  y : Fin 8 → ℚ
  error : Fin 8 → ℚ
  arithmetic : GroundBorderResponse.Arithmetic originalBackground d.a d.z d.r C q y error

def certificates : (i : Fin 14) → Certificate (points i) :=
  Fin.cases ⟨GroundResponses.Point000.C, GroundResponses.Point000.q, GroundResponses.Point000.y, GroundResponses.Point000.error, GroundResponses.Point000.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point001.C, GroundResponses.Point001.q, GroundResponses.Point001.y, GroundResponses.Point001.error, GroundResponses.Point001.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point002.C, GroundResponses.Point002.q, GroundResponses.Point002.y, GroundResponses.Point002.error, GroundResponses.Point002.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point003.C, GroundResponses.Point003.q, GroundResponses.Point003.y, GroundResponses.Point003.error, GroundResponses.Point003.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point004.C, GroundResponses.Point004.q, GroundResponses.Point004.y, GroundResponses.Point004.error, GroundResponses.Point004.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point005.C, GroundResponses.Point005.q, GroundResponses.Point005.y, GroundResponses.Point005.error, GroundResponses.Point005.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point006.C, GroundResponses.Point006.q, GroundResponses.Point006.y, GroundResponses.Point006.error, GroundResponses.Point006.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point007.C, GroundResponses.Point007.q, GroundResponses.Point007.y, GroundResponses.Point007.error, GroundResponses.Point007.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point008.C, GroundResponses.Point008.q, GroundResponses.Point008.y, GroundResponses.Point008.error, GroundResponses.Point008.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point009.C, GroundResponses.Point009.q, GroundResponses.Point009.y, GroundResponses.Point009.error, GroundResponses.Point009.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point010.C, GroundResponses.Point010.q, GroundResponses.Point010.y, GroundResponses.Point010.error, GroundResponses.Point010.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point011.C, GroundResponses.Point011.q, GroundResponses.Point011.y, GroundResponses.Point011.error, GroundResponses.Point011.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point012.C, GroundResponses.Point012.q, GroundResponses.Point012.y, GroundResponses.Point012.error, GroundResponses.Point012.arithmetic⟩ (
  Fin.cases ⟨GroundResponses.Point013.C, GroundResponses.Point013.q, GroundResponses.Point013.y, GroundResponses.Point013.error, GroundResponses.Point013.arithmetic⟩ (
  (fun i => Fin.elim0 i)))))))))))))))

def enclosures (i : Fin 14) : Matrix (Fin 8) (Fin 8) GroundRationalInterval.Interval :=
  GroundBorderResponse.halfInterval originalBackground (couplings i) (points i).z (points i).r
    (certificates i).C (certificates i).error

theorem sample_arithmetic (i : Fin 14) :
    GroundBorderResponse.Arithmetic originalBackground (couplings i) (points i).z (points i).r
      (certificates i).C (certificates i).q (certificates i).y (certificates i).error := by
  simpa only [(point_bounds i).1] using (certificates i).arithmetic

theorem actual_response_error (i : Fin 14) (j : Fin 8) :
    ‖GroundBorderResponse.response (background originalBackground) (couplings i)
        (GroundOriginalContinuation.branch (couplings i)) j -
      GroundResidualEnclosure.preconditioner (certificates i).C
        (GroundBorderResponse.rhs (background originalBackground) (couplings i)
          (GroundOriginalContinuation.branch (couplings i)) j)‖ ≤ ((certificates i).error j : ℝ) :=
  GroundBorderResponse.arithmetic_response_error (sample_arithmetic i)
    (branch_in_sample_ball i) (sample_ground_return i).2.2.2.1 j

theorem actual_half_entries (i : Fin 14) (a j : Fin 8) :
    (enclosures i a j).Contains
      (GroundNormalizedJacobian.normalizedJacobian (background originalBackground) (couplings i) (1/2)
        (GroundOriginalContinuation.branch (couplings i)).1 (GroundLocalDynamics.column j) a) :=
  GroundBorderResponse.halfInterval_sound (sample_arithmetic i) (branch_in_sample_ball i)
    (sample_ground_return i).2.2.2.1 (sample_ground_return i).2.2.2.2 a j

end
end SbtCosmo.Derivation.GroundOriginalResponses
