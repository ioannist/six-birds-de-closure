"""Assemble all14 concrete response records and actual Jacobian enclosures."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT/'lean/SbtCosmo/Derivation/GroundOriginalResponses.lean'


def render():
    s = 'import SbtCosmo.Derivation.GroundOriginalSamples\n'
    s += ''.join(f'import SbtCosmo.Derivation.GroundResponses.Point{i:03d}\n' for i in range(14))
    s += '''
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
'''
    body = '(fun i => Fin.elim0 i)'
    for i in reversed(range(14)):
        p = f'GroundResponses.Point{i:03d}.'
        entry = '⟨'+', '.join(p+k for k in ['C','q','y','error','arithmetic'])+'⟩'
        body = 'Fin.cases '+entry+' (\n  '+body+')'
    s += '  '+body+'\n'
    s += '''
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
'''
    return s


if __name__ == '__main__':
    TARGET.write_text(render())
    print('Rendered14 populated response records and actual normalized-Jacobian entry return')
