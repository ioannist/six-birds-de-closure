"""Reify a fully populated finite family of actual derivative norm returns."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'lean/SbtCosmo/Derivation/GroundOriginalCoordinates.lean'


def render():
    s='import SbtCosmo.Derivation.GroundMatrixCoordinates\n'
    for i in range(12):s+=f'import SbtCosmo.Derivation.GroundCoordinates.Point{i:03d}\n'
    s+='''
/-! Concrete coordinate norm bounds at all12 original coupling samples,
and actual native complex local attraction at the10 contracting samples. -/
namespace SbtCosmo.Derivation.GroundOriginalCoordinates
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundKernelTube GroundOriginalFirstTube GroundOriginalSamples
open GroundMatrixCoordinates GroundNativeLocal
open Filter Metric
open scoped Topology BigOperators

def sampleIndex (i : Fin 12) : Fin 14 := i.castLE (by decide)

structure Certificate (i : Fin 12) where
  S : QMatrix
  P : QMatrix
  R : QMatrix
  Q : QMatrix
  rate : ℚ
  real_inverse : InverseArithmetic S P
  imag_inverse : InverseArithmetic R Q
  real_rows : RowArithmetic S P (GroundOriginalResponses.enclosures (sampleIndex i)) rate
  imag_rows : RowArithmetic R Q
    (imaginaryIntervals originalBackground (couplings (sampleIndex i))
      (points (sampleIndex i)).z (points (sampleIndex i)).r) (501/1000)

def certificates : (i : Fin 12) → Certificate i :=
'''
    for i in range(12):
        n=f'GroundCoordinates.Point{i:03d}'
        s+=f'''  Fin.cases ⟨{n}.S, {n}.P, {n}.R, {n}.Q,
    {n}.rate, {n}.real_inverse, {n}.imag_inverse,
    (by
      change RowArithmetic {n}.S {n}.P (GroundOriginalResponses.enclosures {i}) {n}.rate
      rw [← {n}.realBox_return]
      exact {n}.real_rows),
    (by
      change RowArithmetic {n}.R {n}.Q
        (imaginaryIntervals originalBackground GroundSamples.Point{i:03d}.a GroundSamples.Point{i:03d}.z GroundSamples.Point{i:03d}.r) (501/1000)
      rw [← {n}.imagBox_return]
      exact {n}.imag_rows)⟩ (
'''
    s+='  (fun i => Fin.elim0 i)'+')'*12+'\n\n'
    s+='''def realBasis (i : Fin 12) : Field ≃L[ℝ] Field := basis (certificates i).real_inverse
def imagBasis (i : Fin 12) : Field ≃L[ℝ] Field := basis (certificates i).imag_inverse
def fullBasis (i : Fin 12) := (realBasis i).prodCongr (imagBasis i)
def root (i : Fin 12) : Field := (GroundOriginalContinuation.branch (couplings (sampleIndex i))).1

theorem actual_real_rows (i : Fin 12) (a : Fin 8) :
    (∑ j, |GroundLocalDynamics.coordinateJacobian (realBasis i) (background originalBackground)
      (couplings (sampleIndex i)) (1/2) (root i) (GroundLocalDynamics.column j) a|) ≤
        ((certificates i).rate : ℝ) :=
  conjugate_rows (certificates i).real_inverse _ _ (certificates i).real_rows
    (GroundOriginalResponses.actual_half_entries (sampleIndex i)) a

theorem actual_real_norm (i : Fin 12) :
    ‖GroundLocalDynamics.coordinateJacobian (realBasis i) (background originalBackground)
      (couplings (sampleIndex i)) (1/2) (root i)‖ ≤ ((certificates i).rate : ℝ) :=
  GroundLocalDynamics.operator_norm_le_rows _ (by exact_mod_cast (certificates i).real_rows.nonneg)
    (actual_real_rows i)

theorem actual_imag_rows (i : Fin 12) (a : Fin 8) :
    (∑ j, |imaginaryCoordinate (imagBasis i) (1/2) (root i) (GroundLocalDynamics.column j) a|) ≤
      (501/1000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    (conjugate_rows (certificates i).imag_inverse _ _ (certificates i).imag_rows
    (imaginaryIntervals_sound originalBackground (couplings (sampleIndex i))
      (points (sampleIndex i)).z (points (sampleIndex i)).r
      (branch_in_sample_ball (sampleIndex i))) a)

theorem actual_imag_norm (i : Fin 12) :
    ‖imaginaryCoordinate (imagBasis i) (1/2) (root i)‖ ≤ (501/1000 : ℝ) :=
  GroundLocalDynamics.operator_norm_le_rows _ (by norm_num) (actual_imag_rows i)

theorem actual_full_norm (i : Fin 12) :
    ‖coordinateDerivative (fullBasis i) (background originalBackground)
      (couplings (sampleIndex i)) (1/2) (root i)‖ ≤ max ((certificates i).rate : ℝ) (501/1000) := by
  rw [fullBasis, coordinateDerivative_blocks]
  exact (product_operator_norm_bound _ _).trans (max_le_max (actual_real_norm i) (actual_imag_norm i))

theorem stable_rates : ∀ i : Fin 10, (certificates (i.castLE (by decide))).rate < 1 := by
  decide +kernel

theorem actual_stable_full_norm (i : Fin 10) :
    ‖coordinateDerivative (fullBasis (i.castLE (by decide))) (background originalBackground)
      (couplings (sampleIndex (i.castLE (by decide)))) (1/2) (root (i.castLE (by decide)))‖ < 1 := by
  apply (actual_full_norm (i.castLE (by decide))).trans_lt
  apply max_lt
  · exact_mod_cast stable_rates i
  · norm_num

theorem actual_native_attraction (i : Fin 10) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis (i.castLE (by decide))).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis (i.castLE (by decide))).symm (root (i.castLE (by decide)), 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        (background originalBackground) (couplings (sampleIndex (i.castLE (by decide)))) (1/2))^[n] z)
        atTop (nhds (realEmbed (root (i.castLE (by decide))))) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        (background originalBackground) (couplings (sampleIndex (i.castLE (by decide))))
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (background originalBackground) (couplings (sampleIndex (i.castLE (by decide)))) (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        (background originalBackground) (couplings (sampleIndex (i.castLE (by decide)))) (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (background originalBackground) (couplings (sampleIndex (i.castLE (by decide)))) (1/2))^[n] z) :=
  native_complex_local_attraction (fullBasis (i.castLE (by decide)))
    (sample_ground_return (sampleIndex (i.castLE (by decide)))).2.2.1
    (sample_ground_return (sampleIndex (i.castLE (by decide)))).2.2.2.2 GroundNativeControls.originalTolerance_guard.1
    GroundNativeControls.originalTolerance_guard.2 (actual_stable_full_norm i)

theorem actual_twenty_norm :
    ‖coordinateDerivative (fullBasis 10) (background originalBackground) 20 (1/2) (root 10)‖ ≤ 3/2 := by
  have h := actual_full_norm 10
  have hr : (certificates 10).rate = 3/2 := by decide +kernel
  have hk : couplings (sampleIndex 10) = 20 := by decide +kernel
  have hm : max (((3/2 : ℚ) : ℝ)) (501/1000) = 3/2 := by norm_num
  rw [hr, hk, hm] at h
  exact h

theorem actual_thirty_norm :
    ‖coordinateDerivative (fullBasis 11) (background originalBackground) 30 (1/2) (root 11)‖ ≤ 3 := by
  have h := actual_full_norm 11
  have hr : (certificates 11).rate = 3 := by decide +kernel
  have hk : couplings (sampleIndex 11) = 30 := by decide +kernel
  have hm : max (((3 : ℚ) : ℝ)) (501/1000) = 3 := by norm_num
  rw [hr, hk, hm] at h
  exact h

end
end SbtCosmo.Derivation.GroundOriginalCoordinates
'''
    return s


if __name__=='__main__':
    OUT.write_text(render());print('Reified actual coordinate norm and attraction family')
