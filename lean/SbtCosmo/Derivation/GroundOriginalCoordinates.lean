import SbtCosmo.Derivation.GroundMatrixCoordinates
import SbtCosmo.Derivation.GroundCoordinates.Point000
import SbtCosmo.Derivation.GroundCoordinates.Point001
import SbtCosmo.Derivation.GroundCoordinates.Point002
import SbtCosmo.Derivation.GroundCoordinates.Point003
import SbtCosmo.Derivation.GroundCoordinates.Point004
import SbtCosmo.Derivation.GroundCoordinates.Point005
import SbtCosmo.Derivation.GroundCoordinates.Point006
import SbtCosmo.Derivation.GroundCoordinates.Point007
import SbtCosmo.Derivation.GroundCoordinates.Point008
import SbtCosmo.Derivation.GroundCoordinates.Point009
import SbtCosmo.Derivation.GroundCoordinates.Point010
import SbtCosmo.Derivation.GroundCoordinates.Point011

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
  Fin.cases ⟨GroundCoordinates.Point000.S, GroundCoordinates.Point000.P, GroundCoordinates.Point000.R, GroundCoordinates.Point000.Q,
    GroundCoordinates.Point000.rate, GroundCoordinates.Point000.real_inverse, GroundCoordinates.Point000.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point000.S GroundCoordinates.Point000.P (GroundOriginalResponses.enclosures 0) GroundCoordinates.Point000.rate
      rw [← GroundCoordinates.Point000.realBox_return]
      exact GroundCoordinates.Point000.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point000.R GroundCoordinates.Point000.Q
        (imaginaryIntervals originalBackground GroundSamples.Point000.a GroundSamples.Point000.z GroundSamples.Point000.r) (501/1000)
      rw [← GroundCoordinates.Point000.imagBox_return]
      exact GroundCoordinates.Point000.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point001.S, GroundCoordinates.Point001.P, GroundCoordinates.Point001.R, GroundCoordinates.Point001.Q,
    GroundCoordinates.Point001.rate, GroundCoordinates.Point001.real_inverse, GroundCoordinates.Point001.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point001.S GroundCoordinates.Point001.P (GroundOriginalResponses.enclosures 1) GroundCoordinates.Point001.rate
      rw [← GroundCoordinates.Point001.realBox_return]
      exact GroundCoordinates.Point001.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point001.R GroundCoordinates.Point001.Q
        (imaginaryIntervals originalBackground GroundSamples.Point001.a GroundSamples.Point001.z GroundSamples.Point001.r) (501/1000)
      rw [← GroundCoordinates.Point001.imagBox_return]
      exact GroundCoordinates.Point001.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point002.S, GroundCoordinates.Point002.P, GroundCoordinates.Point002.R, GroundCoordinates.Point002.Q,
    GroundCoordinates.Point002.rate, GroundCoordinates.Point002.real_inverse, GroundCoordinates.Point002.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point002.S GroundCoordinates.Point002.P (GroundOriginalResponses.enclosures 2) GroundCoordinates.Point002.rate
      rw [← GroundCoordinates.Point002.realBox_return]
      exact GroundCoordinates.Point002.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point002.R GroundCoordinates.Point002.Q
        (imaginaryIntervals originalBackground GroundSamples.Point002.a GroundSamples.Point002.z GroundSamples.Point002.r) (501/1000)
      rw [← GroundCoordinates.Point002.imagBox_return]
      exact GroundCoordinates.Point002.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point003.S, GroundCoordinates.Point003.P, GroundCoordinates.Point003.R, GroundCoordinates.Point003.Q,
    GroundCoordinates.Point003.rate, GroundCoordinates.Point003.real_inverse, GroundCoordinates.Point003.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point003.S GroundCoordinates.Point003.P (GroundOriginalResponses.enclosures 3) GroundCoordinates.Point003.rate
      rw [← GroundCoordinates.Point003.realBox_return]
      exact GroundCoordinates.Point003.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point003.R GroundCoordinates.Point003.Q
        (imaginaryIntervals originalBackground GroundSamples.Point003.a GroundSamples.Point003.z GroundSamples.Point003.r) (501/1000)
      rw [← GroundCoordinates.Point003.imagBox_return]
      exact GroundCoordinates.Point003.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point004.S, GroundCoordinates.Point004.P, GroundCoordinates.Point004.R, GroundCoordinates.Point004.Q,
    GroundCoordinates.Point004.rate, GroundCoordinates.Point004.real_inverse, GroundCoordinates.Point004.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point004.S GroundCoordinates.Point004.P (GroundOriginalResponses.enclosures 4) GroundCoordinates.Point004.rate
      rw [← GroundCoordinates.Point004.realBox_return]
      exact GroundCoordinates.Point004.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point004.R GroundCoordinates.Point004.Q
        (imaginaryIntervals originalBackground GroundSamples.Point004.a GroundSamples.Point004.z GroundSamples.Point004.r) (501/1000)
      rw [← GroundCoordinates.Point004.imagBox_return]
      exact GroundCoordinates.Point004.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point005.S, GroundCoordinates.Point005.P, GroundCoordinates.Point005.R, GroundCoordinates.Point005.Q,
    GroundCoordinates.Point005.rate, GroundCoordinates.Point005.real_inverse, GroundCoordinates.Point005.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point005.S GroundCoordinates.Point005.P (GroundOriginalResponses.enclosures 5) GroundCoordinates.Point005.rate
      rw [← GroundCoordinates.Point005.realBox_return]
      exact GroundCoordinates.Point005.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point005.R GroundCoordinates.Point005.Q
        (imaginaryIntervals originalBackground GroundSamples.Point005.a GroundSamples.Point005.z GroundSamples.Point005.r) (501/1000)
      rw [← GroundCoordinates.Point005.imagBox_return]
      exact GroundCoordinates.Point005.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point006.S, GroundCoordinates.Point006.P, GroundCoordinates.Point006.R, GroundCoordinates.Point006.Q,
    GroundCoordinates.Point006.rate, GroundCoordinates.Point006.real_inverse, GroundCoordinates.Point006.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point006.S GroundCoordinates.Point006.P (GroundOriginalResponses.enclosures 6) GroundCoordinates.Point006.rate
      rw [← GroundCoordinates.Point006.realBox_return]
      exact GroundCoordinates.Point006.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point006.R GroundCoordinates.Point006.Q
        (imaginaryIntervals originalBackground GroundSamples.Point006.a GroundSamples.Point006.z GroundSamples.Point006.r) (501/1000)
      rw [← GroundCoordinates.Point006.imagBox_return]
      exact GroundCoordinates.Point006.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point007.S, GroundCoordinates.Point007.P, GroundCoordinates.Point007.R, GroundCoordinates.Point007.Q,
    GroundCoordinates.Point007.rate, GroundCoordinates.Point007.real_inverse, GroundCoordinates.Point007.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point007.S GroundCoordinates.Point007.P (GroundOriginalResponses.enclosures 7) GroundCoordinates.Point007.rate
      rw [← GroundCoordinates.Point007.realBox_return]
      exact GroundCoordinates.Point007.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point007.R GroundCoordinates.Point007.Q
        (imaginaryIntervals originalBackground GroundSamples.Point007.a GroundSamples.Point007.z GroundSamples.Point007.r) (501/1000)
      rw [← GroundCoordinates.Point007.imagBox_return]
      exact GroundCoordinates.Point007.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point008.S, GroundCoordinates.Point008.P, GroundCoordinates.Point008.R, GroundCoordinates.Point008.Q,
    GroundCoordinates.Point008.rate, GroundCoordinates.Point008.real_inverse, GroundCoordinates.Point008.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point008.S GroundCoordinates.Point008.P (GroundOriginalResponses.enclosures 8) GroundCoordinates.Point008.rate
      rw [← GroundCoordinates.Point008.realBox_return]
      exact GroundCoordinates.Point008.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point008.R GroundCoordinates.Point008.Q
        (imaginaryIntervals originalBackground GroundSamples.Point008.a GroundSamples.Point008.z GroundSamples.Point008.r) (501/1000)
      rw [← GroundCoordinates.Point008.imagBox_return]
      exact GroundCoordinates.Point008.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point009.S, GroundCoordinates.Point009.P, GroundCoordinates.Point009.R, GroundCoordinates.Point009.Q,
    GroundCoordinates.Point009.rate, GroundCoordinates.Point009.real_inverse, GroundCoordinates.Point009.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point009.S GroundCoordinates.Point009.P (GroundOriginalResponses.enclosures 9) GroundCoordinates.Point009.rate
      rw [← GroundCoordinates.Point009.realBox_return]
      exact GroundCoordinates.Point009.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point009.R GroundCoordinates.Point009.Q
        (imaginaryIntervals originalBackground GroundSamples.Point009.a GroundSamples.Point009.z GroundSamples.Point009.r) (501/1000)
      rw [← GroundCoordinates.Point009.imagBox_return]
      exact GroundCoordinates.Point009.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point010.S, GroundCoordinates.Point010.P, GroundCoordinates.Point010.R, GroundCoordinates.Point010.Q,
    GroundCoordinates.Point010.rate, GroundCoordinates.Point010.real_inverse, GroundCoordinates.Point010.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point010.S GroundCoordinates.Point010.P (GroundOriginalResponses.enclosures 10) GroundCoordinates.Point010.rate
      rw [← GroundCoordinates.Point010.realBox_return]
      exact GroundCoordinates.Point010.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point010.R GroundCoordinates.Point010.Q
        (imaginaryIntervals originalBackground GroundSamples.Point010.a GroundSamples.Point010.z GroundSamples.Point010.r) (501/1000)
      rw [← GroundCoordinates.Point010.imagBox_return]
      exact GroundCoordinates.Point010.imag_rows)⟩ (
  Fin.cases ⟨GroundCoordinates.Point011.S, GroundCoordinates.Point011.P, GroundCoordinates.Point011.R, GroundCoordinates.Point011.Q,
    GroundCoordinates.Point011.rate, GroundCoordinates.Point011.real_inverse, GroundCoordinates.Point011.imag_inverse,
    (by
      change RowArithmetic GroundCoordinates.Point011.S GroundCoordinates.Point011.P (GroundOriginalResponses.enclosures 11) GroundCoordinates.Point011.rate
      rw [← GroundCoordinates.Point011.realBox_return]
      exact GroundCoordinates.Point011.real_rows),
    (by
      change RowArithmetic GroundCoordinates.Point011.R GroundCoordinates.Point011.Q
        (imaginaryIntervals originalBackground GroundSamples.Point011.a GroundSamples.Point011.z GroundSamples.Point011.r) (501/1000)
      rw [← GroundCoordinates.Point011.imagBox_return]
      exact GroundCoordinates.Point011.imag_rows)⟩ (
  (fun i => Fin.elim0 i)))))))))))))

def realBasis (i : Fin 12) : Field ≃L[ℝ] Field := basis (certificates i).real_inverse
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
