import SbtCosmo.Derivation.GroundOffsetStability.Point000
import SbtCosmo.Derivation.GroundOffsetStability.Point001
import SbtCosmo.Derivation.GroundOffsetStability.Point002
import SbtCosmo.Derivation.GroundOffsetStability.Point003
import SbtCosmo.Derivation.GroundOffsetStability.Point004
import SbtCosmo.Derivation.GroundOffsetStability.Point005
import SbtCosmo.Derivation.GroundOffsetStability.Point006
import SbtCosmo.Derivation.GroundOffsetStability.Point007
import SbtCosmo.Derivation.GroundOffsetStability.Point008
import SbtCosmo.Derivation.GroundOffsetStability.Point009
import SbtCosmo.Derivation.GroundOffsetStability.Point010
import SbtCosmo.Derivation.GroundOffsetStability.Point011
import SbtCosmo.Derivation.GroundOffsetStability.Point012
import SbtCosmo.Derivation.GroundOffsetStability.Point013
import SbtCosmo.Derivation.GroundOffsetStability.Point014
import SbtCosmo.Derivation.GroundOffsetStability.Point015
import SbtCosmo.Derivation.GroundOffsetStability.Point016
import SbtCosmo.Derivation.GroundOffsetStability.Point017
import SbtCosmo.Derivation.GroundOriginalOffsets
import SbtCosmo.Derivation.GroundNativeReflection

/-! Actual native complex attraction at all eighteen original background offsets.
The complete arithmetic certificates are populated, and the whole input boxes
cover exact and rounded source inputs. Frozen-seed entry remains a separate task. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsetStability
noncomputable section
set_option maxHeartbeats 5000000
open GroundState GroundBorder GroundSourceJacobian GroundRationalInterval
open GroundMatrixCoordinates GroundNativeLocal
open Filter Metric
open scoped Topology BigOperators

structure Certificate (i : Fin 18) where
  C : Matrix (Fin 9) (Fin 9) ℚ
  q : ℚ
  y : Fin 8 → ℚ
  error : Fin 8 → ℚ
  S : QMatrix
  P : QMatrix
  R : QMatrix
  Q : QMatrix
  realBox : Matrix (Fin 8) (Fin 8) Interval
  imagBox : Matrix (Fin 8) (Fin 8) Interval
  rate : ℚ
  response_arithmetic : GroundUncertainBorderResponse.Arithmetic
    (GroundOriginalOffsets.certificates i).B (GroundOriginalOffsets.certificates i).κ
    (GroundOriginalOffsets.certificates i).z (GroundOriginalOffsets.certificates i).r C q y error
  real_inverse : InverseArithmetic S P
  imag_inverse : InverseArithmetic R Q
  realBox_included : GroundUncertainBorderResponse.Included
    (GroundUncertainBorderResponse.halfInterval (GroundOriginalOffsets.certificates i).B
      (GroundOriginalOffsets.certificates i).κ (GroundOriginalOffsets.certificates i).z
      (GroundOriginalOffsets.certificates i).r C error) realBox
  imagBox_included : GroundUncertainBorderResponse.Included
    (GroundUncertainBorderResponse.imaginaryIntervals (GroundOriginalOffsets.certificates i).B
      (GroundOriginalOffsets.certificates i).κ (GroundOriginalOffsets.certificates i).z
      (GroundOriginalOffsets.certificates i).r) imagBox
  real_rows : RowArithmetic S P realBox rate
  imag_rows : RowArithmetic R Q imagBox (501/1000)
  stable_rate : rate < 1

def certificates : (i : Fin 18) → Certificate i :=
  Fin.cases ⟨GroundOffsetStability.Point000.C, GroundOffsetStability.Point000.q, GroundOffsetStability.Point000.y, GroundOffsetStability.Point000.error, GroundOffsetStability.Point000.S, GroundOffsetStability.Point000.P, GroundOffsetStability.Point000.R, GroundOffsetStability.Point000.Q, GroundOffsetStability.Point000.realBox, GroundOffsetStability.Point000.imagBox, GroundOffsetStability.Point000.rate, GroundOffsetStability.Point000.response_arithmetic, GroundOffsetStability.Point000.real_inverse, GroundOffsetStability.Point000.imag_inverse, GroundOffsetStability.Point000.realBox_included, GroundOffsetStability.Point000.imagBox_included, GroundOffsetStability.Point000.real_rows, GroundOffsetStability.Point000.imag_rows, GroundOffsetStability.Point000.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point001.C, GroundOffsetStability.Point001.q, GroundOffsetStability.Point001.y, GroundOffsetStability.Point001.error, GroundOffsetStability.Point001.S, GroundOffsetStability.Point001.P, GroundOffsetStability.Point001.R, GroundOffsetStability.Point001.Q, GroundOffsetStability.Point001.realBox, GroundOffsetStability.Point001.imagBox, GroundOffsetStability.Point001.rate, GroundOffsetStability.Point001.response_arithmetic, GroundOffsetStability.Point001.real_inverse, GroundOffsetStability.Point001.imag_inverse, GroundOffsetStability.Point001.realBox_included, GroundOffsetStability.Point001.imagBox_included, GroundOffsetStability.Point001.real_rows, GroundOffsetStability.Point001.imag_rows, GroundOffsetStability.Point001.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point002.C, GroundOffsetStability.Point002.q, GroundOffsetStability.Point002.y, GroundOffsetStability.Point002.error, GroundOffsetStability.Point002.S, GroundOffsetStability.Point002.P, GroundOffsetStability.Point002.R, GroundOffsetStability.Point002.Q, GroundOffsetStability.Point002.realBox, GroundOffsetStability.Point002.imagBox, GroundOffsetStability.Point002.rate, GroundOffsetStability.Point002.response_arithmetic, GroundOffsetStability.Point002.real_inverse, GroundOffsetStability.Point002.imag_inverse, GroundOffsetStability.Point002.realBox_included, GroundOffsetStability.Point002.imagBox_included, GroundOffsetStability.Point002.real_rows, GroundOffsetStability.Point002.imag_rows, GroundOffsetStability.Point002.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point003.C, GroundOffsetStability.Point003.q, GroundOffsetStability.Point003.y, GroundOffsetStability.Point003.error, GroundOffsetStability.Point003.S, GroundOffsetStability.Point003.P, GroundOffsetStability.Point003.R, GroundOffsetStability.Point003.Q, GroundOffsetStability.Point003.realBox, GroundOffsetStability.Point003.imagBox, GroundOffsetStability.Point003.rate, GroundOffsetStability.Point003.response_arithmetic, GroundOffsetStability.Point003.real_inverse, GroundOffsetStability.Point003.imag_inverse, GroundOffsetStability.Point003.realBox_included, GroundOffsetStability.Point003.imagBox_included, GroundOffsetStability.Point003.real_rows, GroundOffsetStability.Point003.imag_rows, GroundOffsetStability.Point003.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point004.C, GroundOffsetStability.Point004.q, GroundOffsetStability.Point004.y, GroundOffsetStability.Point004.error, GroundOffsetStability.Point004.S, GroundOffsetStability.Point004.P, GroundOffsetStability.Point004.R, GroundOffsetStability.Point004.Q, GroundOffsetStability.Point004.realBox, GroundOffsetStability.Point004.imagBox, GroundOffsetStability.Point004.rate, GroundOffsetStability.Point004.response_arithmetic, GroundOffsetStability.Point004.real_inverse, GroundOffsetStability.Point004.imag_inverse, GroundOffsetStability.Point004.realBox_included, GroundOffsetStability.Point004.imagBox_included, GroundOffsetStability.Point004.real_rows, GroundOffsetStability.Point004.imag_rows, GroundOffsetStability.Point004.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point005.C, GroundOffsetStability.Point005.q, GroundOffsetStability.Point005.y, GroundOffsetStability.Point005.error, GroundOffsetStability.Point005.S, GroundOffsetStability.Point005.P, GroundOffsetStability.Point005.R, GroundOffsetStability.Point005.Q, GroundOffsetStability.Point005.realBox, GroundOffsetStability.Point005.imagBox, GroundOffsetStability.Point005.rate, GroundOffsetStability.Point005.response_arithmetic, GroundOffsetStability.Point005.real_inverse, GroundOffsetStability.Point005.imag_inverse, GroundOffsetStability.Point005.realBox_included, GroundOffsetStability.Point005.imagBox_included, GroundOffsetStability.Point005.real_rows, GroundOffsetStability.Point005.imag_rows, GroundOffsetStability.Point005.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point006.C, GroundOffsetStability.Point006.q, GroundOffsetStability.Point006.y, GroundOffsetStability.Point006.error, GroundOffsetStability.Point006.S, GroundOffsetStability.Point006.P, GroundOffsetStability.Point006.R, GroundOffsetStability.Point006.Q, GroundOffsetStability.Point006.realBox, GroundOffsetStability.Point006.imagBox, GroundOffsetStability.Point006.rate, GroundOffsetStability.Point006.response_arithmetic, GroundOffsetStability.Point006.real_inverse, GroundOffsetStability.Point006.imag_inverse, GroundOffsetStability.Point006.realBox_included, GroundOffsetStability.Point006.imagBox_included, GroundOffsetStability.Point006.real_rows, GroundOffsetStability.Point006.imag_rows, GroundOffsetStability.Point006.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point007.C, GroundOffsetStability.Point007.q, GroundOffsetStability.Point007.y, GroundOffsetStability.Point007.error, GroundOffsetStability.Point007.S, GroundOffsetStability.Point007.P, GroundOffsetStability.Point007.R, GroundOffsetStability.Point007.Q, GroundOffsetStability.Point007.realBox, GroundOffsetStability.Point007.imagBox, GroundOffsetStability.Point007.rate, GroundOffsetStability.Point007.response_arithmetic, GroundOffsetStability.Point007.real_inverse, GroundOffsetStability.Point007.imag_inverse, GroundOffsetStability.Point007.realBox_included, GroundOffsetStability.Point007.imagBox_included, GroundOffsetStability.Point007.real_rows, GroundOffsetStability.Point007.imag_rows, GroundOffsetStability.Point007.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point008.C, GroundOffsetStability.Point008.q, GroundOffsetStability.Point008.y, GroundOffsetStability.Point008.error, GroundOffsetStability.Point008.S, GroundOffsetStability.Point008.P, GroundOffsetStability.Point008.R, GroundOffsetStability.Point008.Q, GroundOffsetStability.Point008.realBox, GroundOffsetStability.Point008.imagBox, GroundOffsetStability.Point008.rate, GroundOffsetStability.Point008.response_arithmetic, GroundOffsetStability.Point008.real_inverse, GroundOffsetStability.Point008.imag_inverse, GroundOffsetStability.Point008.realBox_included, GroundOffsetStability.Point008.imagBox_included, GroundOffsetStability.Point008.real_rows, GroundOffsetStability.Point008.imag_rows, GroundOffsetStability.Point008.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point009.C, GroundOffsetStability.Point009.q, GroundOffsetStability.Point009.y, GroundOffsetStability.Point009.error, GroundOffsetStability.Point009.S, GroundOffsetStability.Point009.P, GroundOffsetStability.Point009.R, GroundOffsetStability.Point009.Q, GroundOffsetStability.Point009.realBox, GroundOffsetStability.Point009.imagBox, GroundOffsetStability.Point009.rate, GroundOffsetStability.Point009.response_arithmetic, GroundOffsetStability.Point009.real_inverse, GroundOffsetStability.Point009.imag_inverse, GroundOffsetStability.Point009.realBox_included, GroundOffsetStability.Point009.imagBox_included, GroundOffsetStability.Point009.real_rows, GroundOffsetStability.Point009.imag_rows, GroundOffsetStability.Point009.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point010.C, GroundOffsetStability.Point010.q, GroundOffsetStability.Point010.y, GroundOffsetStability.Point010.error, GroundOffsetStability.Point010.S, GroundOffsetStability.Point010.P, GroundOffsetStability.Point010.R, GroundOffsetStability.Point010.Q, GroundOffsetStability.Point010.realBox, GroundOffsetStability.Point010.imagBox, GroundOffsetStability.Point010.rate, GroundOffsetStability.Point010.response_arithmetic, GroundOffsetStability.Point010.real_inverse, GroundOffsetStability.Point010.imag_inverse, GroundOffsetStability.Point010.realBox_included, GroundOffsetStability.Point010.imagBox_included, GroundOffsetStability.Point010.real_rows, GroundOffsetStability.Point010.imag_rows, GroundOffsetStability.Point010.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point011.C, GroundOffsetStability.Point011.q, GroundOffsetStability.Point011.y, GroundOffsetStability.Point011.error, GroundOffsetStability.Point011.S, GroundOffsetStability.Point011.P, GroundOffsetStability.Point011.R, GroundOffsetStability.Point011.Q, GroundOffsetStability.Point011.realBox, GroundOffsetStability.Point011.imagBox, GroundOffsetStability.Point011.rate, GroundOffsetStability.Point011.response_arithmetic, GroundOffsetStability.Point011.real_inverse, GroundOffsetStability.Point011.imag_inverse, GroundOffsetStability.Point011.realBox_included, GroundOffsetStability.Point011.imagBox_included, GroundOffsetStability.Point011.real_rows, GroundOffsetStability.Point011.imag_rows, GroundOffsetStability.Point011.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point012.C, GroundOffsetStability.Point012.q, GroundOffsetStability.Point012.y, GroundOffsetStability.Point012.error, GroundOffsetStability.Point012.S, GroundOffsetStability.Point012.P, GroundOffsetStability.Point012.R, GroundOffsetStability.Point012.Q, GroundOffsetStability.Point012.realBox, GroundOffsetStability.Point012.imagBox, GroundOffsetStability.Point012.rate, GroundOffsetStability.Point012.response_arithmetic, GroundOffsetStability.Point012.real_inverse, GroundOffsetStability.Point012.imag_inverse, GroundOffsetStability.Point012.realBox_included, GroundOffsetStability.Point012.imagBox_included, GroundOffsetStability.Point012.real_rows, GroundOffsetStability.Point012.imag_rows, GroundOffsetStability.Point012.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point013.C, GroundOffsetStability.Point013.q, GroundOffsetStability.Point013.y, GroundOffsetStability.Point013.error, GroundOffsetStability.Point013.S, GroundOffsetStability.Point013.P, GroundOffsetStability.Point013.R, GroundOffsetStability.Point013.Q, GroundOffsetStability.Point013.realBox, GroundOffsetStability.Point013.imagBox, GroundOffsetStability.Point013.rate, GroundOffsetStability.Point013.response_arithmetic, GroundOffsetStability.Point013.real_inverse, GroundOffsetStability.Point013.imag_inverse, GroundOffsetStability.Point013.realBox_included, GroundOffsetStability.Point013.imagBox_included, GroundOffsetStability.Point013.real_rows, GroundOffsetStability.Point013.imag_rows, GroundOffsetStability.Point013.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point014.C, GroundOffsetStability.Point014.q, GroundOffsetStability.Point014.y, GroundOffsetStability.Point014.error, GroundOffsetStability.Point014.S, GroundOffsetStability.Point014.P, GroundOffsetStability.Point014.R, GroundOffsetStability.Point014.Q, GroundOffsetStability.Point014.realBox, GroundOffsetStability.Point014.imagBox, GroundOffsetStability.Point014.rate, GroundOffsetStability.Point014.response_arithmetic, GroundOffsetStability.Point014.real_inverse, GroundOffsetStability.Point014.imag_inverse, GroundOffsetStability.Point014.realBox_included, GroundOffsetStability.Point014.imagBox_included, GroundOffsetStability.Point014.real_rows, GroundOffsetStability.Point014.imag_rows, GroundOffsetStability.Point014.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point015.C, GroundOffsetStability.Point015.q, GroundOffsetStability.Point015.y, GroundOffsetStability.Point015.error, GroundOffsetStability.Point015.S, GroundOffsetStability.Point015.P, GroundOffsetStability.Point015.R, GroundOffsetStability.Point015.Q, GroundOffsetStability.Point015.realBox, GroundOffsetStability.Point015.imagBox, GroundOffsetStability.Point015.rate, GroundOffsetStability.Point015.response_arithmetic, GroundOffsetStability.Point015.real_inverse, GroundOffsetStability.Point015.imag_inverse, GroundOffsetStability.Point015.realBox_included, GroundOffsetStability.Point015.imagBox_included, GroundOffsetStability.Point015.real_rows, GroundOffsetStability.Point015.imag_rows, GroundOffsetStability.Point015.stable_rate⟩ (
  Fin.cases ⟨GroundOffsetStability.Point016.C, GroundOffsetStability.Point016.q, GroundOffsetStability.Point016.y, GroundOffsetStability.Point016.error, GroundOffsetStability.Point016.S, GroundOffsetStability.Point016.P, GroundOffsetStability.Point016.R, GroundOffsetStability.Point016.Q, GroundOffsetStability.Point016.realBox, GroundOffsetStability.Point016.imagBox, GroundOffsetStability.Point016.rate, GroundOffsetStability.Point016.response_arithmetic, GroundOffsetStability.Point016.real_inverse, GroundOffsetStability.Point016.imag_inverse, GroundOffsetStability.Point016.realBox_included, GroundOffsetStability.Point016.imagBox_included, GroundOffsetStability.Point016.real_rows, GroundOffsetStability.Point016.imag_rows, GroundOffsetStability.Point016.stable_rate⟩ (
  fun _ => ⟨GroundOffsetStability.Point017.C, GroundOffsetStability.Point017.q, GroundOffsetStability.Point017.y, GroundOffsetStability.Point017.error, GroundOffsetStability.Point017.S, GroundOffsetStability.Point017.P, GroundOffsetStability.Point017.R, GroundOffsetStability.Point017.Q, GroundOffsetStability.Point017.realBox, GroundOffsetStability.Point017.imagBox, GroundOffsetStability.Point017.rate, GroundOffsetStability.Point017.response_arithmetic, GroundOffsetStability.Point017.real_inverse, GroundOffsetStability.Point017.imag_inverse, GroundOffsetStability.Point017.realBox_included, GroundOffsetStability.Point017.imagBox_included, GroundOffsetStability.Point017.real_rows, GroundOffsetStability.Point017.imag_rows, GroundOffsetStability.Point017.stable_rate⟩)))))))))))))))))

def realBasis (i : Fin 18) : Field ≃L[ℝ] Field := basis (certificates i).real_inverse
def imagBasis (i : Fin 18) : Field ≃L[ℝ] Field := basis (certificates i).imag_inverse
def fullBasis (i : Fin 18) := (realBasis i).prodCongr (imagBasis i)

theorem actual_real_entries (i : Fin 18) {β : Field} {x : Point}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j))
    (hx : x ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ))
    (hg : groundPair (sourcePotential β (GroundOriginalOffsets.certificates i).κ x.1) = x)
    (hf : groundMap β (GroundOriginalOffsets.certificates i).κ x.1 = x.1) (a b : Fin 8) :
    ((certificates i).realBox a b).Contains
      (entries (GroundNormalizedJacobian.normalizedJacobian β
        (GroundOriginalOffsets.certificates i).κ (1/2) x.1) a b) :=
  GroundUncertainBorderResponse.included_sound (certificates i).realBox_included
    (GroundUncertainBorderResponse.halfInterval_sound
      (certificates i).response_arithmetic hβ hx hg hf a b)

theorem actual_imag_entries (i : Fin 18) {β : Field} {x : Point}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j))
    (hx : x ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ)) (a b : Fin 8) :
    ((certificates i).imagBox a b).Contains
      (entries (GroundNativeJacobian.imaginaryDerivative (1/2) x.1) a b) :=
  GroundUncertainBorderResponse.included_sound (certificates i).imagBox_included
    (GroundUncertainBorderResponse.imaginaryIntervals_sound _ _ _ _ hβ hx a b)

theorem actual_real_norm (i : Fin 18) {β : Field} {x : Point}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j))
    (hx : x ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ))
    (hg : groundPair (sourcePotential β (GroundOriginalOffsets.certificates i).κ x.1) = x)
    (hf : groundMap β (GroundOriginalOffsets.certificates i).κ x.1 = x.1) :
    ‖GroundLocalDynamics.coordinateJacobian (realBasis i) β
      (GroundOriginalOffsets.certificates i).κ (1/2) x.1‖ ≤ ((certificates i).rate : ℝ) :=
  conjugate_norm (certificates i).real_inverse _ _ (certificates i).real_rows
    (actual_real_entries i hβ hx hg hf)

theorem actual_imag_norm (i : Fin 18) {β : Field} {x : Point}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j))
    (hx : x ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ)) :
    ‖imaginaryCoordinate (imagBasis i) (1/2) x.1‖ ≤ (501/1000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    (conjugate_norm (certificates i).imag_inverse _ _ (certificates i).imag_rows
      (actual_imag_entries i hβ hx))

theorem actual_full_norm (i : Fin 18) {β : Field} {x : Point}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j))
    (hx : x ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ))
    (hg : groundPair (sourcePotential β (GroundOriginalOffsets.certificates i).κ x.1) = x)
    (hf : groundMap β (GroundOriginalOffsets.certificates i).κ x.1 = x.1) :
    ‖coordinateDerivative (fullBasis i) β (GroundOriginalOffsets.certificates i).κ (1/2) x.1‖ ≤
      max ((certificates i).rate : ℝ) (501/1000) := by
  rw [fullBasis, coordinateDerivative_blocks]
  exact (product_operator_norm_bound _ _).trans
    (max_le_max (actual_real_norm i hβ hx hg hf) (actual_imag_norm i hβ hx))

theorem actual_stable_full_norm (i : Fin 18) {β : Field} {x : Point}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j))
    (hx : x ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ))
    (hg : groundPair (sourcePotential β (GroundOriginalOffsets.certificates i).κ x.1) = x)
    (hf : groundMap β (GroundOriginalOffsets.certificates i).κ x.1 = x.1) :
    ‖coordinateDerivative (fullBasis i) β (GroundOriginalOffsets.certificates i).κ (1/2) x.1‖ < 1 := by
  apply (actual_full_norm i hβ hx hg hf).trans_lt
  apply max_lt
  · exact_mod_cast (certificates i).stable_rate
  · norm_num

def tube (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) :=
  GroundUncertainBackgroundTube.tube (GroundOriginalOffsets.certificates i).arithmetic hβ
def wholeRoot (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) : Point :=
  (tube i hβ).root (GroundOriginalOffsets.certificates i).κ

theorem whole_root_return (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) :
    wholeRoot i hβ ∈ closedBall (GroundKernelTube.center (GroundOriginalOffsets.certificates i).z)
      ((GroundOriginalOffsets.certificates i).r : ℝ) ∧
    normSq (wholeRoot i hβ).1 = 1 ∧
    groundPair (sourcePotential β (GroundOriginalOffsets.certificates i).κ (wholeRoot i hβ).1) = wholeRoot i hβ ∧
    groundMap β (GroundOriginalOffsets.certificates i).κ (wholeRoot i hβ).1 = (wholeRoot i hβ).1 := by
  have hk : ((GroundOriginalOffsets.certificates i).κ : ℝ) ∈ (tube i hβ).interval := ⟨le_rfl, le_rfl⟩
  have hs := (tube i hβ).root_spec hk
  exact ⟨hs.1, hs.2.2.1.1,
    GroundOriginalOffsets.ground_pair_return hs.2.2.1 ((tube i hβ).field_positive _ hs.1),
    hs.2.2.2.1⟩

theorem whole_background_box_native_attraction (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis i).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis i).symm ((wholeRoot i hβ).1, 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
        atTop (nhds (realEmbed (wholeRoot i hβ).1)) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) := by
  have hs := whole_root_return i hβ
  exact native_complex_local_attraction (fullBasis i) hs.2.1 hs.2.2.2
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2
    (actual_stable_full_norm i hβ hs.1 hs.2.2.1 hs.2.2.2)

theorem actual_exact_native_attraction (i : Fin 18) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis i).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis i).symm ((GroundOriginalOffsets.root i).1, 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
        atTop (nhds (realEmbed (GroundOriginalOffsets.root i).1)) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) :=
  whole_background_box_native_attraction i (GroundOriginalOffsets.exact_inputs_sound i)

theorem actual_rounded_native_attraction (i : Fin 18) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis i).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis i).symm ((GroundOriginalOffsets.roundedRoot i).1, 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
        atTop (nhds (realEmbed (GroundOriginalOffsets.roundedRoot i).1)) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) :=
  whole_background_box_native_attraction i (GroundOriginalOffsets.rounded_inputs_sound i)

theorem whole_background_box_negative_native_attraction (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis i).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis i).symm (-(wholeRoot i hβ).1, 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
        atTop (nhds (realEmbed (-(wholeRoot i hβ).1))) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) := by
  have hs := whole_root_return i hβ
  exact GroundNativeReflection.native_negative_local_attraction (fullBasis i) hs.2.1 hs.2.2.2
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2
    (actual_stable_full_norm i hβ hs.1 hs.2.2.1 hs.2.2.2)

theorem actual_exact_negative_native_attraction (i : Fin 18) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis i).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis i).symm (-(GroundOriginalOffsets.root i).1, 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
        atTop (nhds (realEmbed (-(GroundOriginalOffsets.root i).1))) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) :=
  whole_background_box_negative_native_attraction i (GroundOriginalOffsets.exact_inputs_sound i)

theorem actual_rounded_negative_native_attraction (i : Fin 18) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis i).symm (GroundNativePhase.unpack z) ∈
        closedBall ((fullBasis i).symm (-(GroundOriginalOffsets.roundedRoot i).1, 0)) r →
      Tendsto (fun n : ℕ => (GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
        atTop (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) ∧
      ∀ n : ℕ, GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2)
        ((GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
          (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) :=
  whole_background_box_negative_native_attraction i (GroundOriginalOffsets.rounded_inputs_sound i)

theorem zero_selector_preconditioner_rejected : ¬ GroundUncertainBorderResponse.Arithmetic
    (GroundOriginalOffsets.certificates 0).B (GroundOriginalOffsets.certificates 0).κ
    (GroundOriginalOffsets.certificates 0).z (GroundOriginalOffsets.certificates 0).r
    (fun _ _ => 0) (certificates 0).q (certificates 0).y (certificates 0).error := by
  intro h
  have hn : ¬ (∑ j : Fin 9, ((GroundBorderResponse.borderDefectExpr (fun _ _ => 0) 0 j).enclose
    (GroundUncertainBackgroundTube.box (GroundOriginalOffsets.certificates 0).B
      (GroundOriginalOffsets.certificates 0).κ (GroundOriginalOffsets.certificates 0).κ
      (GroundOriginalOffsets.certificates 0).z (GroundOriginalOffsets.certificates 0).r)).bound) ≤
      (certificates 0).q := by decide +kernel
  exact hn (h.defect_rows 0)

end
end SbtCosmo.Derivation.GroundOriginalOffsetStability
