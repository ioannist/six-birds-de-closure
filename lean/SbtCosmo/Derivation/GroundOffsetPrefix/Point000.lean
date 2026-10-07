import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step000
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step001
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step002
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step003
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step004
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step005
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step006
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step007
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step008
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step009
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step010
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step011
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step012
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step013
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step014
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step015
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step016
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step017
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step018
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step019
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step020
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step021
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step022
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step023
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step024
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step025
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step026
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step027
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step028
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step029
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step030
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step031
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step032
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step033
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step034
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step035
import SbtCosmo.Derivation.GroundOffsetPrefix.Point000.Step036
import SbtCosmo.Derivation.GroundOffsetSeedReturn

/-! Populated rounded-offset original-seed entry into the actual negative basin.
Every finite seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.GroundOffsetPrefix.Point000
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundCertifiedNativeEntry GroundOffsetSeedReturn GroundUncertainNativeBasin.Certificate
open Metric

def N : ℕ := 37
def δ : ℚ := (936157031712729382553133/39614081257132168796771975168)
def steps : Fin N → GroundCertifiedNativePrefix.Step (β 0) (κ 0) GroundNativePrefixInitial.τ :=
  Fin.cases GroundOffsetPrefix.Point000.Step000.step (
  Fin.cases GroundOffsetPrefix.Point000.Step001.step (
  Fin.cases GroundOffsetPrefix.Point000.Step002.step (
  Fin.cases GroundOffsetPrefix.Point000.Step003.step (
  Fin.cases GroundOffsetPrefix.Point000.Step004.step (
  Fin.cases GroundOffsetPrefix.Point000.Step005.step (
  Fin.cases GroundOffsetPrefix.Point000.Step006.step (
  Fin.cases GroundOffsetPrefix.Point000.Step007.step (
  Fin.cases GroundOffsetPrefix.Point000.Step008.step (
  Fin.cases GroundOffsetPrefix.Point000.Step009.step (
  Fin.cases GroundOffsetPrefix.Point000.Step010.step (
  Fin.cases GroundOffsetPrefix.Point000.Step011.step (
  Fin.cases GroundOffsetPrefix.Point000.Step012.step (
  Fin.cases GroundOffsetPrefix.Point000.Step013.step (
  Fin.cases GroundOffsetPrefix.Point000.Step014.step (
  Fin.cases GroundOffsetPrefix.Point000.Step015.step (
  Fin.cases GroundOffsetPrefix.Point000.Step016.step (
  Fin.cases GroundOffsetPrefix.Point000.Step017.step (
  Fin.cases GroundOffsetPrefix.Point000.Step018.step (
  Fin.cases GroundOffsetPrefix.Point000.Step019.step (
  Fin.cases GroundOffsetPrefix.Point000.Step020.step (
  Fin.cases GroundOffsetPrefix.Point000.Step021.step (
  Fin.cases GroundOffsetPrefix.Point000.Step022.step (
  Fin.cases GroundOffsetPrefix.Point000.Step023.step (
  Fin.cases GroundOffsetPrefix.Point000.Step024.step (
  Fin.cases GroundOffsetPrefix.Point000.Step025.step (
  Fin.cases GroundOffsetPrefix.Point000.Step026.step (
  Fin.cases GroundOffsetPrefix.Point000.Step027.step (
  Fin.cases GroundOffsetPrefix.Point000.Step028.step (
  Fin.cases GroundOffsetPrefix.Point000.Step029.step (
  Fin.cases GroundOffsetPrefix.Point000.Step030.step (
  Fin.cases GroundOffsetPrefix.Point000.Step031.step (
  Fin.cases GroundOffsetPrefix.Point000.Step032.step (
  Fin.cases GroundOffsetPrefix.Point000.Step033.step (
  Fin.cases GroundOffsetPrefix.Point000.Step034.step (
  Fin.cases GroundOffsetPrefix.Point000.Step035.step (
  fun _ => GroundOffsetPrefix.Point000.Step036.step))))))))))))))))))))))))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 0 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def targetBox : StateBox := negativeTargetBox GroundOffsets.Point000.z GroundOffsets.Point000.r
def entryBox : StateBox := GroundOffsetPrefix.Point000.Step036.output

theorem entry_arithmetic : ∀ j : Fin 8,
    ((((GroundOriginalOffsetBasins.data 0).c).coordinateBox (differenceBox entryBox targetBox)).R j).bound ≤ δ ∧
    ((((GroundOriginalOffsetBasins.data 0).c).coordinateBox (differenceBox entryBox targetBox)).I j).bound ≤ δ := by
  decide +kernel

theorem entry_margin : 0 ≤ δ ∧ δ < (GroundOriginalOffsetBasins.data 0).ρ := by decide +kernel

theorem distance : dist ((GroundOriginalOffsetBasins.T 0).symm (unpack (orbit 0 N)))
    ((GroundOriginalOffsetBasins.T 0).symm (-(GroundOriginalOffsets.roundedRoot 0).1,0)) ≤ (δ : ℝ) := by
  have hx : entryBox.Contains (unpack (orbit 0 N)) := by
    have h := certificate.enclosed (background_sound 0) (Fin.last N)
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using h
  have ht : targetBox.Contains (-(GroundOriginalOffsets.roundedRoot 0).1,0) :=
    negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box 0
      (GroundOriginalOffsets.rounded_inputs_sound 0))
  exact coordinate_distance (GroundOriginalOffsetBasins.data 0).c entry_margin.1 hx ht entry_arithmetic

theorem entry : (GroundOriginalOffsetBasins.T 0).symm (unpack (orbit 0 N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T 0).symm (-(GroundOriginalOffsets.roundedRoot 0).1,0))
    ((GroundOriginalOffsetBasins.data 0).ρ : ℝ) := by
  rw [mem_closedBall]
  exact distance.trans (Rat.cast_le.mpr entry_margin.2.le)

end
end SbtCosmo.Derivation.GroundOffsetPrefix.Point000
