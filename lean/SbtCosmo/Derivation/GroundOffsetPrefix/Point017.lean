import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step000
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step001
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step002
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step003
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step004
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step005
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step006
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step007
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step008
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step009
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step010
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step011
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step012
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step013
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step014
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step015
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step016
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step017
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step018
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step019
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step020
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step021
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step022
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step023
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step024
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step025
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step026
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step027
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step028
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step029
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step030
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step031
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step032
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step033
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step034
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step035
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step036
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step037
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step038
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step039
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step040
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step041
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step042
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step043
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step044
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step045
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step046
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step047
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step048
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step049
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step050
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017.Step051
import SbtCosmo.Derivation.GroundOffsetSeedReturn

/-! Populated rounded-offset original-seed entry into the actual negative basin.
Every finite seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.GroundOffsetPrefix.Point017
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundCertifiedNativeEntry GroundOffsetSeedReturn GroundUncertainNativeBasin.Certificate
open Metric

def N : ℕ := 52
def δ : ℚ := (358743317636823322904099/158456325028528675187087900672)
def steps : Fin N → GroundCertifiedNativePrefix.Step (β 17) (κ 17) GroundNativePrefixInitial.τ :=
  Fin.cases GroundOffsetPrefix.Point017.Step000.step (
  Fin.cases GroundOffsetPrefix.Point017.Step001.step (
  Fin.cases GroundOffsetPrefix.Point017.Step002.step (
  Fin.cases GroundOffsetPrefix.Point017.Step003.step (
  Fin.cases GroundOffsetPrefix.Point017.Step004.step (
  Fin.cases GroundOffsetPrefix.Point017.Step005.step (
  Fin.cases GroundOffsetPrefix.Point017.Step006.step (
  Fin.cases GroundOffsetPrefix.Point017.Step007.step (
  Fin.cases GroundOffsetPrefix.Point017.Step008.step (
  Fin.cases GroundOffsetPrefix.Point017.Step009.step (
  Fin.cases GroundOffsetPrefix.Point017.Step010.step (
  Fin.cases GroundOffsetPrefix.Point017.Step011.step (
  Fin.cases GroundOffsetPrefix.Point017.Step012.step (
  Fin.cases GroundOffsetPrefix.Point017.Step013.step (
  Fin.cases GroundOffsetPrefix.Point017.Step014.step (
  Fin.cases GroundOffsetPrefix.Point017.Step015.step (
  Fin.cases GroundOffsetPrefix.Point017.Step016.step (
  Fin.cases GroundOffsetPrefix.Point017.Step017.step (
  Fin.cases GroundOffsetPrefix.Point017.Step018.step (
  Fin.cases GroundOffsetPrefix.Point017.Step019.step (
  Fin.cases GroundOffsetPrefix.Point017.Step020.step (
  Fin.cases GroundOffsetPrefix.Point017.Step021.step (
  Fin.cases GroundOffsetPrefix.Point017.Step022.step (
  Fin.cases GroundOffsetPrefix.Point017.Step023.step (
  Fin.cases GroundOffsetPrefix.Point017.Step024.step (
  Fin.cases GroundOffsetPrefix.Point017.Step025.step (
  Fin.cases GroundOffsetPrefix.Point017.Step026.step (
  Fin.cases GroundOffsetPrefix.Point017.Step027.step (
  Fin.cases GroundOffsetPrefix.Point017.Step028.step (
  Fin.cases GroundOffsetPrefix.Point017.Step029.step (
  Fin.cases GroundOffsetPrefix.Point017.Step030.step (
  Fin.cases GroundOffsetPrefix.Point017.Step031.step (
  Fin.cases GroundOffsetPrefix.Point017.Step032.step (
  Fin.cases GroundOffsetPrefix.Point017.Step033.step (
  Fin.cases GroundOffsetPrefix.Point017.Step034.step (
  Fin.cases GroundOffsetPrefix.Point017.Step035.step (
  Fin.cases GroundOffsetPrefix.Point017.Step036.step (
  Fin.cases GroundOffsetPrefix.Point017.Step037.step (
  Fin.cases GroundOffsetPrefix.Point017.Step038.step (
  Fin.cases GroundOffsetPrefix.Point017.Step039.step (
  Fin.cases GroundOffsetPrefix.Point017.Step040.step (
  Fin.cases GroundOffsetPrefix.Point017.Step041.step (
  Fin.cases GroundOffsetPrefix.Point017.Step042.step (
  Fin.cases GroundOffsetPrefix.Point017.Step043.step (
  Fin.cases GroundOffsetPrefix.Point017.Step044.step (
  Fin.cases GroundOffsetPrefix.Point017.Step045.step (
  Fin.cases GroundOffsetPrefix.Point017.Step046.step (
  Fin.cases GroundOffsetPrefix.Point017.Step047.step (
  Fin.cases GroundOffsetPrefix.Point017.Step048.step (
  Fin.cases GroundOffsetPrefix.Point017.Step049.step (
  Fin.cases GroundOffsetPrefix.Point017.Step050.step (
  fun _ => GroundOffsetPrefix.Point017.Step051.step)))))))))))))))))))))))))))))))))))))))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 17 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def targetBox : StateBox := negativeTargetBox GroundOffsets.Point017.z GroundOffsets.Point017.r
def entryBox : StateBox := GroundOffsetPrefix.Point017.Step051.output

theorem entry_arithmetic : ∀ j : Fin 8,
    ((((GroundOriginalOffsetBasins.data 17).c).coordinateBox (differenceBox entryBox targetBox)).R j).bound ≤ δ ∧
    ((((GroundOriginalOffsetBasins.data 17).c).coordinateBox (differenceBox entryBox targetBox)).I j).bound ≤ δ := by
  decide +kernel

theorem entry_margin : 0 ≤ δ ∧ δ < (GroundOriginalOffsetBasins.data 17).ρ := by decide +kernel

theorem distance : dist ((GroundOriginalOffsetBasins.T 17).symm (unpack (orbit 17 N)))
    ((GroundOriginalOffsetBasins.T 17).symm (-(GroundOriginalOffsets.roundedRoot 17).1,0)) ≤ (δ : ℝ) := by
  have hx : entryBox.Contains (unpack (orbit 17 N)) := by
    have h := certificate.enclosed (background_sound 17) (Fin.last N)
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using h
  have ht : targetBox.Contains (-(GroundOriginalOffsets.roundedRoot 17).1,0) :=
    negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box 17
      (GroundOriginalOffsets.rounded_inputs_sound 17))
  exact coordinate_distance (GroundOriginalOffsetBasins.data 17).c entry_margin.1 hx ht entry_arithmetic

theorem entry : (GroundOriginalOffsetBasins.T 17).symm (unpack (orbit 17 N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T 17).symm (-(GroundOriginalOffsets.roundedRoot 17).1,0))
    ((GroundOriginalOffsetBasins.data 17).ρ : ℝ) := by
  rw [mem_closedBall]
  exact distance.trans (Rat.cast_le.mpr entry_margin.2.le)

end
end SbtCosmo.Derivation.GroundOffsetPrefix.Point017
