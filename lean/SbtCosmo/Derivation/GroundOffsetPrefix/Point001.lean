import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step000
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step001
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step002
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step003
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step004
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step005
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step006
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step007
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step008
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step009
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step010
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step011
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step012
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step013
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step014
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step015
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step016
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step017
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step018
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step019
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step020
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step021
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step022
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step023
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step024
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step025
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step026
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step027
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step028
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step029
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step030
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step031
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step032
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step033
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step034
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step035
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step036
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step037
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step038
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step039
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step040
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step041
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step042
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step043
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step044
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step045
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step046
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step047
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step048
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step049
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step050
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step051
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step052
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step053
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step054
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step055
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step056
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step057
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step058
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step059
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step060
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step061
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step062
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step063
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001.Step064
import SbtCosmo.Derivation.GroundOffsetSeedReturn

/-! Populated rounded-offset original-seed entry into the actual negative basin.
Every finite seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.GroundOffsetPrefix.Point001
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundCertifiedNativeEntry GroundOffsetSeedReturn GroundUncertainNativeBasin.Certificate
open Metric

def N : ℕ := 65
def δ : ℚ := (6857661336553070551585599/316912650057057350374175801344)
def steps : Fin N → GroundCertifiedNativePrefix.Step (β 1) (κ 1) GroundNativePrefixInitial.τ :=
  Fin.cases GroundOffsetPrefix.Point001.Step000.step (
  Fin.cases GroundOffsetPrefix.Point001.Step001.step (
  Fin.cases GroundOffsetPrefix.Point001.Step002.step (
  Fin.cases GroundOffsetPrefix.Point001.Step003.step (
  Fin.cases GroundOffsetPrefix.Point001.Step004.step (
  Fin.cases GroundOffsetPrefix.Point001.Step005.step (
  Fin.cases GroundOffsetPrefix.Point001.Step006.step (
  Fin.cases GroundOffsetPrefix.Point001.Step007.step (
  Fin.cases GroundOffsetPrefix.Point001.Step008.step (
  Fin.cases GroundOffsetPrefix.Point001.Step009.step (
  Fin.cases GroundOffsetPrefix.Point001.Step010.step (
  Fin.cases GroundOffsetPrefix.Point001.Step011.step (
  Fin.cases GroundOffsetPrefix.Point001.Step012.step (
  Fin.cases GroundOffsetPrefix.Point001.Step013.step (
  Fin.cases GroundOffsetPrefix.Point001.Step014.step (
  Fin.cases GroundOffsetPrefix.Point001.Step015.step (
  Fin.cases GroundOffsetPrefix.Point001.Step016.step (
  Fin.cases GroundOffsetPrefix.Point001.Step017.step (
  Fin.cases GroundOffsetPrefix.Point001.Step018.step (
  Fin.cases GroundOffsetPrefix.Point001.Step019.step (
  Fin.cases GroundOffsetPrefix.Point001.Step020.step (
  Fin.cases GroundOffsetPrefix.Point001.Step021.step (
  Fin.cases GroundOffsetPrefix.Point001.Step022.step (
  Fin.cases GroundOffsetPrefix.Point001.Step023.step (
  Fin.cases GroundOffsetPrefix.Point001.Step024.step (
  Fin.cases GroundOffsetPrefix.Point001.Step025.step (
  Fin.cases GroundOffsetPrefix.Point001.Step026.step (
  Fin.cases GroundOffsetPrefix.Point001.Step027.step (
  Fin.cases GroundOffsetPrefix.Point001.Step028.step (
  Fin.cases GroundOffsetPrefix.Point001.Step029.step (
  Fin.cases GroundOffsetPrefix.Point001.Step030.step (
  Fin.cases GroundOffsetPrefix.Point001.Step031.step (
  Fin.cases GroundOffsetPrefix.Point001.Step032.step (
  Fin.cases GroundOffsetPrefix.Point001.Step033.step (
  Fin.cases GroundOffsetPrefix.Point001.Step034.step (
  Fin.cases GroundOffsetPrefix.Point001.Step035.step (
  Fin.cases GroundOffsetPrefix.Point001.Step036.step (
  Fin.cases GroundOffsetPrefix.Point001.Step037.step (
  Fin.cases GroundOffsetPrefix.Point001.Step038.step (
  Fin.cases GroundOffsetPrefix.Point001.Step039.step (
  Fin.cases GroundOffsetPrefix.Point001.Step040.step (
  Fin.cases GroundOffsetPrefix.Point001.Step041.step (
  Fin.cases GroundOffsetPrefix.Point001.Step042.step (
  Fin.cases GroundOffsetPrefix.Point001.Step043.step (
  Fin.cases GroundOffsetPrefix.Point001.Step044.step (
  Fin.cases GroundOffsetPrefix.Point001.Step045.step (
  Fin.cases GroundOffsetPrefix.Point001.Step046.step (
  Fin.cases GroundOffsetPrefix.Point001.Step047.step (
  Fin.cases GroundOffsetPrefix.Point001.Step048.step (
  Fin.cases GroundOffsetPrefix.Point001.Step049.step (
  Fin.cases GroundOffsetPrefix.Point001.Step050.step (
  Fin.cases GroundOffsetPrefix.Point001.Step051.step (
  Fin.cases GroundOffsetPrefix.Point001.Step052.step (
  Fin.cases GroundOffsetPrefix.Point001.Step053.step (
  Fin.cases GroundOffsetPrefix.Point001.Step054.step (
  Fin.cases GroundOffsetPrefix.Point001.Step055.step (
  Fin.cases GroundOffsetPrefix.Point001.Step056.step (
  Fin.cases GroundOffsetPrefix.Point001.Step057.step (
  Fin.cases GroundOffsetPrefix.Point001.Step058.step (
  Fin.cases GroundOffsetPrefix.Point001.Step059.step (
  Fin.cases GroundOffsetPrefix.Point001.Step060.step (
  Fin.cases GroundOffsetPrefix.Point001.Step061.step (
  Fin.cases GroundOffsetPrefix.Point001.Step062.step (
  Fin.cases GroundOffsetPrefix.Point001.Step063.step (
  fun _ => GroundOffsetPrefix.Point001.Step064.step))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 1 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def targetBox : StateBox := negativeTargetBox GroundOffsets.Point001.z GroundOffsets.Point001.r
def entryBox : StateBox := GroundOffsetPrefix.Point001.Step064.output

theorem entry_arithmetic : ∀ j : Fin 8,
    ((((GroundOriginalOffsetBasins.data 1).c).coordinateBox (differenceBox entryBox targetBox)).R j).bound ≤ δ ∧
    ((((GroundOriginalOffsetBasins.data 1).c).coordinateBox (differenceBox entryBox targetBox)).I j).bound ≤ δ := by
  decide +kernel

theorem entry_margin : 0 ≤ δ ∧ δ < (GroundOriginalOffsetBasins.data 1).ρ := by decide +kernel

theorem distance : dist ((GroundOriginalOffsetBasins.T 1).symm (unpack (orbit 1 N)))
    ((GroundOriginalOffsetBasins.T 1).symm (-(GroundOriginalOffsets.roundedRoot 1).1,0)) ≤ (δ : ℝ) := by
  have hx : entryBox.Contains (unpack (orbit 1 N)) := by
    have h := certificate.enclosed (background_sound 1) (Fin.last N)
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using h
  have ht : targetBox.Contains (-(GroundOriginalOffsets.roundedRoot 1).1,0) :=
    negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box 1
      (GroundOriginalOffsets.rounded_inputs_sound 1))
  exact coordinate_distance (GroundOriginalOffsetBasins.data 1).c entry_margin.1 hx ht entry_arithmetic

theorem entry : (GroundOriginalOffsetBasins.T 1).symm (unpack (orbit 1 N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T 1).symm (-(GroundOriginalOffsets.roundedRoot 1).1,0))
    ((GroundOriginalOffsetBasins.data 1).ρ : ℝ) := by
  rw [mem_closedBall]
  exact distance.trans (Rat.cast_le.mpr entry_margin.2.le)

end
end SbtCosmo.Derivation.GroundOffsetPrefix.Point001
