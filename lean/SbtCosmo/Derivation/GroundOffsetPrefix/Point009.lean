import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step000
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step001
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step002
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step003
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step004
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step005
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step006
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step007
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step008
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step009
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step010
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step011
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step012
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step013
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009.Step014
import SbtCosmo.Derivation.GroundOffsetSeedReturn

/-! Populated rounded-offset original-seed entry into the actual negative basin.
Every finite seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.GroundOffsetPrefix.Point009
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundCertifiedNativeEntry GroundOffsetSeedReturn GroundUncertainNativeBasin.Certificate
open Metric

def N : ℕ := 15
def δ : ℚ := (20515660480088468699001705/1267650600228229401496703205376)
def steps : Fin N → GroundCertifiedNativePrefix.Step (β 9) (κ 9) GroundNativePrefixInitial.τ :=
  Fin.cases GroundOffsetPrefix.Point009.Step000.step (
  Fin.cases GroundOffsetPrefix.Point009.Step001.step (
  Fin.cases GroundOffsetPrefix.Point009.Step002.step (
  Fin.cases GroundOffsetPrefix.Point009.Step003.step (
  Fin.cases GroundOffsetPrefix.Point009.Step004.step (
  Fin.cases GroundOffsetPrefix.Point009.Step005.step (
  Fin.cases GroundOffsetPrefix.Point009.Step006.step (
  Fin.cases GroundOffsetPrefix.Point009.Step007.step (
  Fin.cases GroundOffsetPrefix.Point009.Step008.step (
  Fin.cases GroundOffsetPrefix.Point009.Step009.step (
  Fin.cases GroundOffsetPrefix.Point009.Step010.step (
  Fin.cases GroundOffsetPrefix.Point009.Step011.step (
  Fin.cases GroundOffsetPrefix.Point009.Step012.step (
  Fin.cases GroundOffsetPrefix.Point009.Step013.step (
  fun _ => GroundOffsetPrefix.Point009.Step014.step))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 9 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def targetBox : StateBox := negativeTargetBox GroundOffsets.Point009.z GroundOffsets.Point009.r
def entryBox : StateBox := GroundOffsetPrefix.Point009.Step014.output

theorem entry_arithmetic : ∀ j : Fin 8,
    ((((GroundOriginalOffsetBasins.data 9).c).coordinateBox (differenceBox entryBox targetBox)).R j).bound ≤ δ ∧
    ((((GroundOriginalOffsetBasins.data 9).c).coordinateBox (differenceBox entryBox targetBox)).I j).bound ≤ δ := by
  decide +kernel

theorem entry_margin : 0 ≤ δ ∧ δ < (GroundOriginalOffsetBasins.data 9).ρ := by decide +kernel

theorem distance : dist ((GroundOriginalOffsetBasins.T 9).symm (unpack (orbit 9 N)))
    ((GroundOriginalOffsetBasins.T 9).symm (-(GroundOriginalOffsets.roundedRoot 9).1,0)) ≤ (δ : ℝ) := by
  have hx : entryBox.Contains (unpack (orbit 9 N)) := by
    have h := certificate.enclosed (background_sound 9) (Fin.last N)
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using h
  have ht : targetBox.Contains (-(GroundOriginalOffsets.roundedRoot 9).1,0) :=
    negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box 9
      (GroundOriginalOffsets.rounded_inputs_sound 9))
  exact coordinate_distance (GroundOriginalOffsetBasins.data 9).c entry_margin.1 hx ht entry_arithmetic

theorem entry : (GroundOriginalOffsetBasins.T 9).symm (unpack (orbit 9 N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T 9).symm (-(GroundOriginalOffsets.roundedRoot 9).1,0))
    ((GroundOriginalOffsetBasins.data 9).ρ : ℝ) := by
  rw [mem_closedBall]
  exact distance.trans (Rat.cast_le.mpr entry_margin.2.le)

end
end SbtCosmo.Derivation.GroundOffsetPrefix.Point009
