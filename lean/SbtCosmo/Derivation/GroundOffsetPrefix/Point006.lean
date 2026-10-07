import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step000
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step001
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step002
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step003
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step004
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step005
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step006
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step007
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step008
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step009
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step010
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step011
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step012
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step013
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step014
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006.Step015
import SbtCosmo.Derivation.GroundOffsetSeedReturn

/-! Populated rounded-offset original-seed entry into the actual negative basin.
Every finite seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.GroundOffsetPrefix.Point006
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundCertifiedNativeEntry GroundOffsetSeedReturn GroundUncertainNativeBasin.Certificate
open Metric

def N : ℕ := 16
def δ : ℚ := (16429121077524812651206583/1267650600228229401496703205376)
def steps : Fin N → GroundCertifiedNativePrefix.Step (β 6) (κ 6) GroundNativePrefixInitial.τ :=
  Fin.cases GroundOffsetPrefix.Point006.Step000.step (
  Fin.cases GroundOffsetPrefix.Point006.Step001.step (
  Fin.cases GroundOffsetPrefix.Point006.Step002.step (
  Fin.cases GroundOffsetPrefix.Point006.Step003.step (
  Fin.cases GroundOffsetPrefix.Point006.Step004.step (
  Fin.cases GroundOffsetPrefix.Point006.Step005.step (
  Fin.cases GroundOffsetPrefix.Point006.Step006.step (
  Fin.cases GroundOffsetPrefix.Point006.Step007.step (
  Fin.cases GroundOffsetPrefix.Point006.Step008.step (
  Fin.cases GroundOffsetPrefix.Point006.Step009.step (
  Fin.cases GroundOffsetPrefix.Point006.Step010.step (
  Fin.cases GroundOffsetPrefix.Point006.Step011.step (
  Fin.cases GroundOffsetPrefix.Point006.Step012.step (
  Fin.cases GroundOffsetPrefix.Point006.Step013.step (
  Fin.cases GroundOffsetPrefix.Point006.Step014.step (
  fun _ => GroundOffsetPrefix.Point006.Step015.step)))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 6 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def targetBox : StateBox := negativeTargetBox GroundOffsets.Point006.z GroundOffsets.Point006.r
def entryBox : StateBox := GroundOffsetPrefix.Point006.Step015.output

theorem entry_arithmetic : ∀ j : Fin 8,
    ((((GroundOriginalOffsetBasins.data 6).c).coordinateBox (differenceBox entryBox targetBox)).R j).bound ≤ δ ∧
    ((((GroundOriginalOffsetBasins.data 6).c).coordinateBox (differenceBox entryBox targetBox)).I j).bound ≤ δ := by
  decide +kernel

theorem entry_margin : 0 ≤ δ ∧ δ < (GroundOriginalOffsetBasins.data 6).ρ := by decide +kernel

theorem distance : dist ((GroundOriginalOffsetBasins.T 6).symm (unpack (orbit 6 N)))
    ((GroundOriginalOffsetBasins.T 6).symm (-(GroundOriginalOffsets.roundedRoot 6).1,0)) ≤ (δ : ℝ) := by
  have hx : entryBox.Contains (unpack (orbit 6 N)) := by
    have h := certificate.enclosed (background_sound 6) (Fin.last N)
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using h
  have ht : targetBox.Contains (-(GroundOriginalOffsets.roundedRoot 6).1,0) :=
    negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box 6
      (GroundOriginalOffsets.rounded_inputs_sound 6))
  exact coordinate_distance (GroundOriginalOffsetBasins.data 6).c entry_margin.1 hx ht entry_arithmetic

theorem entry : (GroundOriginalOffsetBasins.T 6).symm (unpack (orbit 6 N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T 6).symm (-(GroundOriginalOffsets.roundedRoot 6).1,0))
    ((GroundOriginalOffsetBasins.data 6).ρ : ℝ) := by
  rw [mem_closedBall]
  exact distance.trans (Rat.cast_le.mpr entry_margin.2.le)

end
end SbtCosmo.Derivation.GroundOffsetPrefix.Point006
