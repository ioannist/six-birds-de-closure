import SbtCosmo.Derivation.GroundOffsetPrefix.Point017
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step052
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step053
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step054
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step055
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step056
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step057
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step058
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017.Step059

/-! Earned original rounded-input enclosures at iterations59 and60. -/
namespace SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval GroundOffsetSeedReturn

def N : ℕ := 60
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
  Fin.cases GroundOffsetPrefix.Point017.Step051.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step052.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step053.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step054.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step055.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step056.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step057.step (
  Fin.cases GroundOffsetSixtyPrefix.Point017.Step058.step (
  fun _ => GroundOffsetSixtyPrefix.Point017.Step059.step)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 17 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def previousBox : StateBox := GroundOffsetSixtyPrefix.Point017.Step058.output
def currentBox : StateBox := GroundOffsetSixtyPrefix.Point017.Step059.output

theorem previous_enclosed : previousBox.Contains (unpack (orbit 17 59)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound 17) ⟨59,by decide⟩

theorem current_enclosed : currentBox.Contains (unpack (orbit 17 60)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound 17) (Fin.last N)

end
end SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point017
