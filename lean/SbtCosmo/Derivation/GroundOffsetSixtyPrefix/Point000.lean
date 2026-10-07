import SbtCosmo.Derivation.GroundOffsetPrefix.Point000
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step037
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step038
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step039
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step040
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step041
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step042
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step043
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step044
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step045
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step046
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step047
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step048
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step049
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step050
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step051
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step052
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step053
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step054
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step055
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step056
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step057
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step058
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000.Step059

/-! Earned original rounded-input enclosures at iterations59 and60. -/
namespace SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval GroundOffsetSeedReturn

def N : ℕ := 60
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
  Fin.cases GroundOffsetPrefix.Point000.Step036.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step037.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step038.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step039.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step040.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step041.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step042.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step043.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step044.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step045.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step046.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step047.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step048.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step049.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step050.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step051.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step052.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step053.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step054.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step055.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step056.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step057.step (
  Fin.cases GroundOffsetSixtyPrefix.Point000.Step058.step (
  fun _ => GroundOffsetSixtyPrefix.Point000.Step059.step)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 0 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def previousBox : StateBox := GroundOffsetSixtyPrefix.Point000.Step058.output
def currentBox : StateBox := GroundOffsetSixtyPrefix.Point000.Step059.output

theorem previous_enclosed : previousBox.Contains (unpack (orbit 0 59)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound 0) ⟨59,by decide⟩

theorem current_enclosed : currentBox.Contains (unpack (orbit 0 60)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound 0) (Fin.last N)

end
end SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point000
