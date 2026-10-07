import SbtCosmo.Derivation.GroundOffsetPrefix.Point016
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step016
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step017
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step018
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step019
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step020
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step021
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step022
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step023
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step024
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step025
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step026
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step027
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step028
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step029
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step030
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step031
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step032
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step033
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step034
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step035
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step036
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step037
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step038
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step039
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step040
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step041
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step042
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step043
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step044
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step045
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step046
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step047
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step048
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step049
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step050
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step051
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step052
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step053
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step054
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step055
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step056
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step057
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step058
import SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016.Step059

/-! Earned original rounded-input enclosures at iterations59 and60. -/
namespace SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval GroundOffsetSeedReturn

def N : ℕ := 60
def steps : Fin N → GroundCertifiedNativePrefix.Step (β 16) (κ 16) GroundNativePrefixInitial.τ :=
  Fin.cases GroundOffsetPrefix.Point016.Step000.step (
  Fin.cases GroundOffsetPrefix.Point016.Step001.step (
  Fin.cases GroundOffsetPrefix.Point016.Step002.step (
  Fin.cases GroundOffsetPrefix.Point016.Step003.step (
  Fin.cases GroundOffsetPrefix.Point016.Step004.step (
  Fin.cases GroundOffsetPrefix.Point016.Step005.step (
  Fin.cases GroundOffsetPrefix.Point016.Step006.step (
  Fin.cases GroundOffsetPrefix.Point016.Step007.step (
  Fin.cases GroundOffsetPrefix.Point016.Step008.step (
  Fin.cases GroundOffsetPrefix.Point016.Step009.step (
  Fin.cases GroundOffsetPrefix.Point016.Step010.step (
  Fin.cases GroundOffsetPrefix.Point016.Step011.step (
  Fin.cases GroundOffsetPrefix.Point016.Step012.step (
  Fin.cases GroundOffsetPrefix.Point016.Step013.step (
  Fin.cases GroundOffsetPrefix.Point016.Step014.step (
  Fin.cases GroundOffsetPrefix.Point016.Step015.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step016.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step017.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step018.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step019.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step020.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step021.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step022.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step023.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step024.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step025.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step026.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step027.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step028.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step029.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step030.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step031.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step032.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step033.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step034.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step035.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step036.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step037.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step038.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step039.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step040.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step041.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step042.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step043.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step044.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step045.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step046.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step047.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step048.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step049.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step050.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step051.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step052.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step053.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step054.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step055.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step056.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step057.step (
  Fin.cases GroundOffsetSixtyPrefix.Point016.Step058.step (
  fun _ => GroundOffsetSixtyPrefix.Point016.Step059.step)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

def certificate : Prefix 16 N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def previousBox : StateBox := GroundOffsetSixtyPrefix.Point016.Step058.output
def currentBox : StateBox := GroundOffsetSixtyPrefix.Point016.Step059.output

theorem previous_enclosed : previousBox.Contains (unpack (orbit 16 59)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound 16) ⟨59,by decide⟩

theorem current_enclosed : currentBox.Contains (unpack (orbit 16 60)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound 16) (Fin.last N)

end
end SbtCosmo.Derivation.GroundOffsetSixtyPrefix.Point016
