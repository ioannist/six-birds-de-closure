import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point000
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point001
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point002
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point003
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point004
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point005
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point006
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point007
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point008
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point009
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point010
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point011
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point012
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point013
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point014
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point015
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point016
import SbtCosmo.Derivation.GroundOffsetSixtyTests.Point017

/-! Exact mathematical sixty-update verdicts for the eighteen original rounded
background offsets. Uses the original threshold, tolerance, seed, mixing,
actual sourced ground selector, both phase calls and actual Rayleigh energy.
Eventual convergence is already proved, including all three finite failures.
No per-operation IEEE execution or first stopping index is asserted. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsetSixty
noncomputable section
open GroundOffsetSeedReturn

def verdict : Fin 18 → Bool :=
  ![true,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false]

def Tests (i : Fin 18) : Prop := GroundSourceDiagnostics.MeetsConvergence
  GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
  (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2) (orbit i 59) (orbit i 60)

theorem original_sixty_verdict (i : Fin 18) : Tests i ↔ verdict i = true := by
  fin_cases i
  · constructor
    · intro _
      rfl
    · intro _
      exact GroundOffsetSixtyTests.Point000.actual_four_source_tests
  · constructor
    · intro h
      exact (GroundOffsetSixtyTests.Point001.actual_four_source_tests_fail h).elim
    · intro h
      cases h
  · constructor
    · intro h
      exact (GroundOffsetSixtyTests.Point002.actual_four_source_tests_fail h).elim
    · intro h
      cases h
  · constructor
    · intro _
      rfl
    · intro _
      exact GroundOffsetSixtyTests.Point003.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point004.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point004.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point005.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point005.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point006.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point006.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point007.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point007.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point008.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point008.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point009.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point009.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point010.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point010.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point011.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point011.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point012.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point012.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point013.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point013.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point014.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point014.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact by simpa only [GroundOffsetSixtyTests.Point015.ε,GroundOriginalResiduals.ε] using GroundOffsetSixtyTests.Point015.actual_four_source_tests
  · constructor
    · intro _
      rfl
    · intro _
      exact GroundOffsetSixtyTests.Point016.actual_four_source_tests
  · constructor
    · intro h
      exact (GroundOffsetSixtyTests.Point017.actual_four_source_tests_fail h).elim
    · intro h
      cases h

theorem failed_offsets (i : Fin 18) : ¬ Tests i ↔ i = 1 ∨ i = 2 ∨ i = 17 := by
  rw [original_sixty_verdict]
  fin_cases i <;> simp [verdict]

theorem passing_count : (Finset.univ.filter (fun i : Fin 18 => verdict i = true)).card = 15 := by
  decide +kernel

theorem failing_count : (Finset.univ.filter (fun i : Fin 18 => verdict i = false)).card = 3 := by
  decide +kernel

end
end SbtCosmo.Derivation.GroundOriginalOffsetSixty
