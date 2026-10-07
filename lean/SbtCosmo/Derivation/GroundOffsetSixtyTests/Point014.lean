import SbtCosmo.Derivation.GroundOffsetPrefix.Point014
import SbtCosmo.Derivation.GroundOffsetSelectorBudget
import SbtCosmo.Derivation.GroundComplexFiniteBudget
import SbtCosmo.Derivation.GroundOriginalOffsetSeed
namespace SbtCosmo.Derivation.GroundOffsetSixtyTests.Point014
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundOffsetSeedReturn GroundRationalInterval GroundNativeBox
open GroundOffsetSelectorBudget
open scoped BigOperators
def a : ℚ := (18419287/16777216)
def d : ℚ := 1/100000000000
theorem selector_rows : 0 ≤ a ∧ ∀ j : Fin 8, (∑ k : Fin 8,
      (((GroundOriginalOffsetBasins.data 14).c.DG (k.castAdd 8) j).bound+
       ((GroundOriginalOffsetBasins.data 14).c.DG (Fin.natAdd 8 k) j).bound)) ≤ a := by decide +kernel

theorem candidate_arithmetic :
    (4*(GroundOriginalOffsetBasins.data 14).s+4*a)*
      ((GroundOriginalOffsetBasins.data 14).c.rate^45*GroundOffsetPrefix.Point014.δ) ≤ d := by decide +kernel

theorem actual_candidate_distance :
    GroundComplexEuclidean.l2 (orbit 14 60-(-GroundNativeIteration.nativeCandidate
      (GroundOriginalOffsets.rounded_b 14) (κ 14 : ℝ) (orbit 14 60))) ≤ (d : ℝ) := by
  have h := candidate_distance 14 GroundOffsetPrefix.Point014.entry GroundOffsetPrefix.Point014.distance
    selector_rows.1 selector_rows.2 45
  have hc : (4*((GroundOriginalOffsetBasins.data 14).s : ℝ)+4*(a : ℝ))*
      ((GroundOriginalOffsetBasins.rate 14 : ℝ)^45*(GroundOffsetPrefix.Point014.δ : ℝ)) ≤ (d : ℝ) := by
    change (4*((GroundOriginalOffsetBasins.data 14).s : ℝ)+4*(a : ℝ))*
      (((GroundOriginalOffsetBasins.data 14).c.rate : ℝ)^45*(GroundOffsetPrefix.Point014.δ : ℝ)) ≤ (d : ℝ)
    exact_mod_cast candidate_arithmetic
  exact h.trans hc

theorem update_arithmetic :
    4*(GroundOriginalOffsetBasins.data 14).s*
      (((GroundOriginalOffsetBasins.data 14).c.rate^44+
        (GroundOriginalOffsetBasins.data 14).c.rate^45)*GroundOffsetPrefix.Point014.δ) ≤ d := by decide +kernel

theorem source_bounds_arithmetic : ∀ j : Fin 8,
    3 ≤ (GroundUncertainNativeBox.sourceBox (GroundOriginalOffsetBasins.data 14).c.β
      (GroundOriginalOffsetBasins.data 14).c.κ (GroundOriginalOffsetBasins.data 14).c.input j).lo ∧
    (GroundUncertainNativeBox.sourceBox (GroundOriginalOffsetBasins.data 14).c.β
      (GroundOriginalOffsetBasins.data 14).c.κ (GroundOriginalOffsetBasins.data 14).c.input j).hi ≤ 4 := by decide +kernel

theorem actual_update_distance : GroundComplexEuclidean.l2 (orbit 14 60-orbit 14 59) ≤ (d : ℝ) := by
  have h59 := euclidean_tail_bound 14 GroundOffsetPrefix.Point014.entry GroundOffsetPrefix.Point014.distance 44
  have h60 := euclidean_tail_bound 14 GroundOffsetPrefix.Point014.entry GroundOffsetPrefix.Point014.distance 45
  have h := GroundComplexEuclidean.l2_sub_triangle (orbit 14 60)
    (realEmbed (-(GroundOriginalOffsets.roundedRoot 14).1)) (orbit 14 59)
  have hn : realEmbed (-(GroundOriginalOffsets.roundedRoot 14).1)-orbit 14 59 =
      -(orbit 14 59-realEmbed (-(GroundOriginalOffsets.roundedRoot 14).1)) := by abel
  rw [hn,GroundComplexEuclidean.l2_neg] at h
  have hc : 4*((GroundOriginalOffsetBasins.data 14).s : ℝ)*
      (((GroundOriginalOffsetBasins.rate 14 : ℝ)^44+
        (GroundOriginalOffsetBasins.rate 14 : ℝ)^45)*(GroundOffsetPrefix.Point014.δ : ℝ)) ≤ (d : ℝ) := by
    change 4*((GroundOriginalOffsetBasins.data 14).s : ℝ)*
      ((((GroundOriginalOffsetBasins.data 14).c.rate : ℝ)^44+
        ((GroundOriginalOffsetBasins.data 14).c.rate : ℝ)^45)*(GroundOffsetPrefix.Point014.δ : ℝ)) ≤ (d : ℝ)
    exact_mod_cast update_arithmetic
  simp only [GroundOffsetPrefix.Point014.N,Nat.reduceAdd] at h59 h60
  nlinarith

def ε : ℝ := 3022314549036573/302231454903657293676544

theorem actual_four_source_tests : GroundSourceDiagnostics.MeetsConvergence
    GroundNativeControls.originalTolerance ε (GroundOriginalOffsets.rounded_b 14) (κ 14 : ℝ)
      (1/2) (orbit 14 59) (orbit 14 60) := by
  have hstep : GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
    (GroundOriginalOffsets.rounded_b 14) (κ 14 : ℝ) (1/2) (orbit 14 59) = orbit 14 60 := by
    exact (Function.iterate_succ_apply' (f 14) 59 GroundOriginalSeed.initial).symm
  have hpot := sourced_potential_bounds 14 GroundOffsetPrefix.Point014.entry source_bounds_arithmetic 45
  apply GroundComplexFiniteBudget.tests_of_budgets
    GroundNativeControls.originalTolerance_guard.1 (by norm_num [ε]) (by norm_num [d])
    ((GroundOriginalOffsetSeed.rounded_original_seed_return 14).2 60).2.2
    actual_candidate_distance actual_update_distance hstep (by norm_num at hpot; exact hpot)
  · norm_num [d]
  · norm_num [d,GroundNativeControls.originalTolerance]
  · norm_num [d,ε]
end
end SbtCosmo.Derivation.GroundOffsetSixtyTests.Point014
