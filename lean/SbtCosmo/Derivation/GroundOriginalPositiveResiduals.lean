import SbtCosmo.Derivation.GroundOriginalBasinEstimates
import SbtCosmo.Derivation.GroundComplexResidualBudget
import SbtCosmo.Derivation.GroundSourceDiagnostics

/-! The original .3 seed passes all four exact mathematical source diagnostics
at60 updates. The sourced candidate and Rayleigh energy are the actual ones. -/
namespace SbtCosmo.Derivation.GroundOriginalPositiveResiduals
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean GroundComplexResidual
open GroundSourceDiagnostics GroundOriginalBasinEstimates
open GroundOriginalBasin (b u)
open GroundNativePrefixInitial (κ)
open GroundBasin.Point002Data (basisBudget)
open scoped BigOperators

def τ : ℝ := GroundNativeControls.originalTolerance
def ε : ℝ := 3022314549036573/302231454903657293676544
def orbit (n : ℕ) : ComplexField := GroundOriginalNativePrefix.orbit n
def potential : Field := complexSourcePotential b (κ : ℝ) (orbit 60)
def g : ComplexField := -nativeCandidate b (κ : ℝ) (orbit 60)
def eigenvalue : ℝ := energy potential (positiveGround potential)
def d : ℝ := 1/10000000000

theorem tolerance_budget : 0 ≤ τ ∧ τ < 1/2 ∧ (1/100000000 : ℝ) < ε := by
  norm_num [τ, GroundNativeControls.originalTolerance, ε]

theorem orbit_unit (n : ℕ) : complexNormSq (orbit n) = 1 := GroundOriginalBasin.original_seed_all_unit n

theorem orbit_distance_fifty_nine : l2 (orbit 59-realEmbed (-u)) ≤ d := by
  exact (euclidean_tail_bound 43).trans (by norm_num [basisBudget, d])

theorem orbit_distance_sixty : l2 (orbit 60-realEmbed (-u)) ≤ d := by
  exact (euclidean_tail_bound 44).trans (by norm_num [basisBudget, d])

theorem actual_candidate_distance_sixty : l2 (orbit 60-g) ≤ d := by
  exact (actual_candidate_distance 44).trans (by norm_num [basisBudget, d])

theorem potential_budget : ∀ i, 0 ≤ potential i ∧ potential i ≤ 1/2 := sourced_potential_budget 44

theorem actual_candidate_ground_data : complexNormSq g = 1 ∧
    (∀ i, complexHamiltonian potential g i = (eigenvalue : ℂ)*g i) ∧
    0 ≤ eigenvalue ∧ eigenvalue ≤ 1/2 := by
  have hg := (positiveGround_spec potential).2
  have he : g = -realEmbed (positiveGround potential) := rfl
  refine ⟨?_, ?_, GroundComplexResidualBudget.ground_energy_budget hg potential_budget⟩
  · rw [he, GroundNativeReflection.complexNormSq_neg]
    exact realEmbed_normalized hg.1
  · intro i
    have hn : complexHamiltonian potential (-realEmbed (positiveGround potential)) i =
        -complexHamiltonian potential (realEmbed (positiveGround potential)) i := by
      simp [complexHamiltonian]; ring
    rw [he, hn, realEmbed_eigen hg i]
    change -(↑eigenvalue * realEmbed (positiveGround potential) i) = ↑eigenvalue * -realEmbed (positiveGround potential) i
    ring

theorem last_update_threshold : lastUpdateResidual τ b (κ : ℝ) (1/2) (orbit 59) < ε := by
  have he : nativeUpdate τ b (κ : ℝ) (1/2) (orbit 59) = orbit 60 := by
    change GroundOriginalNativePrefix.f (GroundOriginalNativePrefix.f^[59] GroundOriginalSeed.initial) =
      GroundOriginalNativePrefix.f^[60] GroundOriginalSeed.initial
    exact (Function.iterate_succ_apply' GroundOriginalNativePrefix.f 59 GroundOriginalSeed.initial).symm
  rw [lastUpdateResidual, he]
  have h := l2_sub_triangle (orbit 60) (realEmbed (-u)) (orbit 59)
  have hn : realEmbed (-u)-orbit 59 = -(orbit 59-realEmbed (-u)) := by abel
  rw [hn, l2_neg] at h
  have hsmall : 2*d < (1/100000000 : ℝ) := by norm_num [d]
  linarith [orbit_distance_sixty, orbit_distance_fifty_nine, tolerance_budget.2.2]

theorem final_fixed_gap_threshold : finalFixedGap τ b (κ : ℝ) (orbit 60) < ε ∧
    τ < ‖overlap (nativePhase τ (nativeCandidate b (κ : ℝ) (orbit 60)) (orbit 60)) (orbit 60)‖ := by
  have hd := double_phase_gap actual_candidate_ground_data.1 (orbit_unit 60) actual_candidate_distance_sixty
    (by norm_num [d] : (0:ℝ) ≤ d) (by norm_num [d] : 2*d^2 ≤ 1)
    tolerance_budget.1 (by norm_num [τ, GroundNativeControls.originalTolerance, d] : τ < 1-2*d^2)
  have he : nativePhase τ (nativeCandidate b (κ : ℝ) (orbit 60)) (orbit 60) = nativePhase τ g (orbit 60) := by
    have hc : nativeCandidate b (κ : ℝ) (orbit 60) = -g := by simp [g]
    rw [hc, nativePhase_real_sign_invariant tolerance_budget.1 hd.1]
  constructor
  · rw [finalFixedGap, he]
    have hsmall : 4*d < (1/100000000 : ℝ) := by norm_num [d]
    linarith [hd.2.2, tolerance_budget.2.2]
  · rw [he]; exact hd.2.1

theorem final_eigen_threshold : finalEigenResidual b (κ : ℝ) (orbit 60) < ε := by
  have hM : ∀ w, l2 (shifted potential eigenvalue w) ≤ (5/2)*l2 w := by
    intro w
    simpa only [show (2 : ℝ)+1/2 = 5/2 by norm_num] using
      GroundComplexResidualBudget.shifted_l2_bound (by norm_num : (0:ℝ) ≤ 1/2)
        potential_budget actual_candidate_ground_data.2.2 w
  have h := eigen_residual_bound actual_candidate_ground_data.2.1 (orbit_unit 60) hM
  have hd := actual_candidate_distance_sixty
  have hs : (l2 (orbit 60-g))^2 ≤ d^2 := by nlinarith [l2_nonneg (orbit 60-g), show (0 : ℝ) ≤ d by norm_num [d]]
  have hsmall : (5/2 : ℝ)*d+(5/2 : ℝ)*d^2 < 1/100000000 := by norm_num [d]
  change l2 (shifted potential (complexEnergy potential (orbit 60)) (orbit 60)) < ε
  nlinarith [tolerance_budget.2.2]

theorem final_sourcing_threshold : finalSourcingResidual b (κ : ℝ) (orbit 60) = 0 ∧
    finalSourcingResidual b (κ : ℝ) (orbit 60) < ε := by
  rw [sourcing_self_comparison_zero]
  exact ⟨rfl, by linarith [tolerance_budget.2.2]⟩

theorem actual_seed_positive_sixty_convergence_tests :
    MeetsConvergence τ ε b (κ : ℝ) (1/2) (orbit 59) (orbit 60) ∧
    ∀ n : ℕ, ActivePhase τ b (κ : ℝ) (orbit n) ∧ NativeLegal τ b (κ : ℝ) (1/2) (orbit n) := by
  exact ⟨⟨last_update_threshold.le, final_fixed_gap_threshold.1.le, final_eigen_threshold.le,
    final_sourcing_threshold.2.le⟩, GroundOriginalBasin.original_seed_all_guards⟩

end
end SbtCosmo.Derivation.GroundOriginalPositiveResiduals
