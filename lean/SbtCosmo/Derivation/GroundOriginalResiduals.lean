import SbtCosmo.Derivation.GroundSourceDiagnostics

/-! All four original-source convergence thresholds for the exact native
original-seed zero-coupling orbit after60 updates. No IEEE execution claim. -/
namespace SbtCosmo.Derivation.GroundOriginalResiduals
noncomputable section
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean GroundComplexResidual
open GroundSourceDiagnostics GroundOriginalFirstTube GroundKernelTube GroundOriginalSeed
open GroundOriginalSeedFinite
open scoped BigOperators

def b : Field := background originalBackground
def τ : ℝ := GroundNativeControls.originalTolerance
def ε : ℝ := 3022314549036573/302231454903657293676544
def orbit (n : ℕ) : ComplexField := (nativeUpdate τ b 0 (1/2))^[n] initial
def target : ComplexField := realEmbed (-(GroundOriginalContinuation.branch 0).1)
def eigenvalue : ℝ := energy b (positiveGround b)

theorem background_arithmetic : ∀ i : Fin 8, 0 ≤ originalBackground i ∧ originalBackground i ≤ 2/5 := by
  decide +kernel

theorem background_budget : ∀ i, 0 ≤ b i ∧ b i ≤ 2/5 := by
  intro i
  dsimp only [b, background]
  constructor
  · exact_mod_cast (background_arithmetic i).1
  · have h : (originalBackground i : ℝ) ≤ (((2/5 : ℚ) : ℝ)) := by
      exact_mod_cast (background_arithmetic i).2
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h

theorem tolerance_budget : 0 ≤ τ ∧ τ < 1/2 ∧ (1/100000000 : ℝ) < ε := by
  norm_num [τ, GroundNativeControls.originalTolerance, ε]

theorem target_ground_data : complexNormSq target = 1 ∧
    (∀ i, complexHamiltonian b target i = (eigenvalue : ℂ)*target i) ∧
    0 ≤ eigenvalue ∧ eigenvalue ≤ 2/5 := by
  have hg := (positiveGround_spec b).2
  have he : target = -realEmbed (positiveGround b) := by
    rw [target, ← ground_identity, GroundNativeReflection.realEmbed_neg]; rfl
  refine ⟨?_, ?_, ground_energy_budget hg background_budget⟩
  · rw [he, GroundNativeReflection.complexNormSq_neg]; exact realEmbed_normalized hg.1
  · intro i
    have hn : complexHamiltonian b (-realEmbed (positiveGround b)) i =
        -complexHamiltonian b (realEmbed (positiveGround b)) i := by
      simp [complexHamiltonian]; ring
    rw [he, hn, realEmbed_eigen hg i]
    change -(↑eigenvalue * realEmbed (positiveGround b) i) = ↑eigenvalue * -realEmbed (positiveGround b) i
    ring

theorem candidate_zero_return (z : ComplexField) : nativeCandidate b 0 z = -target := by
  rw [nativeCandidate, source_zero]
  rw [target, ← ground_identity, GroundNativeReflection.realEmbed_neg, neg_neg]
  rfl

theorem orbit_unit (n : ℕ) : complexNormSq (orbit n) = 1 := by
  cases n with
  | zero => exact initial_unit
  | succ n =>
    rw [orbit, Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit tolerance_budget.1 (actual_seed_zero_convergence.2 n).2

theorem orbit_distance_sixty : l2 (orbit 60-target) < 1/500000000 := by
  have h := actual_seed_sixty_distance_sq
  change complexNormSq (orbit 60-target) < (1/500000000 : ℝ)^2 at h
  rw [← l2_sq] at h
  nlinarith [l2_nonneg (orbit 60-target)]

theorem orbit_distance_fifty_nine : l2 (orbit 59-target) < 3/1000000000 := by
  have h := actual_seed_fifty_nine_distance_sq
  change complexNormSq (orbit 59-target) < (3/1000000000 : ℝ)^2 at h
  rw [← l2_sq] at h
  nlinarith [l2_nonneg (orbit 59-target)]

theorem last_update_threshold : lastUpdateResidual τ b 0 (1/2) (orbit 59) < ε := by
  have he : nativeUpdate τ b 0 (1/2) (orbit 59) = orbit 60 := by
    rw [orbit, show 60 = 59+1 from rfl, Function.iterate_succ_apply']; rfl
  rw [lastUpdateResidual, he]
  have hd := l2_sub_triangle (orbit 60) target (orbit 59)
  have hn : target-orbit 59 = -(orbit 59-target) := by abel
  rw [hn, l2_neg] at hd
  linarith [orbit_distance_sixty, orbit_distance_fifty_nine, tolerance_budget.2.2]

theorem final_fixed_gap_threshold : finalFixedGap τ b 0 (orbit 60) < ε ∧
    τ < ‖overlap (nativePhase τ (nativeCandidate b 0 (orbit 60)) (orbit 60)) (orbit 60)‖ := by
  have hd := double_phase_gap target_ground_data.1 (orbit_unit 60) orbit_distance_sixty.le
    (by norm_num : (0:ℝ) ≤ 1/500000000) (by norm_num : 2*(1/500000000 : ℝ)^2 ≤ 1)
    tolerance_budget.1 (by linarith [tolerance_budget.2.1] : τ < 1-2*(1/500000000 : ℝ)^2)
  have he : nativePhase τ (nativeCandidate b 0 (orbit 60)) (orbit 60) =
      nativePhase τ target (orbit 60) := by
    rw [candidate_zero_return, nativePhase_real_sign_invariant tolerance_budget.1 hd.1]
  constructor
  · rw [finalFixedGap, he]
    linarith [hd.2.2, tolerance_budget.2.2]
  · rw [he]; exact hd.2.1

theorem final_eigen_threshold : finalEigenResidual b 0 (orbit 60) < ε := by
  rw [finalEigenResidual, source_zero]
  have h := eigen_residual_bound target_ground_data.2.1 (orbit_unit 60)
    (shifted_l2_bound background_budget target_ground_data.2.2)
  have hd := orbit_distance_sixty
  have hp : (l2 (orbit 60-target))^2 ≤ (1/500000000 : ℝ)^2 := by
    nlinarith [l2_nonneg (orbit 60-target)]
  have ht : (12/5 : ℝ)*(1/500000000)+(12/5 : ℝ)*(1/500000000)^2 < 1/100000000 := by norm_num
  nlinarith [tolerance_budget.2.2]

theorem final_sourcing_threshold : finalSourcingResidual b 0 (orbit 60) = 0 ∧
    finalSourcingResidual b 0 (orbit 60) < ε := by
  rw [sourcing_self_comparison_zero]
  constructor
  · rfl
  · linarith [tolerance_budget.2.2]

/-- The exact mathematical source's four convergence tests all pass at60.
This retains the actual twice-aligned gap and Rayleigh energy diagnostic. -/
theorem actual_seed_zero_sixty_convergence_tests : MeetsConvergence τ ε b 0 (1/2) (orbit 59) (orbit 60) ∧
    ∀ n : ℕ, ActivePhase τ b 0 (orbit n) ∧ NativeLegal τ b 0 (1/2) (orbit n) := by
  exact ⟨⟨last_update_threshold.le, final_fixed_gap_threshold.1.le, final_eigen_threshold.le,
    final_sourcing_threshold.2.le⟩, actual_seed_zero_convergence.2⟩

end
end SbtCosmo.Derivation.GroundOriginalResiduals
