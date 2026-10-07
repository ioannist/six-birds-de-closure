import NativeCycleSeed30Return
import SbtCosmo.Derivation.GroundNativeCouplingContinuation

/-! All baseline inputs for robust original-seed cycle continuation are earned
from the checked coupling-30 pair and original finite seed transport. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30Baseline
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open scoped Topology ContDiff
abbrev Parameter := GroundNativeCouplingContinuation.Parameter

def baseline : Parameter :=
  (GroundKernelTube.background GroundOriginalFirstTube.originalBackground,(NativeCycleFrame30.κ : ℝ))
def map (p : Parameter) : State → State :=
  GroundNativeCouplingContinuation.f NativeCycleFrame30.T (GroundNativePrefixInitial.τ : ℝ) (1/2) p
def source (x : State) : ComplexField := pack (NativeCycleFrame30.T x)
def seed : State := NativeCycleFrame30.T.symm (unpack GroundOriginalSeed.initial)
def guard : Set (Parameter × State) :=
  GroundNativeCouplingContinuation.guard NativeCycleFrame30.T (GroundNativePrefixInitial.τ : ℝ) (1/2)
def pairGuard : Set (Parameter × State) :=
  GroundNativeCouplingContinuation.pairGuard NativeCycleFrame30.T (GroundNativePrefixInitial.τ : ℝ) (1/2)

theorem threshold_nonneg : 0 ≤ (GroundNativePrefixInitial.τ : ℝ) := by
  exact_mod_cast NativeCycle30.Step000.threshold_nonneg

theorem baseline_map : map baseline = NativeCycle30.f := rfl

theorem source_seed : source seed = GroundOriginalSeed.initial := by
  dsimp [source,seed]
  rw [NativeCycleFrame30.T.apply_symm_apply]
  exact packCLE.apply_symm_apply _

theorem source_iterate (p : Parameter) (x : State) (n : ℕ) :
    source ((map p)^[n] x) = (nativeUpdate (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2))^[n] (source x) :=
  GroundNativeCouplingContinuation.source_iterate NativeCycleFrame30.T _ _ p x n

theorem source_continuous : Continuous source := packCLE.continuous.comp NativeCycleFrame30.T.continuous

theorem original_seed_guards (n : ℕ) : (baseline,(map baseline)^[n] seed) ∈ guard := by
  obtain ⟨z₀,z₁,_,_,_,_,_,_,_,hg,_⟩ := NativeCycleSeed30.original_seed_cycle
  have hsrc : source ((map baseline)^[n] seed) = (NativeCycleSeed30.g^[n]) GroundOriginalSeed.initial := by
    simpa only [source_seed] using source_iterate baseline seed n
  change ActivePhase _ _ _ (source _) ∧ NativeLegal _ _ _ _ (source _)
  rw [hsrc]
  exact ⟨(hg n).1,(hg n).2.1⟩

theorem strict_interior_budget :
    NativeCycle30.selfDefect/(1-NativeCycle30.pairRate) < NativeCycle30.Step000.ρ := by decide +kernel

/-- A cycle point, strict full-state two-step contraction, a density gap and
convergence from the actual original seed, with no incoming dynamical premise. -/
theorem actual_baseline : ∃ a : State,
    ((map baseline)^[2]) a = a ∧
    ‖fderiv ℝ ((map baseline)^[2]) a‖ < 1 ∧
    (baseline,a) ∈ pairGuard ∧
    (9/20 : ℝ) < Complex.normSq (source (map baseline a) 4)-Complex.normSq (source a 4) ∧
    Tendsto (fun n : ℕ => ((map baseline)^[2])^[n] seed) atTop (nhds a) := by
  obtain ⟨a,ha,hfix,_,hclose,hr⟩ := NativeCycle30.actual_cycle
  have hinner : a ∈ ball NativeCycle30.pair.first.center (NativeCycle30.Step000.ρ : ℝ) := by
    apply mem_ball.mpr
    exact hclose.trans_lt (by exact_mod_cast strict_interior_budget)
  have hnhds : closedBall NativeCycle30.pair.first.center (NativeCycle30.Step000.ρ : ℝ) ∈ nhds a :=
    mem_of_superset (isOpen_ball.mem_nhds hinner) ball_subset_closedBall
  have hd : ‖fderiv ℝ ((map baseline)^[2]) a‖ < 1 := by
    apply (norm_fderiv_le_of_lipschitzOn ℝ hnhds
      (NativeCycle30.pair.lipschitz NativeCycleFrame30.background_sound)).trans_lt
    change (NativeCycle30.pairRate : ℝ) < 1
    exact_mod_cast NativeCycle30.cycle_budgets.1
  have hguards := NativePairOrbit.guards NativeCycle30.pair NativeCycleFrame30.background_sound
    NativeCycle30.invariant ha
  have hpg : (baseline,a) ∈ pairGuard := by
    exact ⟨by simpa only [Function.iterate_zero_apply] using hguards 0,
      by simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using hguards 1⟩
  have hgap := NativePairDensity.pair_gap NativeCycle30.pair NativeCycleFrame30.background_sound
    ha NativeCycle30.density_gap_arithmetic
  rw [← NativePairDensity.complex_density,← NativePairDensity.complex_density] at hgap
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hgap
  have hentry : (NativeCycle30.f^[2*NativeCycleSeed30.N]) seed ∈
      closedBall NativeCycle30.pair.first.center (NativeCycle30.Step000.ρ : ℝ) := by
    have he := NativeCycleSeed30.original_seed_entry
    change NativeCycleFrame30.T.symm (unpack
      ((nativeUpdate (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2))^[2*NativeCycleSeed30.N]
        GroundOriginalSeed.initial)) ∈ _ at he
    rw [NativePairOrbit.coordinate_from_source (T := NativeCycleFrame30.T)
      (κ := NativeCycleFrame30.κ) (τ := GroundNativePrefixInitial.τ)
      (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) GroundOriginalSeed.initial (2*NativeCycleSeed30.N)] at he
    exact he
  have htail := hr _ hentry
  have he := (NativeOriginalSeedCycleReturn.even_entry_returns NativeCycle30.f NativeCycleSeed30.N
    htail.1 htail.2.1).1
  refine ⟨a,hfix,hd,hpg,hgap,?_⟩
  simpa only [← Function.iterate_mul,baseline_map] using he
end
end SbtCosmo.Derivation.GroundOriginalCycle30Baseline
