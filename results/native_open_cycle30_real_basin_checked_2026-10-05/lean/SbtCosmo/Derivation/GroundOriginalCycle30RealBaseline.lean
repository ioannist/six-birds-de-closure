import NativeCycleSeed30RealReturn
import SbtCosmo.Derivation.GroundOriginalCycle30Baseline

/-! The baseline point used for the common basin is itself exactly real.
This follows from the previously earned real cycle and uniqueness of the
actual original-seed even limit. The incoming seed is not assumed real. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30RealBaseline
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration Filter Metric
open GroundOriginalCycle30Baseline
open scoped Topology ContDiff

theorem actual_real_baseline : ∃ a : State,
    NativeRealProfiles.IsReal (source a) ∧
    ((GroundOriginalCycle30Baseline.map baseline)^[2]) a = a ∧
    ‖fderiv ℝ ((GroundOriginalCycle30Baseline.map baseline)^[2]) a‖ < 1 ∧
    (baseline,a) ∈ pairGuard ∧
    (9/20 : ℝ) < Complex.normSq (source (GroundOriginalCycle30Baseline.map baseline a) 4)-
      Complex.normSq (source a 4) ∧
    Tendsto (fun n : ℕ => ((GroundOriginalCycle30Baseline.map baseline)^[2])^[n] seed)
      atTop (nhds a) := by
  obtain ⟨a,hf,hd,hg,hgap,he⟩ := actual_baseline
  obtain ⟨z₀,z₁,hreal,_,_,_,_,_,_,he',_⟩ := NativeCycleSeed30.RealReturn.original_seed_cycle_real
  have hsource : Tendsto (fun n : ℕ => (NativeCycleSeed30.g^[2*n]) GroundOriginalSeed.initial)
      atTop (nhds (source a)) := by
    have hh := source_continuous.continuousAt.tendsto.comp he
    simpa only [Function.comp_def,← Function.iterate_mul,source_iterate,source_seed,
      NativeCycleSeed30.g,baseline] using hh
  have hr : NativeRealProfiles.IsReal (source a) := by
    rw [tendsto_nhds_unique hsource he']
    exact hreal
  exact ⟨a,hr,hf,hd,hg,hgap,he⟩
end
end SbtCosmo.Derivation.GroundOriginalCycle30RealBaseline
