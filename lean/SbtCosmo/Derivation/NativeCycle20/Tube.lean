import SbtCosmo.Derivation.NativeCycle20.PowerArithmetic
namespace SbtCosmo.Derivation.NativeCycle20
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval GroundNativeBox Metric
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open StateBoxComposition NativeTransportPowers NativePairCertificates NativeFinitePairJets
open scoped BigOperators Topology
theorem self_defect : dist ((f^[8]) (centers 0)) (centers 0) ≤ (selfDefect : ℝ) := by
  have h := pointTube.enclosed NativeCycleFrame20.background_sound
    (Metric.mem_closedBall_self (by norm_num [pointTube,pointRadii] : (0 : ℝ) ≤ (pointTube.radii 0 : ℝ))) (Fin.last 4)
  have he := GroundFiniteNativeTransport.endpoint_distance h center_gap
  convert he using 1; norm_num [pointTube,pointRadii,selfDefect,centerGap,Fin.last]

theorem cycle_budgets : powerRate < 1 ∧ powerRate*Step000.ρ+selfDefect ≤ Step000.ρ ∧
    Pair000.pairRate*(selfDefect/(1-powerRate))+secondSelfDefect ≤ Step000.ρ ∧
    (Step001.input.R 4).hi < (Step000.input.R 4).lo := by decide +kernel

/-- An actual eighth-iterate fixed point is constructed, then commutation and
local uniqueness identify actual period two through the separate inner budget. -/
theorem actual_cycle : ∃ a ∈ closedBall (centers 0) (Step000.ρ : ℝ),
    (f^[2]) a = a ∧ f a ≠ a ∧ dist a (centers 0) ≤
      (selfDefect : ℝ)/(1-(powerRate : ℝ)) ∧
    ∀ y ∈ closedBall (centers 0) (Step000.ρ : ℝ),
      Filter.Tendsto (fun n : ℕ => (f^[2*n]) y) Filter.atTop (nhds a) ∧
      Filter.Tendsto (fun n : ℕ => (f^[2*n+1]) y) Filter.atTop (nhds (f a)) ∧
      (∀ n : ℕ, dist (((f^[8])^[n]) y) a ≤ (powerRate : ℝ)^n*dist y a) ∧
      ¬ ∃ l, Filter.Tendsto (fun n : ℕ => (f^[n]) y) Filter.atTop (nhds l) := by
  apply NativeActualCycleConstruction.actual_period_two_from_power_certificate (p := 4) f
    (by omega) (by exact_mod_cast Step000.radius_nonneg)
    (by change (powerRate : ℝ) < 1; exact_mod_cast cycle_budgets.1) power_lipschitz self_defect
    (by change (powerRate : ℝ)*(Step000.ρ : ℝ)+(selfDefect : ℝ) ≤ (Step000.ρ : ℝ); exact_mod_cast cycle_budgets.2.1)
    (Pair000.pair.lipschitz NativeCycleFrame20.background_sound)
    second_self_defect
    (by change (Pair000.pairRate : ℝ)*((selfDefect : ℝ)/(1-(powerRate : ℝ)))+(secondSelfDefect : ℝ) ≤ (Step000.ρ : ℝ); exact_mod_cast cycle_budgets.2.2.1)
  · intro a ha
    exact Pair000.pair.separated NativeCycleFrame20.background_sound cycle_budgets.2.2.2 ha
  · intro a ha j
    exact (NativeFinitePairJets.derivative_power tube NativeCycleFrame20.background_sound ha
      (2*j.val) (by omega)).continuousAt
  · intro a ha
    exact (native_derivative Step000.transport NativeCycleFrame20.background_sound ha).continuousAt
end
end SbtCosmo.Derivation.NativeCycle20
