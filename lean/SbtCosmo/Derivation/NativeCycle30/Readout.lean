import SbtCosmo.Derivation.NativeCycle30.Source
import SbtCosmo.Derivation.NativeOriginalSeedCycleReturn
namespace SbtCosmo.Derivation.NativeCycle30
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval Metric Filter
open scoped Topology

theorem actual_density_cycle : ∃ z₀ z₁ : ComplexField,
    g z₀ = z₁ ∧ g z₁ = z₀ ∧ complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
    (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
    ∀ z : ComplexField, NativeCycleFrame30.T.symm (unpack z) ∈
        closedBall pair.first.center (Step000.ρ : ℝ) →
      Tendsto (fun n : ℕ => Complex.normSq ((g^[2*n]) z 4)) atTop (nhds (Complex.normSq (z₀ 4))) ∧
      Tendsto (fun n : ℕ => Complex.normSq ((g^[2*n+1]) z 4)) atTop (nhds (Complex.normSq (z₁ 4))) ∧
      (∀ᶠ n : ℕ in atTop, (9/20 : ℝ) < Complex.normSq ((g^[2*n+1]) z 4)-Complex.normSq ((g^[2*n]) z 4)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq ((g^[n]) z 4)) atTop (nhds l) := by
  obtain ⟨z₀,z₁,h01,h10,_,hu0,hu1,hgap,hr⟩ := actual_source_cycle
  refine ⟨z₀,z₁,h01,h10,hu0,hu1,hgap,fun z hz => ?_⟩
  have h := hr z hz
  exact NativeOriginalSeedCycleReturn.density_returns (u := fun n => (g^[n]) z) h.1 h.2.1 hgap (by norm_num)
end
end SbtCosmo.Derivation.NativeCycle30
