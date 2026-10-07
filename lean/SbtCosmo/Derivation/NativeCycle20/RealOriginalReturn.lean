import SbtCosmo.Derivation.NativeCycle20.RealProfiles
import SbtCosmo.Derivation.NativeCycle20.OriginalReturn
namespace SbtCosmo.Derivation.NativeCycle20.RealOriginalReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration NativeRealProfiles Metric Filter
open scoped Topology

/-- The exact original seed has real even/odd cycle limits provided its even
entry is supplied. This statement neither supplies entry nor removes the
separate finite-prefix source guards needed by the complete runtime return. -/
theorem real_even_odd_limits_of_entry (N : ℕ)
    (hentry : NativeCycleFrame20.T.symm (unpack ((g^[2*N]) GroundOriginalSeed.initial)) ∈
      closedBall (centers 0) (Step000.ρ : ℝ)) :
    ∃ a c : ComplexField,
      IsReal a ∧ IsReal c ∧ g a = c ∧ g c = a ∧ c ≠ a ∧
      complexNormSq a = 1 ∧ complexNormSq c = 1 ∧
      (1/4 : ℝ) < Complex.normSq (c 4)-Complex.normSq (a 4) ∧
      Tendsto (fun n : ℕ => (g^[2*n]) GroundOriginalSeed.initial) atTop (nhds a) ∧
      Tendsto (fun n : ℕ => (g^[2*n+1]) GroundOriginalSeed.initial) atTop (nhds c) := by
  obtain ⟨a,c,ha,hc,h01,h10,hne,hu0,hu1,hgap,hreturn⟩ := RealProfiles.actual_source_cycle_real
  have hr := hreturn ((g^[2*N]) GroundOriginalSeed.initial) hentry
  have ht := NativeOriginalSeedCycleReturn.even_entry_returns g N hr.1 hr.2.1
  exact ⟨a,c,ha,hc,h01,h10,hne,hu0,hu1,hgap,ht.1,ht.2⟩

/-- Every pair of actual original-seed subsequence limits agrees with the real
local cycle. Witness selection cannot change this conclusion. -/
theorem limits_real_of_entry (N : ℕ)
    (hentry : NativeCycleFrame20.T.symm (unpack ((g^[2*N]) GroundOriginalSeed.initial)) ∈
      closedBall (centers 0) (Step000.ρ : ℝ))
    {a c : ComplexField}
    (he : Tendsto (fun n : ℕ => (g^[2*n]) GroundOriginalSeed.initial) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => (g^[2*n+1]) GroundOriginalSeed.initial) atTop (nhds c)) :
    IsReal a ∧ IsReal c := by
  obtain ⟨r,s,hr,hs,_,_,_,_,_,_,he',ho'⟩ := real_even_odd_limits_of_entry N hentry
  constructor
  · rw [tendsto_nhds_unique he he']
    exact hr
  · rw [tendsto_nhds_unique ho ho']
    exact hs
end
end SbtCosmo.Derivation.NativeCycle20.RealOriginalReturn
