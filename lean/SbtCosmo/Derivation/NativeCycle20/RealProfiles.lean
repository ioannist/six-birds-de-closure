import SbtCosmo.Derivation.NativeCycle20.Source
import SbtCosmo.Derivation.NativeRealProfiles
namespace SbtCosmo.Derivation.NativeCycle20.RealProfiles
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration Metric Filter NativeRealProfiles
open scoped Topology

theorem center_real : IsReal (source (centers 0)) := by
  change IsReal (pack (NativeCycleFrame20.T
    (NativeCycleFrame20.T.symm (GroundNativeTransportGeometry.point Step000.u Step000.v))))
  rw [NativeCycleFrame20.T.apply_symm_apply]
  intro i
  fin_cases i <;> norm_num [GroundNativeTransportGeometry.point,pack,Step000.v]

/-- Genuine attracting source two-cycles have exactly real profiles. Their
attraction and guards still cover every complex start in the full16D ball. -/
theorem actual_source_cycle_real : ∃ z₀ z₁ : ComplexField,
    IsReal z₀ ∧ IsReal z₁ ∧ g z₀ = z₁ ∧ g z₁ = z₀ ∧ z₁ ≠ z₀ ∧
    complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
    (1/4 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
    ∀ z : ComplexField, NativeCycleFrame20.T.symm (unpack z) ∈
        closedBall (centers 0) (Step000.ρ : ℝ) →
      Tendsto (fun n : ℕ => (g^[2*n]) z) atTop (nhds z₀) ∧
      Tendsto (fun n : ℕ => (g^[2*n+1]) z) atTop (nhds z₁) ∧
      (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
        (NativeCycleFrame20.κ : ℝ) ((g^[n]) z) ∧
        NativeLegal (GroundNativePrefixInitial.τ : ℝ)
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground)
          (NativeCycleFrame20.κ : ℝ) (1/2) ((g^[n]) z)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => (g^[n]) z) atTop (nhds l) := by
  obtain ⟨a,b,h01,h10,hne,hu0,hu1,hgap,hreturn⟩ := actual_source_cycle
  have hcenter : NativeCycleFrame20.T.symm (unpack (source (centers 0))) ∈
      closedBall (centers 0) (Step000.ρ : ℝ) := by
    change NativeCycleFrame20.T.symm (packCLE.symm (packCLE (NativeCycleFrame20.T (centers 0)))) ∈ _
    rw [packCLE.symm_apply_apply,NativeCycleFrame20.T.symm_apply_apply]
    exact mem_closedBall_self (by exact_mod_cast Step000.radius_nonneg)
  have hlimits := hreturn (source (centers 0)) hcenter
  have hreal (n : ℕ) : IsReal ((g^[n]) (source (centers 0))) := by
    exact iterate_real _ _ _ (by exact_mod_cast Step000.threshold_nonneg) center_real n
  have ha : IsReal a := limit_real (fun n => hreal (2*n)) hlimits.1
  have hb : IsReal b := limit_real (fun n => hreal (2*n+1)) hlimits.2.1
  exact ⟨a,b,ha,hb,h01,h10,hne,hu0,hu1,hgap,hreturn⟩
end
end SbtCosmo.Derivation.NativeCycle20.RealProfiles
