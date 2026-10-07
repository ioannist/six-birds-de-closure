import SbtCosmo.Derivation.GroundOriginalCycle30FiniteVerdicts
import SbtCosmo.Derivation.GroundOriginalCycle30AttractorLanding

/-! The same positive parameter neighborhood supports the finite experiment's
failed verdicts at every truncation within sixty updates and the original
seed's infinite real-cycle return.
The original source runs a fixed iteration count before its convergence flag.
Finite-prefix verdicts are earned independently of eventual failure. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30FiniteAttractorLanding
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration GroundSourceDiagnostics Filter Metric
open GroundOriginalCycle30FiniteVerdicts
open scoped Topology

theorem baseline_return : baseline = GroundOriginalCycle30Baseline.baseline := rfl

theorem native_return (p : Parameter) : native p = GroundOriginalCycle30OpenReturn.native p := by
  unfold native GroundOriginalCycle30OpenReturn.native
  rw [GroundNativePrefixInitial.tolerance_return]

theorem orbit_return (p : Parameter) (n : ℕ) :
    orbit p n = (GroundOriginalCycle30OpenReturn.native p)^[n] GroundOriginalSeed.initial := by
  rw [orbit,native_return]

/-- The finite sixty-update failure and the guarded original-seed attraction to
an exactly real two-cycle hold simultaneously on a genuine open neighborhood. -/
theorem open_finite_and_real_cycle : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    ∃ z₀ z₁ : ComplexField,
      NativeRealProfiles.IsReal z₀ ∧ NativeRealProfiles.IsReal z₁ ∧
      native p z₀ = z₁ ∧ native p z₁ = z₀ ∧
      complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
      (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
      Tendsto (fun n : ℕ => orbit p (2*n)) atTop (nhds z₀) ∧
      Tendsto (fun n : ℕ => orbit p (2*n+1)) atTop (nhds z₁) ∧
      (∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance p.1 p.2 (orbit p n) ∧
        NativeLegal GroundNativeControls.originalTolerance p.1 p.2 (1/2) (orbit p n) ∧
        complexNormSq (orbit p n) = 1) ∧
      (¬ ∃ l, Tendsto (fun n : ℕ => orbit p n) atTop (nhds l)) ∧
      (¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq (orbit p n 4)) atTop (nhds l)) ∧
      (∀ n : ℕ, n < 60 → ¬ MeetsConvergence GroundNativeControls.originalTolerance
        GroundOriginalResiduals.ε p.1 p.2 (1/2) (orbit p n) (orbit p (n+1))) ∧
      ∃ s : Set ComplexField, s ∈ nhds z₀ ∧ ∀ z ∈ s,
        Tendsto (fun n : ℕ => (native p)^[2*n] z) atTop (nhds z₀) ∧
        Tendsto (fun n : ℕ => (native p)^[2*n+1] z) atTop (nhds z₁) ∧
        (∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance p.1 p.2 ((native p)^[n] z) ∧
          NativeLegal GroundNativeControls.originalTolerance p.1 p.2 (1/2) ((native p)^[n] z)) ∧
        ∀ n : ℕ, complexNormSq ((native p)^[n+1] z) = 1 := by
  obtain ⟨δf,hδf,hfinite⟩ := open_first_sixty_fail
  obtain ⟨δr,hδr,hreal⟩ := GroundOriginalCycle30AttractorLanding.open_real_attracting_cycle
  refine ⟨min δf δr,lt_min hδf hδr,fun p hp => ?_⟩
  have hpf : p ∈ closedBall baseline δf :=
    mem_closedBall.mpr ((mem_closedBall.mp hp).trans (min_le_left _ _))
  have hpr : p ∈ closedBall GroundOriginalCycle30Baseline.baseline δr :=
    mem_closedBall.mpr ((mem_closedBall.mp hp).trans (min_le_right _ _))
  obtain ⟨z₀,z₁,hreal₀,hreal₁,h01,h10,hu₀,hu₁,hgap,he',ho',hg',s,hs,hlocal⟩ := hreal p hpr
  have he : Tendsto (fun n : ℕ => orbit p (2*n)) atTop (nhds z₀) := by
    simpa only [orbit_return] using he'
  have ho : Tendsto (fun n : ℕ => orbit p (2*n+1)) atTop (nhds z₁) := by
    simpa only [orbit_return] using ho'
  have hg (n : ℕ) : ActivePhase GroundNativeControls.originalTolerance p.1 p.2 (orbit p n) ∧
      NativeLegal GroundNativeControls.originalTolerance p.1 p.2 (1/2) (orbit p n) ∧
      complexNormSq (orbit p n) = 1 := by
    simpa only [orbit_return,GroundNativePrefixInitial.tolerance_return] using hg' n
  have hne : z₁ ≠ z₀ := by
    intro h
    rw [h] at hgap
    linarith
  have hd := NativeOriginalSeedCycleReturn.density_returns
    (u := fun n => orbit p n) he ho hgap (by norm_num)
  refine ⟨z₀,z₁,hreal₀,hreal₁,?_,?_,hu₀,hu₁,hgap,he,ho,hg,?_,hd.2.2.2,?_,s,hs,?_⟩
  · simpa only [native_return] using h01
  · simpa only [native_return] using h10
  · exact NativeOriginalSeedCycleReturn.no_limit_of_distinct_subsequences (fun n => orbit p n) he ho hne
  · intro n hn
    exact ((hfinite p hpf).1 n hn).2.2.2
  · simpa only [native_return,GroundNativePrefixInitial.tolerance_return] using hlocal
end
end SbtCosmo.Derivation.GroundOriginalCycle30FiniteAttractorLanding
