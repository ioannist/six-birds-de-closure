import NativeCycleSeed20PrefixFailures
import SbtCosmo.Derivation.GroundFiniteParameterContinuity
import SbtCosmo.Derivation.GroundNativeSourceParameterSmooth

/-! Failed convergence verdicts for every truncation at updates1..60 persist on a positive joint
background/coupling neighborhood. The populated prefix, not eventual failure,
supplies the strict defects. The source uses a fixed iteration count and tests
convergence afterward; no implemented early-exit branch is asserted. No infinite
orbit hypothesis is used. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle20FiniteVerdicts
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean GroundSourceDiagnostics
open Filter Metric
open scoped Topology
abbrev Parameter := Field × ℝ

def baseline : Parameter :=
  (GroundKernelTube.background GroundOriginalFirstTube.originalBackground,(NativeCycleFrame20.κ : ℝ))
def native (p : Parameter) : ComplexField → ComplexField :=
  nativeUpdate GroundNativeControls.originalTolerance p.1 p.2 (1/2)
def orbit (p : Parameter) (n : ℕ) : ComplexField := (native p)^[n] GroundOriginalSeed.initial
def stepLength (p : Parameter) (n : ℕ) : ℝ := l2 (orbit p (n+1)-orbit p n)

theorem l2_continuous : Continuous l2 := by
  have heq : l2 = (fun z : ComplexField => Real.sqrt (complexNormSq z)) := by
    funext z
    rw [← l2_sq,Real.sqrt_sq (l2_nonneg z)]
  rw [heq]
  unfold complexNormSq
  fun_prop

theorem baseline_guards (n : ℕ) (hn : n < 60) :
    ActivePhase GroundNativeControls.originalTolerance baseline.1 baseline.2 (orbit baseline n) ∧
    NativeLegal GroundNativeControls.originalTolerance baseline.1 baseline.2 (1/2) (orbit baseline n) :=
  NativeCycleSeed20.Sixty.finite_guards n hn

theorem orbit_continuous_at (n : ℕ) (hn : n ≤ 60) :
    ContinuousAt (fun p : Parameter => orbit p n) baseline := by
  apply GroundFiniteParameterContinuity.finite_iterate_parameter_continuous_at
  intro j hj
  have h := baseline_guards j (by omega)
  exact (GroundNativeSourceParameterSmooth.native_joint_smooth_at
    GroundNativeControls.originalTolerance_guard.1 h.1 h.2).continuousAt

theorem stepLength_continuous_at (n : ℕ) (hn : n < 60) :
    ContinuousAt (fun p : Parameter => stepLength p n) baseline :=
  l2_continuous.continuousAt.comp
    ((orbit_continuous_at (n+1) (by omega)).sub (orbit_continuous_at n hn.le))

/-- Every literal last-update norm in the populated original first sixty
steps is strictly above the original convergence tolerance. -/
theorem strict_stepLength_baseline (n : ℕ) (hn : n < 60) :
    GroundOriginalResiduals.ε < stepLength baseline n := by
  by_cases h : n < 59
  · let j : Fin 59 := ⟨n,h⟩
    have he : GroundOriginalResiduals.ε = (NativeCycleSeed20.PrefixFailures.εRat : ℝ) := by
      norm_num [GroundOriginalResiduals.ε,NativeCycleSeed20.PrefixFailures.εRat]
    have hg : (NativeCycleSeed20.PrefixFailures.εRat : ℝ) <
        (NativeBoxUpdateGap.gap (NativeCycleSeed20.PrefixFailures.previousBox j)
          (NativeCycleSeed20.PrefixFailures.currentBox j) (NativeCycleSeed20.PrefixFailures.imag j)
          (NativeCycleSeed20.PrefixFailures.positive j) (NativeCycleSeed20.PrefixFailures.coordinate j) : ℝ) := by
      exact_mod_cast NativeCycleSeed20.PrefixFailures.gap_arithmetic j
    have hbound := NativeBoxUpdateGap.gap_le_update
      (NativeCycleSeed20.PrefixFailures.previous_enclosed j) (NativeCycleSeed20.PrefixFailures.current_enclosed j)
      (NativeCycleSeed20.PrefixFailures.imag j) (NativeCycleSeed20.PrefixFailures.positive j)
      (NativeCycleSeed20.PrefixFailures.coordinate j)
    rw [he]
    exact hg.trans_le hbound
  · have he : n = 59 := by omega
    subst n
    have hε : GroundOriginalResiduals.ε < (1/4 : ℝ) := by norm_num [GroundOriginalResiduals.ε]
    have hg := NativeCycleSeed20.SixtyGeometry.update_gap_of_enclosures
      NativeCycleSeed20.Sixty.previous_enclosed NativeCycleSeed20.Sixty.current_enclosed
    exact hε.trans hg

/-- Every source convergence verdict after updates1..60 fails on a genuine open parameter
neighborhood, attached to a guarded unit original-seed execution through 60. -/
theorem open_first_sixty_fail : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    (∀ n : ℕ, n < 60 →
      ActivePhase GroundNativeControls.originalTolerance p.1 p.2 (orbit p n) ∧
      NativeLegal GroundNativeControls.originalTolerance p.1 p.2 (1/2) (orbit p n) ∧
      GroundOriginalResiduals.ε < stepLength p n ∧
      ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε p.1 p.2 (1/2)
        (orbit p n) (orbit p (n+1))) ∧
    ∀ n : ℕ, n ≤ 60 → complexNormSq (orbit p n) = 1 := by
  have hfail (n : ℕ) (hn : n < 60) : ∀ᶠ p in nhds baseline,
      GroundOriginalResiduals.ε < stepLength p n :=
    (stepLength_continuous_at n hn).eventually (Ioi_mem_nhds (strict_stepLength_baseline n hn))
  have hguard (n : ℕ) (hn : n < 60) : ∀ᶠ p in nhds baseline,
      ActivePhase GroundNativeControls.originalTolerance p.1 p.2 (orbit p n) ∧
      NativeLegal GroundNativeControls.originalTolerance p.1 p.2 (1/2) (orbit p n) := by
    have h := baseline_guards n hn
    have hp : ContinuousAt (fun p : Parameter => (p,orbit p n)) baseline :=
      continuousAt_id.prodMk (orbit_continuous_at n hn.le)
    exact hp.eventually (GroundNativeSourceParameterSmooth.native_joint_guards_near
      GroundNativeControls.originalTolerance_guard.1 h.1 h.2)
  have he (n : ℕ) (hn : n ∈ Finset.range 60) : ∀ᶠ p in nhds baseline,
      (ActivePhase GroundNativeControls.originalTolerance p.1 p.2 (orbit p n) ∧
        NativeLegal GroundNativeControls.originalTolerance p.1 p.2 (1/2) (orbit p n)) ∧
      GroundOriginalResiduals.ε < stepLength p n :=
    (hguard n (Finset.mem_range.mp hn)).and (hfail n (Finset.mem_range.mp hn))
  have hall := (eventually_all_finset (Finset.range 60)).2 he
  obtain ⟨δ,hδ,hnear⟩ := nhds_basis_closedBall.mem_iff.mp hall
  refine ⟨δ,hδ,fun p hp => ⟨(fun n hn => ?_),?_⟩⟩
  · have h := hnear hp n (Finset.mem_range.mpr hn)
    refine ⟨h.1.1,h.1.2,h.2,fun ht => ?_⟩
    have hstep : nativeUpdate GroundNativeControls.originalTolerance p.1 p.2 (1/2) (orbit p n) =
        orbit p (n+1) := (Function.iterate_succ_apply' (native p) n GroundOriginalSeed.initial).symm
    have hupdate : lastUpdateResidual GroundNativeControls.originalTolerance p.1 p.2 (1/2)
        (orbit p n) = stepLength p n := by rw [lastUpdateResidual,hstep];rfl
    exact (not_lt_of_ge ht.1) (by simpa only [hupdate] using h.2)
  · intro n hn
    cases n with
    | zero => exact GroundOriginalSeed.initial_unit
    | succ n =>
      have hguard' := (hnear hp n (Finset.mem_range.mpr (by omega))).1.2
      rw [orbit,Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 hguard'
end
end SbtCosmo.Derivation.GroundOriginalCycle20FiniteVerdicts
