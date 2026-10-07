import SbtCosmo.Derivation.GroundOriginalCycle30AttractorLanding
import SbtCosmo.Derivation.GroundNativeSourceParameterSmooth

/-! Full complex attraction neighborhoods at both phases of the same earned
nearby real two-cycle. Arbitrary nearby initial states need not start real or
unit; both guards hold from time zero and unit norms hold after update one. -/
namespace SbtCosmo.Derivation.GroundOriginalCycle30TwoPhaseBasin
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundNativePhase GroundNativeIteration
open GroundOriginalCycle30Baseline GroundOriginalCycle30OpenReturn
open Filter Metric
open scoped Topology

def Guard (p : Parameter) (z : ComplexField) : Prop :=
  ActivePhase (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 z ∧
  NativeLegal (GroundNativePrefixInitial.τ : ℝ) p.1 p.2 (1/2) z

def Landing (p : Parameter) (z₀ z₁ z : ComplexField) : Prop :=
  Tendsto (fun n : ℕ => (native p)^[2*n] z) atTop (nhds z₀) ∧
  Tendsto (fun n : ℕ => (native p)^[2*n+1] z) atTop (nhds z₁) ∧
  (∀ n : ℕ, Guard p ((native p)^[n] z)) ∧
  ∀ n : ℕ, complexNormSq ((native p)^[n+1] z) = 1

theorem shifted_landing {p : Parameter} {z₀ z₁ z : ComplexField}
    (hg : Guard p z) (h : Landing p z₀ z₁ (native p z)) :
    Landing p z₁ z₀ z := by
  have he : Tendsto (fun n : ℕ => (native p)^[2*(n+1)] z) atTop (nhds z₁) := by
    exact h.2.1
  refine ⟨(tendsto_add_atTop_iff_nat 1).1 he,?_,?_,?_⟩
  · simpa only [Function.iterate_succ_apply] using h.1
  · intro n
    cases n with
    | zero => exact hg
    | succ n =>
      rw [Function.iterate_succ_apply]
      exact h.2.2.1 n
  · intro n
    cases n with
    | zero =>
      exact GroundNativeEscape.nativeUpdate_unit
        (by rw [GroundNativePrefixInitial.tolerance_return];exact GroundNativeControls.originalTolerance_guard.1) hg.2
    | succ n =>
      simpa only [Nat.succ_eq_add_one,Function.iterate_succ_apply] using h.2.2.2 n

/-- Pull the earned first-phase basin back through one guarded source update. -/
theorem opposite_phase_neighborhood {p : Parameter} {z₀ z₁ : ComplexField}
    (h01 : native p z₀ = z₁) (h10 : native p z₁ = z₀)
    {s₀ : Set ComplexField} (hs₀ : s₀ ∈ nhds z₀)
    (hlocal : ∀ z ∈ s₀, Landing p z₀ z₁ z) :
    ∃ s₁ : Set ComplexField, s₁ ∈ nhds z₁ ∧ ∀ z ∈ s₁, Landing p z₁ z₀ z := by
  have hg : Guard p z₁ := by
    have h := (hlocal z₀ (mem_of_mem_nhds hs₀)).2.2.1 1
    simpa only [Function.iterate_one,h01] using h
  have hτ : 0 ≤ (GroundNativePrefixInitial.τ : ℝ) := by
    rw [GroundNativePrefixInitial.tolerance_return]
    exact GroundNativeControls.originalTolerance_guard.1
  have hmap : ContinuousAt (native p) z₁ :=
    (GroundNativeSourceParameterSmooth.native_joint_smooth_at hτ hg.1 hg.2).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
  have hnearGuard : ∀ᶠ z in nhds z₁, Guard p z :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (GroundNativeSourceParameterSmooth.native_joint_guards_near hτ hg.1 hg.2)
  have hnearMap : ∀ᶠ z in nhds z₁, native p z ∈ s₀ :=
    hmap.eventually (by simpa only [h10] using hs₀)
  refine ⟨{z | Guard p z ∧ native p z ∈ s₀},hnearGuard.and hnearMap,?_⟩
  intro z hz
  exact shifted_landing hz.1 (hlocal (native p z) hz.2)

/-- The same exactly real attracting source cycle has full complex neighborhoods
at both phases, together with the original complex seed's earned returns. -/
theorem open_both_phases_attracting_cycle : ∃ δ > 0, ∀ p ∈ closedBall baseline δ,
    ∃ z₀ z₁ : ComplexField,
      NativeRealProfiles.IsReal z₀ ∧ NativeRealProfiles.IsReal z₁ ∧
      native p z₀ = z₁ ∧ native p z₁ = z₀ ∧
      complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
      (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
      Landing p z₀ z₁ GroundOriginalSeed.initial ∧
      (∀ n : ℕ, complexNormSq ((native p)^[n] GroundOriginalSeed.initial) = 1) ∧
      ∃ s₀ s₁ : Set ComplexField,
        s₀ ∈ nhds z₀ ∧ s₁ ∈ nhds z₁ ∧
        (∀ z ∈ s₀, Landing p z₀ z₁ z) ∧
        ∀ z ∈ s₁, Landing p z₁ z₀ z := by
  obtain ⟨δ,hδ,hreturns⟩ := GroundOriginalCycle30AttractorLanding.open_real_attracting_cycle
  refine ⟨δ,hδ,fun p hp => ?_⟩
  obtain ⟨z₀,z₁,hr₀,hr₁,h01,h10,hu₀,hu₁,hgap,he,ho,hguards,s₀,hs₀,hlocal⟩ := hreturns p hp
  have hl : ∀ z ∈ s₀, Landing p z₀ z₁ z := hlocal
  obtain ⟨s₁,hs₁,hl₁⟩ := opposite_phase_neighborhood h01 h10 hs₀ hl
  refine ⟨z₀,z₁,hr₀,hr₁,h01,h10,hu₀,hu₁,hgap,?_,fun n => (hguards n).2.2,s₀,s₁,hs₀,hs₁,hl,hl₁⟩
  exact ⟨he,ho,fun n => ⟨(hguards n).1,(hguards n).2.1⟩,fun n => (hguards (n+1)).2.2⟩
end
end SbtCosmo.Derivation.GroundOriginalCycle30TwoPhaseBasin
