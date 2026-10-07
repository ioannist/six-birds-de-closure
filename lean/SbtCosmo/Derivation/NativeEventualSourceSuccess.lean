import SbtCosmo.Derivation.GroundComplexFiniteBudget
import Mathlib.Topology.Order.LeftRight

/-! Stable native limits imply eventual passage of the literal four source
diagnostics. This does not assert a first stopping index or IEEE execution. -/
namespace SbtCosmo.Derivation.NativeEventualSourceSuccess
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean
open GroundSourceDiagnostics Filter
open scoped Topology BigOperators

theorem continuous_source (b : Field) (κ : ℝ) :
    Continuous (complexSourcePotential b κ) := by
  unfold complexSourcePotential BackgroundSelection.potential complexGradient
  fun_prop

theorem continuous_candidate (b : Field) (κ : ℝ) :
    Continuous (nativeCandidate b κ) := by
  have hs := continuous_positiveGround.comp (continuous_source b κ)
  unfold nativeCandidate realEmbed
  fun_prop

theorem continuous_l2 : Continuous l2 := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 8 => ℂ)).norm

theorem candidate_at_negative_root {b u : Field} {κ : ℝ}
    (hf : GroundSourceJacobian.groundMap b κ u = u) :
    nativeCandidate b κ (realEmbed (-u)) = realEmbed u := by
  rw [GroundNativeReflection.realEmbed_neg, nativeCandidate,
    GroundNativeReflection.complexSourcePotential_neg, complexSourcePotential_realEmbed]
  change realEmbed (GroundSourceJacobian.groundMap b κ u) = realEmbed u
  rw [hf]

theorem small_budget_exists {τ ε C : ℝ} (hτ : τ < 1) (hε : 0 < ε) :
    ∃ d > 0, 2*d^2 ≤ 1 ∧ τ < 1-2*d^2 ∧ 4*d ≤ ε ∧ C*(d+d^2) ≤ ε := by
  have h1 : ∀ᶠ d : ℝ in nhds 0, 2*d^2 < 1 := by
    apply Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    have hc : Continuous (fun d : ℝ => 2*d^2) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  have h2 : ∀ᶠ d : ℝ in nhds 0, τ < 1-2*d^2 := by
    have hc : Continuous (fun d : ℝ => 1-2*d^2) := by fun_prop
    have ht : Tendsto (fun d : ℝ => 1-2*d^2) (nhds 0) (nhds 1) := by
      simpa using hc.continuousAt.tendsto (x := 0)
    exact ht.eventually (eventually_gt_nhds hτ)
  have h3 : ∀ᶠ d : ℝ in nhds 0, 4*d < ε := by
    apply Tendsto.eventually_lt_const hε
    have hc : Continuous (fun d : ℝ => 4*d) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  have h4 : ∀ᶠ d : ℝ in nhds 0, C*(d+d^2) < ε := by
    apply Tendsto.eventually_lt_const hε
    have hc : Continuous (fun d : ℝ => C*(d+d^2)) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  obtain ⟨d, hd, hb⟩ := (h1.and (h2.and (h3.and h4))).exists_gt
  exact ⟨d, hd, hb.1.le, hb.2.1, hb.2.2.1.le, hb.2.2.2.le⟩

/-- The recurrence and unit property are explicit; convergence alone does not
silently grant legal source execution before the eventual diagnostics. -/
theorem eventual_tests_of_stable_limit {τ ε κ : ℝ} {b u : Field}
    {z : ℕ → ComplexField}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hε : 0 < ε)
    (hf : GroundSourceJacobian.groundMap b κ u = u)
    (hz : ∀ n, complexNormSq (z n) = 1)
    (hstep : ∀ n, nativeUpdate τ b κ (1/2) (z n) = z (n+1))
    (ht : Tendsto z atTop (nhds (realEmbed (-u)))) :
    ∀ᶠ n in atTop, MeetsConvergence τ ε b κ (1/2) (z n) (z (n+1)) := by
  let v := complexSourcePotential b κ (realEmbed (-u))
  let M := ‖v‖+1
  have hs := (continuous_source b κ).tendsto _ |>.comp ht
  have hv : ∀ᶠ n in atTop, ‖complexSourcePotential b κ (z (n+1))-v‖ < 1 := by
    have hn := hs.comp (tendsto_add_atTop_nat 1)
    have hn0 : Tendsto (fun n => ‖complexSourcePotential b κ (z (n+1))-v‖)
        atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ => v) atTop (nhds v) := tendsto_const_nhds
      simpa only [v, Function.comp_apply, sub_self, norm_zero] using (hn.sub hconst).norm
    exact hn0.eventually_lt_const (by norm_num)
  obtain ⟨d, hd, hp, hg, hfix, heig⟩ :=
    small_budget_exists (C := 2+(M-(-M))) hτ1 hε
  have hn := ht.comp (tendsto_add_atTop_nat 1)
  have hc := (continuous_candidate b κ).tendsto _ |>.comp hn
  have hd0 : Tendsto (fun n => l2 (z (n+1)-(-nativeCandidate b κ (z (n+1)))))
      atTop (nhds 0) := by
    have hh := continuous_l2.tendsto _ |>.comp (hn.sub hc.neg)
    have he : realEmbed (-u)-(-nativeCandidate b κ (realEmbed (-u))) = 0 := by
      rw [candidate_at_negative_root hf, GroundNativeReflection.realEmbed_neg]
      simp
    rw [he] at hh
    simpa only [Function.comp_apply, l2, WithLp.toLp_zero, norm_zero] using hh
  have hu0 : Tendsto (fun n => l2 (z (n+1)-z n)) atTop (nhds 0) := by
    have hh := continuous_l2.tendsto _ |>.comp (hn.sub ht)
    simpa [l2] using hh
  filter_upwards [hv, hd0.eventually_le_const hd, hu0.eventually_le_const hε]
    with n hvn hdn hun
  have hpot : ∀ i, -M ≤ complexSourcePotential b κ (z (n+1)) i ∧
      complexSourcePotential b κ (z (n+1)) i ≤ M := by
    intro i
    have hdelta := norm_le_pi_norm (complexSourcePotential b κ (z (n+1))-v) i
    have hroot := norm_le_pi_norm v i
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hdelta hroot
    have ha := abs_le.mp (hdelta.trans hvn.le)
    have hb := abs_le.mp hroot
    dsimp only [M]
    constructor <;> linarith
  exact GroundComplexFiniteBudget.tests_of_budgets hτ0 hε.le hd.le (hz (n+1))
    hdn hun (hstep n) hpot hp hg ⟨le_rfl, hfix, heig⟩
end
end SbtCosmo.Derivation.NativeEventualSourceSuccess
