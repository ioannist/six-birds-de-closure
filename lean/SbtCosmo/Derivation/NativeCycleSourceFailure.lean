import SbtCosmo.Derivation.NativeOriginalSeedCycleReturn
import SbtCosmo.Derivation.GroundSourceDiagnostics
import SbtCosmo.Derivation.GroundOriginalResiduals
namespace NativeCycleSourceFailure
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundComplexEuclidean GroundSourceDiagnostics Filter
open scoped BigOperators Topology

theorem complex_component_le_l2 (z : ComplexField) (i : Fin 8) : ‖z i‖ ≤ l2 z := by
  have h := Finset.single_le_sum (fun (j : Fin 8) (_ : j ∈ Finset.univ) =>
    (show 0 ≤ Complex.normSq (z j) from Complex.normSq_nonneg _)) (Finset.mem_univ i)
  change Complex.normSq (z i) ≤ complexNormSq z at h
  rw [Complex.normSq_eq_norm_sq, ← l2_sq] at h
  nlinarith [norm_nonneg (z i), l2_nonneg z]

/-- A unit-state density change cannot conceal a small Euclidean update. -/
theorem density_step_bound {z w : ComplexField} (hz : complexNormSq z = 1)
    (hw : complexNormSq w = 1) (i : Fin 8) :
    Complex.normSq (w i)-Complex.normSq (z i) ≤ 2*l2 (w-z) := by
  have hz' : ‖z i‖ ≤ 1 := by simpa only [l2_unit hz] using complex_component_le_l2 z i
  have hw' : ‖w i‖ ≤ 1 := by simpa only [l2_unit hw] using complex_component_le_l2 w i
  have hd : ‖w i‖-‖z i‖ ≤ l2 (w-z) :=
    (norm_sub_norm_le (w i) (z i)).trans (complex_component_le_l2 (w-z) i)
  have hsum : ‖w i‖+‖z i‖ ≤ 2 := by linarith
  have hp := mul_le_mul_of_nonneg_right hd (add_nonneg (norm_nonneg (w i)) (norm_nonneg (z i)))
  have hq := mul_le_mul_of_nonneg_left hsum (l2_nonneg (w-z))
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
  nlinarith

/-- Both directions of the oscillation are retained, including the odd update
whose target is the next even state. -/
theorem successive_density_gap {u : ℕ → ComplexField} {a b : ComplexField}
    (he : Tendsto (fun n : ℕ => u (2*n)) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => u (2*n+1)) atTop (nhds b)) {i : Fin 8} {gap : ℝ}
    (hg : gap < Complex.normSq (b i)-Complex.normSq (a i)) :
    ∀ᶠ n : ℕ in atTop,
      gap < |Complex.normSq (u (n+1) i)-Complex.normSq (u n i)| := by
  have hc : Continuous (fun z : ComplexField => Complex.normSq (z i)) := by fun_prop
  have he' := (hc.tendsto a).comp he
  have ho' := (hc.tendsto b).comp ho
  have hen : Tendsto (fun n : ℕ => Complex.normSq (u (2*(n+1)) i)) atTop
      (nhds (Complex.normSq (a i))) := he'.comp (tendsto_add_atTop_nat 1)
  have hg0 := (ho'.sub he').eventually (Ioi_mem_nhds hg)
  have hg1 := (ho'.sub hen).eventually (Ioi_mem_nhds hg)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hg0.and hg1)
  apply eventually_atTop.2
  refine ⟨2*N,fun n hn => ?_⟩
  have hdiv : N ≤ n/2 := by omega
  have hv := hN (n/2) hdiv
  have hi := Nat.mod_add_div n 2
  by_cases hm : n%2=0
  · have hn' : n = 2*(n/2) := by omega
    rw [hn']
    exact hv.1.trans_le (le_abs_self _)
  · have hn' : n = 2*(n/2)+1 := by omega
    rw [hn']
    have heq : 2*(n/2)+1+1 = 2*(n/2+1) := by omega
    rw [heq]
    have h := hv.2.trans_le (le_abs_self (Complex.normSq (u (2*(n/2)+1) i)-Complex.normSq (u (2*(n/2+1)) i)))
    simpa only [abs_sub_comm] using h

theorem successive_l2_away {u : ℕ → ComplexField} {a b : ComplexField}
    (he : Tendsto (fun n : ℕ => u (2*n)) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => u (2*n+1)) atTop (nhds b))
    (hu : ∀ n, complexNormSq (u n) = 1) {i : Fin 8} {gap : ℝ}
    (hg : gap < Complex.normSq (b i)-Complex.normSq (a i)) :
    ∀ᶠ n : ℕ in atTop, gap/2 < l2 (u (n+1)-u n) := by
  filter_upwards [successive_density_gap he ho hg] with n hn
  have h1 := density_step_bound (hu n) (hu (n+1)) i
  have h2 := density_step_bound (hu (n+1)) (hu n) i
  have hneg : u n-u (n+1) = -(u (n+1)-u n) := by abel
  rw [hneg,l2_neg] at h2
  have ha : |Complex.normSq (u (n+1) i)-Complex.normSq (u n i)| ≤
      2*l2 (u (n+1)-u n) := abs_le.2 ⟨by linarith,h1⟩
  linarith

/-- The actual source conjunction fails eventually when the earned two-phase
density gap exceeds twice its tolerance. No first stopping time is asserted. -/
theorem source_tests_eventually_fail {τ ε κ m : ℝ} {bg : Field} {z a b : ComplexField}
    (he : Tendsto (fun n : ℕ => ((nativeUpdate τ bg κ m)^[2*n]) z) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => ((nativeUpdate τ bg κ m)^[2*n+1]) z) atTop (nhds b))
    (hu : ∀ n, complexNormSq (((nativeUpdate τ bg κ m)^[n]) z) = 1)
    {i : Fin 8} {gap : ℝ} (hg : gap < Complex.normSq (b i)-Complex.normSq (a i))
    (hε : ε < gap/2) :
    ∀ᶠ n : ℕ in atTop, ¬ MeetsConvergence τ ε bg κ m
      (((nativeUpdate τ bg κ m)^[n]) z) (((nativeUpdate τ bg κ m)^[n+1]) z) := by
  filter_upwards [successive_l2_away he ho hu hg] with n hn
  intro h
  have hs : ((nativeUpdate τ bg κ m)^[n+1]) z =
      nativeUpdate τ bg κ m (((nativeUpdate τ bg κ m)^[n]) z) :=
    Function.iterate_succ_apply' _ n z
  rw [hs] at hn
  exact (not_lt_of_ge h.1) (hε.trans hn)
end
end NativeCycleSourceFailure
