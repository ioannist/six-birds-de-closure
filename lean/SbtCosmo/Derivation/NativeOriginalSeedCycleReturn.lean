import SbtCosmo.Derivation.NativeFinitePairOrbit
import SbtCosmo.Derivation.NativeActualCycleConstruction
namespace NativeOriginalSeedCycleReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox Metric NativePairCertificates NativeFinitePairJets
open Filter
open scoped Topology
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State} {N : ℕ}

theorem finite_source_guards (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {z : ComplexField}
    (hi : T.symm (unpack z) ∈ closedBall (c.centers 0) (c.radii 0 : ℝ))
    (n : ℕ) (hn : n < 2*N) :
    ActivePhase (τ : ℝ) b (κ : ℝ) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) := by
  have hg := (steps c ⟨n,hn⟩).native_guards hb (orbit_enclosed c hb hi ⟨n,hn⟩)
  simpa only [NativePairOrbit.source_iterate] using hg

/-- An even finite entry preserves the phase ordering of the two subsequence
limits. The finite prefix is removed only through the cofinal shift theorem. -/
theorem even_entry_returns {α : Type*} [TopologicalSpace α] (g : α → α)
    {z a b : α} (N : ℕ)
    (he : Tendsto (fun n : ℕ => (g^[2*n]) ((g^[2*N]) z)) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => (g^[2*n+1]) ((g^[2*N]) z)) atTop (nhds b)) :
    Tendsto (fun n : ℕ => (g^[2*n]) z) atTop (nhds a) ∧
    Tendsto (fun n : ℕ => (g^[2*n+1]) z) atTop (nhds b) := by
  constructor
  · apply (tendsto_add_atTop_iff_nat N).mp
    convert he using 1
    funext n
    rw [← Function.iterate_add_apply]
    congr 1
    ring
  · apply (tendsto_add_atTop_iff_nat N).mp
    convert ho using 1
    funext n
    rw [← Function.iterate_add_apply]
    congr 1
    ring

theorem full_guards (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {z : ComplexField}
    (hi : T.symm (unpack z) ∈ closedBall (c.centers 0) (c.radii 0 : ℝ))
    (htail : ∀ n : ℕ,
      ActivePhase (τ : ℝ) b (κ : ℝ) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n]
        (((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[2*N]) z)) ∧
      NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n]
        (((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[2*N]) z))) (n : ℕ) :
    ActivePhase (τ : ℝ) b (κ : ℝ) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) := by
  by_cases hn : n < 2*N
  · exact finite_source_guards c hb hi n hn
  · have he : n-2*N+2*N = n := by omega
    simpa only [← Function.iterate_add_apply,he] using htail (n-2*N)

theorem full_unit {b : Field} {z : ComplexField} (hτ : 0 ≤ τ)
    (hu : complexNormSq z = 1)
    (hg : ∀ n : ℕ, NativeLegal (τ : ℝ) b (κ : ℝ) (1/2)
      ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z)) (n : ℕ) :
    complexNormSq ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) = 1 := by
  cases n with
  | zero => exact hu
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit (by exact_mod_cast hτ) (hg n)

theorem no_limit_of_distinct_subsequences {α : Type*} [TopologicalSpace α] [T2Space α]
    (u : ℕ → α) {a b : α}
    (he : Tendsto (fun n : ℕ => u (2*n)) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => u (2*n+1)) atTop (nhds b)) (hne : b ≠ a) :
    ¬ ∃ l, Tendsto u atTop (nhds l) := by
  rintro ⟨l,hl⟩
  have hse : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (by intro n;change n ≤ 2*n;omega) tendsto_id
  have hso : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (by intro n;change n ≤ 2*n+1;omega) tendsto_id
  exact hne ((tendsto_nhds_unique ho (hl.comp hso)).trans (tendsto_nhds_unique he (hl.comp hse)).symm)

theorem density_returns {u : ℕ → ComplexField} {a b : ComplexField}
    (he : Tendsto (fun n : ℕ => u (2*n)) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => u (2*n+1)) atTop (nhds b)) {i : Fin 8} {gap : ℝ}
    (hgap : gap < Complex.normSq (b i)-Complex.normSq (a i)) (hg : 0 ≤ gap) :
    Tendsto (fun n : ℕ => Complex.normSq (u (2*n) i)) atTop (nhds (Complex.normSq (a i))) ∧
    Tendsto (fun n : ℕ => Complex.normSq (u (2*n+1) i)) atTop (nhds (Complex.normSq (b i))) ∧
    (∀ᶠ n : ℕ in atTop, gap < Complex.normSq (u (2*n+1) i)-Complex.normSq (u (2*n) i)) ∧
    ¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq (u n i)) atTop (nhds l) := by
  have hc : Continuous (fun z : ComplexField => Complex.normSq (z i)) := by fun_prop
  have he' := (hc.tendsto a).comp he
  have ho' := (hc.tendsto b).comp ho
  refine ⟨he',ho',?_,?_⟩
  · exact (ho'.sub he').eventually (Ioi_mem_nhds hgap)
  · apply no_limit_of_distinct_subsequences _ he' ho'
    linarith
end
end NativeOriginalSeedCycleReturn
