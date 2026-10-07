import SbtCosmo.Derivation.GroundSourceNormalization
import SbtCosmo.Derivation.GroundNativeControls

/-! Return of the existing phase-cancellation witness to exception-aware source
execution. Input and eigensolver normalizations succeed; half-mixing cancels
exactly, so no state is returned on any positive iteration count. The witness
is a supplied starting state, not the experiment's original starting state. -/
namespace SbtCosmo.Derivation.GroundSourceNormalizationFailure
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundSourceJacobian GroundNormalizedJacobian
open GroundNativePhase GroundNativeIteration GroundNativeControls GroundSourceNormalization

theorem imaginary_ground_execution {b u : Field} {κ τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    complexNormSq (pack (0,u)) = 1 ∧
    ActivePhase τ b κ (pack (0,u)) ∧
    attempt τ (pack (0,u)) = some (pack (0,u)) ∧
    attempt τ (nativeCandidate b κ (pack (0,u))) =
      some (nativeCandidate b κ (pack (0,u))) ∧
    run τ (nativeMixed τ b κ (1/2)) (pack (0,u)) 1 = none := by
  obtain ⟨hn,ha,hm,_⟩ := native_half_imaginary_illegal hu hf hτ0 hτ1
  have hc : complexNormSq (nativeCandidate b κ (pack (0,u))) = 1 :=
    realEmbed_normalized (positiveGround_spec _).2.1
  refine ⟨hn,ha,unit_preserved hτ1 hn,unit_preserved hτ1 hc,?_⟩
  change attempt τ (nativeMixed τ b κ (1/2) (pack (0,u))) = none
  rw [hm]
  exact zero_rejected hτ0

theorem imaginary_ground_no_continuation {b u : Field} {κ τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (N : ℕ) (hN : 0 < N) :
    run τ (nativeMixed τ b κ (1/2)) (pack (0,u)) N = none := by
  obtain ⟨_,_,_,_,hfirst⟩ := imaginary_ground_execution hu hf hτ0 hτ1
  cases N with
  | zero => omega
  | succ k => simpa only [Nat.add_comm] using failure_persists hfirst k

/-- Actual all-parameter witnesses are earned from the established ground
existence theorem. No fixed point or illegal starting state is a caller premise. -/
theorem exists_unit_execution_failure (b : Field) (κ : ℝ) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ∃ z : ComplexField, complexNormSq z = 1 ∧ ActivePhase τ b κ z ∧
      attempt τ z = some z ∧
      attempt τ (nativeCandidate b κ z) = some (nativeCandidate b κ z) ∧
      run τ (nativeMixed τ b κ (1/2)) z 1 = none ∧
      ∀ N : ℕ, 0 < N → run τ (nativeMixed τ b κ (1/2)) z N = none := by
  obtain ⟨u,hp,e,hg⟩ := exists_selfConsistent_ground b κ
  have hf : groundMap b κ u = u := positive_ground_fixed hp ⟨e,hg⟩
  obtain ⟨hn,ha,hi,hc,hfirst⟩ := imaginary_ground_execution hg.1 hf hτ0 hτ1
  exact ⟨pack (0,u),hn,ha,hi,hc,hfirst,
    imaginary_ground_no_continuation hg.1 hf hτ0 hτ1⟩

theorem original_tolerance_unit_execution_failure (b : Field) (κ : ℝ) :
    ∃ z : ComplexField, complexNormSq z = 1 ∧
      ActivePhase originalTolerance b κ z ∧
      attempt originalTolerance z = some z ∧
      attempt originalTolerance (nativeCandidate b κ z) = some (nativeCandidate b κ z) ∧
      run originalTolerance (nativeMixed originalTolerance b κ (1/2)) z 1 = none ∧
      ∀ N : ℕ, 0 < N → run originalTolerance (nativeMixed originalTolerance b κ (1/2)) z N = none :=
  exists_unit_execution_failure b κ originalTolerance_guard.1 originalTolerance_guard.2

/-- Equal densities and equal source potentials do not determine whether the
retained phase-sign implementation returns a state. The witnesses differ by
a single global phase and are earned for every background and coupling. -/
theorem exists_phase_execution_split (b : Field) (κ : ℝ) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ∃ a z : ComplexField, z = (fun j => Complex.I * a j) ∧
      complexNormSq a = 1 ∧ complexNormSq z = 1 ∧
      (∀ j, Complex.normSq (a j) = Complex.normSq (z j)) ∧
      complexSourcePotential b κ a = complexSourcePotential b κ z ∧
      run τ (nativeMixed τ b κ (1/2)) a 1 = some a ∧
      run τ (nativeMixed τ b κ (1/2)) z 1 = none ∧
      ∀ N : ℕ, 0 < N → run τ (nativeMixed τ b κ (1/2)) z N = none := by
  obtain ⟨u,hp,e,hg⟩ := exists_selfConsistent_ground b κ
  have hf : groundMap b κ u = u := positive_ground_fixed hp ⟨e,hg⟩
  obtain ⟨hz,_,_,_,hfirst⟩ := imaginary_ground_execution hg.1 hf hτ0 hτ1
  refine ⟨realEmbed u,pack (0,u),?_,realEmbed_normalized hg.1,hz,?_,?_,?_,hfirst,
    imaginary_ground_no_continuation hg.1 hf hτ0 hτ1⟩
  · funext j
    apply Complex.ext <;> simp [pack,realEmbed]
  · intro j
    simp [pack,realEmbed,Complex.normSq_apply]
  · rw [complexSourcePotential_realEmbed,source_pack,pairSource_imaginary]
  · have ho : τ < overlapNorm b κ (u,0) := by
      rw [(overlap_at_fixed hg.1 hf).2.2]
      exact hτ1
    have hm : nativeMixed τ b κ (1/2) (realEmbed u) = realEmbed u := by
      change nativeMixed τ b κ (1/2) (pack (u,0)) = pack (u,0)
      rw [← pack_mixed_native hτ0 b κ (1/2) (u,0) ho,mixed_fixed hg.1 hf]
    change attempt τ (nativeMixed τ b κ (1/2) (realEmbed u)) = some (realEmbed u)
    rw [hm]
    exact unit_preserved hτ1 (realEmbed_normalized hg.1)

end
end SbtCosmo.Derivation.GroundSourceNormalizationFailure
