import SbtCosmo.Derivation.GroundNativeLocal

/-! Source-return controls: the original IEEE tolerance, real eigensolver sign,
all-parameter legal fixed points, and an explicit illegal normalization caused
by the unchanged phase-sign error. -/
namespace SbtCosmo.Derivation.GroundNativeControls
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian
open GroundNativePhase GroundNativeDerivative GroundNativeIteration GroundNativeJacobian
open scoped BigOperators

/-- Exact real reification of the original binary64 `1e-10`, not decimal 10⁻¹⁰. -/
def originalTolerance : ℝ := 7737125245533627 / 77371252455336267181195264

theorem originalTolerance_guard : 0 ≤ originalTolerance ∧ originalTolerance < 1 := by
  norm_num [originalTolerance]

theorem unit_real_lowest_sign {v w : Field}
    (hw : normSq w = 1)
    (he : ∀ i, hamiltonian v w i = energy v (positiveGround v) * w i) :
    w = positiveGround v ∨ w = -positiveGround v := by
  obtain ⟨c, hc⟩ := real_lowest_eigen_span (positiveGround_spec v).2 he
  have hn := hw
  rw [hc, normSq_homogeneous, (positiveGround_spec v).2.1, mul_one] at hn
  have hs : c = 1 ∨ c = -1 := by
    rcases le_total 0 c with h | h
    · left; nlinarith
    · right; nlinarith
  rcases hs with hs | hs
  · left; simpa [hs] using hc
  · right; simpa [hs] using hc

/-- The active native phase output is independent of the real sign chosen by
the original real symmetric eigensolver. No arbitrary complex-phase invariance. -/
theorem real_eigensolver_phase_return {v w : Field} {z : ComplexField} {τ : ℝ}
    (hw : normSq w = 1)
    (he : ∀ i, hamiltonian v w i = energy v (positiveGround v) * w i)
    (hτ : 0 ≤ τ) (ho : τ < ‖overlap (realEmbed (positiveGround v)) z‖) :
    nativePhase τ (realEmbed w) z = nativePhase τ (realEmbed (positiveGround v)) z := by
  rcases unit_real_lowest_sign hw he with hh | hh
  · rw [hh]
  · rw [hh]
    have hneg : realEmbed (-positiveGround v) = -realEmbed (positiveGround v) := by
      funext i; simp [realEmbed]
    rw [hneg]
    exact nativePhase_real_sign_invariant hτ ho

theorem real_mode_full_return {b u h : Field} {κ m ℓ : ℝ}
    (he : normalizedJacobian b κ m u h = ℓ • h) :
    fullDerivative b κ m u (h, 0) = ℓ • (h, 0) := by
  simp [fullDerivative, he]

theorem exists_legal_native_fixed (b : Field) (κ m : ℝ) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ∃ u : Field, (∀ i, 0 < u i) ∧ normSq u = 1 ∧
      nativeUpdate τ b κ m (realEmbed u) = realEmbed u ∧
      ActivePhase τ b κ (realEmbed u) ∧ NativeLegal τ b κ m (realEmbed u) := by
  obtain ⟨u, hp, e, hg⟩ := exists_selfConsistent_ground b κ
  have hf := positive_ground_fixed hp ⟨e, hg⟩
  have hlocal := (nativeUpdate_near_fixed (m := m) hg.1 hf hτ0 hτ1).self_of_nhds
  refine ⟨u, hp, hg.1, ?_, hlocal.2⟩
  change nativeUpdate τ b κ m (pack (u, 0)) = pack (u, 0)
  rw [← hlocal.1, fullMap_fixed hg.1 hf]

theorem pairSource_imaginary (b : Field) (κ : ℝ) (u : Field) :
    pairSource b κ (0, u) = sourcePotential b κ u := by
  funext i
  simp [pairSource, sourcePotential, BackgroundSelection.potential, GroundState.gradient]

theorem selected_imaginary (b : Field) (κ : ℝ) (u : Field) :
    selected b κ (0, u) = groundMap b κ u := by rw [selected, pairSource_imaginary]; rfl

theorem overlap_imaginary_fixed {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    realOverlap b κ (0, u) = 0 ∧ imagOverlap b κ (0, u) = 1 ∧ overlapNorm b κ (0, u) = 1 := by
  have hr : realOverlap b κ (0, u) = 0 := by simp [realOverlap, dot]
  have hi : imagOverlap b κ (0, u) = 1 := by
    simp [imagOverlap, selected_imaginary, hf, dot_self, hu]
  exact ⟨hr, hi, by simp [overlapNorm, overlapSq, hr, hi]⟩

theorem aligned_imaginary_fixed {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    aligned b κ (0, u) = (0, -u) := by
  obtain ⟨hr, hi, hn⟩ := overlap_imaginary_fixed hu hf
  apply Prod.ext <;> funext i <;>
    simp [aligned, hr, hi, hn, selected_imaginary, hf]

theorem half_mixed_imaginary_cancellation {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    mixed b κ (1/2) (0, u) = 0 := by
  rw [mixed, aligned_imaginary_fixed hu hf]
  apply Prod.ext <;> funext i
  all_goals simp
  ring

/-- A unit pure-imaginary ground input has active phase alignment but the
original half-mixing normalization raises: its mixed field is exactly zero. -/
theorem native_half_imaginary_illegal {b u : Field} {κ τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    complexNormSq (pack (0, u)) = 1 ∧ ActivePhase τ b κ (pack (0, u)) ∧
      nativeMixed τ b κ (1/2) (pack (0, u)) = 0 ∧
      ¬ NativeLegal τ b κ (1/2) (pack (0, u)) := by
  have ho : τ < overlapNorm b κ (0, u) := by
    rw [(overlap_imaginary_fixed hu hf).2.2]; exact hτ1
  have hm : nativeMixed τ b κ (1/2) (pack (0, u)) = 0 := by
    rw [← pack_mixed_native hτ0 b κ (1/2) (0, u) ho, half_mixed_imaginary_cancellation hu hf]
    rfl
  refine ⟨?_, ?_, hm, ?_⟩
  · rw [norm_pack]
    change normSq (0 : Field) + normSq u = 1
    rw [hu]
    simp [normSq]
  · simpa [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using ho
  · unfold NativeLegal
    rw [hm]
    simpa [complexNormSq] using not_lt.mpr hτ0

end
end SbtCosmo.Derivation.GroundNativeControls
