import SbtCosmo.Derivation.GroundNativeEscape

/-! Reflection of the unchanged native map on its active phase branch.
The fallback phase branch is retained; oddness is not asserted there. -/
namespace SbtCosmo.Derivation.GroundNativeReflection
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeLocal
open Filter Metric
open scoped Topology BigOperators

theorem complexNormSq_neg (z : ComplexField) : complexNormSq (-z) = complexNormSq z := by
  simp [complexNormSq]

theorem complexSourcePotential_neg (b : Field) (κ : ℝ) (z : ComplexField) :
    complexSourcePotential b κ (-z) = complexSourcePotential b κ z := by
  have hg (i : Fin 8) : complexGradient (-z) i = -complexGradient z i := by
    simp only [complexGradient, Pi.neg_apply]
    ring
  funext i
  simp only [complexSourcePotential, Pi.neg_apply, Complex.normSq_neg, hg]

theorem nativeCandidate_neg (b : Field) (κ : ℝ) (z : ComplexField) :
    nativeCandidate b κ (-z) = nativeCandidate b κ z := by
  rw [nativeCandidate, complexSourcePotential_neg]
  rfl

theorem overlap_neg_right (candidate reference : ComplexField) :
    overlap candidate (-reference) = -overlap candidate reference := by
  simp [overlap, Finset.sum_neg_distrib]

theorem unpack_neg (z : ComplexField) : unpack (-z) = -unpack z := by rfl

theorem realEmbed_neg (u : Field) : realEmbed (-u) = -realEmbed u := by
  funext i
  simp [realEmbed]

theorem activePhase_neg_iff (τ : ℝ) (b : Field) (κ : ℝ) (z : ComplexField) :
    ActivePhase τ b κ (-z) ↔ ActivePhase τ b κ z := by
  simp only [ActivePhase, nativeCandidate_neg, overlap_neg_right, norm_neg]

theorem nativePhase_neg_reference {τ : ℝ} {candidate reference : ComplexField}
    (hτ : 0 ≤ τ) (ho : τ < ‖overlap candidate reference‖) :
    nativePhase τ candidate (-reference) = -nativePhase τ candidate reference := by
  have hn : τ < ‖overlap candidate (-reference)‖ := by simpa [overlap_neg_right] using ho
  rw [nativePhase_ratio hτ hn, nativePhase_ratio hτ ho, overlap_neg_right]
  funext i
  simp
  ring

theorem complexNormalize_neg (z : ComplexField) : complexNormalize (-z) = -complexNormalize z := by
  funext i
  simp [complexNormalize, complexNormSq_neg]
  ring

theorem nativeMixed_neg {τ : ℝ} (b : Field) (κ m : ℝ) (z : ComplexField)
    (hτ : 0 ≤ τ) (ho : ActivePhase τ b κ z) :
    nativeMixed τ b κ m (-z) = -nativeMixed τ b κ m z := by
  rw [nativeMixed, nativeCandidate_neg, nativePhase_neg_reference hτ ho]
  simp [nativeMixed, add_comm]

theorem nativeUpdate_neg {τ : ℝ} (b : Field) (κ m : ℝ) (z : ComplexField)
    (hτ : 0 ≤ τ) (ho : ActivePhase τ b κ z) :
    nativeUpdate τ b κ m (-z) = -nativeUpdate τ b κ m z := by
  rw [nativeUpdate, nativeMixed_neg b κ m z hτ ho, complexNormalize_neg]
  rfl

theorem nativeLegal_neg_iff {τ : ℝ} (b : Field) (κ m : ℝ) (z : ComplexField)
    (hτ : 0 ≤ τ) (ho : ActivePhase τ b κ z) :
    NativeLegal τ b κ m (-z) ↔ NativeLegal τ b κ m z := by
  simp only [NativeLegal, nativeMixed_neg b κ m z hτ ho, complexNormSq_neg]

/-- Reflection uses only the active original orbit prefix, with no global
oddness assumption on the threshold fallback branch. -/
theorem native_iterate_neg {τ : ℝ} (b : Field) (κ m : ℝ) (z : ComplexField)
    (hτ : 0 ≤ τ) (N : ℕ)
    (ha : ∀ j < N, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[j] z)) :
    (nativeUpdate τ b κ m)^[N] (-z) = -((nativeUpdate τ b κ m)^[N] z) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hp := ih (fun j hj => ha j (hj.trans (Nat.lt_succ_self N)))
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hp]
    exact nativeUpdate_neg b κ m _ hτ (ha N (Nat.lt_succ_self N))

theorem native_negative_local_attraction (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : GroundSourceJacobian.groundMap b κ u = u)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hd : ‖coordinateDerivative T b κ m u‖ < 1) :
    ∃ r > 0, ∀ z : ComplexField, T.symm (unpack z) ∈ closedBall (T.symm (-u, 0)) r →
      Tendsto (fun n : ℕ => (nativeUpdate τ b κ m)^[n] z) atTop (nhds (realEmbed (-u))) ∧
      ∀ n : ℕ, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[n] z) ∧
        NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) := by
  obtain ⟨r, hr, hp⟩ := native_complex_local_attraction T hu hf hτ0 hτ1 hd
  refine ⟨r, hr, fun z hz => ?_⟩
  have hx : T.symm (unpack (-z)) ∈ closedBall (T.symm (u, 0)) r := by
    rw [mem_closedBall, unpack_neg, map_neg]
    have he : T.symm (-u, 0) = -T.symm (u, 0) := by
      rw [← map_neg]
      simp only [Prod.neg_mk, neg_zero]
    rw [mem_closedBall, he] at hz
    have heq := dist_neg_neg (T.symm (unpack z)) (-T.symm (u, 0))
    simp only [neg_neg] at heq
    rw [heq]
    exact hz
  obtain ⟨ht, hg⟩ := hp (-z) hx
  have he (n : ℕ) : (nativeUpdate τ b κ m)^[n] z = -((nativeUpdate τ b κ m)^[n] (-z)) := by
    simpa only [neg_neg] using native_iterate_neg b κ m (-z) hτ0 n (fun j _ => (hg j).1)
  refine ⟨?_, fun n => ?_⟩
  · simpa only [← he, ← realEmbed_neg] using ht.neg
  · rw [he]
    exact ⟨(activePhase_neg_iff τ b κ _).mpr (hg n).1,
      (nativeLegal_neg_iff b κ m _ hτ0 (hg n).1).mpr (hg n).2⟩

theorem native_negative_local_escape (T : State ≃L[ℝ] State) {b u : Field}
    {κ m τ ℓ : ℝ} {v : State}
    (hu : normSq u = 1) (hf : GroundSourceJacobian.groundMap b κ u = u)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hv : ‖v‖ = 1)
    (heigen : coordinateDerivative T b κ m u v = ℓ • v)
    (hℓ : 1 < |ℓ|) (hgap : ‖coordinateDerivative T b κ m u‖ < |ℓ|^2) :
    ∃ s > 0, ∀ ε > 0, ∃ z : ComplexField, ∃ N : ℕ,
      complexNormSq z = 1 ∧ ‖T.symm (unpack z) - T.symm (-u, 0)‖ < ε ∧
      s/2 ≤ ‖T.symm (unpack ((nativeUpdate τ b κ m)^[N] z)) - T.symm (-u, 0)‖ ∧
      ∀ k ≤ N, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[k] z) ∧
        NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[k] z) := by
  obtain ⟨s, hs, hp⟩ := GroundNativeEscape.native_complex_local_escape T hu hf hτ0 hτ1 hv heigen hℓ hgap
  have hc : T.symm (-u, 0) = -T.symm (u, 0) := by
    rw [← map_neg]
    simp only [Prod.neg_mk, neg_zero]
  refine ⟨s, hs, fun ε hε => ?_⟩
  obtain ⟨z, N, hz, hi, ho, hg⟩ := hp ε hε
  have he (j : ℕ) (hj : j ≤ N) : (nativeUpdate τ b κ m)^[j] (-z) = -((nativeUpdate τ b κ m)^[j] z) :=
    native_iterate_neg b κ m z hτ0 j (fun k hk => (hg k (hk.le.trans hj)).1)
  refine ⟨-z, N, ?_, ?_, ?_, fun j hj => ?_⟩
  · simpa only [complexNormSq_neg] using hz
  · simpa only [unpack_neg, map_neg, hc, neg_sub_neg, norm_sub_rev] using hi
  · simpa only [he N le_rfl, unpack_neg, map_neg, hc, neg_sub_neg, norm_sub_rev] using ho
  · rw [he j hj]
    exact ⟨(activePhase_neg_iff τ b κ _).mpr (hg j hj).1,
      (nativeLegal_neg_iff b κ m _ hτ0 (hg j hj).1).mpr (hg j hj).2⟩

end
end SbtCosmo.Derivation.GroundNativeReflection
