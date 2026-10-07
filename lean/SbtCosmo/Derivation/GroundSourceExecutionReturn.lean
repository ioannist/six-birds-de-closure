import SbtCosmo.Derivation.GroundSourceNormalization

/-! Exact return from the normalization-exception execution to the total map.
Successful runs return precisely its iterates; success is equivalent to the
normalization guards along the entire finite prefix. No phase or guard premise
is silently inferred from the total formula. -/
namespace SbtCosmo.Derivation.GroundSourceExecutionReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativeIteration GroundSourceNormalization

def normalized (rawUpdate : ComplexField → ComplexField) : ComplexField → ComplexField :=
  fun z => complexNormalize (rawUpdate z)

theorem attempt_some_iff (τ : ℝ) (z w : ComplexField) :
    attempt τ z = some w ↔ τ < Real.sqrt (complexNormSq z) ∧ complexNormalize z = w := by
  by_cases h : τ < Real.sqrt (complexNormSq z)
  · simp [attempt,h]
  · simp [attempt,h]

theorem run_guarded (τ : ℝ) (f : ComplexField → ComplexField) (z : ComplexField) (N : ℕ)
    (hN : ∀ n < N, τ < Real.sqrt (complexNormSq (f ((normalized f)^[n] z)))) :
    run τ f z N = some ((normalized f)^[N] z) := by
  revert hN
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hN
    have hp := ih (fun n hn => hN n (Nat.lt_succ_of_lt hn))
    rw [run,hp,Option.bind_some]
    apply (attempt_some_iff _ _ _).2
    exact ⟨hN N (Nat.lt_succ_self N), by
      simp only [Function.iterate_succ_apply',normalized]⟩

theorem successful_run_return (τ : ℝ) (f : ComplexField → ComplexField) (z : ComplexField)
    (N : ℕ) {w : ComplexField} (hw : run τ f z N = some w) :
    (normalized f)^[N] z = w := by
  induction N generalizing w with
  | zero => simpa only [run,Function.iterate_zero_apply,Option.some.injEq] using hw
  | succ N ih =>
    cases hp : run τ f z N with
    | none => simp only [run,hp,Option.bind_none] at hw; cases hw
    | some v =>
      have hv : attempt τ (f v) = some w := by
        simpa only [run,hp,Option.bind_some] using hw
      have hr := ih hp
      rw [Function.iterate_succ_apply',hr]
      exact (attempt_some_iff _ _ _).1 hv |>.2

theorem successful_run_guards (τ : ℝ) (f : ComplexField → ComplexField) (z : ComplexField)
    (N : ℕ) {w : ComplexField} (hw : run τ f z N = some w) :
    ∀ n < N, τ < Real.sqrt (complexNormSq (f ((normalized f)^[n] z))) := by
  induction N generalizing w with
  | zero => intro n hn; omega
  | succ N ih =>
    cases hp : run τ f z N with
    | none => simp only [run,hp,Option.bind_none] at hw; cases hw
    | some v =>
      have hv : attempt τ (f v) = some w := by
        simpa only [run,hp,Option.bind_some] using hw
      intro n hn
      obtain hn | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn)
      · exact ih hp n hn
      · rw [successful_run_return τ f z _ hp]
        exact (attempt_some_iff _ _ _).1 hv |>.1

theorem run_iff_guards (τ : ℝ) (f : ComplexField → ComplexField) (z : ComplexField) (N : ℕ) :
    run τ f z N = some ((normalized f)^[N] z) ↔
      ∀ n < N, τ < Real.sqrt (complexNormSq (f ((normalized f)^[n] z))) :=
  ⟨successful_run_guards τ f z N,run_guarded τ f z N⟩

theorem native_run_guarded (τ : ℝ) (b : Field) (κ m : ℝ) (z : ComplexField) (N : ℕ)
    (hN : ∀ n < N, NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z)) :
    run τ (nativeMixed τ b κ m) z N = some ((nativeUpdate τ b κ m)^[N] z) :=
  run_guarded τ (nativeMixed τ b κ m) z N hN

theorem native_run_iff_guards (τ : ℝ) (b : Field) (κ m : ℝ) (z : ComplexField) (N : ℕ) :
    run τ (nativeMixed τ b κ m) z N = some ((nativeUpdate τ b κ m)^[N] z) ↔
      ∀ n < N, NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) :=
  run_iff_guards τ (nativeMixed τ b κ m) z N

/-- The exact unit ground selector also survives the source's normalization
inside its eigensolver. This does not model an IEEE eigensolver trace. -/
theorem candidate_normalization_preserved {τ : ℝ} (hτ : τ < 1)
    (b : Field) (κ : ℝ) (z : ComplexField) :
    attempt τ (nativeCandidate b κ z) = some (nativeCandidate b κ z) := by
  apply unit_preserved hτ
  apply GroundState.realEmbed_normalized
  exact (GroundState.positiveGround_spec _).2.1

end
end SbtCosmo.Derivation.GroundSourceExecutionReturn
