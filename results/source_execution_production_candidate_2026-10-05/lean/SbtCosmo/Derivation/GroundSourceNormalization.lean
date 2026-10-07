import SbtCosmo.Derivation.GroundNativeEscape

/-! Exception-aware exact source normalization. A failed normalization has no
returned state; the total division formula at zero is never an execution output.
The update argument is arbitrary, so successful-return bounds do not depend on
an eigenvector selector, phase rule, convergence, coupling or local basin. -/
namespace SbtCosmo.Derivation.GroundSourceNormalization
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativeIteration
open scoped BigOperators

def attempt (τ : ℝ) (z : ComplexField) : Option ComplexField :=
  if τ < Real.sqrt (complexNormSq z) then some (complexNormalize z) else none

def run (τ : ℝ) (rawUpdate : ComplexField → ComplexField) (seed : ComplexField) : ℕ → Option ComplexField
  | 0 => some seed
  | n+1 => (run τ rawUpdate seed n).bind (fun z => attempt τ (rawUpdate z))

/-- Every successfully returned normalization, with the literal nonnegative
threshold, has norm one. No value is returned on the rejected branch. -/
theorem returned_unit {τ : ℝ} {z w : ComplexField} (hτ : 0 ≤ τ)
    (hw : attempt τ z = some w) : complexNormSq w = 1 := by
  by_cases h : τ < Real.sqrt (complexNormSq z)
  · have he : complexNormalize z = w := by simpa only [attempt,if_pos h,Option.some.injEq] using hw
    rw [← he]
    exact GroundNativeEscape.complexNormalize_unit (Real.sqrt_pos.mp (hτ.trans_lt h))
  · simp only [attempt,if_neg h] at hw
    cases hw

theorem rejected_iff (τ : ℝ) (z : ComplexField) :
    attempt τ z = none ↔ Real.sqrt (complexNormSq z) ≤ τ := by
  simp [attempt,not_lt]

theorem zero_rejected {τ : ℝ} (hτ : 0 ≤ τ) : attempt τ 0 = none := by
  apply (rejected_iff τ 0).2
  simpa [complexNormSq] using hτ

/-- An already normalized successful source state is preserved by normalization
at the original threshold, which is strictly below one. -/
theorem unit_preserved {τ : ℝ} {z : ComplexField} (hτ : τ < 1) (hz : complexNormSq z = 1) :
    attempt τ z = some z := by
  have hn : complexNormalize z = z := by
    funext i
    simp [complexNormalize,hz]
  simp [attempt,hz,hτ,hn]

/-- A normalization exception terminates this execution; it cannot become an
ordinary state on later updates. -/
theorem failure_persists {τ : ℝ} {f : ComplexField → ComplexField} {z : ComplexField} {n : ℕ}
    (hn : run τ f z n = none) (k : ℕ) : run τ f z (n+k) = none := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    change (run τ f z (n+k)).bind (fun x => attempt τ (f x)) = none
    simp only [ih,Option.bind_none]

theorem positive_return_unit {τ : ℝ} {f : ComplexField → ComplexField} {z w : ComplexField}
    (hτ : 0 ≤ τ) {n : ℕ} (hn : 0 < n) (hw : run τ f z n = some w) : complexNormSq w = 1 := by
  cases n with
  | zero => omega
  | succ n =>
    cases he : run τ f z n with
    | none =>
      simp only [run,he,Option.bind_none] at hw
      cases hw
    | some v =>
      have h : attempt τ (f v) = some w := by simpa only [run,he,Option.bind_some] using hw
      exact returned_unit hτ h

/-- Any successful truncation of a normalized source execution has norm one,
even if a later truncation aborts. No all-time legality premise is needed. -/
theorem successful_run_unit {τ : ℝ} {f : ComplexField → ComplexField} {z w : ComplexField}
    (hτ : 0 ≤ τ) (hz : complexNormSq z = 1) (n : ℕ) (hw : run τ f z n = some w) :
    complexNormSq w = 1 := by
  cases n with
  | zero =>
    have he : z = w := by simpa only [run,Option.some.injEq] using hw
    simpa only [← he] using hz
  | succ n => exact positive_return_unit hτ (by omega) hw

theorem successful_run_density_bound {τ : ℝ} {f : ComplexField → ComplexField} {z w : ComplexField}
    (hτ : 0 ≤ τ) (hz : complexNormSq z = 1) (n : ℕ) (hw : run τ f z n = some w) (i : Fin 8) :
    Complex.normSq (w i) ≤ 1 := by
  have hu := successful_run_unit hτ hz n hw
  have hb := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 8))) => Complex.normSq_nonneg (w j))
    (Finset.mem_univ i)
  change Complex.normSq (w i) ≤ complexNormSq w at hb
  simpa only [hu] using hb
end
end SbtCosmo.Derivation.GroundSourceNormalization
