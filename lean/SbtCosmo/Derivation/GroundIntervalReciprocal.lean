import SbtCosmo.Derivation.GroundRationalInterval

/-! Rational inverse-square-root witnesses, sound for every real value in the
whole input interval. Positivity is earned before any division. -/
namespace SbtCosmo.Derivation.GroundIntervalReciprocal
noncomputable section
open GroundRationalInterval

structure Arithmetic (N K : Interval) : Prop where
  input_pos : 0 < N.lo
  lower_pos : 0 < K.lo
  upper_pos : 0 < K.hi
  lower_budget : K.lo^2*N.hi ≤ 1
  upper_budget : 1 ≤ K.hi^2*N.lo

theorem inverse_sqrt_sound {N K : Interval} (h : Arithmetic N K) {n : ℝ}
    (hn : N.Contains n) : 0 < n ∧ K.Contains (Real.sqrt n)⁻¹ := by
  have hn0 : (0 : ℝ) < (N.lo : ℝ) := by exact_mod_cast h.input_pos
  have hlo : (0 : ℝ) < (K.lo : ℝ) := by exact_mod_cast h.lower_pos
  have hhi : (0 : ℝ) < (K.hi : ℝ) := by exact_mod_cast h.upper_pos
  have hlb : (K.lo : ℝ)^2*(N.hi : ℝ) ≤ 1 := by exact_mod_cast h.lower_budget
  have hub : 1 ≤ (K.hi : ℝ)^2*(N.lo : ℝ) := by exact_mod_cast h.upper_budget
  have hp : 0 < n := hn0.trans_le hn.1
  have hs := Real.sq_sqrt hp.le
  have hsp := Real.sqrt_pos.mpr hp
  have hl : (K.lo : ℝ)*Real.sqrt n ≤ 1 := by
    apply (sq_le_sq₀ (mul_nonneg hlo.le hsp.le) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [mul_pow, hs, one_pow]
    exact (mul_le_mul_of_nonneg_left hn.2 (sq_nonneg _)).trans hlb
  have hu : 1 ≤ (K.hi : ℝ)*Real.sqrt n := by
    apply (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg hhi.le hsp.le)).mp
    rw [mul_pow, hs, one_pow]
    exact hub.trans (mul_le_mul_of_nonneg_left hn.1 (sq_nonneg _))
  refine ⟨hp, ?_, ?_⟩
  · rw [← one_div]
    exact (le_div_iff₀ hsp).mpr hl
  · rw [← one_div]
    exact (div_le_iff₀ hsp).mpr hu

theorem threshold_guard {N : Interval} {n τ : ℝ} (hn : N.Contains n)
    (hτ : 0 ≤ τ) (hbudget : τ^2 < (N.lo : ℝ)) : τ < Real.sqrt n := by
  have hp : 0 < n := lt_of_lt_of_le (lt_of_le_of_lt (sq_nonneg τ) hbudget) hn.1
  have hb : τ^2 < n := hbudget.trans_le hn.1
  nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg n]

end
end SbtCosmo.Derivation.GroundIntervalReciprocal
