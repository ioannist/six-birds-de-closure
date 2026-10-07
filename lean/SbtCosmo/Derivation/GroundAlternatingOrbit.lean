import SbtCosmo.Derivation.GroundAlternatingRelaxation
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual alternating-slice iteration, local attraction and finite escape.
Attraction is scoped to this invariant slice, not all eight-site modes. -/
namespace SbtCosmo.Derivation.GroundAlternatingOrbit
noncomputable section
open Filter GroundState GroundAlternating GroundAlternatingRelaxation
open scoped Topology

theorem scalar_orbit_live {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) (n : ℕ) :
    (mixedResponse b κ m)^[n] p ∈ Set.Ioo (-1) 1 := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mixed_response_live ih hm b κ

theorem iterate_state_return {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) (n : ℕ) :
    (normalizedRelaxed (selectedMap b κ) m)^[n] (state p) =
      state ((mixedResponse b κ m)^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact normalized_state_return (scalar_orbit_live hp hm b κ n) hm b κ

theorem iterate_contrast_return {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) (n : ℕ) :
    contrast ((normalizedRelaxed (selectedMap b κ) m)^[n] (state p)) =
      (mixedResponse b κ m)^[n] p := by
  rw [iterate_state_return hp hm]
  exact state_contrast (scalar_orbit_live hp hm b κ n)

theorem contraction_orbit_bound {f : ℝ → ℝ} {r ε p : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ q : ℝ, |q| < ε → |f q| ≤ r * |q|) (hp : |p| < ε) (n : ℕ) :
    |f^[n] p| ≤ r ^ n * |p| ∧ |f^[n] p| < ε := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := hg _ ih.2
    constructor
    · calc
        |f (f^[n] p)| ≤ r * |f^[n] p| := hh
        _ ≤ r * (r ^ n * |p|) := mul_le_mul_of_nonneg_left ih.1 hr
        _ = r ^ (n + 1) * |p| := by rw [pow_succ]; ring
    · exact hh.trans_lt ((mul_le_of_le_one_left (abs_nonneg _) hr1.le).trans_lt ih.2)

theorem contraction_orbit_converges {f : ℝ → ℝ} {r ε p : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ q : ℝ, |q| < ε → |f q| ≤ r * |q|) (hp : |p| < ε) :
    Tendsto (fun n : ℕ => f^[n] p) atTop (nhds 0) := by
  have hbound := contraction_orbit_bound hr hr1 hg hp
  have hgeom := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const |p|
  have ha : Tendsto (fun n : ℕ => |f^[n] p|) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun n => (hbound n).1) (by simpa using hgeom)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ha)

theorem continuous_state : Continuous state := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [state, pair] <;> fun_prop

/-- A full iteration/convergence theorem for actual fields on the declared slice. -/
theorem actual_local_attraction {b κ m : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hmode : |mode b κ m| < 1) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, |p| < ε →
      Tendsto (fun n : ℕ => (normalizedRelaxed (selectedMap b κ) m)^[n] (state p))
        atTop (nhds uniform) := by
  let r := (|mode b κ m| + 1) / 2
  have hr : |mode b κ m| < r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨ε, hε, hε1, hg⟩ := local_gain_upper (mixed_response_derivative b κ m)
    (mixed_response_zero b κ m) hr
  refine ⟨ε, hε, hε1, ?_⟩
  intro p hp
  have hlive : p ∈ Set.Ioo (-1) 1 := abs_lt.mp (hp.trans_le hε1)
  have hscalar := contraction_orbit_converges hr0 hr1 hg hp
  have hstate := continuous_state.continuousAt.tendsto.comp hscalar
  rw [state_zero] at hstate
  exact hstate.congr (fun n => (iterate_state_return hlive hm b κ n).symm)

theorem expansion_orbit_escapes {f : ℝ → ℝ} {r ε p : ℝ} (hr : 1 < r)
    (hg : ∀ q : ℝ, 0 < |q| → |q| < ε → r * |q| < |f q|)
    (hp : 0 < |p|) : ∃ n : ℕ, ε ≤ |f^[n] p| := by
  by_contra hno
  push_neg at hno
  have hr0 : 0 < r := by linarith
  have hb : ∀ n : ℕ, r ^ n * |p| ≤ |f^[n] p| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hpos : 0 < |f^[n] p| := lt_of_lt_of_le (mul_pos (pow_pos hr0 n) hp) ih
      calc
        r ^ (n + 1) * |p| = r * (r ^ n * |p|) := by rw [pow_succ]; ring
        _ ≤ r * |f^[n] p| := mul_le_mul_of_nonneg_left ih hr0.le
        _ ≤ |f (f^[n] p)| := (hg _ hpos (hno n)).le
  have ht := (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hp
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_atTop ε)).exists
  exact (hno n).not_ge (hn.le.trans (hb n))

/-- Local nonlinear instability: every nonzero small alternating perturbation escapes. -/
theorem actual_local_escape {b κ m : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hmode : 1 < |mode b κ m|) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, 0 < |p| → |p| < ε →
      ∃ n : ℕ, ε ≤ |contrast ((normalizedRelaxed (selectedMap b κ) m)^[n] (state p))| := by
  let r := (|mode b κ m| + 1) / 2
  have hr : r < |mode b κ m| := by dsimp [r]; linarith
  have hr1 : 1 < r := by dsimp [r]; linarith
  obtain ⟨ε, hε, hε1, hg⟩ := local_gain_lower (mixed_response_derivative b κ m)
    (mixed_response_zero b κ m) hr
  refine ⟨ε, hε, hε1, ?_⟩
  intro p hp hpε
  have hlive : p ∈ Set.Ioo (-1) 1 := abs_lt.mp (hpε.trans_le hε1)
  obtain ⟨n, hn⟩ := expansion_orbit_escapes hr1 hg hp
  exact ⟨n, by rw [iterate_contrast_return hlive hm]; exact hn⟩

theorem half_local_attraction {b κ : ℝ} (h : -8 < κ * b ∧ κ * b < 24) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, |p| < ε →
      Tendsto (fun n : ℕ => (normalizedRelaxed (selectedMap b κ) (1 / 2))^[n] (state p))
        atTop (nhds uniform) :=
  actual_local_attraction (by norm_num) ((half_mode_stable_iff b κ).mpr h)

theorem half_local_escape {b κ : ℝ} (h : κ * b < -8 ∨ 24 < κ * b) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, 0 < |p| → |p| < ε →
      ∃ n : ℕ, ε ≤ |contrast ((normalizedRelaxed (selectedMap b κ) (1 / 2))^[n] (state p))| := by
  apply actual_local_escape (by norm_num)
  have hm : mode b κ (1 / 2) = 1 / 2 - κ * b / 16 := by dsimp [mode]; ring
  rw [hm]
  rcases h with h | h
  · have hp : 1 < 1 / 2 - κ * b / 16 := by linarith
    exact hp.trans_le (le_abs_self _)
  · have hn : 1 < -(1 / 2 - κ * b / 16) := by linarith
    exact hn.trans_le (neg_le_abs _)

theorem coupling_escape_control :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, 0 < |p| → |p| < ε →
      ∃ n : ℕ, ε ≤ |contrast ((normalizedRelaxed (selectedMap 1 30) (1 / 2))^[n] (state p))| :=
  half_local_escape (by norm_num)

theorem background_escape_control :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, 0 < |p| → |p| < ε →
      ∃ n : ℕ, ε ≤ |contrast ((normalizedRelaxed (selectedMap 100 (3 / 10)) (1 / 2))^[n] (state p))| :=
  half_local_escape (by norm_num)

end
end SbtCosmo.Derivation.GroundAlternatingOrbit
