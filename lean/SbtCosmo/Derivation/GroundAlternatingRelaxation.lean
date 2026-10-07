import SbtCosmo.Derivation.GroundAlternating
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The actual normalized relaxation on the positive alternating slice.
The derivative is earned from the exact selected state response. -/
namespace SbtCosmo.Derivation.GroundAlternatingRelaxation
noncomputable section
set_option maxHeartbeats 1000000
open GroundState GroundAlternating

def even (p : ℝ) : ℝ := Real.sqrt ((1 + p) / 8)
def odd (p : ℝ) : ℝ := Real.sqrt ((1 - p) / 8)
def mixedEven (b κ m p : ℝ) : ℝ := (1 - m) * even p + m * even (response b κ p)
def mixedOdd (b κ m p : ℝ) : ℝ := (1 - m) * odd p + m * odd (response b κ p)
def quotient (a b : ℝ) : ℝ := (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2)
def mixedResponse (b κ m p : ℝ) : ℝ := quotient (mixedEven b κ m p) (mixedOdd b κ m p)
def mode (b κ m : ℝ) : ℝ := 1 - m - m * κ * b / 8

theorem normalized_pair_contrast (a b : ℝ) :
    contrast (fun i => pair a b i / Real.sqrt (normSq (pair a b))) = quotient a b := by
  have hs := Real.sq_sqrt (normSq_nonneg (pair a b))
  change 4 * ((a / Real.sqrt (normSq (pair a b))) ^ 2 -
    (b / Real.sqrt (normSq (pair a b))) ^ 2) = quotient a b
  unfold quotient
  rw [div_pow, div_pow, hs, pair_norm, ← sub_div]
  by_cases hz : a ^ 2 + b ^ 2 = 0
  · simp [hz]
  · field_simp

theorem mixed_pair_return {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) (b κ m : ℝ) :
    relaxed (selectedMap b κ) m (state p) = pair (mixedEven b κ m p) (mixedOdd b κ m p) := by
  unfold relaxed
  rw [show selectedMap b κ (state p) = state (response b κ p) from selected_state_return hp b κ]
  funext i
  fin_cases i <;> rfl

/-- The selected ground, affine mixing and native normalization all return. -/
theorem normalized_response_return {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) (b κ m : ℝ) :
    contrast (normalizedRelaxed (selectedMap b κ) m (state p)) = mixedResponse b κ m p := by
  unfold normalizedRelaxed
  rw [mixed_pair_return hp]
  exact normalized_pair_contrast _ _

theorem even_derivative : HasDerivAt even (1 / (16 * even 0)) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).const_add 1).div_const 8
  have h := hd.sqrt (by norm_num : (1 + (0 : ℝ)) / 8 ≠ 0)
  convert h using 1; dsimp [even]; ring

theorem odd_derivative : HasDerivAt odd (-1 / (16 * even 0)) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).const_sub 1).div_const 8
  have h := hd.sqrt (by norm_num : (1 - (0 : ℝ)) / 8 ≠ 0)
  convert h using 1; dsimp [odd, even]; ring

theorem even_zero_properties : 0 < even 0 ∧ (even 0) ^ 2 = 1 / 8 := by
  constructor
  · exact Real.sqrt_pos.mpr (by norm_num)
  · simpa only [even, add_zero] using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 8))

theorem mixed_zero (b κ m : ℝ) :
    mixedEven b κ m 0 = even 0 ∧ mixedOdd b κ m 0 = even 0 := by
  simp [mixedEven, mixedOdd, response, odd, even]
  ring

theorem mixed_even_derivative (b κ m : ℝ) :
    HasDerivAt (mixedEven b κ m) (mode b κ m / (16 * even 0)) 0 := by
  have hg : HasDerivAt (fun p => even (response b κ p))
      ((1 / (16 * even 0)) * (-κ * b / 8)) 0 := by
    have hf : HasDerivAt even (1 / (16 * even 0)) (response b κ 0) := by
      simpa [response] using even_derivative
    exact hf.comp 0 (response_derivative b κ)
  have h := (even_derivative.const_mul (1 - m)).add (hg.const_mul m)
  convert h using 1; dsimp [mixedEven, mode]; ring

theorem mixed_odd_derivative (b κ m : ℝ) :
    HasDerivAt (mixedOdd b κ m) (-mode b κ m / (16 * even 0)) 0 := by
  have hg : HasDerivAt (fun p => odd (response b κ p))
      ((-1 / (16 * even 0)) * (-κ * b / 8)) 0 := by
    have hf : HasDerivAt odd (-1 / (16 * even 0)) (response b κ 0) := by
      simpa [response] using odd_derivative
    exact hf.comp 0 (response_derivative b κ)
  have h := (odd_derivative.const_mul (1 - m)).add (hg.const_mul m)
  convert h using 1; dsimp [mixedOdd, mode]; ring

theorem mixed_response_derivative (b κ m : ℝ) :
    HasDerivAt (mixedResponse b κ m) (mode b κ m) 0 := by
  have ha := mixed_even_derivative b κ m
  have hb := mixed_odd_derivative b κ m
  have hn : mixedEven b κ m 0 ^ 2 + mixedOdd b κ m 0 ^ 2 ≠ 0 := by
    rw [(mixed_zero b κ m).1, (mixed_zero b κ m).2, (even_zero_properties).2]
    norm_num
  have h := ((ha.pow 2).sub (hb.pow 2)).div ((ha.pow 2).add (hb.pow 2)) hn
  have hq := (even_zero_properties).2
  have hp := (even_zero_properties).1.ne'
  convert h using 1
  dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply]
  rw [(mixed_zero b κ m).1, (mixed_zero b κ m).2]
  norm_num
  field_simp
  ring_nf
  rw [hq]
  ring

theorem state_zero : state 0 = uniform := by
  funext i
  fin_cases i <;> norm_num [state, pair, uniform]

theorem selected_uniform (b κ : ℝ) : selectedMap b κ uniform = uniform := by
  rw [← state_zero, selected_state_return (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)]
  simp [response]

theorem normalized_uniform (b κ m : ℝ) :
    normalizedRelaxed (selectedMap b κ) m uniform = uniform :=
  normalizedRelaxed_fixes _ _ (selected_uniform b κ) uniform_normalized

theorem mixed_response_zero (b κ m : ℝ) : mixedResponse b κ m 0 = 0 := by
  unfold mixedResponse quotient
  rw [(mixed_zero b κ m).1, (mixed_zero b κ m).2]
  simp

theorem positive_mixed {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) (i : Fin 8) :
    0 < relaxed (selectedMap b κ) m (state p) i := by
  have ha := state_positive hp i
  have hb := state_positive (response_live b κ p) i
  unfold relaxed
  rw [selected_state_return hp]
  have hx := mul_nonneg (sub_nonneg.mpr hm.2) ha.le
  by_cases hz : m = 0
  · simpa [hz] using ha
  · have hy := mul_pos (lt_of_le_of_ne hm.1 (Ne.symm hz)) hb
    linarith

/-- Normalization is genuinely defined on the positive slice for convex mixing. -/
theorem mixed_norm_positive {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) :
    0 < normSq (relaxed (selectedMap b κ) m (state p)) := by
  apply lt_of_le_of_ne (normSq_nonneg _)
  intro hz
  have he := (normSq_zero_iff _).mp hz.symm
  have hp0 := positive_mixed hp hm b κ 0
  rw [he] at hp0
  exact lt_irrefl 0 hp0

theorem normalized_pair_unit {a b : ℝ} (hn : 0 < normSq (pair a b)) :
    normSq (pair (a / Real.sqrt (normSq (pair a b)))
      (b / Real.sqrt (normSq (pair a b)))) = 1 := by
  have hs := Real.sq_sqrt hn.le
  rw [pair_norm, div_pow, div_pow, hs, ← add_div, pair_norm]
  have h : a ^ 2 + b ^ 2 ≠ 0 := by rw [pair_norm] at hn; nlinarith
  field_simp [h]

/-- Convex mixing preserves a genuine invariant positive alternating slice. -/
theorem normalized_state_return {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) :
    normalizedRelaxed (selectedMap b κ) m (state p) = state (mixedResponse b κ m p) := by
  let a := mixedEven b κ m p
  let o := mixedOdd b κ m p
  have he : relaxed (selectedMap b κ) m (state p) = pair a o := mixed_pair_return hp b κ m
  have hn : 0 < normSq (pair a o) := by rw [← he]; exact mixed_norm_positive hp hm b κ
  have ha : 0 < a := by simpa only [he, pair, Matrix.cons_val_zero] using positive_mixed hp hm b κ 0
  have ho : 0 < o := by simpa only [he, pair, Matrix.cons_val_one] using positive_mixed hp hm b κ 1
  have hr := Real.sqrt_pos.mpr hn
  have hrec := positive_pair_reconstructed (div_pos ha hr) (div_pos ho hr) (normalized_pair_unit hn)
  have hrel : normalizedRelaxed (selectedMap b κ) m (state p) =
      pair (a / Real.sqrt (normSq (pair a o))) (o / Real.sqrt (normSq (pair a o))) := by
    unfold normalizedRelaxed
    rw [he]
    funext i
    fin_cases i <;> rfl
  rw [← hrel, normalized_response_return hp] at hrec
  exact hrec.symm

theorem mixed_response_live {p m : ℝ} (hp : p ∈ Set.Ioo (-1) 1)
    (hm : m ∈ Set.Icc 0 1) (b κ : ℝ) : mixedResponse b κ m p ∈ Set.Ioo (-1) 1 := by
  have ha : 0 < mixedEven b κ m p := by
    have h := positive_mixed hp hm b κ 0
    rw [mixed_pair_return hp] at h
    exact h
  have hb : 0 < mixedOdd b κ m p := by
    have h := positive_mixed hp hm b κ 1
    rw [mixed_pair_return hp] at h
    exact h
  have hn : 0 < mixedEven b κ m p ^ 2 + mixedOdd b κ m p ^ 2 := by positivity
  change -1 < quotient _ _ ∧ quotient _ _ < 1
  unfold quotient
  rw [lt_div_iff₀ hn, div_lt_iff₀ hn]
  constructor <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]

/-- Earned derivative of the original normalized map on an actual field curve. -/
theorem actual_response_derivative (b κ m : ℝ) :
    HasDerivAt (fun p => contrast (normalizedRelaxed (selectedMap b κ) m (state p)))
      (mode b κ m) 0 := by
  apply (mixed_response_derivative b κ m).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with p hp
  exact normalized_response_return hp b κ m

theorem mode_stable_iff {m : ℝ} (hm : 0 < m) (b κ : ℝ) :
    |mode b κ m| < 1 ↔ -1 < κ * b / 8 ∧ κ * b / 8 < 2 / m - 1 := by
  have he : mode b κ m = (1 - m) + m * (-κ * b / 8) := by dsimp [mode]; ring
  rw [he, relaxed_real_mode_stable_iff hm]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Exact half-mixing criterion for this actual alternating tangent mode. -/
theorem half_mode_stable_iff (b κ : ℝ) :
    |mode b κ (1 / 2)| < 1 ↔ -8 < κ * b ∧ κ * b < 24 := by
  rw [mode_stable_iff (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem coupling_half_control :
    |mode 1 10 (1 / 2)| < 1 ∧ 1 < |mode 1 30 (1 / 2)| := by
  norm_num [mode]

theorem background_half_control :
    |mode 0 (3 / 10) (1 / 2)| < 1 ∧ 1 < |mode 100 (3 / 10) (1 / 2)| := by
  norm_num [mode]

/-- Differentiability supplies a strict local gain bound; zero is included. -/
theorem local_gain_upper {f : ℝ → ℝ} {d r : ℝ} (hf : HasDerivAt f d 0)
    (h0 : f 0 = 0) (hr : |d| < r) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, |p| < ε → |f p| ≤ r * |p| := by
  have he := (hf.hasDerivWithinAt (s := Set.univ)).limsup_norm_slope_le
    (by simpa only [Real.norm_eq_abs] using hr)
  simp only [nhdsWithin_univ, sub_zero, h0, Real.norm_eq_abs] at he
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro p hp
  by_cases hz : p = 0
  · simp [hz, h0]
  · have h := he (by simpa only [Real.dist_eq, sub_zero] using hp.trans_le (min_le_left _ _))
    have ha := abs_pos.mpr hz
    have hdiv : |f p| / |p| < r := by simpa only [div_eq_mul_inv, mul_comm] using h
    exact ((div_lt_iff₀ ha).mp hdiv).le

theorem local_gain_lower {f : ℝ → ℝ} {d r : ℝ} (hf : HasDerivAt f d 0)
    (h0 : f 0 = 0) (hr : r < |d|) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ p : ℝ, 0 < |p| → |p| < ε → r * |p| < |f p| := by
  have he : ∀ᶠ p in nhdsWithin 0 ({0}ᶜ), r < |slope f 0 p| :=
    hf.tendsto_slope.norm (isOpen_Ioi.mem_nhds (by simpa only [Real.norm_eq_abs] using hr))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro p hp hpε
  have h := he (by simpa only [Real.dist_eq, sub_zero] using hpε.trans_le (min_le_left _ _))
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (abs_pos.mp hp))
  simp only [slope_def_field, h0, sub_zero, abs_div] at h
  exact (lt_div_iff₀ hp).mp h

/-- Actual local nonlinear contraction along the alternating field curve. -/
theorem actual_local_contraction {b κ m : ℝ} (h : |mode b κ m| < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ ε > 0, ε ≤ 1 ∧
      ∀ p : ℝ, |p| < ε →
        |contrast (normalizedRelaxed (selectedMap b κ) m (state p))| ≤ r * |p| := by
  let r := (|mode b κ m| + 1) / 2
  have hr : |mode b κ m| < r := by dsimp [r]; linarith
  refine ⟨r, by dsimp [r]; positivity, by dsimp [r]; linarith, ?_⟩
  apply local_gain_upper (actual_response_derivative b κ m) _ hr
  rw [state_zero, normalized_uniform]
  simp [contrast, uniform]

/-- Actual one-step local expansion, rather than an assumed scalar mode. -/
theorem actual_local_expansion {b κ m : ℝ} (h : 1 < |mode b κ m|) :
    ∃ r : ℝ, 1 < r ∧ ∃ ε > 0, ε ≤ 1 ∧
      ∀ p : ℝ, 0 < |p| → |p| < ε →
        r * |p| < |contrast (normalizedRelaxed (selectedMap b κ) m (state p))| := by
  let r := (|mode b κ m| + 1) / 2
  have hr : r < |mode b κ m| := by dsimp [r]; linarith
  refine ⟨r, by dsimp [r]; linarith, ?_⟩
  apply local_gain_lower (actual_response_derivative b κ m) _ hr
  rw [state_zero, normalized_uniform]
  simp [contrast, uniform]

theorem coupling_actual_expansion :
    ∃ r : ℝ, 1 < r ∧ ∃ ε > 0, ε ≤ 1 ∧
      ∀ p : ℝ, 0 < |p| → |p| < ε →
        r * |p| < |contrast (normalizedRelaxed (selectedMap 1 30) (1 / 2) (state p))| :=
  actual_local_expansion coupling_half_control.2

theorem background_actual_expansion :
    ∃ r : ℝ, 1 < r ∧ ∃ ε > 0, ε ≤ 1 ∧
      ∀ p : ℝ, 0 < |p| → |p| < ε →
        r * |p| < |contrast (normalizedRelaxed (selectedMap 100 (3 / 10)) (1 / 2) (state p))| :=
  actual_local_expansion background_half_control.2

end
end SbtCosmo.Derivation.GroundAlternatingRelaxation
