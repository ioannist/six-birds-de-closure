import SbtCosmo.Derivation.GroundSelector
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact alternating positive slice of the unchanged eight-site ground map.
The selected ground response is constructed; no derivative or spectral mode
of the nonlinear ground selector is supplied as a premise. -/
namespace SbtCosmo.Derivation.GroundAlternating
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
open GroundState

def pair (a b : ℝ) : Field := ![a, b, a, b, a, b, a, b]

theorem pair_norm (a b : ℝ) : normSq (pair a b) = 4 * (a ^ 2 + b ^ 2) := by
  simp [normSq, pair, Fin.sum_univ_succ]
  ring

theorem pair_gradient (a b : ℝ) : gradient (pair a b) = 0 := by
  funext i
  fin_cases i <;> simp [gradient, pair, next, prev]

theorem pairing_symmetric (v u w : Field) :
    (∑ i, u i * hamiltonian v w i) = ∑ i, w i * hamiltonian v u i := by
  simp [hamiltonian, next, prev, Fin.sum_univ_succ]
  ring

/-- Positivity makes the overlap with the constructed positive ground nonzero. -/
theorem positive_eigen_ground {v u : Field} {e : ℝ}
    (hu : ∀ i, 0 < u i) (hn : normSq u = 1)
    (he : ∀ i, hamiltonian v u i = e * u i) : IsGround v u e := by
  let g := positiveGround v
  let f := energy v g
  have hg := (positiveGround_spec v).2
  have hgp : ∀ i, 0 < g i := (positiveGround_spec v).1
  have ho : 0 < ∑ i, u i * g i :=
    Finset.sum_pos (fun i _ => mul_pos (hu i) (hgp i)) Finset.univ_nonempty
  have hp := pairing_symmetric v u g
  have hge : ∀ i, hamiltonian v g i = f * g i := hg.2.1
  simp only [hge, he] at hp
  have hp' : f * (∑ i, u i * g i) = e * (∑ i, u i * g i) := by
    simpa only [Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using hp
  have hef : e = f := (mul_right_cancel₀ ho.ne' hp').symm
  exact ⟨hn, he, by simpa only [hef] using hg.2.2⟩

def radius (d : ℝ) : ℝ := Real.sqrt (1 + d ^ 2)
def ratio (d : ℝ) : ℝ := radius d + d
def amplitude (d : ℝ) : ℝ := 1 / Real.sqrt (4 * (1 + ratio d ^ 2))
def ground (d : ℝ) : Field := pair (amplitude d) (ratio d * amplitude d)

theorem radius_properties (d : ℝ) :
    0 < radius d ∧ (radius d) ^ 2 = 1 + d ^ 2 ∧ |d| < radius d := by
  have hp : 0 < 1 + d ^ 2 := by positivity
  have hr : 0 < radius d := Real.sqrt_pos.mpr hp
  have hs : (radius d) ^ 2 = 1 + d ^ 2 := Real.sq_sqrt hp.le
  refine ⟨hr, hs, ?_⟩
  nlinarith [sq_abs d, abs_nonneg d]

theorem ratio_positive (d : ℝ) : 0 < ratio d := by
  have h := radius_properties d
  dsimp [ratio]
  linarith [neg_abs_le d]

theorem amplitude_properties (d : ℝ) :
    0 < amplitude d ∧ 4 * (1 + ratio d ^ 2) * amplitude d ^ 2 = 1 := by
  have hp : 0 < 4 * (1 + ratio d ^ 2) := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn := (Real.sqrt_pos.mpr hp).ne'
  refine ⟨div_pos (by norm_num) (Real.sqrt_pos.mpr hp), ?_⟩
  dsimp [amplitude]
  rw [div_pow, one_pow, hs]
  exact mul_div_cancel₀ _ hp.ne'

theorem ground_positive (d : ℝ) (i : Fin 8) : 0 < ground d i := by
  have ha := (amplitude_properties d).1
  have hb := mul_pos (ratio_positive d) ha
  fin_cases i <;> simp [ground, pair] <;> assumption

theorem ground_normalized (d : ℝ) : normSq (ground d) = 1 := by
  rw [ground, pair_norm]
  nlinarith [(amplitude_properties d).2]

theorem ground_eigen (c d : ℝ) (i : Fin 8) :
    hamiltonian (pair (c + d) (c - d)) (ground d) i =
      (1 + c - radius d) * ground d i := by
  have hr := (radius_properties d).2.1
  fin_cases i <;> simp [hamiltonian, ground, pair, next, prev, ratio] <;>
    ring_nf
  all_goals try rw [hr]
  all_goals ring

theorem ground_selected (c d : ℝ) :
    positiveGround (pair (c + d) (c - d)) = ground d := by
  exact positive_ground_unique (positiveGround_spec _).2
    (positive_eigen_ground (ground_positive d) (ground_normalized d) (ground_eigen c d))
    (positiveGround_spec _).1 (ground_positive d)

/-- Density contrast on a paired unit field, equal to even-site mass minus odd-site mass. -/
def contrast (u : Field) : ℝ := 4 * ((u 0) ^ 2 - (u 1) ^ 2)

theorem ground_contrast (d : ℝ) : contrast (ground d) = -d / radius d := by
  have hs := (radius_properties d).2.1
  have hp := (amplitude_properties d).2
  have hr := (radius_properties d).1.ne'
  have he := ground_eigen 0 d (0 : Fin 8)
  have ho := ground_eigen 0 d (1 : Fin 8)
  simp [ground, pair, hamiltonian, next, prev] at he ho
  have h0 : radius d * (amplitude d ^ 2 - (ratio d * amplitude d) ^ 2) +
      d * (amplitude d ^ 2 + (ratio d * amplitude d) ^ 2) = 0 := by
    linear_combination amplitude d * he - (ratio d * amplitude d) * ho
  have hn := ground_normalized d
  rw [ground, pair_norm] at hn
  dsimp [contrast, ground, pair]
  apply (eq_div_iff hr).mpr
  linear_combination 4 * h0 - d * hn

def state (p : ℝ) : Field := pair (Real.sqrt ((1 + p) / 8)) (Real.sqrt ((1 - p) / 8))
def response (b κ p : ℝ) : ℝ := -(κ * b * p / 8) / radius (κ * b * p / 8)
def selectedMap (b κ : ℝ) (u : Field) : Field := positiveGround (sourcePotential (fun _ => b) κ u)

theorem state_positive {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) (i : Fin 8) :
    0 < state p i := by
  have ha : 0 < Real.sqrt ((1 + p) / 8) := Real.sqrt_pos.mpr (by linarith [hp.1, hp.2])
  have hb : 0 < Real.sqrt ((1 - p) / 8) := Real.sqrt_pos.mpr (by linarith [hp.1, hp.2])
  fin_cases i <;> dsimp [state, pair] <;> assumption

theorem state_normalized {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) : normSq (state p) = 1 := by
  rw [state, pair_norm]
  rw [Real.sq_sqrt (by linarith [hp.1, hp.2] : 0 ≤ (1 + p) / 8),
    Real.sq_sqrt (by linarith [hp.1, hp.2] : 0 ≤ (1 - p) / 8)]
  ring

theorem state_contrast {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) : contrast (state p) = p := by
  dsimp [contrast, state, pair]
  rw [Real.sq_sqrt (by linarith [hp.1, hp.2] : 0 ≤ (1 + p) / 8),
    Real.sq_sqrt (by linarith [hp.1, hp.2] : 0 ≤ (1 - p) / 8)]
  ring

theorem state_source {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) (b κ : ℝ) :
    sourcePotential (fun _ => b) κ (state p) =
      pair (b + κ * b / 8 + κ * b * p / 8) (b + κ * b / 8 - κ * b * p / 8) := by
  have hg : gradient (state p) = 0 := pair_gradient _ _
  have ha := Real.sq_sqrt (by linarith [hp.1, hp.2] : 0 ≤ (1 + p) / 8)
  have hb := Real.sq_sqrt (by linarith [hp.1, hp.2] : 0 ≤ (1 - p) / 8)
  funext i
  simp only [sourcePotential, BackgroundSelection.potential, hg, Pi.zero_apply]
  fin_cases i <;> dsimp [state, pair]
  all_goals first | rw [ha] | rw [hb]
  all_goals ring

/-- Exact return to the actual positive ground selector of the unchanged cycle. -/
theorem selected_response {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) (b κ : ℝ) :
    selectedMap b κ (state p) = ground (κ * b * p / 8) ∧
      contrast (selectedMap b κ (state p)) = response b κ p := by
  have h : selectedMap b κ (state p) = ground (κ * b * p / 8) := by
    rw [selectedMap, state_source hp, ground_selected]
  exact ⟨h, by rw [h, ground_contrast]; rfl⟩

theorem positive_pair_reconstructed {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hn : normSq (pair a b) = 1) : state (contrast (pair a b)) = pair a b := by
  rw [pair_norm] at hn
  have hc : contrast (pair a b) = 4 * (a ^ 2 - b ^ 2) := rfl
  have he : (1 + contrast (pair a b)) / 8 = a ^ 2 := by rw [hc]; linarith
  have ho : (1 - contrast (pair a b)) / 8 = b ^ 2 := by rw [hc]; linarith
  simp only [state, he, ho, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le]

theorem ground_eq_state (d : ℝ) : ground d = state (-d / radius d) := by
  have h := positive_pair_reconstructed (ground_positive d 0) (ground_positive d 1)
    (ground_normalized d)
  change state (contrast (ground d)) = ground d at h
  rw [ground_contrast] at h
  exact h.symm

theorem response_live (b κ p : ℝ) : response b κ p ∈ Set.Ioo (-1) 1 := by
  have h := radius_properties (κ * b * p / 8)
  have he : |response b κ p| < 1 := by
    dsimp [response]
    rw [abs_div, abs_neg, abs_of_pos h.1]
    exact (div_lt_one h.1).mpr h.2.2
  exact (abs_lt.mp he)

theorem selected_state_return {p : ℝ} (hp : p ∈ Set.Ioo (-1) 1) (b κ : ℝ) :
    selectedMap b κ (state p) = state (response b κ p) := by
  rw [(selected_response hp b κ).1, ground_eq_state]
  rfl

theorem response_derivative (b κ : ℝ) : HasDerivAt (response b κ) (-κ * b / 8) 0 := by
  have hd : HasDerivAt (fun p : ℝ => κ * b * p / 8) (κ * b / 8) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul (κ * b)).div_const 8 using 1; ring
  have hr := ((hd.pow 2).const_add 1).sqrt (by norm_num : (1 : ℝ) + (κ * b * 0 / 8) ^ 2 ≠ 0)
  have hh := hd.neg.div hr (by simp [radius] : radius (κ * b * 0 / 8) ≠ 0)
  have h : HasDerivAt (response b κ) (-(κ * b / 8)) 0 := by
    simpa [response, radius] using hh
  convert h using 1; ring

end
end SbtCosmo.Derivation.GroundAlternating
