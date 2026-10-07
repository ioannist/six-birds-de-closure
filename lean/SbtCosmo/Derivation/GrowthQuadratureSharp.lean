import SbtCosmo.Derivation.GrowthQuadrature

/-! Correlation-preserving whole-cell enclosures for the actual native integrand. -/
namespace SbtCosmo.Derivation.GrowthQuadratureSharp
noncomputable section
open Set MeasureTheory GrowthQuadrature

def densitySquare (lam a : ℝ) : ℝ := a^3 / (1 + lam * a^3)^3

theorem densitySquare_derivative {lam a : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a) :
    HasDerivAt (densitySquare lam) (3 * a^2 * (1 - 2 * lam * a^3) / (1 + lam * a^3)^4) a := by
  have hn : HasDerivAt (fun x : ℝ => x^3) (3 * a^2) a := by
    simpa using (hasDerivAt_id a).pow 3
  have hd := ((hn.const_mul lam).const_add 1).pow 3
  have hp : 0 < 1 + lam * a^3 := by positivity
  have h := hn.div hd (pow_ne_zero 3 hp.ne')
  convert h using 1
  simp only [Pi.pow_apply, Nat.cast_ofNat] at *
  field_simp
  ring

theorem densitySquare_monotone {lam a b : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hb : 2 * lam * b^3 ≤ 1) : MonotoneOn (densitySquare lam) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x hx => (densitySquare_derivative hlam (ha.trans hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (densitySquare_derivative hlam (ha.trans (interior_subset hx).1)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hxb := pow_le_pow_left₀ (ha.trans (interior_subset hx).1) (interior_subset hx).2 3
  have hc : 0 ≤ 1 - 2 * lam * x^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hxb hlam]
  rw [(densitySquare_derivative hlam (ha.trans (interior_subset hx).1)).deriv]
  exact div_nonneg (mul_nonneg (by positivity) hc) (by positivity)

theorem densitySquare_antitone {lam a b : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hb : 1 ≤ 2 * lam * a^3) : AntitoneOn (densitySquare lam) (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun x hx => (densitySquare_derivative hlam (ha.trans hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (densitySquare_derivative hlam (ha.trans (interior_subset hx).1)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hax := pow_le_pow_left₀ ha (interior_subset hx).1 3
  have hc : 1 - 2 * lam * x^3 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hax hlam]
  rw [(densitySquare_derivative hlam (ha.trans (interior_subset hx).1)).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc) (by positivity)

theorem density_monotone {lam a b : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hb : 2 * lam * b^3 ≤ 1) : MonotoneOn (density lam) (Icc a b) := by
  intro x hx y hy hxy
  apply (sq_le_sq₀ density_nonnegative density_nonnegative).mp
  rw [density_sq hlam (ha.trans hx.1), density_sq hlam (ha.trans hy.1)]
  exact densitySquare_monotone hlam ha hb hx hy hxy

theorem density_antitone {lam a b : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hb : 1 ≤ 2 * lam * a^3) : AntitoneOn (density lam) (Icc a b) := by
  intro x hx y hy hxy
  apply (sq_le_sq₀ density_nonnegative density_nonnegative).mp
  rw [density_sq hlam (ha.trans hx.1), density_sq hlam (ha.trans hy.1)]
  exact densitySquare_antitone hlam ha hb hx hy hxy

theorem density_global_upper {lam x hi : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x)
    (hhi : 0 ≤ hi) (hcert : 4 ≤ 27 * lam * hi^2) : density lam x ≤ hi := by
  have hz : 0 ≤ lam * x^3 := by positivity
  have hf : 0 ≤ (2 * (lam * x^3) - 1)^2 * (lam * x^3 + 4) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have he : 4 * (1 + lam * x^3)^3 - 27 * lam * x^3 =
      (2 * (lam * x^3) - 1)^2 * (lam * x^3 + 4) := by ring
  have hpeak : 27 * lam * x^3 ≤ 4 * (1 + lam * x^3)^3 := by linarith
  have hm := mul_le_mul_of_nonneg_right hcert (by positivity : 0 ≤ (1 + lam * x^3)^3)
  have hs : x^3 ≤ hi^2 * (1 + lam * x^3)^3 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : 0 < 27 * lam)).mp
    nlinarith
  apply (sq_le_sq₀ density_nonnegative hhi).mp
  rw [density_sq hlam.le hx]
  exact (div_le_iff₀ (by positivity : 0 < (1 + lam * x^3)^3)).mpr hs

/-- The minimum endpoint value bounds a unimodal cell from below. -/
theorem density_cell_lower {lam a b x lo : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hx : x ∈ Icc a b) (hlo : 0 ≤ lo)
    (hleft : lo^2 * (1 + lam * a^3)^3 ≤ a^3)
    (hright : lo^2 * (1 + lam * b^3)^3 ≤ b^3) : lo ≤ density lam x := by
  have hfa : lo ≤ density lam a := by
    apply (sq_le_sq₀ hlo density_nonnegative).mp
    rw [density_sq hlam ha]
    exact (le_div_iff₀ (by positivity : 0 < (1 + lam * a^3)^3)).mpr hleft
  have hb : 0 ≤ b := ha.trans (hx.1.trans hx.2)
  have hfb : lo ≤ density lam b := by
    apply (sq_le_sq₀ hlo density_nonnegative).mp
    rw [density_sq hlam hb]
    exact (le_div_iff₀ (by positivity : 0 < (1 + lam * b^3)^3)).mpr hright
  by_cases hc : 2 * lam * x^3 ≤ 1
  · exact hfa.trans (density_monotone hlam ha hc ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1)
  · exact hfb.trans (density_antitone hlam (ha.trans hx.1) (le_of_not_ge hc)
      ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2)

/-- Upper endpoints on monotone cells, or the exact global peak across the turning point. -/
theorem density_cell_upper {lam a b x hi : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a)
    (hx : x ∈ Icc a b) (hhi : 0 ≤ hi)
    (hcert : (2 * lam * b^3 ≤ 1 ∧ b^3 ≤ hi^2 * (1 + lam * b^3)^3) ∨
      (1 ≤ 2 * lam * a^3 ∧ a^3 ≤ hi^2 * (1 + lam * a^3)^3) ∨ 4 ≤ 27 * lam * hi^2) :
    density lam x ≤ hi := by
  rcases hcert with ⟨hmono, hbound⟩ | ⟨hanti, hbound⟩ | hpeak
  · have hb : 0 ≤ b := ha.trans (hx.1.trans hx.2)
    have hfb : density lam b ≤ hi := by
      apply (sq_le_sq₀ density_nonnegative hhi).mp
      rw [density_sq hlam.le hb]
      exact (div_le_iff₀ (by positivity : 0 < (1 + lam * b^3)^3)).mpr hbound
    exact (density_monotone hlam.le ha hmono hx ⟨hx.1.trans hx.2, le_rfl⟩ hx.2).trans hfb
  · have hfa : density lam a ≤ hi := by
      apply (sq_le_sq₀ density_nonnegative hhi).mp
      rw [density_sq hlam.le ha]
      exact (div_le_iff₀ (by positivity : 0 < (1 + lam * a^3)^3)).mpr hbound
    exact (density_antitone hlam.le ha hanti ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1).trans hfa
  · exact density_global_upper hlam (ha.trans hx.1) hhi hpeak


theorem integral_grid_bounds {lam : ℝ} {n : ℕ} {a lo hi : ℕ → ℝ}
    (hlam : 0 ≤ lam)
    (hcell : ∀ i < n, 0 < a i ∧ a i ≤ a (i + 1) ∧
      ∀ x ∈ Icc (a i) (a (i + 1)), lo i ≤ density lam x ∧ density lam x ≤ hi i) :
    (∑ i ∈ Finset.range n, (a (i + 1) - a i) * lo i) ≤ integral lam (a 0) (a n) ∧
      integral lam (a 0) (a n) ≤ (∑ i ∈ Finset.range n, (a (i + 1) - a i) * hi i) := by
  have hint : ∀ i < n, IntervalIntegrable (density lam) volume (a i) (a (i + 1)) :=
    fun i h => density_intervalIntegrable hlam (hcell i h).1 (hcell i h).2.1
  have hbound : ∀ i < n,
      (a (i + 1) - a i) * lo i ≤ ∫ x in a i..a (i + 1), density lam x ∧
        (∫ x in a i..a (i + 1), density lam x) ≤ (a (i + 1) - a i) * hi i := by
    intro i h
    obtain ⟨_, hab, hp⟩ := hcell i h
    constructor
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
        intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint i h)
          (fun x hx => (hp x hx).1)
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
        intervalIntegral.integral_mono_on hab (hint i h) intervalIntegrable_const
          (fun x hx => (hp x hx).2)
  rw [GrowthQuadrature.integral, ← intervalIntegral.sum_integral_adjacent_intervals hint]
  exact ⟨Finset.sum_le_sum (fun i hi => (hbound i (Finset.mem_range.mp hi)).1),
    Finset.sum_le_sum (fun i hi => (hbound i (Finset.mem_range.mp hi)).2)⟩

end
end SbtCosmo.Derivation.GrowthQuadratureSharp
