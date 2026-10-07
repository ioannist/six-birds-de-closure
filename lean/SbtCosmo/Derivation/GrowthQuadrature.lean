import SbtCosmo.Derivation.GrowthScaleReturn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Native quadrature and exact finite-cell enclosures for the constructed growth family. -/
namespace SbtCosmo.Derivation.GrowthQuadrature
noncomputable section
open Set MeasureTheory GrowthComparison GrowthExistence GrowthScaleReturn

def density (lam a : ℝ) : ℝ := Real.sqrt (a^3) / (Real.sqrt (1 + lam * a^3))^3
def integral (lam a0 A : ℝ) : ℝ := ∫ a in a0..A, density lam a
def nativeRoot (lam a : ℝ) : ℝ := Real.sqrt (1 / a^3 + lam)
def nativePrefactor (lam a0 : ℝ) : ℝ := lam * a0^2 + 5 / (2 * a0)

theorem log_exponential_power {a0 a : ℝ} (ha0 : 0 < a0) (ha : 0 < a) (n : ℕ) :
    Real.exp (-(n : ℝ) * logScale a0 a) = (a0 / a)^n := by
  rw [show -(n : ℝ) * logScale a0 a = -((n : ℝ) * logScale a0 a) by ring,
    Real.exp_neg, Real.exp_nat_mul]
  unfold logScale
  rw [Real.exp_log (div_pos ha ha0)]
  rw [← inv_pow, inv_div]

theorem root_log_bridge {a0 a lam : ℝ} (ha0 : 0 < a0) (ha : 0 < a) :
    root (lam * a0^3) (logScale a0 a) =
      Real.sqrt (a0^3) * Real.sqrt (1 + lam * a^3) / Real.sqrt (a^3) := by
  have he := log_exponential_power ha0 ha 3
  norm_num only [Nat.cast_ofNat] at he
  unfold root rootSquared
  rw [he]
  have hq : (a0 / a)^3 + lam * a0^3 = a0^3 * (1 + lam * a^3) / a^3 := by
    field_simp
  rw [hq, Real.sqrt_div' _ (pow_pos ha 3).le, Real.sqrt_mul (pow_pos ha0 3).le]

theorem density_nonnegative {lam a : ℝ} : 0 ≤ density lam a := by
  exact div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)

theorem density_continuousAt {lam a : ℝ} (hlam : 0 ≤ lam) (ha : 0 < a) :
    ContinuousAt (density lam) a := by
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  apply pow_ne_zero
  exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + lam * a^3)).ne'

theorem density_intervalIntegrable {lam a b : ℝ} (hlam : 0 ≤ lam)
    (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable (density lam) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  exact (density_continuousAt hlam (ha.trans_le hx.1)).continuousWithinAt

theorem log_integrand_bridge {a0 a lam : ℝ} (ha0 : 0 < a0) (ha : 0 < a)
    (hlam : 0 ≤ lam) :
    integrand (lam * a0^3) (logScale a0 a) * (1 / a) =
      (a0^2 / (Real.sqrt (a0^3))^3) * density lam a := by
  have hb := (Real.sqrt_pos.mpr (pow_pos ha0 3)).ne'
  have ht := (Real.sqrt_pos.mpr (pow_pos ha 3)).ne'
  have hs := (Real.sqrt_pos.mpr (by positivity : 0 < 1 + lam * a^3)).ne'
  have ht2 := Real.sq_sqrt (pow_pos ha 3).le
  have he := log_exponential_power ha0 ha 2
  norm_num only [Nat.cast_ofNat] at he
  unfold integrand density
  rw [he, root_log_bridge ha0 ha]
  have ht3 : (Real.sqrt (a^3))^3 = a^3 * Real.sqrt (a^3) := by
    rw [pow_succ, ht2]
  field_simp [ha.ne', hb, ht, hs]
  nlinarith [ht3]

/-- The change of variables returns the log integral to the exact native scale interval. -/
theorem primitive_native_bridge {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) :
    primitive (lam * a0^3) (logScale a0 A) =
      (a0^2 / (Real.sqrt (a0^3))^3) * integral lam a0 A := by
  have hl : Live a0 lam (logScale a0 A) := by
    intro x _
    unfold scale
    positivity
  have hr := rootLive_of_live hl
  have hder : ∀ x ∈ uIcc a0 A, HasDerivAt (logScale a0) (1 / x) x := by
    intro x hx
    rw [uIcc_of_le hA] at hx
    exact hasDerivAt_logScale ha0.ne' (ha0.trans_le hx.1).ne'
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (uIcc a0 A) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    rw [uIcc_of_le hA] at hx
    exact (ha0.trans_le hx.1).ne'
  have hg : ContinuousOn (integrand (lam * a0^3)) ((logScale a0) '' uIcc a0 A) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [uIcc_of_le hA] at ha
    exact (integrand_continuousAt (hr _ (logScale_mem ha0 ha))).continuousWithinAt
  have he := intervalIntegral.integral_comp_mul_deriv' hder hc hg
  simp only [logScale, Real.log_div_self] at he
  change (∫ x in (0 : ℝ)..Real.log (A / a0), integrand (lam * a0^3) x) =
    (a0^2 / (Real.sqrt (a0^3))^3) * (∫ x in a0..A, density lam x)
  rw [← he]
  change (∫ x in a0..A, integrand (lam * a0^3) (logScale a0 x) * (1 / x)) = _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hA] at ha
  exact log_integrand_bridge ha0 (ha0.trans_le ha.1) hlam

theorem root_native_bridge {a0 a lam : ℝ} (ha0 : 0 < a0) (ha : 0 < a) :
    root (lam * a0^3) (logScale a0 a) = Real.sqrt (a0^3) * nativeRoot lam a := by
  rw [root_log_bridge ha0 ha]
  unfold nativeRoot
  have he : 1 / a^3 + lam = (1 + lam * a^3) / a^3 := by field_simp
  rw [he, Real.sqrt_div' _ (pow_pos ha 3).le]
  ring

/-- Exact native growth quadrature, including the parameter-dependent finite-start term. -/
theorem native_growth_quadrature {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : 0 ≤ lam) :
    nativeGrowth a0 lam A = nativeRoot lam A *
      ((nativeRoot lam a0)⁻¹ + nativePrefactor lam a0 * integral lam a0 A) := by
  have hB := (Real.sqrt_pos.mpr (pow_pos ha0 3)).ne'
  have hB2 := Real.sq_sqrt (pow_pos ha0 3).le
  have hB3 : (Real.sqrt (a0^3))^3 = a0^3 * Real.sqrt (a0^3) := by
    rw [pow_succ, hB2]
  have h0 : root (lam * a0^3) 0 = Real.sqrt (a0^3) * nativeRoot lam a0 := by
    simpa [logScale] using root_native_bridge (lam := lam) ha0 ha0
  unfold nativeGrowth growth
  rw [root_native_bridge ha0 (ha0.trans_le hA), h0, primitive_native_bridge ha0 hA hlam]
  unfold prefactor nativePrefactor
  rw [hB3]
  field_simp [hB, ha0.ne']

theorem density_sq {lam a : ℝ} (hlam : 0 ≤ lam) (ha : 0 ≤ a) :
    (density lam a)^2 = a^3 / (1 + lam * a^3)^3 := by
  unfold density
  rw [div_pow, ← pow_mul, mul_comm 3 2, pow_mul,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- Rational square bounds on each cell give pointwise bounds without sampled interpolation. -/
theorem density_cell_bounds {lam a b x lo hi : ℝ} (hlam : 0 ≤ lam)
    (ha : 0 ≤ a) (hx : x ∈ Icc a b) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hbelow : lo^2 * (1 + lam * b^3)^3 ≤ a^3)
    (habove : b^3 ≤ hi^2 * (1 + lam * a^3)^3) :
    lo ≤ density lam x ∧ density lam x ≤ hi := by
  have hx0 := ha.trans hx.1
  have hb0 := hx0.trans hx.2
  have ha3 := pow_le_pow_left₀ ha hx.1 3
  have hb3 := pow_le_pow_left₀ hx0 hx.2 3
  have hden : 0 < (1 + lam * x^3)^3 := by positivity
  have hlower : (1 + lam * a^3)^3 ≤ (1 + lam * x^3)^3 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left ha3 hlam]) 3
  have hupper : (1 + lam * x^3)^3 ≤ (1 + lam * b^3)^3 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hb3 hlam]) 3
  have hs := density_sq hlam hx0
  constructor
  · have he : lo^2 ≤ (density lam x)^2 := by
      rw [hs]
      apply (le_div_iff₀ hden).mpr
      exact (mul_le_mul_of_nonneg_left hupper (sq_nonneg lo)).trans (hbelow.trans ha3)
    exact (sq_le_sq₀ hlo density_nonnegative).mp he
  · have he : (density lam x)^2 ≤ hi^2 := by
      rw [hs]
      apply (div_le_iff₀ hden).mpr
      exact (hb3.trans habove).trans (mul_le_mul_of_nonneg_left hlower (sq_nonneg hi))
    exact (sq_le_sq₀ density_nonnegative hhi).mp he

theorem integral_grid_bounds {lam : ℝ} {n : ℕ} {a lo hi : ℕ → ℝ}
    (hlam : 0 ≤ lam)
    (hcell : ∀ i < n, 0 < a i ∧ a i ≤ a (i + 1) ∧ 0 ≤ lo i ∧ 0 ≤ hi i ∧
      (lo i)^2 * (1 + lam * (a (i + 1))^3)^3 ≤ (a i)^3 ∧
      (a (i + 1))^3 ≤ (hi i)^2 * (1 + lam * (a i)^3)^3) :
    (∑ i ∈ Finset.range n, (a (i + 1) - a i) * lo i) ≤ integral lam (a 0) (a n) ∧
      integral lam (a 0) (a n) ≤ (∑ i ∈ Finset.range n, (a (i + 1) - a i) * hi i) := by
  have hint : ∀ i < n, IntervalIntegrable (density lam) volume (a i) (a (i + 1)) :=
    fun i h => density_intervalIntegrable hlam (hcell i h).1 (hcell i h).2.1
  have hbound : ∀ i < n,
      (a (i + 1) - a i) * lo i ≤ ∫ x in a i..a (i + 1), density lam x ∧
        (∫ x in a i..a (i + 1), density lam x) ≤ (a (i + 1) - a i) * hi i := by
    intro i h
    obtain ⟨ha, hab, hlo, hhi, hbelow, habove⟩ := hcell i h
    have hp : ∀ x ∈ Icc (a i) (a (i + 1)), lo i ≤ density lam x ∧ density lam x ≤ hi i :=
      fun _ hx => density_cell_bounds hlam ha.le hx hlo hhi hbelow habove
    constructor
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
        intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint i h)
          (fun x hx => (hp x hx).1)
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
        intervalIntegral.integral_mono_on hab (hint i h) intervalIntegrable_const
          (fun x hx => (hp x hx).2)
  rw [integral, ← intervalIntegral.sum_integral_adjacent_intervals hint]
  exact ⟨Finset.sum_le_sum (fun i hi => (hbound i (Finset.mem_range.mp hi)).1),
    Finset.sum_le_sum (fun i hi => (hbound i (Finset.mem_range.mp hi)).2)⟩

end
end SbtCosmo.Derivation.GrowthQuadrature
