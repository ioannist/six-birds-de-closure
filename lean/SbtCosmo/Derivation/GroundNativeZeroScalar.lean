import SbtCosmo.Derivation.GroundNativeZeroGeometry

/-! Exact scalar estimates for the original conjugate-phase half-mixing step.
Positive real overlap supplies quantitative margins, not a local basin premise. -/
namespace SbtCosmo.Derivation.GroundNativeZeroScalar
noncomputable section
set_option maxHeartbeats 2000000

theorem mixed_bounds {a r d : ℝ} (ha : 0 < a) (har : a ≤ r) (hr1 : r ≤ 1)
    (hd : d = (1-r+2*a^2/r)/2) : 0 < d ∧ a ≤ Real.sqrt d ∧ Real.sqrt d ≤ 1 := by
  have hr : 0 < r := ha.trans_le har
  have he : 2*r*d = r-r^2+2*a^2 := by rw [hd]; field_simp
  have has : a^2 ≤ r^2 := by nlinarith
  have hlo := mul_nonneg (sub_nonneg.mpr hr1) (by positivity : 0 ≤ r+2*a^2)
  have hdlo : a^2 ≤ d := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2*r)).mp
    nlinarith
  have hru := mul_nonneg hr.le (sub_nonneg.mpr hr1)
  have hdu : d ≤ 1 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2*r)).mp
    nlinarith
  refine ⟨lt_of_lt_of_le (sq_pos_of_pos ha) hdlo, ?_, Real.sqrt_le_one.mpr hdu⟩
  calc a = Real.sqrt (a^2) := (Real.sqrt_sq ha.le).symm
       _ ≤ Real.sqrt d := Real.sqrt_le_sqrt hdlo

theorem coefficient_monotone {a r d c : ℝ} (ha : 0 < a) (har : a ≤ r) (hr1 : r ≤ 1)
    (hd : d = (1-r+2*a^2/r)/2) (hc : c = a*(r+1)/(2*r*Real.sqrt d)) : a ≤ c := by
  obtain ⟨hdp, _, hs⟩ := mixed_bounds ha har hr1 hd
  have hr : 0 < r := ha.trans_le har
  have hsp : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdp
  rw [hc]
  apply (le_div_iff₀ (by positivity : 0 < 2*r*Real.sqrt d)).mpr
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*r)
  have hb : 2*r*Real.sqrt d ≤ r+1 := by linarith
  have h := mul_le_mul_of_nonneg_left hb ha.le
  nlinarith

theorem gain_numerator {a r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (has : a^2 ≤ r^2) :
    1-a^2 ≤ (r+1)^2-2*r*(r-r^2+2*a^2) := by
  by_cases hr : 1/4 ≤ r
  · have h1 := mul_nonneg (by positivity : 0 ≤ 2*r) (by nlinarith : 0 ≤ 1-r^2)
    have h2 := mul_nonneg (by linarith : 0 ≤ 4*r-1) (sub_nonneg.mpr has)
    nlinarith
  · have h1 := mul_nonneg hr0 (by nlinarith [sq_nonneg r] : 0 ≤ 2*r^2-r+2)
    have h2 := mul_nonneg (by linarith : 0 ≤ 1-4*r) (sq_nonneg a)
    nlinarith

theorem coefficient_square {a r d c : ℝ} (hr : 0 < r) (hdp : 0 < d)
    (hd : d = (1-r+2*a^2/r)/2) (hc : c = a*(r+1)/(2*r*Real.sqrt d)) :
    (2*r*(r-r^2+2*a^2))*c^2 = a^2*(r+1)^2 := by
  have hs := Real.sq_sqrt hdp.le
  rw [hc]
  have he : 2*r*d = r-r^2+2*a^2 := by rw [hd]; field_simp
  rw [← he, div_pow, mul_pow, mul_pow, hs]
  field_simp

theorem defect_contraction {a r d c : ℝ} (ha : 0 < a) (har : a ≤ r) (hr1 : r ≤ 1)
    (hd : d = (1-r+2*a^2/r)/2) (hc : c = a*(r+1)/(2*r*Real.sqrt d)) :
    1-c^2 ≤ (1-a^2/4)*(1-a^2) := by
  obtain ⟨hdp, _, hs⟩ := mixed_bounds ha har hr1 hd
  have hr : 0 < r := ha.trans_le har
  have has : a^2 ≤ r^2 := by nlinarith
  have hg := gain_numerator hr.le hr1 has
  have hm := coefficient_monotone ha har hr1 hd hc
  have hn : 0 ≤ c^2-a^2 := by nlinarith
  have he := coefficient_square hr hdp hd hc
  have hd1 : d ≤ 1 := Real.sqrt_le_one.mp hs
  have hde : 2*r*(r-r^2+2*a^2) = 4*r^2*d := by rw [hd]; field_simp; ring
  have hden : 2*r*(r-r^2+2*a^2) ≤ 4 := by
    rw [hde]
    have hrs : r^2 ≤ 1 := by nlinarith
    have ht := mul_le_mul (by nlinarith : 4*r^2 ≤ 4) hd1 hdp.le (by norm_num : (0:ℝ) ≤ 4)
    simpa using ht
  have h1 := mul_le_mul_of_nonneg_right hden hn
  have h2 := mul_le_mul_of_nonneg_left hg (sq_nonneg a)
  nlinarith

end
end SbtCosmo.Derivation.GroundNativeZeroScalar
