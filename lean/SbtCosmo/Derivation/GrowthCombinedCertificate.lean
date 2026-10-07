import SbtCosmo.Derivation.CombinedEdgeQuadrature
import SbtCosmo.Derivation.GrowthRescaledCertificate

/-! Uniform original finite-start quadrature estimates on the wider combined
population/knob rescaling range. Prior narrower estimates are retained. -/
namespace SbtCosmo.Derivation.GrowthCombinedCertificate
noncomputable section
open Set MeasureTheory GrowthScaleReturn GrowthQuadrature CombinedEdgeQuadrature
open GrowthRescaledCertificate

theorem rescaled_start_bounds {c : ℝ} (hc : c ∈ Ioo (1/6) 5) :
    (1/1000:ℝ)/c ∈ Icc (1/5000) (3/500) := by
  have hp : 0 < c := by linarith [hc.1]
  exact ⟨(le_div_iff₀ hp).mpr (by linarith [hc.2]),
    (div_le_iff₀ hp).mpr (by linarith [hc.1])⟩


theorem prefactor_upper {c : ℝ} (hc : c ∈ Ioo (1/6) 5) :
    nativePrefactor (7/2) ((1/1000)/c) ≤ (2500+1/1000)*c := by
  have hp : 0 < c := by linarith [hc.1]
  have hy := rescaled_start_bounds hc
  have hsq := pow_le_pow_left₀ (by linarith [hy.1] : 0 ≤ (1/1000:ℝ)/c) hy.2 2
  have he : 5/(2*((1/1000:ℝ)/c))=2500*c := by field_simp; ring
  unfold nativePrefactor
  rw [he]
  nlinarith [hc.1]


theorem initial_term_upper {c : ℝ} (hc : c ∈ Ioo (1/6) 5) :
    (nativeRoot (7/2) ((1/1000)/c))⁻¹ ≤ c/300 := by
  have hy := rescaled_start_bounds hc
  have hyp : 0 < (1/1000:ℝ)/c := by linarith [hy.1]
  have hcube := pow_le_pow_left₀ hyp.le hy.2 3
  have hdiv : (2000:ℝ)^2 ≤ 1/(((1/1000:ℝ)/c)^3) := by
    apply (le_div_iff₀ (pow_pos hyp 3)).mpr
    nlinarith
  have hr : (2000:ℝ) ≤ nativeRoot (7/2) ((1/1000)/c) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2000) hr
  simp only [one_div] at hi
  have hf : (2000:ℝ)⁻¹ ≤ c/300 := by norm_num; linarith [hc.1]
  simpa only [one_div] using hi.trans hf


theorem lower_prefix_growth {c : ℝ} (hc : c ∈ Ioo (1/6) 5) :
    970*c < nativeGrowth (1/1000) ((5/2)/c^3) (4*c) := by
  have hp : 0 < c := by linarith [hc.1]
  rw [mul_comm 4 c,native_scale_covariance hp.ne',native_growth_quadrature
    (div_pos (by norm_num) hp) (by linarith [(rescaled_start_bounds hc).2]) (by norm_num)]
  have hI : (245:ℝ)/1000 ≤ integral (5/2) ((1/1000)/c) 4 :=
    lower_integral.trans (integral_interval_mono (by norm_num) (by linarith [(rescaled_start_bounds hc).1])
      (rescaled_start_bounds hc).2 (by norm_num) le_rfl)
  have hr : (1586:ℝ)/1000 ≤ nativeRoot (5/2) 4 := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα := prefactor_lower hp (by norm_num : (0:ℝ) ≤ 5/2)
  have hprod := mul_le_mul hα hI (by norm_num : (0:ℝ) ≤ 245/1000)
    (by linarith [hα] : 0 ≤ nativePrefactor (5/2) ((1/1000)/c))
  have hb : 2500*c*(245/1000) ≤ (nativeRoot (5/2) ((1/1000)/c))⁻¹+
      nativePrefactor (5/2) ((1/1000)/c)*integral (5/2) ((1/1000)/c) 4 :=
    hprod.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by positivity : (0:ℝ) ≤ 2500*c*(245/1000)) (Real.sqrt_nonneg _)
  exact (by nlinarith : 970*c < (1586/1000)*(2500*c*(245/1000))).trans_le hm


theorem upper_prefix_growth {c : ℝ} (hc : c ∈ Ioo (1/6) 5) :
    897*c < nativeGrowth (1/1000) ((7/2)/c^3) ((8/3)*c) := by
  have hp : 0 < c := by linarith [hc.1]
  rw [mul_comm (8/3) c,native_scale_covariance hp.ne',native_growth_quadrature
    (div_pos (by norm_num) hp) (by linarith [(rescaled_start_bounds hc).2]) (by norm_num)]
  have hI : (1908:ℝ)/10000 ≤ integral (7/2) ((1/1000)/c) (8/3) :=
    prefix_integral.trans (integral_interval_mono (by norm_num) (by linarith [(rescaled_start_bounds hc).1])
      (rescaled_start_bounds hc).2 (by norm_num) le_rfl)
  have hr : (1884:ℝ)/1000 ≤ nativeRoot (7/2) (8/3) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα := prefactor_lower hp (by norm_num : (0:ℝ) ≤ 7/2)
  have hprod := mul_le_mul hα hI (by norm_num : (0:ℝ) ≤ 1908/10000)
    (by linarith [hα] : 0 ≤ nativePrefactor (7/2) ((1/1000)/c))
  have hb : 2500*c*(1908/10000) ≤ (nativeRoot (7/2) ((1/1000)/c))⁻¹+
      nativePrefactor (7/2) ((1/1000)/c)*integral (7/2) ((1/1000)/c) (8/3) :=
    hprod.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by positivity : (0:ℝ) ≤ 2500*c*(1908/10000)) (Real.sqrt_nonneg _)
  exact (by nlinarith : 897*c < (1884/1000)*(2500*c*(1908/10000))).trans_le hm


theorem upper_horizon_growth {c : ℝ} (hc : c ∈ Ioo (1/6) 5) :
    nativeGrowth (1/1000) ((7/2)/c^3) 20 < 960*c := by
  have hp : 0 < c := by linarith [hc.1]
  have hy := rescaled_start_bounds hc
  have hA : (20:ℝ)/c ∈ Icc 4 120 :=
    ⟨(le_div_iff₀ hp).mpr (by linarith [hc.2]),(div_le_iff₀ hp).mpr (by linarith [hc.1])⟩
  have hscale := native_scale_covariance hp.ne' (1/1000) (7/2) (20/c)
  rw [show c*(20/c)=20 by field_simp] at hscale
  rw [hscale,native_growth_quadrature (div_pos (by norm_num) hp) (by linarith [hy.2,hA.1]) (by norm_num)]
  have hI := (integral_interval_mono (by norm_num : (0:ℝ) ≤ 7/2) (by norm_num)
    hy.1 (by linarith [hy.2,hA.1]) hA.2).trans upper_integral
  have hIpos : (0:ℝ) ≤ integral (7/2) ((1/1000)/c) (20/c) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith [hy.2,hA.1]) (fun _ => density_nonnegative)
  have hr : nativeRoot (7/2) (20/c) ≤ (1876:ℝ)/1000 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hA.1 3
    norm_num at hcube
    have hdiv : 1/((20/c)^3) ≤ (1:ℝ)/64 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 64) hcube
    linarith
  have hprod := mul_le_mul (prefactor_upper hc) hI hIpos (by positivity : (0:ℝ) ≤ (2500+1/1000)*c)
  have hb := add_le_add (initial_term_upper hc) hprod
  have hα := prefactor_lower hp (by norm_num : (0:ℝ) ≤ 7/2)
  have hsumpos : (0:ℝ) ≤ (nativeRoot (7/2) ((1/1000)/c))⁻¹+
      nativePrefactor (7/2) ((1/1000)/c)*integral (7/2) ((1/1000)/c) (20/c) := by
    exact add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (mul_nonneg (by linarith [hα]) hIpos)
  have hm := mul_le_mul hr hb hsumpos (by norm_num : (0:ℝ) ≤ 1876/1000)
  exact hm.trans_lt (by nlinarith : (1876/1000)*(c/300+(2500+1/1000)*c*(2036/10000)) < 960*c)

end
end SbtCosmo.Derivation.GrowthCombinedCertificate
