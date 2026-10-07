import SbtCosmo.Derivation.RobustEdgeQuadrature
import SbtCosmo.Derivation.WindowRobustRecord

/-! Exact scale covariance and uniform finite-start quadrature bounds.
Neither the actual initial term nor its parameter-dependent prefactor is dropped. -/
namespace SbtCosmo.Derivation.GrowthRescaledCertificate
noncomputable section
open Set MeasureTheory GrowthScaleReturn GrowthQuadrature RobustEdgeQuadrature

theorem native_scale_covariance {c : ℝ} (hc : c ≠ 0) (a0 lam A : ℝ) :
    nativeGrowth a0 (lam/c^3) (c*A)=nativeGrowth (a0/c) lam A := by
  unfold nativeGrowth logScale
  congr 1
  · field_simp
  · congr 1
    field_simp

theorem rescaled_start_bounds {c : ℝ} (hc : c ∈ Ioo (1/5) 4) :
    (1/1000:ℝ)/c ∈ Icc (1/4000) (1/200) := by
  have hp : 0 < c := by linarith [hc.1]
  exact ⟨(le_div_iff₀ hp).mpr (by linarith [hc.2]),
    (div_le_iff₀ hp).mpr (by linarith [hc.1])⟩

theorem integral_interval_mono {lam a b u v : ℝ} (hl : 0 ≤ lam)
    (hu : 0 < u) (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v) :
    integral lam a b ≤ integral lam u v :=
  intervalIntegral.integral_mono_interval hua hab hbv
    (Filter.Eventually.of_forall fun _ => density_nonnegative)
    (density_intervalIntegrable hl hu (hua.trans (hab.trans hbv)))

theorem prefactor_lower {c lam : ℝ} (hc : 0 < c) (hl : 0 ≤ lam) :
    2500*c ≤ nativePrefactor lam ((1/1000)/c) := by
  have he : 5/(2*((1/1000:ℝ)/c))=2500*c := by field_simp; ring
  unfold nativePrefactor
  rw [he]
  exact le_add_of_nonneg_left (mul_nonneg hl (sq_nonneg _))

theorem prefactor_upper {c : ℝ} (hc : c ∈ Ioo (1/5) 4) :
    nativePrefactor (7/2) ((1/1000)/c) ≤ (2500+1/1000)*c := by
  have hp : 0 < c := by linarith [hc.1]
  have hy := rescaled_start_bounds hc
  have hsq := pow_le_pow_left₀ (by linarith [hy.1] : 0 ≤ (1/1000:ℝ)/c) hy.2 2
  have he : 5/(2*((1/1000:ℝ)/c))=2500*c := by field_simp; ring
  unfold nativePrefactor
  rw [he]
  nlinarith [hc.1]

theorem initial_term_upper {c : ℝ} (hc : c ∈ Ioo (1/5) 4) :
    (nativeRoot (7/2) ((1/1000)/c))⁻¹ ≤ c/500 := by
  have hy := rescaled_start_bounds hc
  have hyp : 0 < (1/1000:ℝ)/c := by linarith [hy.1]
  have hcube := pow_le_pow_left₀ hyp.le hy.2 3
  have hdiv : (2500:ℝ)^2 ≤ 1/(((1/1000:ℝ)/c)^3) := by
    apply (le_div_iff₀ (pow_pos hyp 3)).mpr
    nlinarith
  have hr : (2500:ℝ) ≤ nativeRoot (7/2) ((1/1000)/c) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2500) hr
  simp only [one_div] at hi
  have hf : (2500:ℝ)⁻¹ ≤ c/500 := by norm_num; linarith [hc.1]
  simpa only [one_div] using hi.trans hf

theorem lower_prefix_growth {c : ℝ} (hc : c ∈ Ioo (1/5) 4) :
    970*c < nativeGrowth (1/1000) (3/c^3) (5*c) := by
  have hp : 0 < c := by linarith [hc.1]
  rw [mul_comm 5 c,native_scale_covariance hp.ne',native_growth_quadrature
    (div_pos (by norm_num) hp) (by linarith [(rescaled_start_bounds hc).2]) (by norm_num)]
  have hI : (224:ℝ)/1000 ≤ integral 3 ((1/1000)/c) 5 :=
    lower_integral.trans (integral_interval_mono (by norm_num) (by linarith [(rescaled_start_bounds hc).1])
      (rescaled_start_bounds hc).2 (by norm_num) le_rfl)
  have hr : (1734:ℝ)/1000 ≤ nativeRoot 3 5 := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα := prefactor_lower hp (by norm_num : (0:ℝ) ≤ 3)
  have hprod := mul_le_mul hα hI (by norm_num : (0:ℝ) ≤ 224/1000)
    (by linarith [hα] : 0 ≤ nativePrefactor 3 ((1/1000)/c))
  have hb : 2500*c*(224/1000) ≤ (nativeRoot 3 ((1/1000)/c))⁻¹+
      nativePrefactor 3 ((1/1000)/c)*integral 3 ((1/1000)/c) 5 :=
    hprod.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by positivity : (0:ℝ) ≤ 2500*c*(224/1000)) (Real.sqrt_nonneg _)
  exact (by nlinarith : 970*c < (1734/1000)*(2500*c*(224/1000))).trans_le hm

theorem upper_prefix_growth {c : ℝ} (hc : c ∈ Ioo (1/5) 4) :
    897*c < nativeGrowth (1/1000) ((7/2)/c^3) ((8/3)*c) := by
  have hp : 0 < c := by linarith [hc.1]
  rw [mul_comm (8/3) c,native_scale_covariance hp.ne',native_growth_quadrature
    (div_pos (by norm_num) hp) (by linarith [(rescaled_start_bounds hc).2]) (by norm_num)]
  have hI : (1909:ℝ)/10000 ≤ integral (7/2) ((1/1000)/c) (8/3) :=
    prefix_integral.trans (integral_interval_mono (by norm_num) (by linarith [(rescaled_start_bounds hc).1])
      (rescaled_start_bounds hc).2 (by norm_num) le_rfl)
  have hr : (1884:ℝ)/1000 ≤ nativeRoot (7/2) (8/3) := by
    apply (Real.le_sqrt' (by norm_num)).mpr
    norm_num
  have hα := prefactor_lower hp (by norm_num : (0:ℝ) ≤ 7/2)
  have hprod := mul_le_mul hα hI (by norm_num : (0:ℝ) ≤ 1909/10000)
    (by linarith [hα] : 0 ≤ nativePrefactor (7/2) ((1/1000)/c))
  have hb : 2500*c*(1909/10000) ≤ (nativeRoot (7/2) ((1/1000)/c))⁻¹+
      nativePrefactor (7/2) ((1/1000)/c)*integral (7/2) ((1/1000)/c) (8/3) :=
    hprod.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hm := mul_le_mul hr hb (by positivity : (0:ℝ) ≤ 2500*c*(1909/10000)) (Real.sqrt_nonneg _)
  exact (by nlinarith : 897*c < (1884/1000)*(2500*c*(1909/10000))).trans_le hm

theorem upper_horizon_growth {c : ℝ} (hc : c ∈ Ioo (1/5) 4) :
    nativeGrowth (1/1000) ((7/2)/c^3) 20 < 960*c := by
  have hp : 0 < c := by linarith [hc.1]
  have hy := rescaled_start_bounds hc
  have hA : (20:ℝ)/c ∈ Icc 5 100 :=
    ⟨(le_div_iff₀ hp).mpr (by linarith [hc.2]),(div_le_iff₀ hp).mpr (by linarith [hc.1])⟩
  have hscale := native_scale_covariance hp.ne' (1/1000) (7/2) (20/c)
  rw [show c*(20/c)=20 by field_simp] at hscale
  rw [hscale,native_growth_quadrature (div_pos (by norm_num) hp) (by linarith [hy.2,hA.1]) (by norm_num)]
  have hI := (integral_interval_mono (by norm_num : (0:ℝ) ≤ 7/2) (by norm_num)
    hy.1 (by linarith [hy.2,hA.1]) hA.2).trans upper_integral
  have hIpos : (0:ℝ) ≤ integral (7/2) ((1/1000)/c) (20/c) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith [hy.2,hA.1]) (fun _ => density_nonnegative)
  have hr : nativeRoot (7/2) (20/c) ≤ (1874:ℝ)/1000 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hA.1 3
    norm_num at hcube
    have hdiv : 1/((20/c)^3) ≤ (1:ℝ)/125 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 125) hcube
    linarith
  have hprod := mul_le_mul (prefactor_upper hc) hI hIpos (by positivity : (0:ℝ) ≤ (2500+1/1000)*c)
  have hb := add_le_add (initial_term_upper hc) hprod
  have hα := prefactor_lower hp (by norm_num : (0:ℝ) ≤ 7/2)
  have hsumpos : (0:ℝ) ≤ (nativeRoot (7/2) ((1/1000)/c))⁻¹+
      nativePrefactor (7/2) ((1/1000)/c)*integral (7/2) ((1/1000)/c) (20/c) := by
    exact add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (mul_nonneg (by linarith [hα]) hIpos)
  have hm := mul_le_mul hr hb hsumpos (by norm_num : (0:ℝ) ≤ 1874/1000)
  exact hm.trans_lt (by nlinarith : (1874/1000)*(c/500+(2500+1/1000)*c*(2035/10000)) < 960*c)

end
end SbtCosmo.Derivation.GrowthRescaledCertificate
