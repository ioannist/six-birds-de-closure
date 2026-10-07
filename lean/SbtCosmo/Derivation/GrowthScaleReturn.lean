import SbtCosmo.Derivation.GrowthExistence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Return the constructed log-time IVP to the implemented scale-factor domain. -/
namespace SbtCosmo.Derivation.GrowthScaleReturn
noncomputable section
open Set GrowthComparison GrowthExistence

def logScale (a0 a : ℝ) : ℝ := Real.log (a / a0)
def nativeGrowth (a0 lam a : ℝ) : ℝ := growth (lam * a0^3) (logScale a0 a)
def nativeDerivative (a0 lam a : ℝ) : ℝ := velocity (lam * a0^3) (logScale a0 a) / a

theorem hasDerivAt_logScale {a0 a : ℝ} (ha0 : a0 ≠ 0) (ha : a ≠ 0) :
    HasDerivAt (logScale a0) (1 / a) a := by
  convert ((hasDerivAt_id a).div_const a0).log (div_ne_zero ha ha0) using 1
  simp only [id_eq]
  field_simp

theorem logScale_mem {a0 A a : ℝ} (ha0 : 0 < a0) (hx : a ∈ Icc a0 A) :
    logScale a0 a ∈ Icc 0 (logScale a0 A) := by
  have ha := ha0.trans_le hx.1
  have hA := ha.trans_le hx.2
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hx.1))
  · exact (Real.log_le_log_iff (div_pos ha ha0) (div_pos hA ha0)).mpr
      (div_le_div_of_nonneg_right hx.2 ha0.le)

theorem horizon_log_nonneg {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A) :
    0 ≤ logScale a0 A := (logScale_mem ha0 ⟨hA, le_rfl⟩).1

theorem native_growth_derivative {a0 A lam a : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hx : a ∈ Icc a0 A) :
    HasDerivAt (nativeGrowth a0 lam) (nativeDerivative a0 lam a) a := by
  have ha := ha0.trans_le hx.1
  have hL := horizon_log_nonneg ha0 hA
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le hA)) hlam
  have hs := constructed_growthSolution hL hl
  simpa [nativeGrowth, nativeDerivative, div_eq_mul_inv] using
    (hs.growth_derivative (logScale a0 a) (logScale_mem ha0 hx)).comp a
      (hasDerivAt_logScale ha0.ne' ha.ne')

theorem native_velocity_derivative {a0 A lam a : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) (hx : a ∈ Icc a0 A) :
    HasDerivAt (nativeDerivative a0 lam)
      (scaleAcceleration a lam (nativeGrowth a0 lam a) (nativeDerivative a0 lam a)) a := by
  have ha := ha0.trans_le hx.1
  have hL := horizon_log_nonneg ha0 hA
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le hA)) hlam
  have hs := constructed_growthSolution hL hl
  have hh : WindowRecords.hubbleSquared a lam ≠ 0 := by
    apply ne_of_gt
    exact (WindowRecords.expanding_horizon_iff a lam).mpr
      ((WindowRecords.negative_horizon_tightens ha hx.2).trans_lt hlam)
  have hscale : scale a0 (logScale a0 a) = a := scale_log_horizon ha0 ha
  have hc : coefficient a0 lam (logScale a0 a) = 3 / (2 * (1 + lam * a^3)) := by
    unfold coefficient
    rw [hscale]
  have hb := scale_acceleration_bridge (D := nativeGrowth a0 lam a)
    (p := nativeDerivative a0 lam a) ha.ne' hh
  dsimp [nativeGrowth, nativeDerivative] at hb
  rw [mul_div_cancel₀ _ ha.ne'] at hb
  convert ((hs.velocity_derivative (logScale a0 a) (logScale_mem ha0 hx)).comp a
    (hasDerivAt_logScale ha0.ne' ha.ne')).div (hasDerivAt_id a) ha.ne' using 1
  simp only [id_eq, Function.comp_apply, mul_one, hc]
  dsimp [nativeGrowth, nativeDerivative]
  rw [one_div, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]
  apply (eq_div_iff (pow_ne_zero 2 ha.ne')).mpr
  nlinarith [hb]

/-- Actual original scale-factor IVP existence, including the native finite-start initial data. -/
theorem exists_original_scale_solution {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) :
    ∃ D p : ℝ → ℝ, D a0 = 1 ∧ p a0 = 1 / a0 ∧
      ∀ a ∈ Icc a0 A, HasDerivAt D (p a) a ∧
        HasDerivAt p (scaleAcceleration a lam (D a) (p a)) a := by
  have hL := horizon_log_nonneg ha0 hA
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le hA)) hlam
  have hs := constructed_growthSolution hL hl
  refine ⟨nativeGrowth a0 lam, nativeDerivative a0 lam, ?_, ?_, ?_⟩
  · simpa [nativeGrowth, logScale] using hs.growth_initial
  · simp only [nativeDerivative, logScale, Real.log_div_self]
    rw [hs.velocity_initial]
  · intro a hx
    exact ⟨native_growth_derivative ha0 hA hlam hx, native_velocity_derivative ha0 hA hlam hx⟩

theorem native_positive {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) :
    ∀ a ∈ Icc a0 A, 0 < nativeGrowth a0 lam a ∧ 0 < nativeDerivative a0 lam a := by
  have hL := horizon_log_nonneg ha0 hA
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le hA)) hlam
  have hp := growth_positive hL hl (constructed_growthSolution hL hl)
  intro a hx
  have hpos := hp (logScale a0 a) (logScale_mem ha0 hx)
  exact ⟨hpos.1, div_pos hpos.2 (ha0.trans_le hx.1)⟩

theorem native_endpoint_continuousAt {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hlam : -(1 / A^3) < lam) : ContinuousAt (fun k => nativeGrowth a0 k A) lam := by
  exact finalGrowth_continuousAt (horizon_log_nonneg ha0 hA)
    (live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le hA)) hlam)

/-- Strict parameter ordering for the constructed solution in the original native domain. -/
theorem native_endpoint_strictAntiOn {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 < A) :
    StrictAntiOn (fun lam => nativeGrowth a0 lam A) (Ioi (-(1 / A^3))) := by
  have hL : 0 < logScale a0 A :=
    Real.log_pos ((lt_div_iff₀ ha0).mpr (by simpa using hA))
  have hm := finalGrowth_strictAntiOn ha0 hL
  intro lam1 hl1 lam2 hl2 hlam
  exact hm (live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans hA)) hl1)
    (live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans hA)) hl2) hlam

end
end SbtCosmo.Derivation.GrowthScaleReturn
