import SbtCosmo.Derivation.GrowthEternalWindow
import SbtCosmo.Derivation.GrowthEndpointSensitivity

/-! Actual finite formation endpoints converge to the constructed infinite endpoint.
The earlier selector's finite-horizon guards are discharged on the entire eventual domain. -/
namespace SbtCosmo.Derivation.GrowthHorizonLimit
noncomputable section
open Set Filter GrowthInfinite GrowthEternalWindow GrowthScaleReturn GrowthComparison GrowthExistence GrowthLimit
open scoped Topology

def finiteEndpoint (a0 T A : ℝ) : ℝ :=
  GrowthEndpointSensitivity.endpoint a0 (logScale a0 A) T

theorem finite_horizon_admissible {a0 T A : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)
    (hA : a0 * T < A) : a0 < A ∧ 0 < logScale a0 A ∧
      T ∈ Ioo (freeGrowth (logScale a0 A)) (Real.exp (logScale a0 A)) := by
  have haA : a0 < A := by nlinarith
  have hAp := ha0.trans haA
  have hl : 0 < logScale a0 A := Real.log_pos ((one_lt_div ha0).mpr haA)
  refine ⟨haA, hl, ?_, ?_⟩
  · unfold freeGrowth
    linarith [Real.exp_pos (-2 * logScale a0 A)]
  · rw [logScale, Real.exp_log (div_pos hAp ha0)]
    exact (lt_div_iff₀ ha0).mpr (by simpa [mul_comm] using hA)

theorem finiteEndpoint_spec {a0 T A : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)
    (hA : a0 * T < A) : 0 < finiteEndpoint a0 T A ∧
      nativeGrowth a0 (finiteEndpoint a0 T A) A = T := by
  have hv := finite_horizon_admissible ha0 hT hA
  exact GrowthEndpointSensitivity.endpoint_spec ha0 hv.2.1 hv.2.2

theorem finiteEndpoint_lt_infinite {a0 T A : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)
    (hA : a0 * T < A) : finiteEndpoint a0 T A < infiniteEndpoint a0 T := by
  have hs := finiteEndpoint_spec ha0 hT hA
  exact finite_endpoint_lt_infinite ha0 hT hs.1 (finite_horizon_admissible ha0 hT hA).1.le hs.2

theorem finiteEndpoint_strictMonoOn {a0 T : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T) :
    StrictMonoOn (finiteEndpoint a0 T) (Ioi (a0 * T)) := by
  intro A hA B hB hAB
  have hvA := finite_horizon_admissible ha0 hT hA
  have hvB := finite_horizon_admissible ha0 hT hB
  have hlog : logScale a0 A < logScale a0 B := by
    apply (Real.log_lt_log_iff (div_pos (ha0.trans hvA.1) ha0)
      (div_pos (ha0.trans hvB.1) ha0)).mpr
    exact (div_lt_div_iff_of_pos_right ha0).mpr hAB
  exact GrowthEndpointSensitivity.endpoint_strict_horizon ha0 hvA.2.1 hlog hvA.2.2 hvB.2.2

/-- The limit concerns the actual finite-horizon root, rather than only a compatible limiting formula. -/
theorem finiteEndpoint_tendsto {a0 T : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T) :
    Tendsto (finiteEndpoint a0 T) atTop (𝓝 (infiniteEndpoint a0 T)) := by
  have hvalid := eventually_gt_atTop (a0 * T)
  have hu := infiniteEndpoint_spec ha0 hT
  apply tendsto_order.mpr
  constructor
  · intro lo hlo
    by_cases hlop : 0 < lo
    · have hLo : T < nativeInfinite a0 lo := (below_infinite_endpoint_iff ha0 hT hlop).mpr hlo
      filter_upwards [hvalid, (native_tendsto ha0 hlop).eventually_const_lt hLo] with A hA hGA
      have hv := finite_horizon_admissible ha0 hT hA
      have hs := finiteEndpoint_spec ha0 hT hA
      have hm := native_endpoint_strictAntiOn ha0 hv.1
      have hcut : -(1 / A^3) < 0 := neg_neg_of_pos
        (one_div_pos.mpr (pow_pos (ha0.trans hv.1) 3))
      apply (hm.lt_iff_gt (hcut.trans hs.1) (hcut.trans hlop)).mp
      simpa only [hs.2] using hGA
    · filter_upwards [hvalid] with A hA
      exact (le_of_not_gt hlop).trans_lt (finiteEndpoint_spec ha0 hT hA).1
  · intro hi hhi
    filter_upwards [hvalid] with A hA
    exact (finiteEndpoint_lt_infinite ha0 hT hA).trans hhi

end
end SbtCosmo.Derivation.GrowthHorizonLimit
