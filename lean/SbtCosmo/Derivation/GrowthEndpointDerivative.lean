import SbtCosmo.Derivation.GrowthParameter
import SbtCosmo.Derivation.WindowSensitivity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Continuously differentiable actual window endpoints and exact scaling sensitivities. -/
namespace SbtCosmo.Derivation.GrowthEndpointDerivative
noncomputable section
open Set Filter GrowthComparison GrowthExistence GrowthLimit GrowthWindow GrowthParameter
  GrowthEndpointSensitivity WindowSensitivity
open scoped Topology

theorem finalGrowth_c1 {a0 L : ℝ} (ha : 0 < a0) (hL : 0 ≤ L) :
    ContDiffOn ℝ 1 (finalGrowth a0 L) (Ioi (-(1 / (scale a0 L)^3))) := by
  have hl : ∀ lam ∈ Ioi (-(1 / (scale a0 L)^3)), Live a0 lam L :=
    fun _ h => live_of_horizon ha rfl h
  have hc : ContinuousOn (finalSensitivity a0 L) (Ioi (-(1 / (scale a0 L)^3))) :=
    fun lam h => (finalSensitivity_continuousAt hL (hl lam h)).continuousWithinAt
  have hd : ContinuousOn (deriv (finalGrowth a0 L)) (Ioi (-(1 / (scale a0 L)^3))) := by
    apply hc.congr
    intro lam h
    exact (finalGrowth_parameter_derivative hL (hl lam h)).deriv
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  exact ⟨fun lam h => (finalGrowth_parameter_derivative hL (hl lam h)).differentiableAt.differentiableWithinAt,
    by simp, contDiffOn_zero.mpr hd⟩

def endpointSensitivity (a0 L T : ℝ) : ℝ :=
  (finalSensitivity a0 L (endpoint a0 L T))⁻¹

/-- The local inverse and its continuity were constructed earlier; the nonzero derivative is now derived. -/
theorem endpoint_parameter_derivative {a0 L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hT : T ∈ Ioo (freeGrowth L) (Real.exp L)) :
    HasDerivAt (endpoint a0 L) (endpointSensitivity a0 L T) T := by
  have hs := endpoint_spec ha hL hT
  have hl := live_nonnegative (L := L) ha.le hs.1.le
  apply HasDerivAt.of_local_left_inverse (endpoint_continuousAt ha hL hT)
    (finalGrowth_parameter_derivative hL.le hl) (finalSensitivity_negative ha hL hl).ne
  filter_upwards [Ioo_mem_nhds hT.1 hT.2] with d hd
  exact (endpoint_spec ha hL hd).2

theorem endpointSensitivity_negative {a0 L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hT : T ∈ Ioo (freeGrowth L) (Real.exp L)) : endpointSensitivity a0 L T < 0 := by
  exact inv_lt_zero.mpr (finalSensitivity_negative ha hL
    (live_nonnegative ha.le (endpoint_spec ha hL hT).1.le))

theorem endpointSensitivity_continuousAt {a0 L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hT : T ∈ Ioo (freeGrowth L) (Real.exp L)) :
    ContinuousAt (endpointSensitivity a0 L) T := by
  have hl := live_nonnegative (L := L) ha.le (endpoint_spec ha hL hT).1.le
  exact (ContinuousAt.comp (f := endpoint a0 L) (x := T)
    (finalSensitivity_continuousAt hL.le hl) (endpoint_continuousAt ha hL hT)).inv₀
      (finalSensitivity_negative ha hL hl).ne

theorem endpoint_c1 {a0 L : ℝ} (ha : 0 < a0) (hL : 0 < L) :
    ContDiffOn ℝ 1 (endpoint a0 L) (Ioo (freeGrowth L) (Real.exp L)) := by
  have hc : ContinuousOn (endpointSensitivity a0 L) (Ioo (freeGrowth L) (Real.exp L)) :=
    fun _ h => (endpointSensitivity_continuousAt ha hL h).continuousWithinAt
  have hd : ContinuousOn (deriv (endpoint a0 L)) (Ioo (freeGrowth L) (Real.exp L)) := by
    apply hc.congr
    intro T hT
    exact (endpoint_parameter_derivative ha hL hT).deriv
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨fun _ h => (endpoint_parameter_derivative ha hL h).differentiableAt.differentiableWithinAt,
    by simp, contDiffOn_zero.mpr hd⟩

theorem scaled_endpoint_delta_derivative {d s : ℝ} (hs : 0 < s)
    (hT : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    HasDerivAt (fun u => scaledEndpoint u s)
      (endpointSensitivity (1 / 1000) (Real.log 20000) (scaledThreshold d s) *
        (WindowSample.aggregateThreshold / (WindowSample.delta * s))) d := by
  have ht : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT
  have hth : HasDerivAt (fun u => scaledThreshold u s)
      (WindowSample.aggregateThreshold / (WindowSample.delta * s)) d := by
    convert ((hasDerivAt_id d).div (hasDerivAt_const d (WindowSample.delta * s))
      (mul_ne_zero original_delta_positive.ne' hs.ne')).mul_const
      WindowSample.aggregateThreshold using 1
    simp only [id_eq]
    field_simp [original_delta_positive.ne', hs.ne']
    ring
  exact (endpoint_parameter_derivative (by norm_num : (0 : ℝ) < 1 / 1000)
    (Real.log_pos (by norm_num : (1 : ℝ) < 20000)) ht).comp d hth

theorem scaled_endpoint_amplitude_derivative {d s : ℝ} (hs : 0 < s)
    (hT : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    HasDerivAt (fun u => scaledEndpoint d u)
      (endpointSensitivity (1 / 1000) (Real.log 20000) (scaledThreshold d s) *
        (-d * WindowSample.aggregateThreshold / (WindowSample.delta * s^2))) s := by
  have ht : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT
  have hth : HasDerivAt (fun u => scaledThreshold d u)
      (-d * WindowSample.aggregateThreshold / (WindowSample.delta * s^2)) s := by
    convert ((hasDerivAt_const s d).div
      ((hasDerivAt_id s).const_mul WindowSample.delta)
        (mul_ne_zero original_delta_positive.ne' hs.ne')).mul_const
          WindowSample.aggregateThreshold using 1
    simp only [id_eq]
    field_simp [original_delta_positive.ne', hs.ne']
    ring
  exact (endpoint_parameter_derivative (by norm_num : (0 : ℝ) < 1 / 1000)
    (Real.log_pos (by norm_num : (1 : ℝ) < 20000)) ht).comp s hth

theorem scaled_endpoint_c1 {p : ℝ × ℝ} (hs : 0 < p.2)
    (hT : scaledThreshold p.1 p.2 ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => scaledEndpoint q.1 q.2) p := by
  have ht : scaledThreshold p.1 p.2 ∈ Ioo (freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT
  have hth : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => scaledThreshold q.1 q.2) p := by
    exact (contDiffAt_fst.div (contDiffAt_const.mul contDiffAt_snd)
      (mul_ne_zero original_delta_positive.ne' hs.ne')).mul contDiffAt_const
  exact ((endpoint_c1 (by norm_num : (0 : ℝ) < 1 / 1000)
    (Real.log_pos (by norm_num : (1 : ℝ) < 20000))).contDiffAt
      (Ioo_mem_nhds ht.1 ht.2)).comp p hth

theorem robustness_rectangle_c1 {d s : ℝ} (hd : d ∈ Icc (6 / 5) 2)
    (hs : s ∈ Icc (1 / 3) 3) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => scaledEndpoint q.1 q.2) (d, s) :=
  scaled_endpoint_c1 (by dsimp; linarith [hs.1]) (robustness_rectangle_admissible hd hs)

theorem scaled_endpoint_delta_derivative_negative {d s : ℝ} (hs : 0 < s)
    (hT : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    deriv (fun u => scaledEndpoint u s) d < 0 := by
  have ht : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT
  rw [(scaled_endpoint_delta_derivative hs hT).deriv]
  exact mul_neg_of_neg_of_pos
    (endpointSensitivity_negative (by norm_num : (0 : ℝ) < 1 / 1000)
      (Real.log_pos (by norm_num : (1 : ℝ) < 20000)) ht)
    (div_pos ((by norm_num : (0 : ℝ) < 900).trans original_aggregate_bounds.1)
      (mul_pos original_delta_positive hs))

theorem scaled_endpoint_amplitude_derivative_positive {d s : ℝ} (hd : 0 < d) (hs : 0 < s)
    (hT : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000)) 20000) :
    0 < deriv (fun u => scaledEndpoint d u) s := by
  have ht : scaledThreshold d s ∈ Ioo (freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 20000)] using hT
  rw [(scaled_endpoint_amplitude_derivative hs hT).deriv]
  exact mul_pos_of_neg_of_neg
    (endpointSensitivity_negative (by norm_num : (0 : ℝ) < 1 / 1000)
      (Real.log_pos (by norm_num : (1 : ℝ) < 20000)) ht)
    (div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hd)
        ((by norm_num : (0 : ℝ) < 900).trans original_aggregate_bounds.1))
      (mul_pos original_delta_positive (pow_pos hs 2)))

end
end SbtCosmo.Derivation.GrowthEndpointDerivative
