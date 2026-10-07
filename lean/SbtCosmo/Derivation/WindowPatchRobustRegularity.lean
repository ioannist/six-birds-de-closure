import SbtCosmo.Derivation.WindowPatchRobust
import SbtCosmo.Derivation.WindowFirstDifferential

/-! Earned C1 and exact sensitivities of the actual added populations' windows
and first times, on the entire original coupled rectangle. -/
namespace SbtCosmo.Derivation.WindowPatchRobustRegularity
noncomputable section
open Set GrowthScaleReturn GrowthParameter GrowthEndpointDerivative WindowRobustRecord WindowPatchRobust

theorem aggregate_c1 {p : ℝ × ℝ} (hs : 0 < p.2) (v : Bool) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => aggregate v q.1 q.2) p :=
  (contDiffAt_fst.div (contDiffAt_const.mul contDiffAt_snd)
    (mul_ne_zero WindowSensitivity.original_delta_positive.ne' hs.ne')).mul contDiffAt_const

theorem threshold_c1 {p : ℝ × ℝ} (hs : 0 < p.2) (v : Bool) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => threshold v q.1 q.2 j) p :=
  (contDiffAt_fst.div (contDiffAt_const.mul contDiffAt_snd)
    (mul_ne_zero WindowSensitivity.original_delta_positive.ne' hs.ne')).mul contDiffAt_const

theorem endpoint_c1 {p : ℝ × ℝ} (hR : Rectangle p.1 p.2) (v : Bool) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => upper v q.1 q.2) p := by
  have ht : aggregate v p.1 p.2 ∈ Ioo (GrowthLimit.freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 20000)] using aggregate_admissible hR v
  exact ((GrowthEndpointDerivative.endpoint_c1 (by norm_num : (0:ℝ) < 1/1000)
    (Real.log_pos (by norm_num : (1:ℝ) < 20000))).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).comp p
      (aggregate_c1 (rectangle_positive hR).2 v)

theorem endpoint_delta_derivative {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    HasDerivAt (fun u => upper v u s)
      (endpointSensitivity (1/1000) (Real.log 20000) (aggregate v d s) *
        (WindowPatchCounts.aggregateThreshold v/(WindowSample.delta*s))) d := by
  have ht : aggregate v d s ∈ Ioo (GrowthLimit.freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 20000)] using aggregate_admissible hR v
  have hth : HasDerivAt (fun u => aggregate v u s)
      (WindowPatchCounts.aggregateThreshold v/(WindowSample.delta*s)) d := by
    convert ((hasDerivAt_id d).div_const (WindowSample.delta*s)).mul_const
      (WindowPatchCounts.aggregateThreshold v) using 1
    ring
  exact (endpoint_parameter_derivative (by norm_num : (0:ℝ) < 1/1000)
    (Real.log_pos (by norm_num : (1:ℝ) < 20000)) ht).comp d hth

theorem endpoint_delta_derivative_negative {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    deriv (fun u => upper v u s) d < 0 := by
  have ht : aggregate v d s ∈ Ioo (GrowthLimit.freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 20000)] using aggregate_admissible hR v
  rw [(endpoint_delta_derivative hR v).deriv]
  exact mul_neg_of_neg_of_pos (endpointSensitivity_negative (by norm_num : (0:ℝ) < 1/1000)
    (Real.log_pos (by norm_num : (1:ℝ) < 20000)) ht)
    (div_pos (by linarith [(WindowPatchCounts.sampled_threshold_bounds v).1])
      (mul_pos WindowSensitivity.original_delta_positive (rectangle_positive hR).2))

theorem endpoint_amplitude_derivative {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    HasDerivAt (fun u => upper v d u)
      (endpointSensitivity (1/1000) (Real.log 20000) (aggregate v d s) *
        (-d*WindowPatchCounts.aggregateThreshold v/(WindowSample.delta*s^2))) s := by
  have ht : aggregate v d s ∈ Ioo (GrowthLimit.freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 20000)] using aggregate_admissible hR v
  have hth : HasDerivAt (fun u => aggregate v d u)
      (-d*WindowPatchCounts.aggregateThreshold v/(WindowSample.delta*s^2)) s := by
    convert (((hasDerivAt_const s d).div ((hasDerivAt_id s).const_mul WindowSample.delta)
      (mul_pos WindowSensitivity.original_delta_positive (rectangle_positive hR).2).ne').mul_const
        (WindowPatchCounts.aggregateThreshold v)) using 1
    dsimp [aggregate,factor]
    field_simp [WindowSensitivity.original_delta_positive.ne',(rectangle_positive hR).2.ne']
    ring
  exact (endpoint_parameter_derivative (by norm_num : (0:ℝ) < 1/1000)
    (Real.log_pos (by norm_num : (1:ℝ) < 20000)) ht).comp s hth

theorem endpoint_amplitude_derivative_positive {d s : ℝ} (hR : Rectangle d s) (v : Bool) :
    0 < deriv (fun u => upper v d u) s := by
  have ht : aggregate v d s ∈ Ioo (GrowthLimit.freeGrowth (Real.log 20000))
      (Real.exp (Real.log 20000)) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 20000)] using aggregate_admissible hR v
  rw [(endpoint_amplitude_derivative hR v).deriv]
  exact mul_pos_of_neg_of_neg (endpointSensitivity_negative (by norm_num : (0:ℝ) < 1/1000)
    (Real.log_pos (by norm_num : (1:ℝ) < 20000)) ht)
    (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (rectangle_positive hR).1)
      (by linarith [(WindowPatchCounts.sampled_threshold_bounds v).1]))
      (mul_pos WindowSensitivity.original_delta_positive (sq_pos_of_pos (rectangle_positive hR).2)))

theorem time_joint_c1 {p : (ℝ × ℝ) × ℝ} (v : Bool)
    (hR : Rectangle p.1.1 p.1.2) (hg : gate v p.1.1 p.1.2 p.2) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : (ℝ × ℝ) × ℝ => time v q.1.1 q.1.2 j q.2) p := by
  have ht : ContDiffAt ℝ 1 (fun q : (ℝ × ℝ) × ℝ => threshold v q.1.1 q.1.2 j) p :=
    (threshold_c1 (rectangle_positive hR).2 v j).comp p contDiffAt_fst
  exact (GrowthFirstDifferential.firstTime_joint_contDiffAt (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) (gate_cutoff hR hg) (threshold_interior_bounds hR v j).1
    (strict_final hR hg j)).comp p (ht.prodMk contDiffAt_snd)

theorem time_parameter_derivative {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) :
    HasDerivAt (time v d s j)
      (-finalSensitivity (1/1000) (logScale (1/1000) (time v d s j lam)) lam /
        nativeDerivative (1/1000) lam (time v d s j lam)) lam :=
  GrowthFirstDifferential.firstTime_parameter_derivative (by norm_num) (by norm_num) (gate_cutoff hR hg)
    (threshold_interior_bounds hR v j).1 (strict_final hR hg j)

theorem time_parameter_derivative_positive {v : Bool} {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate v d s lam) (j : Fin 12) :
    0 < deriv (time v d s j) lam :=
  GrowthFirstDifferential.firstTime_parameter_derivative_positive (by norm_num) (by norm_num) (gate_cutoff hR hg)
    (threshold_interior_bounds hR v j).1 (strict_final hR hg j)

theorem ratio_joint_c1 {p : (ℝ × ℝ) × ℝ} (v : Bool)
    (hR : Rectangle p.1.1 p.1.2) (hg : gate v p.1.1 p.1.2 p.2) (hl : p.2 ≠ 0) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : (ℝ × ℝ) × ℝ => ratio v q.1.1 q.1.2 j q.2) p :=
  (contDiffAt_snd.abs hl).mul ((time_joint_c1 v hR hg j).pow 3)

theorem ratio_joint_continuousAt {p : (ℝ × ℝ) × ℝ} (v : Bool)
    (hR : Rectangle p.1.1 p.1.2) (hg : gate v p.1.1 p.1.2 p.2) (j : Fin 12) :
    ContinuousAt (fun q : (ℝ × ℝ) × ℝ => ratio v q.1.1 q.1.2 j q.2) p :=
  continuousAt_snd.abs.mul (((time_joint_c1 v hR hg j).continuousAt).pow 3)

theorem endpoint_time_c1 {p : ℝ × ℝ} (hR : Rectangle p.1 p.2) (v : Bool) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => time v q.1 q.2 j (upper v q.1 q.2)) p := by
  have hg : gate v p.1 p.2 (upper v p.1 p.2) :=
    (gate_iff_window hR v _).mpr ⟨by linarith [(endpoint_spec hR v).1],le_rfl⟩
  exact (time_joint_c1 v hR hg j).comp p (contDiffAt_id.prodMk (endpoint_c1 hR v))

theorem endpoint_ratio_c1 {p : ℝ × ℝ} (hR : Rectangle p.1 p.2) (v : Bool) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => ratio v q.1 q.2 j (upper v q.1 q.2)) p := by
  have hu := (endpoint_spec hR v).1
  have hg : gate v p.1 p.2 (upper v p.1 p.2) :=
    (gate_iff_window hR v _).mpr ⟨by linarith [hu],le_rfl⟩
  exact (ratio_joint_c1 v hR hg hu.ne' j).comp p (contDiffAt_id.prodMk (endpoint_c1 hR v))

theorem ratio_not_differentiable_at_zero {d s : ℝ} (hR : Rectangle d s) (v : Bool) (j : Fin 12) :
    ¬ DifferentiableAt ℝ (ratio v d s j) 0 :=
  WindowFirstDifferential.weighted_abs_not_differentiable
    (time_parameter_derivative hR (gate_zero hR v) j).differentiableAt (time_positive hR (gate_zero hR v) j)

end
end SbtCosmo.Derivation.WindowPatchRobustRegularity
