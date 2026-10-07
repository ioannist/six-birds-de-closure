import SbtCosmo.Derivation.GrowthFirstDifferential
import SbtCosmo.Derivation.WindowFirstRegularity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Earned joint C1 and implicit signed sensitivity returned to the unchanged
original ANY-patch times and ratios, including positive aggregate endpoints. -/
namespace SbtCosmo.Derivation.WindowFirstDifferential
noncomputable section
open Set Filter GrowthScaleReturn GrowthParameter GrowthFirstDifferential WindowSensitivity
  WindowRobustRecord WindowFirstRegularity
open scoped Topology

theorem robust_time_joint_c1 {p : (ℝ × ℝ) × ℝ}
    (hR : Rectangle p.1.1 p.1.2) (hg : gate p.1.1 p.1.2 p.2) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : (ℝ × ℝ) × ℝ => time q.1.1 q.1.2 j q.2) p := by
  have ht : ContDiffAt ℝ 1 (fun q : (ℝ × ℝ) × ℝ => threshold q.1.1 q.1.2 j) p :=
    (robust_threshold_c1 (rectangle_positive hR).2 j).comp p contDiffAt_fst
  exact (firstTime_joint_contDiffAt (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
    (gate_cutoff hR hg) (by linarith [(threshold_bounds hR j).1])
    (robust_strict_final hR hg j)).comp p (ht.prodMk contDiffAt_snd)

theorem robust_time_parameter_derivative {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    HasDerivAt (time d s j)
      (-finalSensitivity (1/1000) (logScale (1/1000) (time d s j lam)) lam /
        nativeDerivative (1/1000) lam (time d s j lam)) lam :=
  firstTime_parameter_derivative (by norm_num) (by norm_num) (gate_cutoff hR hg)
    (by linarith [(threshold_bounds hR j).1]) (robust_strict_final hR hg j)

theorem robust_time_parameter_derivative_positive {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    0 < deriv (time d s j) lam :=
  firstTime_parameter_derivative_positive (by norm_num) (by norm_num) (gate_cutoff hR hg)
    (by linarith [(threshold_bounds hR j).1]) (robust_strict_final hR hg j)

theorem robust_ratio_joint_c1 {p : (ℝ × ℝ) × ℝ}
    (hR : Rectangle p.1.1 p.1.2) (hg : gate p.1.1 p.1.2 p.2) (hl : p.2 ≠ 0) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : (ℝ × ℝ) × ℝ => WindowRobustRatio.ratio q.1.1 q.1.2 j q.2) p :=
  (contDiffAt_snd.abs hl).mul ((robust_time_joint_c1 hR hg j).pow 3)

theorem robust_endpoint_time_c1 {p : ℝ × ℝ} (hR : Rectangle p.1 p.2) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => time q.1 q.2 j (scaledEndpoint q.1 q.2)) p := by
  have hu := (endpoint_spec hR).1
  have hg : gate p.1 p.2 (scaledEndpoint p.1 p.2) :=
    (gate_iff_window hR _).mpr ⟨by linarith,le_rfl⟩
  have hE := GrowthEndpointDerivative.robustness_rectangle_c1 hR.1 hR.2
  exact (robust_time_joint_c1 hR hg j).comp p (contDiffAt_id.prodMk hE)

theorem robust_endpoint_ratio_c1 {p : ℝ × ℝ} (hR : Rectangle p.1 p.2) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => WindowRobustRatio.ratio q.1 q.2 j (scaledEndpoint q.1 q.2)) p := by
  have hu := (endpoint_spec hR).1
  have hg : gate p.1 p.2 (scaledEndpoint p.1 p.2) :=
    (gate_iff_window hR _).mpr ⟨by linarith,le_rfl⟩
  have hE := GrowthEndpointDerivative.robustness_rectangle_c1 hR.1 hR.2
  exact (robust_ratio_joint_c1 hR hg hu.ne' j).comp p (contDiffAt_id.prodMk hE)

theorem original_time_c1 {lam : ℝ} (hg : WindowSample.realizedGate lam) (j : Fin 12) :
    ContDiffAt ℝ 1 (WindowSignedRecord.time j) lam := by
  have hG := ((WindowSample.realized_gate_iff_threshold lam).mp hg).2
  have hs : WindowFirstRecord.threshold j < nativeGrowth (1/1000) lam 20 := by
    linarith [(WindowFirstRecord.threshold_bounds j).2,WindowEdgeCertified.sampled_threshold_tight_bounds.1]
  exact (firstTime_joint_contDiffAt (p := (WindowFirstRecord.threshold j,lam))
    (by norm_num) (by norm_num) (WindowSignedRecord.gate_cutoff hg)
    (by linarith [(WindowFirstRecord.threshold_bounds j).1]) hs).comp lam
      (contDiffAt_const.prodMk contDiffAt_id)

theorem original_time_parameter_derivative {lam : ℝ} (hg : WindowSample.realizedGate lam) (j : Fin 12) :
    HasDerivAt (WindowSignedRecord.time j)
      (-finalSensitivity (1/1000) (logScale (1/1000) (WindowSignedRecord.time j lam)) lam /
        nativeDerivative (1/1000) lam (WindowSignedRecord.time j lam)) lam := by
  have hG := ((WindowSample.realized_gate_iff_threshold lam).mp hg).2
  have hs : WindowFirstRecord.threshold j < nativeGrowth (1/1000) lam 20 := by
    linarith [(WindowFirstRecord.threshold_bounds j).2,WindowEdgeCertified.sampled_threshold_tight_bounds.1]
  exact firstTime_parameter_derivative (by norm_num) (by norm_num) (WindowSignedRecord.gate_cutoff hg)
    (by linarith [(WindowFirstRecord.threshold_bounds j).1]) hs

theorem original_time_parameter_derivative_positive {lam : ℝ}
    (hg : WindowSample.realizedGate lam) (j : Fin 12) : 0 < deriv (WindowSignedRecord.time j) lam := by
  have hG := ((WindowSample.realized_gate_iff_threshold lam).mp hg).2
  have hs : WindowFirstRecord.threshold j < nativeGrowth (1/1000) lam 20 := by
    linarith [(WindowFirstRecord.threshold_bounds j).2,WindowEdgeCertified.sampled_threshold_tight_bounds.1]
  exact firstTime_parameter_derivative_positive (by norm_num) (by norm_num) (WindowSignedRecord.gate_cutoff hg)
    (by linarith [(WindowFirstRecord.threshold_bounds j).1]) hs

theorem original_ratio_c1 {lam : ℝ} (hg : WindowSample.realizedGate lam) (hl : lam ≠ 0) (j : Fin 12) :
    ContDiffAt ℝ 1 (WindowSignedRecord.ratio j) lam :=
  (contDiffAt_abs hl).mul ((original_time_c1 hg j).pow 3)

theorem patch_time_c1 {v : Bool} {lam : ℝ} (hg : WindowPatchCounts.realizedGate v lam) (j : Fin 12) :
    ContDiffAt ℝ 1 (WindowPatchCountRatio.time v j) lam :=
  (firstTime_joint_contDiffAt (by norm_num) (by norm_num) (WindowPatchCountRatio.gate_cutoff hg)
    (WindowPatchCountRatio.threshold_bounds v j).1 (patch_strict_final hg j)).comp lam
      (contDiffAt_const.prodMk contDiffAt_id)

theorem patch_time_parameter_derivative {v : Bool} {lam : ℝ}
    (hg : WindowPatchCounts.realizedGate v lam) (j : Fin 12) :
    HasDerivAt (WindowPatchCountRatio.time v j)
      (-finalSensitivity (1/1000) (logScale (1/1000) (WindowPatchCountRatio.time v j lam)) lam /
        nativeDerivative (1/1000) lam (WindowPatchCountRatio.time v j lam)) lam :=
  firstTime_parameter_derivative (by norm_num) (by norm_num) (WindowPatchCountRatio.gate_cutoff hg)
    (WindowPatchCountRatio.threshold_bounds v j).1 (patch_strict_final hg j)

theorem patch_time_parameter_derivative_positive {v : Bool} {lam : ℝ}
    (hg : WindowPatchCounts.realizedGate v lam) (j : Fin 12) :
    0 < deriv (WindowPatchCountRatio.time v j) lam :=
  firstTime_parameter_derivative_positive (by norm_num) (by norm_num) (WindowPatchCountRatio.gate_cutoff hg)
    (WindowPatchCountRatio.threshold_bounds v j).1 (patch_strict_final hg j)

theorem patch_ratio_c1 {v : Bool} {lam : ℝ} (hg : WindowPatchCounts.realizedGate v lam)
    (hl : lam ≠ 0) (j : Fin 12) : ContDiffAt ℝ 1 (WindowPatchCountRatio.ratio v j) lam :=
  (contDiffAt_abs hl).mul ((patch_time_c1 hg j).pow 3)

/-- A smooth positive first time does not remove the cusp introduced by abs(lambda). -/
theorem weighted_abs_not_differentiable {f : ℝ → ℝ}
    (hd : DifferentiableAt ℝ f 0) (hp : 0 < f 0) :
    ¬ DifferentiableAt ℝ (fun lam => |lam| * (f lam)^3) 0 := by
  intro hr
  have hq := hr.div (hd.pow 3) (pow_ne_zero 3 hp.ne')
  have hn : ∀ᶠ lam in 𝓝 (0:ℝ), f lam ≠ 0 :=
    hd.continuousAt.eventually_ne hp.ne'
  have habs : DifferentiableAt ℝ (fun lam : ℝ => |lam|) 0 := by
    apply hq.congr_of_eventuallyEq
    filter_upwards [hn] with lam hln
    simp [pow_ne_zero 3 hln]
  exact not_differentiableAt_abs_zero habs

theorem robust_ratio_not_differentiable_at_zero {d s : ℝ}
    (hR : Rectangle d s) (j : Fin 12) :
    ¬ DifferentiableAt ℝ (WindowRobustRatio.ratio d s j) 0 :=
  weighted_abs_not_differentiable (robust_time_parameter_derivative hR (gate_zero hR) j).differentiableAt
    (time_positive hR (gate_zero hR) j)

theorem original_ratio_not_differentiable_at_zero (j : Fin 12) :
    ¬ DifferentiableAt ℝ (WindowSignedRecord.ratio j) 0 :=
  weighted_abs_not_differentiable
    (original_time_parameter_derivative (WindowFirstRecord.gate_on_interval (by norm_num)) j).differentiableAt
    (WindowSignedRecord.time_positive (WindowFirstRecord.gate_on_interval (by norm_num)) j)

theorem patch_ratio_not_differentiable_at_zero (v : Bool) (j : Fin 12) :
    ¬ DifferentiableAt ℝ (WindowPatchCountRatio.ratio v j) 0 :=
  weighted_abs_not_differentiable
    (patch_time_parameter_derivative (WindowPatchCounts.zero_passes v) j).differentiableAt
    (WindowPatchCountRatio.time_positive (WindowPatchCounts.zero_passes v) j)

end
end SbtCosmo.Derivation.WindowFirstDifferential
