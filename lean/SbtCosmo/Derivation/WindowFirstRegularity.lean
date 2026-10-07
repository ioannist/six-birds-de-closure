import SbtCosmo.Derivation.GrowthFirstContinuity
import SbtCosmo.Derivation.GrowthEndpointDerivative
import SbtCosmo.Derivation.WindowRobustRatio
import SbtCosmo.Derivation.WindowPatchCountRatio

/-! Joint regularity returned to the original ANY-patch readouts. Strict first
threshold slack is earned from the actual record gate, including its endpoint. -/
namespace SbtCosmo.Derivation.WindowFirstRegularity
noncomputable section
open Set GrowthScaleReturn GrowthFirstContinuity WindowSensitivity WindowRobustRecord

theorem robust_strict_final {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    threshold d s j < nativeGrowth (1/1000) lam 20 := by
  have he := endpoint_spec hR
  have hw := (gate_iff_window hR lam).mp hg
  have hm := (native_endpoint_strictAntiOn (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num : (1/1000:ℝ) < 20)).antitoneOn (gate_cutoff hR hg)
    (show -(1/(20:ℝ)^3) < scaledEndpoint d s by linarith [he.1]) hw.2
  rw [he.2] at hm
  exact (threshold_below_aggregate hR j).trans_le hm

theorem robust_threshold_c1 {p : ℝ × ℝ} (hs : 0 < p.2) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => threshold q.1 q.2 j) p := by
  exact (contDiffAt_fst.div (contDiffAt_const.mul contDiffAt_snd)
    (mul_ne_zero original_delta_positive.ne' hs.ne')).mul contDiffAt_const

theorem robust_time_joint_continuousAt {p : (ℝ × ℝ) × ℝ}
    (hR : Rectangle p.1.1 p.1.2) (hg : gate p.1.1 p.1.2 p.2) (j : Fin 12) :
    ContinuousAt (fun q : (ℝ × ℝ) × ℝ => time q.1.1 q.1.2 j q.2) p := by
  have hth : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => threshold q.1.1 q.1.2 j) p :=
    (robust_threshold_c1 (rectangle_positive hR).2 j).continuousAt.comp continuousAt_fst
  exact (firstTime_joint_continuousAt (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
    (gate_cutoff hR hg) (by linarith [(threshold_bounds hR j).1])
    (robust_strict_final hR hg j)).comp (hth.prodMk continuousAt_snd)

theorem robust_ratio_joint_continuousAt {p : (ℝ × ℝ) × ℝ}
    (hR : Rectangle p.1.1 p.1.2) (hg : gate p.1.1 p.1.2 p.2) (j : Fin 12) :
    ContinuousAt (fun q : (ℝ × ℝ) × ℝ => WindowRobustRatio.ratio q.1.1 q.1.2 j q.2) p :=
  continuousAt_snd.abs.mul ((robust_time_joint_continuousAt hR hg j).pow 3)

/-- Full C1 in both coupled knobs at fixed signed lambda, including window endpoints. -/
theorem robust_time_knobs_c1 {p : ℝ × ℝ} {lam : ℝ}
    (hR : Rectangle p.1 p.2) (hg : gate p.1 p.2 lam) (j : Fin 12) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => time q.1 q.2 j lam) p := by
  have hT : threshold p.1 p.2 j ∈ Ioo 1 (nativeGrowth (1/1000) lam 20) :=
    ⟨by linarith [(threshold_bounds hR j).1],robust_strict_final hR hg j⟩
  exact ((firstTime_threshold_c1 (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
    (gate_cutoff hR hg)).contDiffAt (Ioo_mem_nhds hT.1 hT.2)).comp p
      (robust_threshold_c1 (rectangle_positive hR).2 j)

theorem robust_time_delta_derivative {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    HasDerivAt (fun u => time u s j lam)
      (WindowFirstRecord.threshold j/(WindowSample.delta*s) *
        (nativeDerivative (1/1000) lam (time d s j lam))⁻¹) d := by
  have hth : HasDerivAt (fun u => threshold u s j) (WindowFirstRecord.threshold j/(WindowSample.delta*s)) d := by
    convert ((hasDerivAt_id d).div_const (WindowSample.delta*s)).mul_const (WindowFirstRecord.threshold j) using 1
    ring
  have h := (firstTime_threshold_derivative (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
    (gate_cutoff hR hg) (by linarith [(threshold_bounds hR j).1])
    (robust_strict_final hR hg j)).comp d hth
  convert h using 1
  simp only [time,mul_comm]

theorem robust_time_delta_derivative_positive {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    0 < deriv (fun u => time u s j lam) d := by
  rw [(robust_time_delta_derivative hR hg j).deriv]
  exact mul_pos (div_pos (by linarith [(WindowFirstRecord.threshold_bounds j).1])
    (mul_pos original_delta_positive (rectangle_positive hR).2))
    (inv_pos.mpr (native_positive (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
      (gate_cutoff hR hg) _ (time_spec hR hg j).1).2)

theorem robust_time_amplitude_derivative {d s lam : ℝ} (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    HasDerivAt (fun u => time d u j lam)
      (-(d*WindowSample.delta*WindowFirstRecord.threshold j)/(WindowSample.delta*s)^2 *
        (nativeDerivative (1/1000) lam (time d s j lam))⁻¹) s := by
  have hth : HasDerivAt (fun u => threshold d u j)
      (-(d*WindowSample.delta*WindowFirstRecord.threshold j)/(WindowSample.delta*s)^2) s := by
    convert (((hasDerivAt_const s d).div
      ((hasDerivAt_const s WindowSample.delta).mul (hasDerivAt_id s))
      (mul_pos original_delta_positive (rectangle_positive hR).2).ne').mul_const
        (WindowFirstRecord.threshold j)) using 1
    dsimp [threshold,factor]
    ring
  have h := (firstTime_threshold_derivative (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
    (gate_cutoff hR hg) (by linarith [(threshold_bounds hR j).1])
    (robust_strict_final hR hg j)).comp s hth
  convert h using 1
  simp only [time,mul_comm]

theorem robust_time_amplitude_derivative_negative {d s lam : ℝ}
    (hR : Rectangle d s) (hg : gate d s lam) (j : Fin 12) :
    deriv (fun u => time d u j lam) s < 0 := by
  rw [(robust_time_amplitude_derivative hR hg j).deriv]
  have hcoef : -(d*WindowSample.delta*WindowFirstRecord.threshold j)/(WindowSample.delta*s)^2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos
      (mul_pos (rectangle_positive hR).1 original_delta_positive)
      (by linarith [(WindowFirstRecord.threshold_bounds j).1])))
      (sq_pos_of_pos (mul_pos original_delta_positive (rectangle_positive hR).2))
  exact mul_neg_of_neg_of_pos hcoef
    (inv_pos.mpr (native_positive (by norm_num : (0:ℝ) < 1/1000) (by norm_num)
      (gate_cutoff hR hg) _ (time_spec hR hg j).1).2)

theorem robust_endpoint_time_continuousAt {p : ℝ × ℝ}
    (hR : Rectangle p.1 p.2) (j : Fin 12) :
    ContinuousAt (fun q : ℝ × ℝ => time q.1 q.2 j (scaledEndpoint q.1 q.2)) p := by
  have hu := (endpoint_spec hR).1
  have hg : gate p.1 p.2 (scaledEndpoint p.1 p.2) :=
    (gate_iff_window hR _).mpr ⟨by linarith,le_rfl⟩
  have hE : ContinuousAt (fun q : ℝ × ℝ => scaledEndpoint q.1 q.2) p :=
    (GrowthEndpointDerivative.robustness_rectangle_c1 hR.1 hR.2).continuousAt
  exact (robust_time_joint_continuousAt hR hg j).comp (continuousAt_id.prodMk hE)

theorem robust_endpoint_ratio_continuousAt {p : ℝ × ℝ}
    (hR : Rectangle p.1 p.2) (j : Fin 12) :
    ContinuousAt (fun q : ℝ × ℝ => WindowRobustRatio.ratio q.1 q.2 j (scaledEndpoint q.1 q.2)) p := by
  have hu := (endpoint_spec hR).1
  have hg : gate p.1 p.2 (scaledEndpoint p.1 p.2) :=
    (gate_iff_window hR _).mpr ⟨by linarith,le_rfl⟩
  have hE : ContinuousAt (fun q : ℝ × ℝ => scaledEndpoint q.1 q.2) p :=
    (GrowthEndpointDerivative.robustness_rectangle_c1 hR.1 hR.2).continuousAt
  exact (robust_ratio_joint_continuousAt hR hg j).comp (continuousAt_id.prodMk hE)

theorem original_time_continuousAt {lam : ℝ} (hg : WindowSample.realizedGate lam) (j : Fin 12) :
    ContinuousAt (WindowSignedRecord.time j) lam := by
  have hG := ((WindowSample.realized_gate_iff_threshold lam).mp hg).2
  have hs : WindowFirstRecord.threshold j < nativeGrowth (1/1000) lam 20 := by
    linarith [(WindowFirstRecord.threshold_bounds j).2,WindowEdgeCertified.sampled_threshold_tight_bounds.1]
  exact firstTime_parameter_continuousAt (by norm_num) (by norm_num) (WindowSignedRecord.gate_cutoff hg)
    (by linarith [(WindowFirstRecord.threshold_bounds j).1]) hs

theorem original_ratio_continuousAt {lam : ℝ} (hg : WindowSample.realizedGate lam) (j : Fin 12) :
    ContinuousAt (WindowSignedRecord.ratio j) lam :=
  continuousAt_id.abs.mul ((original_time_continuousAt hg j).pow 3)

theorem patch_strict_final {v : Bool} {lam : ℝ} (hg : WindowPatchCounts.realizedGate v lam) (j : Fin 12) :
    WindowPatchCountRatio.threshold v j < nativeGrowth (1/1000) lam 20 := by
  have hG := ((WindowPatchCounts.realized_gate_iff_threshold v lam).mp hg).2
  rw [WindowPatchCountRatio.aggregate_normalized v] at hG
  linarith [(WindowPatchCountRatio.threshold_bounds v j).2.2.2,(WindowPatchCountRatio.scale_bounds v).1]

theorem patch_time_continuousAt {v : Bool} {lam : ℝ} (hg : WindowPatchCounts.realizedGate v lam) (j : Fin 12) :
    ContinuousAt (WindowPatchCountRatio.time v j) lam :=
  firstTime_parameter_continuousAt (by norm_num) (by norm_num) (WindowPatchCountRatio.gate_cutoff hg)
    (WindowPatchCountRatio.threshold_bounds v j).1 (patch_strict_final hg j)

theorem patch_ratio_continuousAt {v : Bool} {lam : ℝ} (hg : WindowPatchCounts.realizedGate v lam) (j : Fin 12) :
    ContinuousAt (WindowPatchCountRatio.ratio v j) lam :=
  continuousAt_id.abs.mul ((patch_time_continuousAt hg j).pow 3)

end
end SbtCosmo.Derivation.WindowFirstRegularity
