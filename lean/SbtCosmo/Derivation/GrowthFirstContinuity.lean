import SbtCosmo.Derivation.GrowthFirstRecordLive
import SbtCosmo.Derivation.GrowthParameter
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Joint continuity of the actual signed first-threshold selector, including
relative continuity at horizon equality. Ambient regularity needs strict margin. -/
namespace SbtCosmo.Derivation.GrowthFirstContinuity
noncomputable section
open Set Filter GrowthScaleReturn GrowthFirstRecordLive
open scoped Topology

def Domain (a0 A : ℝ) : Set (ℝ × ℝ) :=
  {p | -(1/A^3) < p.2 ∧ 1 < p.1 ∧ p.1 ≤ nativeGrowth a0 p.2 A}

theorem firstTime_eq_of_root {a0 A T lam a : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) (hT : 1 < T) (hf : T ≤ nativeGrowth a0 lam A)
    (ha : a ∈ Icc a0 A) (he : nativeGrowth a0 lam a = T) :
    firstTime a0 A T lam = a := by
  have hs := firstTime_spec ha0 hA hl hT hf
  exact (GrowthFirstRecord.native_strictMonoOn ha0 hA hl).injOn hs.1 ha (hs.2.trans he.symm)

theorem firstTime_interior {a0 A T lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) (hT : 1 < T) (hf : T < nativeGrowth a0 lam A) :
    firstTime a0 A T lam ∈ Ioo a0 A := by
  have hs := firstTime_spec ha0 hA hl hT hf.le
  have hm := GrowthFirstRecord.native_strictMonoOn ha0 hA hl
  constructor
  · apply (hm.lt_iff_lt ⟨le_rfl,hA⟩ hs.1).mp
    rw [native_initial ha0 hA hl,hs.2]
    exact hT
  · apply (hm.lt_iff_lt hs.1 ⟨hA,le_rfl⟩).mp
    rwa [hs.2]

/-- Actual admissibility, not assumed selector continuity, supplies nearby roots. -/
theorem domain_mem_nhds {a0 A : ℝ} {p : ℝ × ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < p.2) (hT : 1 < p.1) (hf : p.1 < nativeGrowth a0 p.2 A) :
    Domain a0 A ∈ 𝓝 p := by
  have hG : ContinuousAt (fun q : ℝ × ℝ => nativeGrowth a0 q.2 A) p :=
    (GrowthParameter.native_parameter_derivative ha0 hA hl ⟨hA,le_rfl⟩).continuousAt.comp continuousAt_snd
  have hcut : ∀ᶠ q : ℝ × ℝ in 𝓝 p, -(1/A^3) < q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hl
  have hinit : ∀ᶠ q : ℝ × ℝ in 𝓝 p, 1 < q.1 :=
    continuousAt_const.eventually_lt continuousAt_fst hT
  have hfinal := continuousAt_fst.eventually_lt hG hf
  filter_upwards [hcut,hinit,hfinal] with q hq1 hq2 hq3
  exact ⟨hq1,hq2,hq3.le⟩

/-- Joint relative continuity on the entire actual domain, even at T=G_lambda(A). -/
theorem firstTime_joint_continuousOn {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A) :
    ContinuousOn (fun p : ℝ × ℝ => firstTime a0 A p.1 p.2) (Domain a0 A) := by
  intro p hp
  have hs := firstTime_spec ha0 hA hp.1 hp.2.1 hp.2.2
  have hvalid : ∀ᶠ q in 𝓝[Domain a0 A] p, q ∈ Domain a0 A := self_mem_nhdsWithin
  apply tendsto_order.mpr
  constructor
  · intro b hb
    by_cases hba : b < a0
    · filter_upwards [hvalid] with q hq
      exact hba.trans_le (firstTime_spec ha0 hA hq.1 hq.2.1 hq.2.2).1.1
    · have hbi : b ∈ Icc a0 A := ⟨le_of_not_gt hba,hb.le.trans hs.1.2⟩
      have hGb : nativeGrowth a0 p.2 b < p.1 := by
        have h := GrowthFirstRecord.native_strictMonoOn ha0 hA hp.1 hbi hs.1 hb
        rwa [hs.2] at h
      have hGc : ContinuousAt (fun q : ℝ × ℝ => nativeGrowth a0 q.2 b) p :=
        (GrowthParameter.native_parameter_derivative ha0 hA hp.1 hbi).continuousAt.comp continuousAt_snd
      have hcmp : ∀ᶠ q in 𝓝[Domain a0 A] p, nativeGrowth a0 q.2 b < q.1 :=
        (hGc.eventually_lt continuousAt_fst hGb).filter_mono nhdsWithin_le_nhds
      filter_upwards [hvalid,hcmp] with q hq hqb
      have hsq := firstTime_spec ha0 hA hq.1 hq.2.1 hq.2.2
      apply (GrowthFirstRecord.native_strictMonoOn ha0 hA hq.1).lt_iff_lt hbi hsq.1 |>.mp
      rwa [hsq.2]
  · intro b hb
    by_cases hAb : A < b
    · filter_upwards [hvalid] with q hq
      exact (firstTime_spec ha0 hA hq.1 hq.2.1 hq.2.2).1.2.trans_lt hAb
    · have hbi : b ∈ Icc a0 A := ⟨hs.1.1.trans hb.le,le_of_not_gt hAb⟩
      have hGb : p.1 < nativeGrowth a0 p.2 b := by
        have h := GrowthFirstRecord.native_strictMonoOn ha0 hA hp.1 hs.1 hbi hb
        rwa [hs.2] at h
      have hGc : ContinuousAt (fun q : ℝ × ℝ => nativeGrowth a0 q.2 b) p :=
        (GrowthParameter.native_parameter_derivative ha0 hA hp.1 hbi).continuousAt.comp continuousAt_snd
      have hcmp : ∀ᶠ q in 𝓝[Domain a0 A] p, q.1 < nativeGrowth a0 q.2 b :=
        (continuousAt_fst.eventually_lt hGc hGb).filter_mono nhdsWithin_le_nhds
      filter_upwards [hvalid,hcmp] with q hq hqb
      have hsq := firstTime_spec ha0 hA hq.1 hq.2.1 hq.2.2
      apply (GrowthFirstRecord.native_strictMonoOn ha0 hA hq.1).lt_iff_lt hsq.1 hbi |>.mp
      rwa [hsq.2]

/-- Strict horizon slack earns full ambient joint continuity of the unchanged selector. -/
theorem firstTime_joint_continuousAt {a0 A : ℝ} {p : ℝ × ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < p.2) (hT : 1 < p.1) (hf : p.1 < nativeGrowth a0 p.2 A) :
    ContinuousAt (fun q : ℝ × ℝ => firstTime a0 A q.1 q.2) p :=
  (firstTime_joint_continuousOn ha0 hA p ⟨hl,hT,hf.le⟩).continuousAt
    (domain_mem_nhds ha0 hA hl hT hf)

theorem firstTime_threshold_continuousAt {a0 A T lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) (hT : 1 < T) (hf : T < nativeGrowth a0 lam A) :
    ContinuousAt (fun d => firstTime a0 A d lam) T :=
  (firstTime_joint_continuousAt ha0 hA hl hT hf).comp (continuousAt_id.prodMk continuousAt_const)

theorem firstTime_parameter_continuousAt {a0 A T lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) (hT : 1 < T) (hf : T < nativeGrowth a0 lam A) :
    ContinuousAt (firstTime a0 A T) lam :=
  (firstTime_joint_continuousAt ha0 hA hl hT hf).comp (continuousAt_const.prodMk continuousAt_id)

/-- The threshold derivative is earned through a local inverse of actual native growth. -/
theorem firstTime_threshold_derivative {a0 A T lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) (hT : 1 < T) (hf : T < nativeGrowth a0 lam A) :
    HasDerivAt (fun d => firstTime a0 A d lam)
      (nativeDerivative a0 lam (firstTime a0 A T lam))⁻¹ T := by
  have hs := firstTime_spec ha0 hA hl hT hf.le
  have hD := native_growth_derivative ha0 hA hl hs.1
  have hp := (native_positive ha0 hA hl _ hs.1).2
  apply HasDerivAt.of_local_left_inverse (firstTime_threshold_continuousAt ha0 hA hl hT hf)
    hD hp.ne'
  filter_upwards [Ioo_mem_nhds hT hf] with d hd
  exact (firstTime_spec ha0 hA hl hd.1 hd.2.le).2

theorem firstTime_threshold_derivative_positive {a0 A T lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) (hT : 1 < T) (hf : T < nativeGrowth a0 lam A) :
    0 < deriv (fun d => firstTime a0 A d lam) T := by
  rw [(firstTime_threshold_derivative ha0 hA hl hT hf).deriv]
  exact inv_pos.mpr (native_positive ha0 hA hl _ (firstTime_spec ha0 hA hl hT hf.le).1).2

theorem firstTime_threshold_sensitivity_continuousAt {a0 A T lam : ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < lam) (hT : 1 < T)
    (hf : T < nativeGrowth a0 lam A) :
    ContinuousAt (fun d => (nativeDerivative a0 lam (firstTime a0 A d lam))⁻¹) T := by
  have hs := firstTime_spec ha0 hA hl hT hf.le
  have hvel := (native_velocity_derivative ha0 hA hl hs.1).continuousAt
  exact (ContinuousAt.comp (f := fun d => firstTime a0 A d lam) (x := T) hvel
    (firstTime_threshold_continuousAt ha0 hA hl hT hf)).inv₀
      (native_positive ha0 hA hl _ hs.1).2.ne'

theorem firstTime_threshold_c1 {a0 A lam : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hl : -(1/A^3) < lam) :
    ContDiffOn ℝ 1 (fun d => firstTime a0 A d lam) (Ioo 1 (nativeGrowth a0 lam A)) := by
  have hc : ContinuousOn (fun d => (nativeDerivative a0 lam (firstTime a0 A d lam))⁻¹)
      (Ioo 1 (nativeGrowth a0 lam A)) :=
    fun _ h => (firstTime_threshold_sensitivity_continuousAt ha0 hA hl h.1 h.2).continuousWithinAt
  have hd : ContinuousOn (deriv (fun d => firstTime a0 A d lam))
      (Ioo 1 (nativeGrowth a0 lam A)) := by
    apply hc.congr
    intro d hd
    exact (firstTime_threshold_derivative ha0 hA hl hd.1 hd.2).deriv
  rw [show (1 : WithTop ℕ∞) = 0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨fun _ h => (firstTime_threshold_derivative ha0 hA hl h.1 h.2).differentiableAt.differentiableWithinAt,
    by simp,contDiffOn_zero.mpr hd⟩

/-- The out-of-domain fallback cannot justify ambient continuity at horizon equality. -/
theorem horizon_equality_not_continuous {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 < A) :
    ¬ ContinuousAt (fun d => firstTime a0 A d 0) (A/a0) := by
  have hT : 1 < A/a0 := (lt_div_iff₀ ha0).mpr (by simpa using hA)
  have hl : -(1/A^3) < (0:ℝ) := neg_neg_of_pos (div_pos (by norm_num) (pow_pos (ha0.trans hA) 3))
  have hG := native_matter_at_zero ha0 hA.le
  have hs : firstTime a0 A (A/a0) 0 = A :=
    firstTime_eq_of_root ha0 hA.le hl hT hG.symm.le ⟨hA.le,le_rfl⟩ hG
  intro hc
  have he : ∀ᶠ d in 𝓝[>] (A/a0), firstTime a0 A d 0 = a0 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hn : ¬ (0 < a0 ∧ a0 ≤ A ∧ -(1/A^3) < (0:ℝ) ∧ 1 < d ∧ d ≤ nativeGrowth a0 0 A) := by
      rw [hG]
      intro hh
      exact hd.not_ge hh.2.2.2.2
    simp only [firstTime,dif_neg hn]
  have hconst : Tendsto (fun d => firstTime a0 A d 0) (𝓝[>] (A/a0)) (𝓝 a0) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  have hlimit : Tendsto (fun d => firstTime a0 A d 0) (𝓝[>] (A/a0))
      (𝓝 (firstTime a0 A (A/a0) 0)) := hc.continuousWithinAt.tendsto
  rw [hs] at hlimit
  have heq : a0 = A := tendsto_nhds_unique hconst hlimit
  exact hA.ne heq

end
end SbtCosmo.Derivation.GrowthFirstContinuity
