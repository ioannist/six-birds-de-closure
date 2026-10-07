import SbtCosmo.Derivation.GrowthFirstContinuity
import SbtCosmo.Derivation.GrowthPopulationSensitivity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Stability of the actual first-ANY-patch root under arbitrary continuous
finite amplitude changes. Maximizing-patch ties are permitted. -/
namespace SbtCosmo.Derivation.FirstPopulationContinuity
noncomputable section
open scoped Topology
open Set Filter GrowthScaleReturn GrowthFirstContinuity GrowthPopulationSensitivity

def maximum {ι : Type*} [Fintype ι] (amplitude : ι → ℝ) : ℝ :=
  tagMaximumValue amplitude (fun _ => false) false

def threshold {ι : Type*} [Fintype ι] (amplitude : ι → ℝ) (delta : ℝ) : ℝ :=
  delta / maximum amplitude

def time {ι : Type*} [Fintype ι] (a0 A : ℝ) (amplitude : ι → ℝ) (delta lam : ℝ) : ℝ :=
  GrowthFirstRecordLive.firstTime a0 A (threshold amplitude delta) lam

theorem maximum_spec {ι : Type*} [Fintype ι] [Nonempty ι] (amplitude : ι → ℝ) :
    (∀ i, amplitude i ≤ maximum amplitude) ∧ ∃ i, amplitude i = maximum amplitude := by
  have ht : (tagSet (fun _ : ι => false) false).Nonempty :=
    ⟨Classical.arbitrary ι,by simp [tagSet]⟩
  have hs := tagMaximumValue_spec amplitude ht
  obtain ⟨i,_,he⟩ := hs.attained
  exact ⟨fun i => hs.bounds i rfl,i,he⟩

theorem maximum_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith 1 (maximum : (ι → ℝ) → ℝ) := tagMaximumValue_lipschitz (fun _ => false) false

theorem maximum_eq_of_attained {ι : Type*} [Fintype ι] [Nonempty ι]
    {amplitude : ι → ℝ} {m : ℝ} (hb : ∀ i, amplitude i ≤ m) (he : ∃ i, amplitude i = m) :
    maximum amplitude = m := by
  obtain ⟨i,hi⟩ := he
  obtain ⟨hbound,j,hj⟩ := maximum_spec amplitude
  exact le_antisymm (hj ▸ hb j) (hi ▸ hbound i)

theorem threshold_continuousAt {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    {amplitude : α → ι → ℝ} {delta : α → ℝ} {p : α}
    (ha : ∀ i, ContinuousAt (fun q => amplitude q i) p) (hd : ContinuousAt delta p)
    (hm : maximum (amplitude p) ≠ 0) :
    ContinuousAt (fun q => threshold (amplitude q) (delta q)) p :=
  hd.div ((maximum_lipschitz.continuous.continuousAt).comp (continuousAt_pi.mpr ha)) hm

theorem time_continuousAt {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    {amplitude : α → ι → ℝ} {delta lam : α → ℝ} {p : α} {a0 A : ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A)
    (ha : ∀ i, ContinuousAt (fun q => amplitude q i) p) (hd : ContinuousAt delta p)
    (hlc : ContinuousAt lam p) (hm : 0 < maximum (amplitude p))
    (hl : -(1/A^3) < lam p) (hT : 1 < threshold (amplitude p) (delta p))
    (hf : threshold (amplitude p) (delta p) < nativeGrowth a0 (lam p) A) :
    ContinuousAt (fun q => time a0 A (amplitude q) (delta q) (lam q)) p :=
  (firstTime_joint_continuousAt ha0 hA hl hT hf).comp
    ((threshold_continuousAt ha hd hm.ne').prodMk hlc)

/-- This returned root is exactly the first collapse of ANY actual patch. -/
theorem time_iff_any_collapse {ι : Type*} [Fintype ι] [Nonempty ι]
    {a0 A delta lam a : ℝ} {amplitude : ι → ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A)
    (hm : 0 < maximum amplitude) (hl : -(1/A^3) < lam)
    (hT : 1 < threshold amplitude delta) (hf : threshold amplitude delta ≤ nativeGrowth a0 lam A)
    (ha : a ∈ Icc a0 A) :
    (∃ i, delta ≤ amplitude i*nativeGrowth a0 lam a) ↔ time a0 A amplitude delta lam ≤ a := by
  have hD := (native_positive ha0 hA hl a ha).1.le
  have hs := maximum_spec amplitude
  exact (GrowthFirstRecord.any_patch_collapse_iff hm hD hs.1 hs.2).trans
    (GrowthFirstRecordLive.firstTime_iff_threshold ha0 hA hl hT hf ha)

/-- A real maximizing-patch switch prevents a universal smooth-maximum claim. -/
theorem tied_maximum : (fun t : ℝ => maximum (fun b : Bool => if b then 1+t else 1-t)) =
    (fun t => 1+|t|) := by
  funext t
  apply maximum_eq_of_attained
  · intro b
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true]
    · linarith [neg_le_abs t]
    · linarith [le_abs_self t]
  · by_cases ht : 0 ≤ t
    · exact ⟨true,by simp [abs_of_nonneg ht]⟩
    · exact ⟨false,by simp [abs_of_neg (lt_of_not_ge ht),sub_eq_add_neg]⟩

theorem tied_maximum_not_differentiable :
    ¬ DifferentiableAt ℝ (fun t : ℝ => maximum (fun b : Bool => if b then 1+t else 1-t)) 0 := by
  rw [tied_maximum]
  intro h
  have ha : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    convert h.sub (differentiableAt_const (c := (1:ℝ))) using 1
    funext t
    change |t| = (1+|t|)-1
    ring
  exact not_differentiableAt_abs_zero ha

/-- The same maximizing-patch tie produces an actual nonsmooth first time. -/
theorem tied_time_eq {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    time (1/1000) 20 (fun b : Bool => if b then 1+t else 1-t) 500 0 =
      (1/2)/(1+|t|) := by
  have hm : maximum (fun b : Bool => if b then 1+t else 1-t) = 1+|t| :=
    congrFun tied_maximum t
  have hp : 0 < 1+|t| := by positivity
  have hlt : |t| < 1 := abs_lt.mpr ht
  have hT : 1 < threshold (fun b : Bool => if b then 1+t else 1-t) 500 := by
    unfold threshold
    rw [hm]
    apply (lt_div_iff₀ hp).mpr
    linarith
  have hf : threshold (fun b : Bool => if b then 1+t else 1-t) 500 ≤ nativeGrowth (1/1000) 0 20 := by
    rw [GrowthFirstRecordLive.native_matter_at_zero (by norm_num : (0:ℝ) < 1/1000) (by norm_num)]
    unfold threshold
    rw [hm]
    apply (div_le_iff₀ hp).mpr
    nlinarith [abs_nonneg t]
  rw [time,GrowthFirstRecordLive.firstTime_at_zero (by norm_num : (0:ℝ) < 1/1000)
    (by norm_num) hT hf]
  unfold threshold
  rw [hm]
  ring

theorem tied_time_not_differentiable :
    ¬ DifferentiableAt ℝ
      (fun t : ℝ => time (1/1000) 20 (fun b : Bool => if b then 1+t else 1-t) 500 0) 0 := by
  intro h
  have ht0 : time (1/1000) 20 (fun b : Bool => if b then 1+(0:ℝ) else 1-0) 500 0 = 1/2 := by
    rw [tied_time_eq (by norm_num : (0:ℝ) ∈ Ioo (-1) 1)]
    norm_num
  have hquot := (differentiableAt_const (c := (1/2:ℝ))).div h (by rw [ht0]; norm_num)
  have he : (fun t : ℝ => maximum (fun b : Bool => if b then 1+t else 1-t)) =ᶠ[𝓝 0]
      (fun t => (1/2)/time (1/1000) 20 (fun b : Bool => if b then 1+t else 1-t) 500 0) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)] with t ht
    rw [tied_time_eq ht,congrFun tied_maximum t]
    have hp : 1+|t| ≠ 0 := (by positivity : (0:ℝ) < 1+|t|).ne'
    field_simp
  exact tied_maximum_not_differentiable (hquot.congr_of_eventuallyEq he)

end
end SbtCosmo.Derivation.FirstPopulationContinuity
