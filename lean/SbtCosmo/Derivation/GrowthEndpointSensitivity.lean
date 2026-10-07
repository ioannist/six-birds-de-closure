import SbtCosmo.Derivation.GrowthWindow

/-! Constructed positive endpoints vary continuously and strictly decrease with threshold. -/
namespace SbtCosmo.Derivation.GrowthEndpointSensitivity
noncomputable section
open Set Filter GrowthComparison GrowthExistence GrowthLimit GrowthWindow
open scoped Topology
attribute [local instance] Classical.propDecidable

def endpoint (a0 L T : ℝ) : ℝ :=
  if h : 0 < a0 ∧ 0 < L ∧ freeGrowth L < T ∧ T < Real.exp L then
    (exists_unique_positive_endpoint h.1 h.2.1 h.2.2.1 h.2.2.2).choose
  else 0

theorem endpoint_spec {a0 L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hT : T ∈ Ioo (freeGrowth L) (Real.exp L)) :
    0 < endpoint a0 L T ∧ finalGrowth a0 L (endpoint a0 L T) = T := by
  have hv : 0 < a0 ∧ 0 < L ∧ freeGrowth L < T ∧ T < Real.exp L :=
    ⟨ha, hL, hT.1, hT.2⟩
  simp only [endpoint, dif_pos hv]
  exact (exists_unique_positive_endpoint ha hL hT.1 hT.2).choose_spec.1

theorem endpoint_eq_of_root {a0 L T lam : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hT : T ∈ Ioo (freeGrowth L) (Real.exp L)) (hlam : 0 < lam)
    (he : finalGrowth a0 L lam = T) : endpoint a0 L T = lam := by
  have hs := endpoint_spec ha hL hT
  exact (((finalGrowth_strictAntiOn ha hL).eq_iff_eq
    (live_nonnegative ha.le hs.1.le) (live_nonnegative ha.le hlam.le)).mp
      (hs.2.trans he.symm)).symm

theorem endpoint_strictAntiOn {a0 L : ℝ} (ha : 0 < a0) (hL : 0 < L) :
    StrictAntiOn (endpoint a0 L) (Ioo (freeGrowth L) (Real.exp L)) := by
  intro T1 h1 T2 h2 h12
  have hs1 := endpoint_spec ha hL h1
  have hs2 := endpoint_spec ha hL h2
  exact ((finalGrowth_strictAntiOn ha hL).lt_iff_gt
    (live_nonnegative ha.le hs1.1.le) (live_nonnegative ha.le hs2.1.le)).mp
      (by simpa only [hs1.2, hs2.2] using h12)

/-- Full continuity at each admissible threshold, not merely continuity within a chosen branch. -/
theorem endpoint_continuousAt {a0 L T : ℝ} (ha : 0 < a0) (hL : 0 < L)
    (hT : T ∈ Ioo (freeGrowth L) (Real.exp L)) : ContinuousAt (endpoint a0 L) T := by
  have hs := endpoint_spec ha hL hT
  have hvalid : ∀ᶠ d in 𝓝 T, d ∈ Ioo (freeGrowth L) (Real.exp L) :=
    Ioo_mem_nhds hT.1 hT.2
  have hg := finalGrowth_strictAntiOn ha hL
  apply tendsto_order.mpr
  constructor
  · intro a haE
    by_cases han : a < 0
    · filter_upwards [hvalid] with d hd
      exact han.trans (endpoint_spec ha hL hd).1
    · have hal : Live a0 a L := live_nonnegative ha.le (le_of_not_gt han)
      have hGa : T < finalGrowth a0 L a := by
        simpa only [hs.2] using hg hal (live_nonnegative ha.le hs.1.le) haE
      filter_upwards [hvalid, Iio_mem_nhds hGa] with d hd hda
      have hsd := endpoint_spec ha hL hd
      exact (hg.lt_iff_gt (live_nonnegative ha.le hsd.1.le) hal).mp
        (by simpa only [hsd.2] using hda)
  · intro b hEb
    have hb : 0 < b := hs.1.trans hEb
    have hGb : finalGrowth a0 L b < T := by
      simpa only [hs.2] using hg (live_nonnegative ha.le hs.1.le)
        (live_nonnegative ha.le hb.le) hEb
    filter_upwards [hvalid, Ioi_mem_nhds hGb] with d hd hbd
    have hsd := endpoint_spec ha hL hd
    exact (hg.lt_iff_gt (live_nonnegative ha.le hb.le)
      (live_nonnegative ha.le hsd.1.le)).mp (by simpa only [hsd.2] using hbd)

theorem endpoint_continuousOn {a0 L : ℝ} (ha : 0 < a0) (hL : 0 < L) :
    ContinuousOn (endpoint a0 L) (Ioo (freeGrowth L) (Real.exp L)) :=
  fun _ hT => (endpoint_continuousAt ha hL hT).continuousWithinAt

/-- A fixed threshold has a larger positive endpoint when more scale-time is available. -/
theorem endpoint_strict_horizon {a0 L1 L2 T : ℝ} (ha : 0 < a0)
    (hL1 : 0 < L1) (h12 : L1 < L2)
    (hT1 : T ∈ Ioo (freeGrowth L1) (Real.exp L1))
    (hT2 : T ∈ Ioo (freeGrowth L2) (Real.exp L2)) :
    endpoint a0 L1 T < endpoint a0 L2 T := by
  have hL2 := hL1.trans h12
  have hs1 := endpoint_spec ha hL1 hT1
  have hs2 := endpoint_spec ha hL2 hT2
  have hl := live_nonnegative (L := L2) ha.le hs1.1.le
  have htime := growth_strict_in_time hL2.le hl (constructed_growthSolution hL2.le hl)
    ⟨hL1.le, h12.le⟩ ⟨hL2.le, le_rfl⟩ h12
  have hG : T < finalGrowth a0 L2 (endpoint a0 L1 T) := by
    change finalGrowth a0 L1 (endpoint a0 L1 T) <
      finalGrowth a0 L2 (endpoint a0 L1 T) at htime
    rwa [hs1.2] at htime
  exact ((finalGrowth_strictAntiOn ha hL2).lt_iff_gt
    (live_nonnegative ha.le hs2.1.le) hl).mp (by simpa only [hs2.2] using hG)

end
end SbtCosmo.Derivation.GrowthEndpointSensitivity
