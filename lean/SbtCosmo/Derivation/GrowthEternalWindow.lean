import SbtCosmo.Derivation.GrowthInfinite
import SbtCosmo.Derivation.GrowthWindow

/-! Infinite-time endpoints constructed from the actual finite-start growth IVP.
Perpetual horizon admissibility is algebraic; it does not assert physical crunch dynamics. -/
namespace SbtCosmo.Derivation.GrowthEternalWindow
noncomputable section
open Set Filter GrowthInfinite GrowthScaleReturn GrowthExistence GrowthLimit
open scoped Topology

theorem exists_unique_infinite_endpoint {a0 T : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T) :
    ∃! upper : ℝ, 0 < upper ∧ nativeInfinite a0 upper = T := by
  let A := a0 * (T + 1)
  have hTp : 0 < T := by linarith
  have hA : a0 < A := by dsimp [A]; nlinarith
  have hr : A / a0 = T + 1 := by dsimp [A]; field_simp
  have hf : freeGrowth (Real.log (A / a0)) < T := by
    unfold freeGrowth
    linarith [Real.exp_pos (-2 * Real.log (A / a0))]
  have hz : T < A / a0 := by rw [hr]; linarith
  obtain ⟨lo, hlo, _⟩ := GrowthWindow.exists_unique_native_threshold_window ha0 hA hf hz
  have hlT : T < nativeInfinite a0 lo := hlo.2.1 ▸ native_lt_infinite ha0 hlo.1 hA.le
  obtain ⟨b, hbT, hb⟩ := ((native_infinite_parameter_limit ha0).eventually_lt_const hT).and
    (eventually_gt_atTop lo) |>.exists
  have hc : ContinuousOn (nativeInfinite a0) (Icc lo b) := by
    intro lam hlam
    exact (native_infinite_continuousAt ha0 (hlo.1.trans_le hlam.1)).continuousWithinAt
  obtain ⟨upper, hu, he⟩ := intermediate_value_Icc' hb.le hc ⟨hbT.le, hlT.le⟩
  refine ⟨upper, ⟨hlo.1.trans_le hu.1, he⟩, ?_⟩
  intro other ho
  exact ((native_infinite_strictAntiOn ha0).eq_iff_eq (hlo.1.trans_le hu.1) ho.1).mp
    (he.trans ho.2.symm)

def infiniteEndpoint (a0 T : ℝ) : ℝ :=
  if h : 0 < a0 ∧ 3 / 2 < T then (exists_unique_infinite_endpoint h.1 h.2).exists.choose else 0

theorem infiniteEndpoint_spec {a0 T : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T) :
    0 < infiniteEndpoint a0 T ∧ nativeInfinite a0 (infiniteEndpoint a0 T) = T := by
  unfold infiniteEndpoint
  rw [dif_pos ⟨ha0, hT⟩]
  exact (exists_unique_infinite_endpoint ha0 hT).exists.choose_spec

theorem below_infinite_endpoint_iff {a0 T lam : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)
    (hlam : 0 < lam) : T < nativeInfinite a0 lam ↔ lam < infiniteEndpoint a0 T := by
  have hu := infiniteEndpoint_spec ha0 hT
  nth_rw 1 [← hu.2]
  exact (native_infinite_strictAntiOn ha0).lt_iff_gt hu.1 hlam

/-- Every finite declared horizon remains strictly before its algebraic turnaround. -/
def perpetualHorizon (a0 lam : ℝ) : Prop := ∀ A : ℝ, a0 ≤ A → -(1 / A^3) < lam

theorem perpetual_horizon_iff {a0 lam : ℝ} (ha0 : 0 < a0) :
    perpetualHorizon a0 lam ↔ 0 ≤ lam := by
  constructor
  · intro h
    have hp : Tendsto (fun A : ℝ => A^3) atTop atTop := tendsto_pow_atTop (by norm_num)
    have hz : Tendsto (fun A : ℝ => -(1 / A^3)) atTop (𝓝 0) := by
      simpa using (hp.const_div_atTop 1).neg
    apply le_of_tendsto hz
    filter_upwards [eventually_ge_atTop a0] with A hA
    exact (h A hA).le
  · intro h A hA
    exact (neg_neg_of_pos (one_div_pos.mpr (pow_pos (ha0.trans_le hA) 3))).trans_le h

/-- Actual finite-epoch attainment, with perpetual horizon retention, has an open upper edge. -/
theorem perpetual_threshold_window {a0 T lam : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T) :
    (perpetualHorizon a0 lam ∧ ∃ a : ℝ, a0 ≤ a ∧ T ≤ nativeGrowth a0 lam a) ↔
      0 ≤ lam ∧ lam < infiniteEndpoint a0 T := by
  rw [perpetual_horizon_iff ha0]
  by_cases hzero : lam = 0
  · subst lam
    have hu := (infiniteEndpoint_spec ha0 hT).1
    constructor
    · intro _
      exact ⟨le_rfl, hu⟩
    · intro _
      have ha : a0 ≤ a0 * (T + 1) := by nlinarith
      refine ⟨le_rfl, a0 * (T + 1), ha, ?_⟩
      rw [GrowthFirstRecordLive.native_matter_at_zero ha0 ha]
      have he : a0 * (T + 1) / a0 = T + 1 := by field_simp
      rw [he]
      linarith
  · constructor
    · rintro ⟨hn, hex⟩
      have hp : 0 < lam := lt_of_le_of_ne hn (Ne.symm hzero)
      exact ⟨hn, (below_infinite_endpoint_iff ha0 hT hp).mp
        ((native_eventual_threshold_iff ha0 hp).mp hex)⟩
    · rintro ⟨hn, hlt⟩
      have hp : 0 < lam := lt_of_le_of_ne hn (Ne.symm hzero)
      exact ⟨hn, (native_eventual_threshold_iff ha0 hp).mpr
        ((below_infinite_endpoint_iff ha0 hT hp).mpr hlt)⟩

theorem finite_endpoint_lt_infinite {a0 T lam A : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)
    (hlam : 0 < lam) (hA : a0 ≤ A) (he : nativeGrowth a0 lam A = T) :
    lam < infiniteEndpoint a0 T :=
  (below_infinite_endpoint_iff ha0 hT hlam).mp (he ▸ native_lt_infinite ha0 hlam hA)

end
end SbtCosmo.Derivation.GrowthEternalWindow
