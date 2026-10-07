import SbtCosmo.Derivation.GrowthWindow

/-! Finite maxima and rank counting return the growth window to seed aggregation. -/
namespace SbtCosmo.Derivation.GrowthPopulation
noncomputable section
open Set GrowthWindow GrowthLimit GrowthScaleReturn
attribute [local instance] Classical.propDecidable

def passingCount {ι : Type*} [Fintype ι] (thresholds : ι → ℝ) (x : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => thresholds j ≤ x)).card

theorem passingCount_mono {ι : Type*} [Fintype ι] (thresholds : ι → ℝ) :
    Monotone (passingCount thresholds) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans hxy

/-- A rank is certified by counts below and at the threshold; ties are retained. -/
theorem passingCount_iff_rank {ι : Type*} [Fintype ι] {thresholds : ι → ℝ} {k : ℕ} {T : ℝ}
    (hbelow : (Finset.univ.filter (fun j => thresholds j < T)).card < k)
    (hat : k ≤ passingCount thresholds T) :
    ∀ x : ℝ, k ≤ passingCount thresholds x ↔ T ≤ x := by
  classical
  intro x
  constructor
  · intro hx
    by_contra hn
    have hxt := lt_of_not_ge hn
    have hc : passingCount thresholds x ≤ (Finset.univ.filter (fun j => thresholds j < T)).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.trans_lt hxt
    exact (not_le_of_gt hbelow) (hx.trans hc)
  · intro htx
    exact hat.trans (passingCount_mono thresholds htx)

/-- Every nonempty finite family has an attained maximum, constructed in the original carrier. -/
theorem finite_attained_maximum {ι : Type*} [Fintype ι] {s : Finset ι}
    (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ m : ℝ, (∃ i ∈ s, f i = m) ∧ ∀ i ∈ s, f i ≤ m := by
  classical
  have hi := hs.image f
  refine ⟨(s.image f).max' hi, ?_, ?_⟩
  · obtain ⟨i, his, he⟩ := Finset.mem_image.mp ((s.image f).max'_mem hi)
    exact ⟨i, his, he⟩
  · intro i his
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem f his)

/-- Positive tagged maxima are derived from a positive patch of that tag. -/
theorem exists_positive_tagMaximum {ι : Type*} [Fintype ι]
    (amplitude : ι → ℝ) (tag : ι → Bool) (b : Bool)
    (hpatch : ∃ i, tag i = b ∧ 0 < amplitude i) :
    ∃ m : ℝ, 0 < m ∧ WindowRecords.TagMaximum amplitude tag b m := by
  classical
  let s := Finset.univ.filter (fun i => tag i = b)
  obtain ⟨i, hit, hip⟩ := hpatch
  have his : i ∈ s := by simp [s, hit]
  obtain ⟨m, ⟨j, hjs, hjm⟩, hm⟩ := finite_attained_maximum ⟨i, his⟩ amplitude
  refine ⟨m, hip.trans_le (hm i his), ⟨⟨j, ?_, hjm⟩, ?_⟩⟩
  · exact (Finset.mem_filter.mp hjs).2
  · intro l hlt
    exact hm l (by simp [s, hlt])

/-- A finite k-th threshold is constructed by minimizing the finite set of passing jumps. -/
theorem exists_count_threshold {ι : Type*} [Fintype ι] (thresholds : ι → ℝ)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    ∃ T : ℝ, (∃ j, thresholds j = T) ∧
      (Finset.univ.filter (fun j => thresholds j < T)).card < k ∧
      k ≤ passingCount thresholds T ∧
      ∀ x : ℝ, k ≤ passingCount thresholds x ↔ T ≤ x := by
  classical
  have hu : (Finset.univ : Finset ι).Nonempty :=
    Finset.card_pos.mp (by simpa using hk.trans_le hkn)
  obtain ⟨M, ⟨j, _, hjM⟩, hM⟩ := finite_attained_maximum hu thresholds
  have hcM : k ≤ passingCount thresholds M := by
    have he : Finset.univ.filter (fun j => thresholds j ≤ M) = (Finset.univ : Finset ι) := by
      ext i
      simp [hM i (Finset.mem_univ i)]
    simpa [passingCount, he] using hkn
  let candidates := (Finset.univ.image thresholds).filter (fun t => k ≤ passingCount thresholds t)
  have hMc : M ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hjM⟩, hcM⟩
  let T := candidates.min' ⟨M, hMc⟩
  have hTc : T ∈ candidates := candidates.min'_mem ⟨M, hMc⟩
  have hat : k ≤ passingCount thresholds T := (Finset.mem_filter.mp hTc).2
  have hbelow : (Finset.univ.filter (fun j => thresholds j < T)).card < k := by
    by_contra hn
    have hbc : k ≤ (Finset.univ.filter (fun j => thresholds j < T)).card := le_of_not_gt hn
    have hbne : (Finset.univ.filter (fun j => thresholds j < T)).Nonempty :=
      Finset.card_pos.mp (hk.trans_le hbc)
    obtain ⟨B, ⟨i, hi, hiB⟩, hB⟩ := finite_attained_maximum hbne thresholds
    have hBT : B < T := hiB ▸ (Finset.mem_filter.mp hi).2
    have hcnt : k ≤ passingCount thresholds B := by
      apply hbc.trans
      apply Finset.card_le_card
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hB l hl⟩
    have hBc : B ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hiB⟩, hcnt⟩
    have hTB : T ≤ B := candidates.min'_le B hBc
    exact hBT.not_ge hTB
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hTc).1
  exact ⟨T, ⟨i, hi⟩, hbelow, hat, passingCount_iff_rank hbelow hat⟩

def nativeRecord {ι : Type*} (amplitude : ι → ℝ) (tag : ι → Bool)
    (a0 A delta lam : ℝ) : Prop :=
  WindowRecords.RecordBearing
    (fun i => ∃ a ∈ Icc a0 A, delta ≤ amplitude i * nativeGrowth a0 lam a) tag

def nativeAggregate {σ ι : Type*} [Fintype σ] (amplitude : σ → ι → ℝ)
    (tag : σ → ι → Bool) (a0 A delta : ℝ) (k : ℕ) (lam : ℝ) : Prop :=
  -(1 / A^3) < lam ∧
    k ≤ (Finset.univ.filter (fun j => nativeRecord (amplitude j) (tag j) a0 A delta lam)).card

/-- A live seed count is computed from the actual continuous native histories. -/
theorem native_record_count_eq {σ ι : Type*} [Fintype σ]
    {amplitude : σ → ι → ℝ} {tag : σ → ι → Bool} {m0 m1 : σ → ℝ} {a0 A delta lam : ℝ}
    (ha : 0 < a0) (hA : a0 ≤ A) (hlam : -(1 / A^3) < lam)
    (hp : ∀ j i, 0 ≤ amplitude j i)
    (h0 : ∀ j, WindowRecords.TagMaximum (amplitude j) (tag j) false (m0 j))
    (h1 : ∀ j, WindowRecords.TagMaximum (amplitude j) (tag j) true (m1 j))
    (hm0 : ∀ j, 0 < m0 j) (hm1 : ∀ j, 0 < m1 j) :
    (Finset.univ.filter (fun j => nativeRecord (amplitude j) (tag j) a0 A delta lam)).card =
      passingCount (fun j => max (delta / m0 j) (delta / m1 j)) (nativeGrowth a0 lam A) := by
  classical
  unfold passingCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact native_record_history_iff_threshold ha hA hlam (hp j) (h0 j) (h1 j) (hm0 j) (hm1 j)

/-- Both rank counts are explicit certificate inputs; no aggregate equivalence is assumed. -/
theorem native_aggregate_iff_threshold {σ ι : Type*} [Fintype σ]
    {amplitude : σ → ι → ℝ} {tag : σ → ι → Bool} {m0 m1 : σ → ℝ} {a0 A delta T : ℝ} {k : ℕ}
    (ha : 0 < a0) (hA : a0 ≤ A) (hp : ∀ j i, 0 ≤ amplitude j i)
    (h0 : ∀ j, WindowRecords.TagMaximum (amplitude j) (tag j) false (m0 j))
    (h1 : ∀ j, WindowRecords.TagMaximum (amplitude j) (tag j) true (m1 j))
    (hm0 : ∀ j, 0 < m0 j) (hm1 : ∀ j, 0 < m1 j)
    (hbelow : (Finset.univ.filter (fun j => max (delta / m0 j) (delta / m1 j) < T)).card < k)
    (hat : k ≤ passingCount (fun j => max (delta / m0 j) (delta / m1 j)) T) :
    ∀ lam : ℝ, nativeAggregate amplitude tag a0 A delta k lam ↔
      (-(1 / A^3) < lam ∧ T ≤ nativeGrowth a0 lam A) := by
  intro lam
  constructor
  · rintro ⟨hl, hc⟩
    rw [native_record_count_eq ha hA hl hp h0 h1 hm0 hm1] at hc
    exact ⟨hl, (passingCount_iff_rank hbelow hat _).mp hc⟩
  · rintro ⟨hl, ht⟩
    refine ⟨hl, ?_⟩
    rw [native_record_count_eq ha hA hl hp h0 h1 hm0 hm1]
    exact (passingCount_iff_rank hbelow hat _).mpr ht

/-- Exact aggregate window with its positive endpoint constructed from the actual ODE. -/
theorem exists_unique_native_aggregate_window {σ ι : Type*} [Fintype σ]
    {amplitude : σ → ι → ℝ} {tag : σ → ι → Bool} {m0 m1 : σ → ℝ} {a0 A delta T : ℝ} {k : ℕ}
    (ha : 0 < a0) (hA : a0 < A) (hp : ∀ j i, 0 ≤ amplitude j i)
    (h0 : ∀ j, WindowRecords.TagMaximum (amplitude j) (tag j) false (m0 j))
    (h1 : ∀ j, WindowRecords.TagMaximum (amplitude j) (tag j) true (m1 j))
    (hm0 : ∀ j, 0 < m0 j) (hm1 : ∀ j, 0 < m1 j)
    (hbelow : (Finset.univ.filter (fun j => max (delta / m0 j) (delta / m1 j) < T)).card < k)
    (hat : k ≤ passingCount (fun j => max (delta / m0 j) (delta / m1 j)) T)
    (hTinf : freeGrowth (Real.log (A / a0)) < T) (hTzero : T < A / a0) :
    ∃! upper : ℝ, 0 < upper ∧ nativeGrowth a0 upper A = T ∧
      ∀ lam : ℝ, nativeAggregate amplitude tag a0 A delta k lam ↔
        (-(1 / A^3) < lam ∧ lam ≤ upper) := by
  obtain ⟨upper, hu, huniq⟩ := exists_unique_native_threshold_window ha hA hTinf hTzero
  have he := native_aggregate_iff_threshold ha hA.le hp h0 h1 hm0 hm1 hbelow hat
  refine ⟨upper, ⟨hu.1, hu.2.1, fun lam => (he lam).trans (hu.2.2 lam)⟩, ?_⟩
  intro other ho
  exact huniq other ⟨ho.1, ho.2.1, fun lam => (he lam).symm.trans (ho.2.2 lam)⟩

end
end SbtCosmo.Derivation.GrowthPopulation
