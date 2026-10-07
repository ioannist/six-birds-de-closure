import SbtCosmo.Derivation.GrowthRankSensitivity
import SbtCosmo.Derivation.GrowthEndpointSensitivity

/-! Constructed tagged maxima, rank thresholds and endpoints are stable under continuous inputs. -/
namespace SbtCosmo.Derivation.GrowthPopulationSensitivity
noncomputable section
open Set GrowthPopulation GrowthRankSensitivity GrowthEndpointSensitivity GrowthLimit
open GrowthScaleReturn
attribute [local instance] Classical.propDecidable

def tagSet {ι : Type*} [Fintype ι] (tag : ι → Bool) (b : Bool) : Finset ι :=
  Finset.univ.filter (fun i => tag i = b)

def tagMaximumValue {ι : Type*} [Fintype ι] (amplitude : ι → ℝ) (tag : ι → Bool) (b : Bool) : ℝ :=
  if h : (tagSet tag b).Nonempty then
    (finite_attained_maximum h amplitude).choose
  else 0

theorem tagMaximumValue_spec {ι : Type*} [Fintype ι] (amplitude : ι → ℝ)
    {tag : ι → Bool} {b : Bool} (htag : (tagSet tag b).Nonempty) :
    WindowRecords.TagMaximum amplitude tag b (tagMaximumValue amplitude tag b) := by
  have hs := (finite_attained_maximum htag amplitude).choose_spec
  simp only [tagMaximumValue, dif_pos htag]
  obtain ⟨i, hi, he⟩ := hs.1
  refine ⟨⟨i, (Finset.mem_filter.mp hi).2, he⟩, ?_⟩
  intro j hj
  exact hs.2 j (by simp [tagSet, hj])

theorem tagMaximumValue_positive {ι : Type*} [Fintype ι] (amplitude : ι → ℝ)
    {tag : ι → Bool} {b : Bool} (hpatch : ∃ i, tag i = b ∧ 0 < amplitude i) :
    0 < tagMaximumValue amplitude tag b := by
  obtain ⟨i, hi, hp⟩ := hpatch
  have ht : (tagSet tag b).Nonempty := ⟨i, by simp [tagSet, hi]⟩
  exact hp.trans_le ((tagMaximumValue_spec amplitude ht).bounds i hi)

theorem tagMaximumValue_eq_of_maximum {ι : Type*} [Fintype ι] {amplitude : ι → ℝ}
    {tag : ι → Bool} {b : Bool} {m : ℝ} (hm : WindowRecords.TagMaximum amplitude tag b m) :
    tagMaximumValue amplitude tag b = m := by
  obtain ⟨i, hi, he⟩ := hm.attained
  have hs := tagMaximumValue_spec amplitude (show (tagSet tag b).Nonempty from
    ⟨i, by simp [tagSet, hi]⟩)
  obtain ⟨j, hj, hej⟩ := hs.attained
  exact le_antisymm (hej ▸ hm.bounds j hj) (he ▸ hs.bounds i hi)

theorem tagMaximumValue_le_add {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    {tag : ι → Bool} {b : Bool} {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ i, g i ≤ f i + ε) :
    tagMaximumValue g tag b ≤ tagMaximumValue f tag b + ε := by
  by_cases ht : (tagSet tag b).Nonempty
  · obtain ⟨i, hi, he⟩ := (tagMaximumValue_spec g ht).attained
    have hf := (tagMaximumValue_spec f ht).bounds i hi
    linarith [hfg i]
  · simp only [tagMaximumValue, dif_neg ht]
    linarith

theorem tagMaximumValue_lipschitz {ι : Type*} [Fintype ι] (tag : ι → Bool) (b : Bool) :
    LipschitzWith 1 (fun amplitude : ι → ℝ => tagMaximumValue amplitude tag b) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [Real.dist_eq]
  have hb (i : ι) : |f i - g i| ≤ dist f g := by
    simpa only [Real.dist_eq] using dist_le_pi_dist f g i
  have h1 := tagMaximumValue_le_add (tag := tag) (b := b) (f := f) (g := g)
    dist_nonneg (fun i => by have h := (abs_le.mp (hb i)).1; linarith)
  have h2 := tagMaximumValue_le_add (tag := tag) (b := b) (f := g) (g := f)
    dist_nonneg (fun i => by have h := (abs_le.mp (hb i)).2; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tagMaximumValue_continuous {ι : Type*} [Fintype ι] (tag : ι → Bool) (b : Bool) :
    Continuous (fun amplitude : ι → ℝ => tagMaximumValue amplitude tag b) :=
  (tagMaximumValue_lipschitz tag b).continuous

def seedThresholds {σ ι : Type*} [Fintype ι] (amplitude : σ → ι → ℝ)
    (tag : σ → ι → Bool) (delta : ℝ) (j : σ) : ℝ :=
  max (delta / tagMaximumValue (amplitude j) (tag j) false)
    (delta / tagMaximumValue (amplitude j) (tag j) true)

def aggregateThreshold {σ ι : Type*} [Fintype σ] [Fintype ι]
    (amplitude : σ → ι → ℝ) (tag : σ → ι → Bool) (delta : ℝ) (k : ℕ) : ℝ :=
  rankThreshold (seedThresholds amplitude tag delta) k

def populationEndpoint {σ ι : Type*} [Fintype σ] [Fintype ι]
    (a0 L : ℝ) (amplitude : σ → ι → ℝ) (tag : σ → ι → Bool) (delta : ℝ) (k : ℕ) : ℝ :=
  endpoint a0 L (aggregateThreshold amplitude tag delta k)

/-- Fixed tags, continuously varying amplitudes and collapse threshold give continuous seed thresholds. -/
theorem seedThresholds_continuousAt {α σ ι : Type*} [TopologicalSpace α] [Fintype ι]
    {amplitude : α → σ → ι → ℝ} {delta : α → ℝ} (tag : σ → ι → Bool) {p : α}
    (ha : ∀ j i, ContinuousAt (fun q => amplitude q j i) p) (hd : ContinuousAt delta p)
    (hm : ∀ j b, tagMaximumValue (amplitude p j) (tag j) b ≠ 0) :
    ContinuousAt (fun q => seedThresholds (amplitude q) tag (delta q)) p := by
  apply continuousAt_pi.mpr
  intro j
  have hc (b : Bool) : ContinuousAt
      (fun q => tagMaximumValue (amplitude q j) (tag j) b) p :=
    ContinuousAt.comp (f := fun q => amplitude q j) (x := p)
      (tagMaximumValue_continuous (tag j) b).continuousAt (continuousAt_pi.mpr (ha j))
  exact (hd.div (hc false) (hm j false)).max (hd.div (hc true) (hm j true))

theorem aggregateThreshold_continuousAt {α σ ι : Type*} [TopologicalSpace α]
    [Fintype σ] [Fintype ι] {amplitude : α → σ → ι → ℝ} {delta : α → ℝ}
    (tag : σ → ι → Bool) {p : α} {k : ℕ} (hk : 0 < k) (hkn : k ≤ Fintype.card σ)
    (ha : ∀ j i, ContinuousAt (fun q => amplitude q j i) p) (hd : ContinuousAt delta p)
    (hm : ∀ j b, tagMaximumValue (amplitude p j) (tag j) b ≠ 0) :
    ContinuousAt (fun q => aggregateThreshold (amplitude q) tag (delta q) k) p := by
  exact ContinuousAt.comp (f := fun q => seedThresholds (amplitude q) tag (delta q)) (x := p)
    (rankThreshold_continuous hk hkn).continuousAt (seedThresholds_continuousAt tag ha hd hm)

/-- Ranking and maximizing-patch switches are allowed: only zero denominators are excluded. -/
theorem populationEndpoint_continuousAt {α σ ι : Type*} [TopologicalSpace α]
    [Fintype σ] [Fintype ι] {amplitude : α → σ → ι → ℝ} {delta : α → ℝ}
    (tag : σ → ι → Bool) {p : α} {k : ℕ} {a0 L : ℝ}
    (ha0 : 0 < a0) (hL : 0 < L) (hk : 0 < k) (hkn : k ≤ Fintype.card σ)
    (ha : ∀ j i, ContinuousAt (fun q => amplitude q j i) p) (hd : ContinuousAt delta p)
    (hm : ∀ j b, tagMaximumValue (amplitude p j) (tag j) b ≠ 0)
    (hT : aggregateThreshold (amplitude p) tag (delta p) k ∈ Ioo (freeGrowth L) (Real.exp L)) :
    ContinuousAt (fun q => populationEndpoint a0 L (amplitude q) tag (delta q) k) p := by
  exact ContinuousAt.comp (f := fun q => aggregateThreshold (amplitude q) tag (delta q) k) (x := p)
    (endpoint_continuousAt ha0 hL hT) (aggregateThreshold_continuousAt tag hk hkn ha hd hm)

/-- The continuous endpoint function is the boundary of the original native record gate. -/
theorem populationEndpoint_native_window {σ ι : Type*} [Fintype σ] [Fintype ι]
    (amplitude : σ → ι → ℝ) (tag : σ → ι → Bool) {a0 A delta : ℝ} {k : ℕ}
    (ha : 0 < a0) (hA : a0 < A) (hk : 0 < k) (hkn : k ≤ Fintype.card σ)
    (hp : ∀ j i, 0 ≤ amplitude j i)
    (hpatch : ∀ j b, ∃ i, tag j i = b ∧ 0 < amplitude j i)
    (hT : aggregateThreshold amplitude tag delta k ∈
      Ioo (freeGrowth (Real.log (A / a0))) (A / a0)) :
    0 < populationEndpoint a0 (Real.log (A / a0)) amplitude tag delta k ∧
      nativeGrowth a0 (populationEndpoint a0 (Real.log (A / a0)) amplitude tag delta k) A =
        aggregateThreshold amplitude tag delta k ∧
      ∀ lam : ℝ, nativeAggregate amplitude tag a0 A delta k lam ↔
        (-(1 / A^3) < lam ∧ lam ≤ populationEndpoint a0 (Real.log (A / a0)) amplitude tag delta k) := by
  have ht (j : σ) (b : Bool) : (tagSet (tag j) b).Nonempty := by
    obtain ⟨i, hi, _⟩ := hpatch j b
    exact ⟨i, by simp [tagSet, hi]⟩
  have hm (j : σ) (b : Bool) := tagMaximumValue_positive (amplitude j) (hpatch j b)
  have hs := rankThreshold_spec (seedThresholds amplitude tag delta) hk hkn
  obtain ⟨upper, hu, _⟩ := exists_unique_native_aggregate_window ha hA hp
    (fun j => tagMaximumValue_spec (amplitude j) (ht j false))
    (fun j => tagMaximumValue_spec (amplitude j) (ht j true))
    (fun j => hm j false) (fun j => hm j true) hs.2.1 hs.2.2.1 hT.1 hT.2
  have hL : 0 < Real.log (A / a0) := Real.log_pos ((one_lt_div ha).mpr hA)
  have hTlog : aggregateThreshold amplitude tag delta k ∈
      Ioo (freeGrowth (Real.log (A / a0))) (Real.exp (Real.log (A / a0))) := by
    simpa only [Real.exp_log (div_pos (ha.trans hA) ha)] using hT
  have he : populationEndpoint a0 (Real.log (A / a0)) amplitude tag delta k = upper :=
    endpoint_eq_of_root ha hL hTlog hu.1 hu.2.1
  simpa only [he] using hu

/-- Uniform positive rescaling preserves fixed tags and scales their actual maxima. -/
theorem tagMaximumValue_mul_pos {ι : Type*} [Fintype ι] (amplitude : ι → ℝ)
    (tag : ι → Bool) (b : Bool) {c : ℝ} (hc : 0 < c) :
    tagMaximumValue (fun i => c * amplitude i) tag b = c * tagMaximumValue amplitude tag b := by
  by_cases ht : (tagSet tag b).Nonempty
  · have hs := tagMaximumValue_spec amplitude ht
    have hsc := tagMaximumValue_spec (fun i => c * amplitude i) ht
    obtain ⟨i, hi, hei⟩ := hs.attained
    obtain ⟨j, hj, hej⟩ := hsc.attained
    have h1 := mul_le_mul_of_nonneg_left (hs.bounds j hj) hc.le
    have h2 := hsc.bounds i hi
    rw [hej] at h1
    rw [hei] at h2
    exact le_antisymm h1 h2
  · simp [tagMaximumValue, ht]

theorem aggregateThreshold_delta_mul_pos {σ ι : Type*} [Fintype σ] [Fintype ι]
    (amplitude : σ → ι → ℝ) (tag : σ → ι → Bool) (delta : ℝ) {k : ℕ} {c : ℝ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card σ) (hc : 0 < c) :
    aggregateThreshold amplitude tag (c * delta) k = c * aggregateThreshold amplitude tag delta k := by
  unfold aggregateThreshold seedThresholds
  simp only [mul_div_assoc, ← mul_max_of_nonneg _ _ hc.le]
  exact rankThreshold_mul_pos _ hk hkn hc

theorem aggregateThreshold_amplitude_mul_pos {σ ι : Type*} [Fintype σ] [Fintype ι]
    (amplitude : σ → ι → ℝ) (tag : σ → ι → Bool) (delta : ℝ) {k : ℕ} {c : ℝ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card σ) (hc : 0 < c) :
    aggregateThreshold (fun j i => c * amplitude j i) tag delta k =
      c⁻¹ * aggregateThreshold amplitude tag delta k := by
  unfold aggregateThreshold seedThresholds
  have he (m : ℝ) : delta / (c * m) = c⁻¹ * (delta / m) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [tagMaximumValue_mul_pos _ _ _ hc, he,
    ← mul_max_of_nonneg _ _ (inv_pos.mpr hc).le]
  exact rankThreshold_mul_pos _ hk hkn (inv_pos.mpr hc)

end
end SbtCosmo.Derivation.GrowthPopulationSensitivity
