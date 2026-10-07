import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
Exact finite audit laws: common-translation invariance and conservative inclusive
upper ranks. The rank cardinality law is deterministic for every score vector,
including ties. Its probabilistic return requires exchangeable scores; it does
not assume that fitting an anchor on the observed data supplies that premise.
-/
namespace SbtCosmo.Derivation.StagingAudit

noncomputable section

def component (split joint splitSigma jointSigma floor : ℝ) : ℝ :=
  |split-joint| / Real.sqrt (splitSigma^2+jointSigma^2+floor^2)

theorem component_translation (split joint splitSigma jointSigma floor shift : ℝ) :
    component (split+shift) (joint+shift) splitSigma jointSigma floor =
      component split joint splitSigma jointSigma floor := by
  unfold component
  congr 2
  ring

theorem common_shift_can_still_fire (shift : ℝ) :
    (1/2 : ℝ) < component (1+shift) (0+shift) 0 0 1 := by
  rw [component_translation]
  norm_num [component]

theorem component_denominator_positive {splitSigma jointSigma floor : ℝ}
    (hf : 0 < floor) : 0 < Real.sqrt (splitSigma^2+jointSigma^2+floor^2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg splitSigma, sq_nonneg jointSigma, sq_pos_of_pos hf]

variable {ι : Type*} [Fintype ι]

def upperSet (score : ι → ℝ) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => score i ≤ score j)

def upperCard (score : ι → ℝ) (i : ι) : ℕ := (upperSet score i).card

def tail (score : ι → ℝ) (k : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => upperCard score i ≤ k)

theorem self_in_upperSet (score : ι → ℝ) (i : ι) : i ∈ upperSet score i := by
  simp [upperSet]

theorem upperCard_positive (score : ι → ℝ) (i : ι) : 0 < upperCard score i := by
  exact Finset.card_pos.mpr ⟨i, self_in_upperSet score i⟩

/-- A deterministic counting law for all finite score vectors, with ties. -/
theorem tail_card_le (score : ι → ℝ) (k : ℕ) : (tail score k).card ≤ k := by
  classical
  by_cases hn : (tail score k).Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (tail score k) score hn
    have hs : tail score k ⊆ upperSet score i := by
      intro j hj
      simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmin j hj
    have hk : upperCard score i ≤ k := (Finset.mem_filter.mp hi).2
    exact le_trans (Finset.card_le_card hs) hk
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

/-- Uniform choice of the audited index has tail fraction at most k/N.
Exchangeability is needed to transfer this to a predetermined future index. -/
theorem uniform_index_tail_bound [Nonempty ι] (score : ι → ℝ) (k : ℕ) :
    ((tail score k).card : ℝ)/(Fintype.card ι : ℝ) ≤
      (k : ℝ)/(Fintype.card ι : ℝ) := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast tail_card_le score k
  · exact (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card ι)).le

theorem nominal_level_bound [Nonempty ι] (score : ι → ℝ) (k : ℕ) (alpha : ℝ)
    (hk : (k : ℝ) ≤ alpha*(Fintype.card ι : ℝ)) :
    ((tail score k).card : ℝ)/(Fintype.card ι : ℝ) ≤ alpha := by
  have hN : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact le_trans (uniform_index_tail_bound score k) ((div_le_iff₀ hN).mpr hk)

/-- Actual finite probability mass of an index's inclusive rank event. -/
def rankMass {Ω : Type*} [Fintype Ω] (weight : Ω → ℝ) (score : Ω → ι → ℝ)
    (k : ℕ) (i : ι) : ℝ := ∑ o, if upperCard (score o) i ≤ k then weight o else 0

theorem sum_rankMass_le {Ω : Type*} [Fintype Ω] (weight : Ω → ℝ)
    (score : Ω → ι → ℝ) (k : ℕ) (hw : ∀ o, 0 ≤ weight o)
    (hunit : ∑ o, weight o = 1) : (∑ i, rankMass weight score k i) ≤ k := by
  classical
  unfold rankMass
  rw [Finset.sum_comm]
  have hi : ∀ o, (∑ i, if upperCard (score o) i ≤ k then weight o else 0) =
      weight o*((tail (score o) k).card : ℝ) := by
    intro o
    rw [← Finset.sum_filter]
    simp [tail, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc
    _ = ∑ o, weight o*((tail (score o) k).card : ℝ) := Finset.sum_congr rfl (fun o _ => hi o)
    _ ≤ ∑ o, weight o*(k : ℝ) := Finset.sum_le_sum (fun o _ =>
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (tail_card_le (score o) k)) (hw o))
    _ = k := by rw [← Finset.sum_mul, hunit, one_mul]

/-- Equal index marginals (derived from exchangeability in the mathematical
return) turn the deterministic counting law into a finite probability bound. -/
theorem balanced_rankMass_bound [Nonempty ι] {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (score : Ω → ι → ℝ) (k : ℕ) (i : ι)
    (hw : ∀ o, 0 ≤ weight o) (hunit : ∑ o, weight o = 1)
    (hbalance : ∀ j, rankMass weight score k j = rankMass weight score k i) :
    rankMass weight score k i ≤ (k : ℝ)/(Fintype.card ι : ℝ) := by
  have hsum := sum_rankMass_le weight score k hw hunit
  have he : (∑ j, rankMass weight score k j) =
      (Fintype.card ι : ℝ)*rankMass weight score k i := by
    simp [hbalance, Finset.sum_const, nsmul_eq_mul]
  rw [he] at hsum
  have hN : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  apply (le_div_iff₀ hN).mpr
  nlinarith

theorem rank_zero_never_rejects (score : ι → ℝ) : tail score 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hk := (Finset.mem_filter.mp hi).2
  have hp := upperCard_positive score i
  omega

/-- With 20 null scores and a future score, the strict top-rank rule has a
conditional exchangeable upper bound smaller than 5%. -/
theorem twenty_null_rank_bound (score : Fin 21 → ℝ) :
    ((tail score 1).card : ℝ)/21 ≤ 1/21 ∧ (1/21 : ℝ) < 1/20 := by
  constructor
  · simpa using uniform_index_tail_bound score 1
  · norm_num

/-- Frozen linear-interpolation cutoff after omitting index i from scores
0,...,20. Python independently constructs and sorts each actual omitted array. -/
def omissionCutoff (i : Fin 21) : ℝ :=
  if i.val < 19 then 19+1/20 else if i.val = 19 then 18+2/20 else 18+1/20

def omissionRejections : Finset (Fin 21) :=
  Finset.univ.filter (fun i => omissionCutoff i < (i.val : ℝ))

theorem omission_rejection_iff (i : Fin 21) :
    omissionCutoff i < (i.val : ℝ) ↔ i = 19 ∨ i = 20 := by
  fin_cases i <;> norm_num [omissionCutoff, Fin.ext_iff]

theorem omission_rejections_eq : omissionRejections = {19, 20} := by
  ext i
  simp [omissionRejections, omission_rejection_iff]

theorem omission_rejections_card : omissionRejections.card = 2 := by
  rw [omission_rejections_eq]
  decide

/-- The exact finite exchangeable omission example exceeds the nominal rate. -/
theorem interpolated_counterexample_rate :
    (omissionRejections.card : ℝ)/21 > 1/20 := by
  rw [omission_rejections_card]
  norm_num

end

end SbtCosmo.Derivation.StagingAudit
