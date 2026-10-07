import Mathlib.Tactic

/-!
Exact Boolean record predicate and expanding-branch horizon bound for the
declared window toy. No growth-ODE comparison, continuum window certification,
elapsed-time crunch, or physical record bridge is asserted.
-/
namespace SbtCosmo.Derivation.WindowRecords

def RecordBearing {ι : Type*} (collapsed : ι → Prop) (tag : ι → Bool) : Prop :=
  ∃ i j, collapsed i ∧ collapsed j ∧ tag i ≠ tag j

theorem both_tags_iff {ι : Type*} (collapsed : ι → Prop) (tag : ι → Bool) :
    RecordBearing collapsed tag ↔
      (∃ i, collapsed i ∧ tag i = false) ∧ (∃ j, collapsed j ∧ tag j = true) := by
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩
    cases hti : tag i <;> cases htj : tag j <;> simp_all
    · exact ⟨⟨i, hi, hti⟩, ⟨j, hj, htj⟩⟩
    · exact ⟨⟨j, hj, htj⟩, ⟨i, hi, hti⟩⟩
  · rintro ⟨⟨i, hi, hti⟩, ⟨j, hj, htj⟩⟩
    exact ⟨i, j, hi, hj, by simp [hti, htj]⟩

theorem constant_tags_fail {ι : Type*} (collapsed : ι → Prop) (b : Bool) :
    ¬ RecordBearing collapsed (fun _ => b) := by
  rintro ⟨i, j, _, _, hij⟩
  exact hij rfl

/-- More collapsed patches preserves RS if the realized tags stay fixed.
Reseeding an RNG for a different N need not realize this coupling. -/
theorem collapse_monotone {ι : Type*} {c d : ι → Prop} {tag : ι → Bool}
    (hcd : ∀ i, c i → d i) (hc : RecordBearing c tag) : RecordBearing d tag := by
  obtain ⟨i, j, hi, hj, hij⟩ := hc
  exact ⟨i, j, hcd i hi, hcd j hj, hij⟩

/-- A genuine irrelevant change: consistently swapping the two tag labels. -/
theorem complement_tags_iff {ι : Type*} (collapsed : ι → Prop) (tag : ι → Bool) :
    RecordBearing collapsed (fun i => !(tag i)) ↔ RecordBearing collapsed tag := by
  have h : ∀ i j, (!(tag i)) ≠ (!(tag j)) ↔ tag i ≠ tag j := by
    intro i j
    cases tag i <;> cases tag j <;> decide
  simp only [RecordBearing, h]

/-- Same collapsed set; only tag distribution/support changes. -/
theorem tag_relevance_witness :
    RecordBearing (fun _ : Bool => True) id ∧
      ¬ RecordBearing (fun _ : Bool => True) (fun _ => false) := by
  constructor
  · exact ⟨false, true, trivial, trivial, by decide⟩
  · exact constant_tags_fail _ _

noncomputable section

/-- An attained maximum for the amplitudes carrying one tag. These hypotheses
are constructed by taking maxima of the actual finite tagged population. -/
structure TagMaximum {ι : Type*} (amplitude : ι → ℝ) (tag : ι → Bool)
    (b : Bool) (maximum : ℝ) : Prop where
  attained : ∃ i, tag i = b ∧ amplitude i = maximum
  bounds : ∀ i, tag i = b → amplitude i ≤ maximum

theorem tag_collapse_iff_max {ι : Type*} {amplitude : ι → ℝ} {tag : ι → Bool}
    {b : Bool} {maximum growth threshold : ℝ}
    (hm : TagMaximum amplitude tag b maximum) (hg : 0 ≤ growth) :
    (∃ i, threshold ≤ amplitude i * growth ∧ tag i = b) ↔
      threshold ≤ maximum * growth := by
  constructor
  · rintro ⟨i, hi, htag⟩
    exact hi.trans (mul_le_mul_of_nonneg_right (hm.bounds i htag) hg)
  · intro h
    obtain ⟨i, htag, hmax⟩ := hm.attained
    exact ⟨i, by simpa [hmax] using h, htag⟩

/-- Both-tag RS is one maximum-of-thresholds condition for the same finite
realization, provided each tag has a positive attained amplitude maximum. -/
theorem record_iff_threshold {ι : Type*} {amplitude : ι → ℝ} {tag : ι → Bool}
    {m0 m1 growth threshold : ℝ} (h0 : TagMaximum amplitude tag false m0)
    (h1 : TagMaximum amplitude tag true m1) (hm0 : 0 < m0) (hm1 : 0 < m1)
    (hg : 0 ≤ growth) :
    RecordBearing (fun i => threshold ≤ amplitude i * growth) tag ↔
      max (threshold / m0) (threshold / m1) ≤ growth := by
  rw [both_tags_iff, tag_collapse_iff_max h0 hg, tag_collapse_iff_max h1 hg,
    max_le_iff, div_le_iff₀ hm0, div_le_iff₀ hm1]
  simp only [mul_comm]

def hubbleSquared (a lam : ℝ) : ℝ := 1 / a^3 + lam

theorem expanding_horizon_iff (a lam : ℝ) :
    0 < hubbleSquared a lam ↔ -(1 / a^3) < lam := by
  unfold hubbleSquared
  constructor <;> intro h <;> linarith

/-- Longer scale-factor persistence tightens the negative lambda bound. -/
theorem negative_horizon_tightens {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    -(1 / a^3) ≤ -(1 / b^3) := by
  have hc : a^3 ≤ b^3 := pow_le_pow_left₀ ha.le hab 3
  have hp : 0 < a^3 := pow_pos ha 3
  have hi := one_div_le_one_div_of_le hp hc
  linarith

theorem base_negative_cutoff : -(1 / (20 : ℝ)^3) = -(1 / 8000) := by
  norm_num

/-- Exact sampled-amplitude threshold reified by `de_original_claim_checks`.
The receipt checks its source and its rank among the twelve seeds; this
arithmetic lemma alone does not certify random draws or ODE integration. -/
theorem base_threshold_growth_bounds :
    (3 : ℝ)/2 < 971912828383572000768 / 1012057850670495125 ∧
      (971912828383572000768 : ℝ) / 1012057850670495125 < 20000 := by
  norm_num

/-- Inclusion-exclusion expression for IID patches with collapse probability
p and an independent true-tag probability q. The probability-model derivation
is in the mathematical note; this module proves algebraic properties of its
exact expression, without assuming a fixed seed sweep is a population law. -/
def populationProbability (n : ℕ) (p q : ℝ) : ℝ :=
  1 - (1 - p*q)^n - (1 - p*(1-q))^n + (1-p)^n

theorem population_increment (n : ℕ) (p q : ℝ) :
    populationProbability (n+1) p q - populationProbability n p q =
      p*q * ((1-p*q)^n - (1-p)^n) +
      p*(1-q) * ((1-p*(1-q))^n - (1-p)^n) := by
  unfold populationProbability
  simp only [pow_succ]
  ring

theorem population_monotone_step (n : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    populationProbability n p q ≤ populationProbability (n+1) p q := by
  have hbase : 0 ≤ 1-p := by linarith
  have hA : (1-p)^n ≤ (1-p*q)^n :=
    pow_le_pow_left₀ hbase (by nlinarith) n
  have hB : (1-p)^n ≤ (1-p*(1-q))^n :=
    pow_le_pow_left₀ hbase (by nlinarith) n
  have hqa : 0 ≤ 1-q := by linarith
  have hleft := mul_nonneg (mul_nonneg hp hq) (sub_nonneg.mpr hA)
  have hright := mul_nonneg (mul_nonneg hp hqa) (sub_nonneg.mpr hB)
  have hi := population_increment n p q
  linarith

theorem population_monotone {p q : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Monotone (fun n => populationProbability n p q) := by
  exact monotone_nat_of_le_succ (fun n => population_monotone_step n hp hp1 hq hq1)

theorem two_patch_probability (p q : ℝ) :
    populationProbability 2 p q = 2*p^2*q*(1-q) := by
  unfold populationProbability
  ring

theorem population_constant_tags (n : ℕ) (p : ℝ) :
    populationProbability n p 0 = 0 ∧ populationProbability n p 1 = 0 := by
  simp [populationProbability]

theorem population_tag_dependence :
    populationProbability 2 1 (1/2) = 1/2 ∧
      populationProbability 2 1 (1/4) = 3/8 := by
  norm_num [populationProbability]

end

end SbtCosmo.Derivation.WindowRecords
