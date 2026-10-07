import SbtCosmo.Derivation.GrowthPopulation
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Finite rank thresholds are monotone and 1-Lipschitz, including at ties. -/
namespace SbtCosmo.Derivation.GrowthRankSensitivity
noncomputable section
open GrowthPopulation
attribute [local instance] Classical.propDecidable

def rankThreshold {ι : Type*} [Fintype ι] (thresholds : ι → ℝ) (k : ℕ) : ℝ :=
  if h : 0 < k ∧ k ≤ Fintype.card ι then
    (exists_count_threshold thresholds h.1 h.2).choose
  else 0

theorem rankThreshold_spec {ι : Type*} [Fintype ι] (thresholds : ι → ℝ) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    (∃ j, thresholds j = rankThreshold thresholds k) ∧
      (Finset.univ.filter (fun j => thresholds j < rankThreshold thresholds k)).card < k ∧
      k ≤ passingCount thresholds (rankThreshold thresholds k) ∧
      ∀ x : ℝ, k ≤ passingCount thresholds x ↔ rankThreshold thresholds k ≤ x := by
  have hv : 0 < k ∧ k ≤ Fintype.card ι := ⟨hk, hkn⟩
  simp only [rankThreshold, dif_pos hv]
  exact (exists_count_threshold thresholds hk hkn).choose_spec

theorem rankThreshold_eq_of_certificate {ι : Type*} [Fintype ι] {thresholds : ι → ℝ}
    {k : ℕ} {T : ℝ} (hk : 0 < k) (hkn : k ≤ Fintype.card ι)
    (hbelow : (Finset.univ.filter (fun j => thresholds j < T)).card < k)
    (hat : k ≤ passingCount thresholds T) : rankThreshold thresholds k = T := by
  have hs := rankThreshold_spec thresholds hk hkn
  exact le_antisymm ((hs.2.2.2 T).mp hat)
    ((passingCount_iff_rank hbelow hat _).mp hs.2.2.1)

/-- A uniform one-sided perturbation of all thresholds bounds the rank perturbation. -/
theorem rankThreshold_le_add {ι : Type*} [Fintype ι] {f g : ι → ℝ} {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hfg : ∀ i, g i ≤ f i + ε) :
    rankThreshold g k ≤ rankThreshold f k + ε := by
  classical
  have hs := rankThreshold_spec f hk hkn
  apply ((rankThreshold_spec g hk hkn).2.2.2 _).mp
  apply hs.2.2.1.trans
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  linarith [hfg i]

theorem rankThreshold_mono {ι : Type*} [Fintype ι] {f g : ι → ℝ} {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hfg : ∀ i, f i ≤ g i) :
    rankThreshold f k ≤ rankThreshold g k := by
  simpa using rankThreshold_le_add (f := g) (g := f) (ε := 0) hk hkn
    (fun i => by simpa using hfg i)

theorem rankThreshold_abs_le {ι : Type*} [Fintype ι] {f g : ι → ℝ} {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hfg : ∀ i, |f i - g i| ≤ ε) :
    |rankThreshold f k - rankThreshold g k| ≤ ε := by
  apply abs_le.mpr
  have h1 := rankThreshold_le_add (f := f) (g := g) (ε := ε) hk hkn (fun i => by
    have h := (abs_le.mp (hfg i)).1
    linarith)
  have h2 := rankThreshold_le_add (f := g) (g := f) (ε := ε) hk hkn (fun i => by
    have h := (abs_le.mp (hfg i)).2
    linarith)
  constructor <;> linarith

/-- Sorting/rank switches introduce no jump: the rank map is globally 1-Lipschitz. -/
theorem rankThreshold_lipschitz {ι : Type*} [Fintype ι] {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    LipschitzWith 1 (fun thresholds : ι → ℝ => rankThreshold thresholds k) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [Real.dist_eq]
  exact rankThreshold_abs_le hk hkn
    (fun i => by simpa only [Real.dist_eq] using dist_le_pi_dist f g i)

theorem rankThreshold_continuous {ι : Type*} [Fintype ι] {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    Continuous (fun thresholds : ι → ℝ => rankThreshold thresholds k) :=
  (rankThreshold_lipschitz hk hkn).continuous

theorem rankThreshold_mul_pos {ι : Type*} [Fintype ι] (f : ι → ℝ) {k : ℕ} {c : ℝ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hc : 0 < c) :
    rankThreshold (fun i => c * f i) k = c * rankThreshold f k := by
  have hs := rankThreshold_spec f hk hkn
  apply rankThreshold_eq_of_certificate hk hkn
  · simpa only [mul_lt_mul_iff_right₀ hc] using hs.2.1
  · simpa only [passingCount, mul_le_mul_iff_right₀ hc] using hs.2.2.1

end
end SbtCosmo.Derivation.GrowthRankSensitivity
