import SbtCosmo.Derivation.ExtendedClosurePrice
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Supporting-functional definitions for actual extended objectives and admissibility.
Restricted objective subgradients are distinct from ambient objective subgradients. -/
namespace SbtCosmo.Derivation.ConvexSubgradient
noncomputable section
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SubgradientOn (A : Set E) (J : E → EReal) (star : E) (p : E →L[ℝ] ℝ) : Prop :=
  star ∈ A ∧ J star ≠ ⊤ ∧ J star ≠ ⊥ ∧ ∀ x ∈ A, J star+(p (x-star) : ℝ) ≤ J x

def Subgradient (J : E → EReal) (star : E) (p : E →L[ℝ] ℝ) : Prop :=
  SubgradientOn univ J star p

def RealSubgradient (f : E → ℝ) (star : E) (p : E →L[ℝ] ℝ) : Prop :=
  ∀ x, f star+p (x-star) ≤ f x

def NormalCone (A : Set E) (star : E) (p : E →L[ℝ] ℝ) : Prop :=
  star ∈ A ∧ ∀ x ∈ A, p (x-star) ≤ 0

def restriction (A : Set E) (J : E → EReal) (x : E) : EReal := by
  classical
  exact if x ∈ A then J x else ⊤
def indicator (A : Set E) : E → EReal := restriction A (fun _ => 0)

/-- This is exactly the subgradient of J plus its admissibility indicator, not of ambient J. -/
theorem restricted_subgradient_iff {A : Set E} {J : E → EReal} {star : E} {p : E →L[ℝ] ℝ} :
    Subgradient (restriction A J) star p ↔ SubgradientOn A J star p := by
  constructor
  · rintro ⟨_,ht,hb,h⟩
    have hs : star ∈ A := by
      by_contra hn
      exact ht (by simp [restriction,hn])
    refine ⟨hs,by simpa [restriction,hs] using ht,by simpa [restriction,hs] using hb,?_⟩
    intro x hx
    simpa [restriction,hs,hx] using h x (mem_univ x)
  · rintro ⟨hs,ht,hb,h⟩
    refine ⟨mem_univ _,by simpa [restriction,hs] using ht,by simpa [restriction,hs] using hb,?_⟩
    intro x _
    by_cases hx : x ∈ A
    · simpa [restriction,hs,hx] using h x hx
    · simp [restriction,hx]

/-- Normal-cone sign agrees with the subgradient of the actual indicator. -/
theorem indicator_subgradient_iff {A : Set E} {star : E} {p : E →L[ℝ] ℝ} :
    Subgradient (indicator A) star p ↔ NormalCone A star p := by
  rw [indicator,restricted_subgradient_iff]
  constructor
  · rintro ⟨hs,_,_,h⟩
    refine ⟨hs,?_⟩
    intro x hx
    have hh := h x hx
    have hh' : (p (x-star) : EReal) ≤ (0 : ℝ) := by simpa only [zero_add] using hh
    exact EReal.coe_le_coe_iff.mp hh'
  · rintro ⟨hs,h⟩
    refine ⟨hs,by norm_num,by norm_num,?_⟩
    intro x hx
    simpa only [zero_add,EReal.coe_zero] using EReal.coe_le_coe_iff.mpr (h x hx)

theorem real_subgradient_iff {f : E → ℝ} {star : E} {p : E →L[ℝ] ℝ} :
    Subgradient (fun x => (f x : EReal)) star p ↔ RealSubgradient f star p := by
  constructor
  · rintro ⟨_,_,_,h⟩ x
    have hh := h x (mem_univ x)
    rw [← EReal.coe_add] at hh
    exact EReal.coe_le_coe_iff.mp hh
  · intro h
    refine ⟨mem_univ _,EReal.coe_ne_top _,EReal.coe_ne_bot _,?_⟩
    intro x _
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (h x)

/-- The zero supporting functional is equivalent to ordinary global extended minimization. -/
theorem zero_subgradientOn_iff {A : Set E} {J : E → EReal} {star : E} :
    SubgradientOn A J star 0 ↔ star ∈ A ∧ J star ≠ ⊤ ∧ J star ≠ ⊥ ∧ ∀ x ∈ A, J star ≤ J x := by
  simp [SubgradientOn]

theorem real_subgradient_add {f g : E → ℝ} {star : E} {p q : E →L[ℝ] ℝ}
    (hp : RealSubgradient f star p) (hq : RealSubgradient g star q) :
    RealSubgradient (fun x => f x+g x) star (p+q) := by
  intro x
  have hf := hp x
  have hg := hq x
  simp only [ContinuousLinearMap.add_apply]
  linarith

/-- Smooth constraints may be removed from a support using actual line derivatives.
Only objective convexity is used; the smooth summand need not be convex. -/
theorem remove_smooth_summand {A : Set E} {J g : E → ℝ} {star : E} {p d : E →L[ℝ] ℝ}
    (hJ : ConvexOn ℝ A J) (hs : star ∈ A)
    (h : ∀ x ∈ A, J star+g star+p (x-star) ≤ J x+g x) (hd : HasFDerivAt g d star) :
    ∀ x ∈ A, J star+(p-d) (x-star) ≤ J x := by
  intro x hx
  let gap := x-star
  have hder : HasDerivAt (fun t : ℝ => p (t • gap)-g (star+t • gap)) (p gap-d gap) 0 := by
    have hp : HasDerivAt (fun t : ℝ => p (t • gap)) (p gap) 0 := by
      simpa only [map_smul,smul_eq_mul,id_eq,one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const (p gap)
    exact hp.sub (hd.hasLineDerivAt gap)
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      p (t • gap)-g (star+t • gap) ≤ p ((0 : ℝ) • gap)-g (star+(0 : ℝ) • gap)+(J x-J star)*t := by
    have hone : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hone,self_mem_nhdsWithin] with t ht ht0
    have ha : 0 ≤ 1-t := by linarith
    have hab : 1-t+t=(1 : ℝ) := by ring
    have hmix := hJ.1 hs hx ha ht0.le hab
    have hj := hJ.2 hs hx ha ht0.le hab
    have hm := h _ hmix
    have he : (1-t) • star+t • x=star+t • gap := by dsimp [gap]; module
    rw [he] at hm hj
    simp only [add_sub_cancel_left,zero_smul,add_zero,map_zero,smul_eq_mul] at hm hj ⊢
    nlinarith
  have hh := ConvexClosurePrice.derivative_le_of_right_support hder hbound
  simp only [ContinuousLinearMap.sub_apply]
  dsimp [gap] at hh
  linarith

/-- On the full ambient space the actual normal cone contains only zero. -/
theorem normal_univ_iff {star : E} {p : E →L[ℝ] ℝ} : NormalCone univ star p ↔ p=0 := by
  constructor
  · intro h
    ext H
    have h1 := h.2 (star+H) (mem_univ _)
    have h2 := h.2 (star-H) (mem_univ _)
    simp only [add_sub_cancel_left] at h1
    have he : star-H-star= -H := by abel
    rw [he,map_neg] at h2
    simp only [ContinuousLinearMap.zero_apply]
    linarith
  · rintro rfl
    exact ⟨mem_univ _,by simp⟩

/-- A smooth finite summand has only its actual derivative as supporting functional. -/
theorem smooth_real_subgradient_eq {g : E → ℝ} {star : E} {p d : E →L[ℝ] ℝ}
    (hp : RealSubgradient g star p) (hd : HasFDerivAt g d star) : p=d := by
  have hh := remove_smooth_summand (convexOn_const (0 : ℝ) convex_univ) (mem_univ star)
    (fun x _ => by simpa using hp x) hd
  have hn : NormalCone univ star (p-d) := ⟨mem_univ _,fun x hx => by simpa using hh x hx⟩
  exact sub_eq_zero.mp (normal_univ_iff.mp hn)

end
end SbtCosmo.Derivation.ConvexSubgradient
