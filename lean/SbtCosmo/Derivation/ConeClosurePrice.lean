import SbtCosmo.Derivation.ConvexClosurePrice
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Construct a positive conic dual from the actual finite value derivative.
The cone laws describe only budget addition and nonnegative scaling. -/
namespace SbtCosmo.Derivation.ConeClosurePrice
noncomputable section
open Set Filter
open scoped Topology

variable {E F : Type*}

def feasibleCosts [Sub F] (A : Set E) (J : E → ℝ) (energy : E → F) (positive : F → Prop) (B : F) : Set ℝ :=
  {r | ∃ x ∈ A, positive (B-energy x) ∧ J x=r}
def value [Sub F] (A : Set E) (J : E → ℝ) (energy : E → F) (positive : F → Prop) (B : F) : ℝ :=
  sInf (feasibleCosts A J energy positive B)

structure PrimalOptimum [Sub F] (A : Set E) (J : E → ℝ) (energy : E → F)
    (positive : F → Prop) (B : F) (star : E) : Prop where
  member : star ∈ A
  feasible : positive (B-energy star)
  optimal : ∀ x ∈ A, positive (B-energy x) → J star ≤ J x

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

structure ConeLaws (positive : F → Prop) : Prop where
  zero : positive 0
  add : ∀ {x y}, positive x → positive y → positive (x+y)
  smul : ∀ {a : ℝ} {x}, 0 ≤ a → positive x → positive (a • x)

structure DualCertificate (A : Set E) (J : E → ℝ) (energy : E → F)
    (positive : F → Prop) (B : F) (price : F →L[ℝ] ℝ) (star : E) : Prop where
  nonnegative : ∀ H, positive H → 0 ≤ price H
  member : star ∈ A
  feasible : positive (B-energy star)
  complementarity : price (energy star-B)=0
  global_minimum : ∀ x ∈ A, J star ≤ J x+price (energy x-B)

omit [NormedSpace ℝ F] in
theorem value_le_candidate {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop} {B : F}
    (hbb : BddBelow (feasibleCosts A J energy positive B)) {x : E}
    (hx : x ∈ A) (he : positive (B-energy x)) : value A J energy positive B ≤ J x :=
  csInf_le hbb ⟨x,hx,he,rfl⟩

omit [NormedSpace ℝ F] in
theorem optimum_value {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop} {B : F} {star : E}
    (h : PrimalOptimum A J energy positive B star) : value A J energy positive B = J star := by
  apply le_antisymm
  · apply value_le_candidate (x := star) ?_ h.member h.feasible
    refine ⟨J star, ?_⟩
    rintro r ⟨x,hx,he,rfl⟩
    exact h.optimal x hx he
  · apply le_csInf (show (feasibleCosts A J energy positive B).Nonempty
      from ⟨J star,star,h.member,h.feasible,rfl⟩)
    rintro r ⟨x,hx,he,rfl⟩
    exact h.optimal x hx he

theorem derivative_nonpositive_on_cone {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B : F} {star : E} {d : F →L[ℝ] ℝ} (hc : ConeLaws positive)
    (hstar : PrimalOptimum A J energy positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B, (feasibleCosts A J energy positive T).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive T))
    (hd : HasFDerivAt (value A J energy positive) d B) :
    ∀ H, positive H → d H ≤ 0 := by
  intro H hH
  have hpath : HasDerivAt (fun t : ℝ => B+t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add B
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (feasibleCosts A J energy positive (B+t • H)).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive (B+t • H)) := by
    have ht : Tendsto (fun t : ℝ => B+t • H) (𝓝[>] (0 : ℝ)) (𝓝 B) := by
      simpa using hpath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually hfinite
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      value A J energy positive (B+t • H) ≤ value A J energy positive (B+(0 : ℝ) • H)+0*t := by
    filter_upwards [hnear, self_mem_nhdsWithin] with t hT ht
    have he : positive (B+t • H-energy star) := by
      have hh := hc.add hstar.feasible (hc.smul ht.le hH)
      convert hh using 1
      abel
    simpa only [zero_smul, add_zero, zero_mul, optimum_value hstar] using
      value_le_candidate hT.2 hstar.member he
  exact ConvexClosurePrice.derivative_le_of_right_support (hd.hasLineDerivAt H) hbound

section Convex
variable [AddCommGroup E] [Module ℝ E]

theorem derivative_global_support {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B : F} {star : E} {d : F →L[ℝ] ℝ} (hc : ConeLaws positive)
    (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B, (feasibleCosts A J energy positive T).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive T))
    (hd : HasFDerivAt (value A J energy positive) d B) :
    ∀ x ∈ A, J star+d (energy x-B) ≤ J x := by
  intro x hx
  let gap := energy x-B
  have hpath : HasDerivAt (fun t : ℝ => B+t • gap) gap 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const gap).const_add B
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (feasibleCosts A J energy positive (B+t • gap)).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive (B+t • gap)) := by
    have ht : Tendsto (fun t : ℝ => B+t • gap) (𝓝[>] (0 : ℝ)) (𝓝 B) := by
      simpa using hpath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually hfinite
  have hone : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      value A J energy positive (B+t • gap) ≤
        value A J energy positive (B+(0 : ℝ) • gap)+(J x-J star)*t := by
    filter_upwards [hnear, hone, self_mem_nhdsWithin] with t hT ht htp
    have ha : 0 ≤ 1-t := by linarith
    have hab : 1-t+t=(1 : ℝ) := by ring
    have hm := hJ.1 hstar.member hx ha htp.le hab
    have hec := hc.add (hc.smul ha hstar.feasible) (he star hstar.member x hx (1-t) t ha htp.le hab)
    have hp : positive (B+t • gap-energy ((1-t) • star+t • x)) := by
      convert hec using 1
      dsimp [gap]
      module
    have hv := value_le_candidate hT.2 hm hp
    have hj := hJ.2 hstar.member hx ha htp.le hab
    simp only [zero_smul, add_zero, optimum_value hstar, smul_eq_mul] at *
    nlinarith
  have h := ConvexClosurePrice.derivative_le_of_right_support (hd.hasLineDerivAt gap) hbound
  dsimp [gap] at h
  linarith

/-- The price is explicitly minus the actual derivative. Nonzero sensitivity is a PSD-direction test. -/
theorem price_certificate {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B : F} {star : E} {d : F →L[ℝ] ℝ} (hc : ConeLaws positive)
    (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B, (feasibleCosts A J energy positive T).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive T))
    (hd : HasFDerivAt (value A J energy positive) d B) :
    DualCertificate A J energy positive B (-d) star := by
  have hpos := derivative_nonpositive_on_cone hc hstar hfinite hd
  have hsupport := derivative_global_support hc hJ he hstar hfinite hd
  refine ⟨fun H hH => by simpa using neg_nonneg.mpr (hpos H hH), hstar.member, hstar.feasible, ?_, ?_⟩
  · have h1 := hsupport star hstar.member
    have h2 := hpos (B-energy star) hstar.feasible
    have heq : d (B-energy star) = -d (energy star-B) := by rw [← neg_sub, map_neg]
    simp only [ContinuousLinearMap.neg_apply]
    rw [heq] at h2
    linarith
  · intro x hx
    have hh := hsupport x hx
    simp only [ContinuousLinearMap.neg_apply]
    linarith

end Convex

theorem strict_sensitivity_nonzero {d : F →L[ℝ] ℝ} {H : F} (hs : d H < 0) : -d ≠ 0 := by
  intro hz
  have he : (-d) H = 0 := by rw [hz]; rfl
  simp only [ContinuousLinearMap.neg_apply] at he
  linarith

def lagrangian (J : E → ℝ) (energy : E → F) (B : F) (price : F →L[ℝ] ℝ) (x : E) : ℝ :=
  J x+price (energy x-B)
def dualValue (A : Set E) (J : E → ℝ) (energy : E → F) (B : F) (price : F →L[ℝ] ℝ) : ℝ :=
  sInf ((lagrangian J energy B price) '' A)

theorem certificate_primal_optimum {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B : F} {price : F →L[ℝ] ℝ} {star : E}
    (h : DualCertificate A J energy positive B price star) : PrimalOptimum A J energy positive B star := by
  refine ⟨h.member,h.feasible,?_⟩
  intro x hx he
  have hp := h.nonnegative (B-energy x) he
  have hh := h.global_minimum x hx
  have hneg : price (B-energy x) = -price (energy x-B) := by rw [← neg_sub, map_neg]
  rw [hneg] at hp
  linarith

theorem certificate_dual_isGLB {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B : F} {price : F →L[ℝ] ℝ} {star : E}
    (h : DualCertificate A J energy positive B price star) :
    IsGLB ((lagrangian J energy B price) '' A) (dualValue A J energy B price) := by
  apply isGLB_csInf (show ((lagrangian J energy B price) '' A).Nonempty from ⟨_,star,h.member,rfl⟩)
  refine ⟨J star,?_⟩
  rintro r ⟨x,hx,rfl⟩
  exact h.global_minimum x hx

theorem certificate_strong_duality {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B : F} {price : F →L[ℝ] ℝ} {star : E}
    (h : DualCertificate A J energy positive B price star) :
    dualValue A J energy B price = value A J energy positive B := by
  rw [optimum_value (certificate_primal_optimum h)]
  have hstar : lagrangian J energy B price star=J star := by simp [lagrangian,h.complementarity]
  apply le_antisymm
  · apply csInf_le (show BddBelow ((lagrangian J energy B price) '' A) from ?_)
      (show J star ∈ (lagrangian J energy B price) '' A from ⟨star,h.member,hstar⟩)
    refine ⟨J star,?_⟩
    rintro r ⟨x,hx,rfl⟩
    exact h.global_minimum x hx
  · apply le_csInf (show ((lagrangian J energy B price) '' A).Nonempty from ⟨_,star,h.member,rfl⟩)
    rintro r ⟨x,hx,rfl⟩
    exact h.global_minimum x hx

end
end SbtCosmo.Derivation.ConeClosurePrice
