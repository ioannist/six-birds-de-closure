import SbtCosmo.Derivation.RelativeDifference
import SbtCosmo.Derivation.RelativeEqualitySupport
import SbtCosmo.Derivation.ConvexSubgradient
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Ambient objective/normal splitting earned from the original relative-interior
qualification, including extended objectives and lower-dimensional domains. -/
namespace SbtCosmo.Derivation.RelativeSumSplit
noncomputable section
open Set Filter ConvexSubgradient ExtendedClosurePrice
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual affine coordinates about a common domain point. -/
def chart (P : Submodule ℝ E) (x₀ : E) : P →ᵃ[ℝ] E where
  toFun u := x₀ + (u : E)
  linear := P.subtype
  map_vadd' p v := by simp [vadd_eq_add]; abel

/-- A convex real objective on its domain and a convex admissibility set split at
an ordinary minimizer when their actual relative interiors intersect. -/
theorem split_real_relative [FiniteDimensional ℝ E]
    {C A : Set E} {f : E → ℝ} {star x₀ : E}
    (hf : ConvexOn ℝ C f) (hA : Convex ℝ A)
    (hC : x₀ ∈ intrinsicInterior ℝ C) (hAr : x₀ ∈ intrinsicInterior ℝ A)
    (hsC : star ∈ C) (hsA : star ∈ A)
    (hmin : ∀ x ∈ C, x ∈ A → f star ≤ f x) :
    ∃ q : E →L[ℝ] ℝ, (∀ x ∈ C, f star+q (x-star) ≤ f x) ∧ NormalCone A star (-q) := by
  let P := (affineSpan ℝ C).direction
  let Q := (affineSpan ℝ A).direction
  let c : (P × Q) →ᵃ[ℝ] E := (chart P x₀).comp (LinearMap.fst ℝ P Q).toAffineMap
  let a : (P × Q) →ᵃ[ℝ] E := (chart Q x₀).comp (LinearMap.snd ℝ P Q).toAffineMap
  let T : Set (P × Q) := c ⁻¹' C ∩ a ⁻¹' A
  let F : (P × Q) → ℝ := f ∘ c
  let energy := RelativeDifference.difference P Q
  have hxC := intrinsicInterior_subset hC
  have hxA := intrinsicInterior_subset hAr
  let liftC (x : E) (hx : x ∈ C) : P :=
    ⟨x-x₀,(affineSpan ℝ C).vsub_mem_direction (subset_affineSpan ℝ C hx) (subset_affineSpan ℝ C hxC)⟩
  let liftA (x : E) (hx : x ∈ A) : Q :=
    ⟨x-x₀,(affineSpan ℝ A).vsub_mem_direction (subset_affineSpan ℝ A hx) (subset_affineSpan ℝ A hxA)⟩
  have hc (x : E) (hx : x ∈ C) (y : E) (hy : y ∈ A) : c (liftC x hx,liftA y hy)=x := by
    change x₀+(x-x₀)=x
    abel
  have ha (x : E) (hx : x ∈ C) (y : E) (hy : y ∈ A) : a (liftC x hx,liftA y hy)=y := by
    change x₀+(y-x₀)=y
    abel
  have hT (x : E) (hx : x ∈ C) (y : E) (hy : y ∈ A) : (liftC x hx,liftA y hy) ∈ T := by
    constructor
    · change c (liftC x hx,liftA y hy) ∈ C
      rwa [hc x hx y hy]
    · change a (liftC x hx,liftA y hy) ∈ A
      rwa [ha x hx y hy]
  have hF : ConvexOn ℝ T F := by
    have hcv := hf.comp_affineMap c
    refine ⟨hcv.1.inter (hA.affine_preimage a),?_⟩
    intro z hz v hv α β hα hβ hab
    exact hcv.2 hz.1 hv.1 hα hβ hab
  let s : P × Q := (liftC star hsC,liftA star hsA)
  have hes : energy s=0 := by ext; simp [energy,RelativeDifference.difference,s,liftC,liftA]
  have hFs : F s=f star := by change f (c s)=f star; rw [hc star hsC star hsA]
  have hopt : ∀ z ∈ T, energy z=0 → F s ≤ F z := by
    intro z hz hez
    have he' := congrArg (fun w : ↥(P ⊔ Q) => (w : E)) hez
    change (z.1 : E)-(z.2 : E)=0 at he'
    have hequal : c z=a z := by
      change x₀+(z.1 : E)=x₀+(z.2 : E)
      rw [sub_eq_zero.mp he']
    rw [hFs]
    exact hmin (c z) hz.1 (hequal ▸ hz.2)
  have hupper : ∀ᶠ w : ↥(P ⊔ Q) in 𝓝 0, ∃ z ∈ T, energy z=w ∧ F z ≤ f x₀+1 := by
    filter_upwards [RelativeDifference.local_bounded_witnesses hf hC hAr] with w hw
    obtain ⟨x,hx,y,hy,he,hfx⟩ := hw
    refine ⟨(liftC x hx,liftA y hy),hT x hx y hy,?_,?_⟩
    · apply Subtype.ext
      change (x-x₀)-(y-x₀)=(w : E)
      calc
        (x-x₀)-(y-x₀)=x-y := by abel
        _ = (w : E) := he
    · change f (c (liftC x hx,liftA y hy)) ≤ f x₀+1
      rwa [hc x hx y hy]
  obtain ⟨d,hd⟩ := RelativeEqualitySupport.supporting_functional hF energy (hT star hsC star hsA) hes hopt hupper
  obtain ⟨q,hq,_⟩ := Real.exists_extension_norm_eq (P ⊔ Q) d
  have hglobal (x : E) (hx : x ∈ C) (y : E) (hy : y ∈ A) : f star+q (x-y) ≤ f x := by
    have hh := hd (liftC x hx,liftA y hy) (hT x hx y hy)
    rw [hFs] at hh
    change f star+d (energy (liftC x hx,liftA y hy)) ≤ f (c (liftC x hx,liftA y hy)) at hh
    rw [hc x hx y hy,← hq] at hh
    have he : ((energy (liftC x hx,liftA y hy)) : E)=x-y := by
      change (x-x₀)-(y-x₀)=x-y
      abel
    rwa [he] at hh
  refine ⟨q,fun x hx => hglobal x hx star hsA,⟨hsA,?_⟩⟩
  intro y hy
  have hh := hglobal star hsC y hy
  have he : q (star-y)= -q (y-star) := by rw [← neg_sub,map_neg]
  rw [he] at hh
  simp only [ContinuousLinearMap.neg_apply]
  linarith

/-- An arbitrary restricted support splits by subtracting its actual linear
functional from the objective, preserving the domain and its qualification. -/
theorem split_real_support_relative [FiniteDimensional ℝ E]
    {C A : Set E} {f : E → ℝ} {star x₀ : E} {p : E →L[ℝ] ℝ}
    (hf : ConvexOn ℝ C f) (hA : Convex ℝ A)
    (hC : x₀ ∈ intrinsicInterior ℝ C) (hAr : x₀ ∈ intrinsicInterior ℝ A)
    (hsC : star ∈ C) (hsA : star ∈ A)
    (hsupport : ∀ x ∈ C, x ∈ A → f star+p (x-star) ≤ f x) :
    ∃ q n : E →L[ℝ] ℝ, (∀ x ∈ C, f star+q (x-star) ≤ f x) ∧
      NormalCone A star n ∧ q+n=p := by
  have hshift : ConvexOn ℝ C (fun x => f x-p x) := hf.sub (p.toLinearMap.concaveOn hf.1)
  have hmin : ∀ x ∈ C, x ∈ A → f star-p star ≤ f x-p x := by
    intro x hx hxa
    have hh := hsupport x hx hxa
    rw [map_sub] at hh
    linarith
  obtain ⟨d,hd,hn⟩ := split_real_relative hshift hA hC hAr hsC hsA hmin
  refine ⟨d+p,-d,?_,hn,?_⟩
  · intro x hx
    have hh := hd x hx
    simp only [ContinuousLinearMap.add_apply,map_sub]
    rw [map_sub] at hh
    linarith
  · abel

/-- The earned relative split returns to the original extended objective at every
ambient point, including its infinite-cost points. -/
theorem split_subgradient [FiniteDimensional ℝ E]
    {A : Set E} {J : E → EReal} {star x₀ : E} {p : E →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : x₀ ∈ intrinsicInterior ℝ (finiteDomain univ J))
    (hAr : x₀ ∈ intrinsicInterior ℝ A) (hp : SubgradientOn A J star p) :
    ∃ q n : E →L[ℝ] ℝ, Subgradient J star q ∧ NormalCone A star n ∧ q+n=p := by
  have hf := epigraph_objective_convex (fun x _ => hbottom x) hJ
  have hsupport : ∀ x ∈ finiteDomain univ J, x ∈ A →
      realObjective J star+p (x-star) ≤ realObjective J x := by
    intro x hx hxa
    have hh := hp.2.2.2 x hxa
    rw [← EReal.coe_toReal hp.2.1 (hbottom star),← EReal.coe_toReal hx.2 (hbottom x),
      ← EReal.coe_add] at hh
    exact EReal.coe_le_coe_iff.mp hh
  obtain ⟨q,n,hq,hn,heq⟩ := split_real_support_relative hf hA hC hAr
    ⟨mem_univ _,hp.2.1⟩ hp.1 hsupport
  refine ⟨q,n,⟨mem_univ _,hp.2.1,hbottom star,?_⟩,hn,heq⟩
  intro x _
  by_cases ht : J x=⊤
  · rw [ht]; exact le_top
  · rw [← EReal.coe_toReal hp.2.1 (hbottom star),← EReal.coe_toReal ht (hbottom x),← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (hq x ⟨mem_univ _,ht⟩)

/-- Joining ambient objective support and an admissibility normal is always valid. -/
theorem join_subgradient {A : Set E} {J : E → EReal} {star : E} {p q n : E →L[ℝ] ℝ}
    (hq : Subgradient J star q) (hn : NormalCone A star n) (heq : q+n=p) :
    SubgradientOn A J star p := by
  refine ⟨hn.1,hq.2.1,hq.2.2.1,?_⟩
  intro x hx
  have hnx := hn.2 x hx
  have hpx : p (x-star) ≤ q (x-star) := by
    rw [← heq,ContinuousLinearMap.add_apply]
    linarith
  exact (add_le_add (le_refl (J star)) (EReal.coe_le_coe_iff.mpr hpx)).trans
    (hq.2.2.2 x (mem_univ _))

/-- Exact ambient objective/indicator sum rule under the original relative-interior
qualification, with an earned split rather than a sum-rule premise. -/
theorem subgradient_sum_iff [FiniteDimensional ℝ E]
    {A : Set E} {J : E → EReal} {star x₀ : E} {p : E →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : x₀ ∈ intrinsicInterior ℝ (finiteDomain univ J))
    (hAr : x₀ ∈ intrinsicInterior ℝ A) :
    Subgradient (restriction A J) star p ↔
      ∃ q n : E →L[ℝ] ℝ, Subgradient J star q ∧ NormalCone A star n ∧ q+n=p := by
  rw [restricted_subgradient_iff]
  constructor
  · exact split_subgradient hbottom hJ hA hC hAr
  · rintro ⟨q,n,hq,hn,heq⟩
    exact join_subgradient hq hn heq

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The literal extended objective plus its zero/top indicator is exactly the
restriction, with no minus-infinity arithmetic silently suppressed. -/
theorem objective_indicator_eq_restriction {A : Set E} {J : E → EReal}
    (hbottom : ∀ x, J x ≠ ⊥) :
    (fun x => J x+ConvexSubgradient.indicator A x)=restriction A J := by
  funext x
  by_cases hx : x ∈ A
  · simp [ConvexSubgradient.indicator,restriction,hx]
  · simp only [ConvexSubgradient.indicator,restriction,hx,ite_false]
    exact EReal.add_top_of_ne_bot (hbottom x)

/-- The same earned sum rule stated for the literal original J+indicator_A. -/
theorem subgradient_add_indicator_iff [FiniteDimensional ℝ E]
    {A : Set E} {J : E → EReal} {star x₀ : E} {p : E →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : x₀ ∈ intrinsicInterior ℝ (finiteDomain univ J))
    (hAr : x₀ ∈ intrinsicInterior ℝ A) :
    Subgradient (fun x => J x+ConvexSubgradient.indicator A x) star p ↔
      ∃ q n : E →L[ℝ] ℝ, Subgradient J star q ∧ NormalCone A star n ∧ q+n=p := by
  rw [objective_indicator_eq_restriction hbottom]
  exact subgradient_sum_iff hbottom hJ hA hC hAr

end
end SbtCosmo.Derivation.RelativeSumSplit
