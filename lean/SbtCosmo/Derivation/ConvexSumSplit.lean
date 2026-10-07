import SbtCosmo.Derivation.ConvexSubgradient
import SbtCosmo.Derivation.ConvexValueSupport

/-! Sum splitting earned by actual epigraph/hypograph separation when one summand
is finite and continuous. Ambient and restricted objective supports remain distinct. -/
namespace SbtCosmo.Derivation.ConvexSumSplit
noncomputable section
open Set Filter ConvexSubgradient ExtendedClosurePrice
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite continuous convex summand earns a split, not a supplied sum-rule field. -/
theorem split_real_of_continuous {A : Set E} {J g : E → ℝ} {star : E}
    (hJ : ConvexOn ℝ A J) (hg : ConvexOn ℝ univ g) (hcont : Continuous g) (hs : star ∈ A)
    (hmin : ∀ x ∈ A, J star+g star ≤ J x+g x) :
    ∃ d : E →L[ℝ] ℝ, (∀ x ∈ A, J star-d (x-star) ≤ J x) ∧ RealSubgradient g star d := by
  let s : Set (E × ℝ) := {z | z.2 < g star-g z.1}
  let t : Set (E × ℝ) := {z | z.1 ∈ A ∧ J z.1-J star ≤ z.2}
  have hsconv : Convex ℝ s := by
    simpa only [s,mem_univ,true_and,Pi.add_apply,Pi.neg_apply,sub_eq_add_neg,add_comm] using (hg.neg.add_const (g star)).convex_strict_hypograph
  have hsopen : IsOpen s := isOpen_lt continuous_snd (continuous_const.sub (hcont.comp continuous_fst))
  have htconv : Convex ℝ t := by
    simpa only [t,sub_eq_add_neg] using (hJ.add_const (-J star)).convex_epigraph
  have hdisjoint : Disjoint s t := by
    apply disjoint_left.mpr
    intro z hz ht
    have hh := hmin z.1 ht.1
    dsimp [s,t] at hz ht
    linarith
  obtain ⟨l,u,hl,hu⟩ := geometric_hahn_banach_open hsconv hsopen htconv hdisjoint
  let c : ℝ := l (0,1)
  let q : E →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (x : E) (r : ℝ) : l (x,r)=q x+c*r := by
    have heq : (x,r)=(x,(0 : ℝ))+r • ((0 : E),1) := by simp
    rw [heq,map_add,map_smul]
    simp [q,c,smul_eq_mul,mul_comm]
  have hstar : u ≤ l (star,0) := hu (star,0) ⟨hs,by simp⟩
  have hc : 0 < c := by
    have hh := hl (star,-1) (by dsimp [s]; simp)
    rw [hsplit] at hh hstar
    linarith
  have hanchor : l (star,0)=u := by
    apply le_antisymm _ hstar
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hl (star,-ε/c) (by dsimp [s]; simp only [sub_self]; simpa only [neg_div] using neg_neg_of_pos (div_pos hε hc))
    rw [hsplit]
    have he : c*(-ε/c)= -ε := mul_div_cancel₀ (-ε) hc.ne'
    rw [hsplit] at hh
    linarith
  let d : E →L[ℝ] ℝ := c⁻¹ • q
  have hdeval (x : E) : d (x-star)=(q x-q star)/c := by
    simp only [d,ContinuousLinearMap.smul_apply,map_sub,smul_eq_mul,div_eq_mul_inv]
    ring
  refine ⟨d,?_,?_⟩
  · intro x hx
    have hh := hu (x,J x-J star) ⟨hx,le_rfl⟩
    rw [← hanchor,hsplit,hsplit] at hh
    rw [hdeval]
    have hd : (q x-q star)/c ≥ J star-J x := (le_div_iff₀ hc).2 (by nlinarith only [hh])
    linarith
  · intro x
    have hclosed : l (x,g star-g x) ≤ l (star,0) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hh := hl (x,g star-g x-ε/c) (by dsimp [s]; linarith [div_pos hε hc])
      rw [← hanchor,hsplit,hsplit] at hh
      rw [hsplit,hsplit]
      have he : c*(ε/c)=ε := mul_div_cancel₀ ε hc.ne'
      nlinarith
    rw [hsplit,hsplit] at hclosed
    rw [hdeval]
    have hd : (q x-q star)/c ≤ g x-g star := (div_le_iff₀ hc).2 (by nlinarith only [hclosed])
    linarith

/-- Finite-dimensional convexity supplies continuity of the finite summand. -/
theorem split_real [FiniteDimensional ℝ E] {A : Set E} {J g : E → ℝ} {star : E}
    (hJ : ConvexOn ℝ A J) (hg : ConvexOn ℝ univ g) (hs : star ∈ A)
    (hmin : ∀ x ∈ A, J star+g star ≤ J x+g x) :
    ∃ d : E →L[ℝ] ℝ, (∀ x ∈ A, J star-d (x-star) ≤ J x) ∧ RealSubgradient g star d :=
  split_real_of_continuous hJ hg (continuousOn_univ.mp (hg.continuousOn isOpen_univ)) hs hmin

/-- Earned split returned to the original extended objective, retaining the admissibility
restriction. This does not silently identify it with an ambient objective subgradient. -/
theorem split_extended [FiniteDimensional ℝ E] {A : Set E} {J : E → EReal} {g : E → ℝ} {star : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hg : ConvexOn ℝ univ g) (hs : star ∈ A) (hfinite : J star ≠ ⊤)
    (hmin : ∀ x ∈ A, J star+(g star : ℝ) ≤ J x+(g x : ℝ)) :
    ∃ d : E →L[ℝ] ℝ, SubgradientOn A J star (-d) ∧ RealSubgradient g star d := by
  have hreal : ∀ x ∈ finiteDomain A J, realObjective J star+g star ≤ realObjective J x+g x := by
    intro x hx
    have hh := hmin x hx.1
    rw [← EReal.coe_toReal hfinite (hbottom star hs),← EReal.coe_toReal hx.2 (hbottom x hx.1),
      ← EReal.coe_add,← EReal.coe_add] at hh
    exact EReal.coe_le_coe_iff.mp hh
  obtain ⟨d,hd,hgsub⟩ := split_real (epigraph_objective_convex hbottom hJ) hg ⟨hs,hfinite⟩ hreal
  refine ⟨d,⟨hs,hfinite,hbottom star hs,?_⟩,hgsub⟩
  intro x hx
  by_cases ht : J x=⊤
  · rw [ht]
    exact le_top
  · rw [← EReal.coe_toReal hfinite (hbottom star hs),← EReal.coe_toReal ht (hbottom x hx),← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [ContinuousLinearMap.neg_apply,sub_eq_add_neg] using hd x ⟨hx,ht⟩

/-- Full objective/constraint/normal-cone stationarity for finite ambient convex J.
The domain qualification is automatic because J is finite everywhere. -/
theorem finite_objective_stationarity [FiniteDimensional ℝ E] {A : Set E} {J g : E → ℝ}
    {star : E} {k : E →L[ℝ] ℝ} (hA : Convex ℝ A) (hJ : ConvexOn ℝ univ J)
    (hg : ConvexOn ℝ univ g) (hs : star ∈ A)
    (hmin : ∀ x ∈ A, J star+g star ≤ J x+g x) (hk : HasFDerivAt g k star) :
    ∃ q n : E →L[ℝ] ℝ, RealSubgradient J star q ∧ NormalCone A star n ∧ q+k+n=0 := by
  have htotal : ConvexOn ℝ univ (fun x => J x+g x) := hJ.add hg
  obtain ⟨d,hd,htotalSub⟩ := split_real (convexOn_const (0 : ℝ) hA) htotal hs
    (fun x hx => by simpa using hmin x hx)
  have hnormal : NormalCone A star (-d) := by
    refine ⟨hs,?_⟩
    intro x hx
    have hh := hd x hx
    simp only [ContinuousLinearMap.neg_apply]
    linarith
  have hq : RealSubgradient J star (d-k) :=
    fun x => remove_smooth_summand hJ (mem_univ _) (fun y _ => htotalSub y) hk x (mem_univ _)
  refine ⟨d-k,-d,hq,hnormal,?_⟩
  abel

end
end SbtCosmo.Derivation.ConvexSumSplit
