import SbtCosmo.Derivation.NonsmoothConePrice

/-! Equality perturbations: actual bounded-cost witnesses and an ordinary attained
minimum earn guarded infima and support. No value/support premise is supplied. -/
namespace SbtCosmo.Derivation.RelativeEqualitySupport
noncomputable section
open Set Filter ConeClosurePrice
open scoped Topology
variable {X F : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [AddCommGroup X] [Module ℝ X] in
theorem equality_cone_laws : ConeLaws (fun w : F => w=0) := by
  constructor
  · rfl
  · intro x y hx hy; rw [hx,hy,add_zero]
  · intro a x _ hx; rw [hx,smul_zero]

/-- Midpoint mixing with a bounded-cost opposite witness earns a uniform lower
bound on every candidate cost near zero. -/
theorem local_finiteness {T : Set X} {f : X → ℝ} {star : X} {M : ℝ}
    (hf : ConvexOn ℝ T f) (energy : X →ₗ[ℝ] F)
    (hmin : ∀ z ∈ T, energy z=0 → f star ≤ f z)
    (hupper : ∀ᶠ w in 𝓝 (0 : F), ∃ z ∈ T, energy z=w ∧ f z ≤ M) :
    ∀ᶠ w in 𝓝 (0 : F),
      (feasibleCosts T f energy (fun w => w=0) w).Nonempty ∧
      BddBelow (feasibleCosts T f energy (fun w => w=0) w) := by
  have hminus : ∀ᶠ w in 𝓝 (0 : F), ∃ z ∈ T, energy z= -w ∧ f z ≤ M := by
    have ht : Tendsto (fun w : F => -w) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0 : F))).tendsto
    exact ht.eventually hupper
  filter_upwards [hupper,hminus] with w hw hm
  obtain ⟨z,hz,hez,_⟩ := hw
  obtain ⟨v,hv,hev,hfv⟩ := hm
  refine ⟨⟨f z,z,hz,by simp [hez],rfl⟩,⟨2*f star-M,?_⟩⟩
  rintro r ⟨u,hu,heu,rfl⟩
  have heu' : energy u=w := (sub_eq_zero.mp heu).symm
  have hh : (0 : ℝ) ≤ 1/2 := by norm_num
  have hab : (1/2 : ℝ)+1/2=1 := by norm_num
  have hmix := hf.1 hu hv hh hh hab
  have hemix : energy ((1/2 : ℝ) • u+(1/2 : ℝ) • v)=0 := by
    rw [map_add,map_smul,map_smul,heu',hev,smul_neg,add_neg_cancel]
  have hopt := hmin _ hmix hemix
  have hconv := hf.2 hu hv hh hh hab
  simp only [smul_eq_mul] at hconv
  linarith

/-- The actual equality-constrained value supplies a support on the budget space.
The value infimum guards are constructed by the previous midpoint argument. -/
theorem supporting_functional [FiniteDimensional ℝ F]
    {T : Set X} {f : X → ℝ} {star : X} {M : ℝ}
    (hf : ConvexOn ℝ T f) (energy : X →ₗ[ℝ] F) (hs : star ∈ T)
    (he : energy star=0) (hmin : ∀ z ∈ T, energy z=0 → f star ≤ f z)
    (hupper : ∀ᶠ w in 𝓝 (0 : F), ∃ z ∈ T, energy z=w ∧ f z ≤ M) :
    ∃ d : F →L[ℝ] ℝ, ∀ z ∈ T, f star+d (energy z) ≤ f z := by
  have hstar : PrimalOptimum T f energy (fun w => w=0) 0 star := by
    refine ⟨hs,by simp [he],?_⟩
    intro z hz hzero
    exact hmin z hz (by simpa using hzero)
  have hlinear : ∀ x ∈ T, ∀ y ∈ T, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a • energy x+b • energy y-energy (a • x+b • y)=0 := by
    intro x _ y _ a b _ _ _
    simp
  obtain ⟨price,hprice⟩ := NonsmoothConePrice.price_certificate equality_cone_laws hf
    hlinear hstar (local_finiteness hf energy hmin hupper)
  refine ⟨-price,?_⟩
  intro z hz
  have hh := hprice.global_minimum z hz
  simp only [ContinuousLinearMap.neg_apply]
  simp only [sub_zero] at hh
  linarith

end
end SbtCosmo.Derivation.RelativeEqualitySupport
