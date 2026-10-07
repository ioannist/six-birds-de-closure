import SbtCosmo.Derivation.RelativeSumSplit
import SbtCosmo.Derivation.ConvexSumSplit

/-! The same canonical scalar price supplies sensitivity, duality and the
qualified objective/energy/normal split. The energy may be nonsmooth. -/
namespace SbtCosmo.Derivation.ScalarPriceStationarity
noncomputable section
open Set Filter ExtendedClosurePrice ConvexSubgradient
open scoped Topology

variable {E : Type*}

/-- Reverse finite-domain return, with all toReal conversions guarded. -/
theorem certificate_real_domain_return {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p : ℝ} {star : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : DualCertificate A J energy B p star) :
    ConvexClosurePrice.DualCertificate (finiteDomain A J) (realObjective J) energy B p star := by
  refine ⟨hc.nonnegative,⟨hc.member,hc.finite⟩,hc.feasible,hc.complementarity,?_⟩
  intro x hx
  have hh := hc.global_minimum x hx.1
  rw [← EReal.coe_toReal hc.finite (hbottom star hc.member),
    ← EReal.coe_toReal hx.2 (hbottom x hx.1),← EReal.coe_add] at hh
  exact EReal.coe_le_coe_iff.mp hh

/-- Every certificate price is identified by the derivative of the actual
extended value, rather than an unrestricted toReal objective. -/
theorem certificate_price_identification {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p d lo hi : ℝ} {star : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : DualCertificate A J energy B p star) (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, value A J energy T ≠ ⊤ ∧ value A J energy T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J energy T).toReal) d B) : p = -d := by
  have heq : (fun T => (value A J energy T).toReal) =ᶠ[𝓝 B]
      ConvexClosurePrice.budgetValue (finiteDomain A J) (realObjective J) energy := by
    filter_upwards [isOpen_Ioo.mem_nhds hB] with T hT
    exact finite_value_domain_return hbottom (hfinite T hT)
  exact ConvexClosurePrice.certificate_price_identification
    (certificate_real_domain_return hbottom hc) hB
    (fun T hT => (finite_cost_guards (hfinite T hT)).1)
    (hd.congr_of_eventuallyEq heq.symm)

/-- Scalar price uniqueness does not assert uniqueness of the primal optimizer,
objective support, energy support, or normal. -/
theorem certificate_price_unique {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p q d lo hi : ℝ} {star other : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hp : DualCertificate A J energy B p star) (hq : DualCertificate A J energy B q other)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, value A J energy T ≠ ⊤ ∧ value A J energy T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J energy T).toReal) d B) : p=q := by
  rw [certificate_price_identification hbottom hp hB hfinite hd,
    certificate_price_identification hbottom hq hB hfinite hd]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Any positive earned scalar certificate supplies the full nonsmooth split
under the actual relative-interior qualification. No split output is supplied. -/
theorem certificate_stationarity {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p : ℝ} {star xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (he : ConvexOn ℝ univ energy)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hc : DualCertificate A J energy B p star) (hp : 0 < p) :
    ∃ q r η : E →L[ℝ] ℝ, Subgradient J star q ∧ RealSubgradient energy star r ∧
      NormalCone A star η ∧ q+p • r+η=0 := by
  let g : E → ℝ := fun x => p*(energy x-B)
  have hg : ConvexOn ℝ univ g := by
    simpa only [g,smul_eq_mul,sub_eq_add_neg] using
      (he.add_const (-B)).smul hp.le
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  have hmin : ∀ x ∈ A, J star+(g star : ℝ) ≤ J x+(g x : ℝ) := by
    simpa only [g,hc.complementarity,EReal.coe_zero,add_zero] using hc.global_minimum
  obtain ⟨k,hk,hgk⟩ := ConvexSumSplit.split_extended (fun x _ => hbottom x)
    hrestricted hg hc.member hc.finite hmin
  obtain ⟨q,η,hq,hη,hqη⟩ := RelativeSumSplit.split_subgradient hbottom hJ hA hC hAr hk
  let r : E →L[ℝ] ℝ := p⁻¹ • k
  have hkr : p • r=k := by simp only [r,smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
  have hr : RealSubgradient energy star r := by
    intro x
    have hh := hgk x
    have heval : p*r (x-star)=k (x-star) := by
      simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul] using
        congrArg (fun f : E →L[ℝ] ℝ => f (x-star)) hkr
    dsimp [g] at hh
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  refine ⟨q,r,η,hq,hr,hη,?_⟩
  rw [hkr]
  calc
    q+k+η=(q+η)+k := by abel
    _ = 0 := by rw [hqη,neg_add_cancel]

/-- Full scalar Theorem S: a single constructed price has actual value
sensitivity, activity, strong duality, and qualified nonsmooth stationarity.
Slater and activity need not be supplied once the local finite negative
value derivative is available. -/
theorem positive_price_stationarity {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B d lo hi : ℝ} {star xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (he : ConvexOn ℝ univ energy)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : PrimalOptimum A J energy B star) (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, value A J energy T ≠ ⊤ ∧ value A J energy T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J energy T).toReal) d B) (hs : d < 0) :
    ∃ (p : ℝ) (q r η : E →L[ℝ] ℝ), p = -d ∧ 0 < p ∧ energy star=B ∧
      DualCertificate A J energy B p star ∧ dualValue A J energy B p=value A J energy B ∧
      Subgradient J star q ∧ RealSubgradient energy star r ∧ NormalCone A star η ∧
      q+p • r+η=0 := by
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  obtain ⟨p,hp,hpos,hact,hc,hdual⟩ := positive_price_certificate (fun x _ => hbottom x)
    hrestricted (he.subset (subset_univ A) hA) hstar hB hfinite hd hs
  obtain ⟨q,r,η,hq,hr,hη,hstation⟩ := certificate_stationarity hbottom hJ hA he hC hAr hc hpos
  exact ⟨p,q,r,η,hp,hpos,hact,hc,hdual,hq,hr,hη,hstation⟩

/-- The same price specializes to the genuine energy derivative when smooth.
Only the actual energy derivative is supplied, not a stationarity functional. -/
theorem positive_price_smooth_stationarity {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B d lo hi : ℝ} {star xr : E} {k : E →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (he : ConvexOn ℝ univ energy)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : PrimalOptimum A J energy B star) (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, value A J energy T ≠ ⊤ ∧ value A J energy T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J energy T).toReal) d B) (hs : d < 0)
    (hk : HasFDerivAt energy k star) :
    ∃ (p : ℝ) (q η : E →L[ℝ] ℝ), p = -d ∧ 0 < p ∧ energy star=B ∧
      DualCertificate A J energy B p star ∧ dualValue A J energy B p=value A J energy B ∧
      Subgradient J star q ∧ NormalCone A star η ∧ q+p • k+η=0 := by
  obtain ⟨p,q,r,η,hp,hpos,hact,hc,hdual,hq,hr,hη,hstation⟩ :=
    positive_price_stationarity hbottom hJ hA he hC hAr hstar hB hfinite hd hs
  have heq := smooth_real_subgradient_eq hr hk
  subst r
  exact ⟨p,q,η,hp,hpos,hact,hc,hdual,hq,hη,hstation⟩

end
end SbtCosmo.Derivation.ScalarPriceStationarity
