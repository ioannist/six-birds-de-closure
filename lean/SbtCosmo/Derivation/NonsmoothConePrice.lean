import SbtCosmo.Derivation.ConeClosurePrice
import SbtCosmo.Derivation.ConvexValueSupport

/-! Derive actual value convexity and a global conic price without a value derivative. -/
namespace SbtCosmo.Derivation.NonsmoothConePrice
noncomputable section
open Set Filter ConeClosurePrice
open scoped Topology
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Approximate feasible costs earn convexity of the actual guarded infimum. -/
theorem value_convex {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {U : Set F} (hc : ConeLaws positive) (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hU : Convex ℝ U)
    (hfinite : ∀ T ∈ U, (feasibleCosts A J energy positive T).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive T)) :
    ConvexOn ℝ U (value A J energy positive) := by
  refine ⟨hU, ?_⟩
  intro T hT S hS a b ha hb hab
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨_, ⟨x,hx,hxf,rfl⟩, hxc⟩ := exists_lt_of_csInf_lt (hfinite T hT).1
    (show value A J energy positive T < value A J energy positive T+ε by linarith)
  obtain ⟨_, ⟨y,hy,hyf,rfl⟩, hyc⟩ := exists_lt_of_csInf_lt (hfinite S hS).1
    (show value A J energy positive S < value A J energy positive S+ε by linarith)
  have hm := hJ.1 hx hy ha hb hab
  have hp : positive (a • T+b • S-energy (a • x+b • y)) := by
    have hh := hc.add (hc.add (hc.smul ha hxf) (hc.smul hb hyf))
      (he x hx y hy a b ha hb hab)
    convert hh using 1
    module
  have hv := value_le_candidate (hfinite _ (hU hT hS ha hb hab)).2 hm hp
  have hj := hJ.2 hx hy ha hb hab
  simp only [smul_eq_mul] at *
  have hh : a*J x+b*J y ≤ a*(value A J energy positive T+ε)+b*(value A J energy positive S+ε) :=
    add_le_add (mul_le_mul_of_nonneg_left hxc.le ha) (mul_le_mul_of_nonneg_left hyc.le hb)
  have hsum : (a+b)*ε=ε := by rw [hab, one_mul]
  nlinarith only [hv, hj, hh, hsum]

omit [AddCommGroup E] [Module ℝ E] in
/-- A positive cone direction locally increases the budget; any support has nonpositive slope. -/
theorem support_nonpositive {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {U : Set F} {B : F} {star : E} {d : F →L[ℝ] ℝ}
    (hc : ConeLaws positive) (hstar : PrimalOptimum A J energy positive B star)
    (hU : IsOpen U) (hB : B ∈ U)
    (hfinite : ∀ T ∈ U, BddBelow (feasibleCosts A J energy positive T))
    (hsupport : ∀ T ∈ U, value A J energy positive B+d (T-B) ≤ value A J energy positive T) :
    ∀ H, positive H → d H ≤ 0 := by
  intro H hH
  have ht : Tendsto (fun t : ℝ => B+t • H) (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    have hcont : Continuous (fun t : ℝ => B+t • H) := by fun_prop
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hnear := ht.eventually (hU.mem_nhds hB)
  obtain ⟨t, hT, ht0⟩ := (hnear.and self_mem_nhdsWithin).exists
  have hp : positive (B+t • H-energy star) := by
    have hh := hc.add hstar.feasible (hc.smul ht0.le hH)
    convert hh using 1
    abel
  have hv := value_le_candidate (hfinite _ hT) hstar.member hp
  have hd := hsupport _ hT
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, optimum_value hstar] at hd hv
  exact nonpos_of_mul_nonpos_right (by linarith : t*d H ≤ 0) ht0

/-- Mix the actual optimizer with every original point to return local support globally. -/
theorem support_global {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {U : Set F} {B : F} {star : E} {d : F →L[ℝ] ℝ}
    (hc : ConeLaws positive) (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star) (hU : IsOpen U) (hB : B ∈ U)
    (hfinite : ∀ T ∈ U, BddBelow (feasibleCosts A J energy positive T))
    (hsupport : ∀ T ∈ U, value A J energy positive B+d (T-B) ≤ value A J energy positive T) :
    ∀ x ∈ A, J star+d (energy x-B) ≤ J x := by
  intro x hx
  let gap := energy x-B
  have ht : Tendsto (fun t : ℝ => B+t • gap) (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    have hcont : Continuous (fun t : ℝ => B+t • gap) := by fun_prop
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hone : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨hT,ht1⟩, ht0⟩ := ((ht.eventually (hU.mem_nhds hB)).and hone |>.and self_mem_nhdsWithin).exists
  have ha : 0 ≤ 1-t := by linarith
  have hab : 1-t+t=(1 : ℝ) := by ring
  have hm := hJ.1 hstar.member hx ha ht0.le hab
  have hp : positive (B+t • gap-energy ((1-t) • star+t • x)) := by
    have hh := hc.add (hc.smul ha hstar.feasible) (he star hstar.member x hx (1-t) t ha ht0.le hab)
    convert hh using 1
    dsimp [gap]
    module
  have hv := value_le_candidate (hfinite _ hT) hm hp
  have hj := hJ.2 hstar.member hx ha ht0.le hab
  have hd := hsupport _ hT
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, optimum_value hstar] at hd hv hj
  have hh : t*(J star+d gap-J x) ≤ 0 := by nlinarith
  have hh' := nonpos_of_mul_nonpos_right hh ht0
  dsimp [gap] at hh'
  linarith

/-- Local actual finite costs and finite-dimensional budgets earn a dual certificate,
without any derivative, supplied support, complementarity or duality assumption. -/
theorem price_certificate [FiniteDimensional ℝ F]
    {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop} {B : F} {star : E}
    (hc : ConeLaws positive) (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B, (feasibleCosts A J energy positive T).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive T)) :
    ∃ price : F →L[ℝ] ℝ, DualCertificate A J energy positive B price star := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hfinite
  have hconv := value_convex hc hJ he (convex_ball B r) (fun T hT => hball hT)
  obtain ⟨d,hd⟩ := ConvexValueSupport.supporting_functional Metric.isOpen_ball hconv (Metric.mem_ball_self hr)
  have hbb : ∀ T ∈ Metric.ball B r, BddBelow (feasibleCosts A J energy positive T) :=
    fun _ hT => (hball hT).2
  have hpos := support_nonpositive hc hstar Metric.isOpen_ball (Metric.mem_ball_self hr) hbb hd
  have hglob := support_global hc hJ he hstar Metric.isOpen_ball (Metric.mem_ball_self hr) hbb hd
  refine ⟨-d, ⟨fun H hH => by simpa using neg_nonneg.mpr (hpos H hH), hstar.member, hstar.feasible, ?_, ?_⟩⟩
  · have h1 := hglob star hstar.member
    have h2 := hpos (B-energy star) hstar.feasible
    have heq : d (B-energy star) = -d (energy star-B) := by rw [← neg_sub, map_neg]
    simp only [ContinuousLinearMap.neg_apply]
    rw [heq] at h2
    linarith
  · intro x hx
    have hh := hglob x hx
    simp only [ContinuousLinearMap.neg_apply]
    linarith

/-- An interior Slater slack and ordinary attained optimum earn nonempty costs and a
uniform lower bound near the budget, by mixing with the strict feasible point. -/
theorem slater_local_finiteness
    {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop} {B : F} {star x₀ : E}
    (hc : ConeLaws positive) (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star) (hx₀ : x₀ ∈ A)
    (hslater : B-energy x₀ ∈ interior {H : F | positive H}) :
    ∀ᶠ T in 𝓝 B, (feasibleCosts A J energy positive T).Nonempty ∧
      BddBelow (feasibleCosts A J energy positive T) := by
  have hn := mem_interior_iff_mem_nhds.mp hslater
  have hp : ∀ᶠ T in 𝓝 B, positive (T-energy x₀) :=
    ((continuous_id.sub continuous_const).continuousAt (x := B)).tendsto.eventually hn
  have hm : ∀ᶠ T in 𝓝 B, positive ((B-energy x₀)+(B-T)) := by
    have hcont : Continuous (fun T : F => (B-energy x₀)+(B-T)) := by fun_prop
    have ht : Tendsto (fun T : F => (B-energy x₀)+(B-T)) (𝓝 B) (𝓝 (B-energy x₀)) := by
      simpa only [sub_self, add_zero] using (hcont.continuousAt (x := B)).tendsto
    exact ht.eventually hn
  filter_upwards [hp,hm] with T hT hminus
  refine ⟨⟨J x₀,x₀,hx₀,hT,rfl⟩, ⟨2*J star-J x₀, ?_⟩⟩
  rintro r ⟨x,hx,hxf,rfl⟩
  have hh : (0 : ℝ) ≤ 1/2 := by norm_num
  have hsum : (1/2 : ℝ)+1/2=1 := by norm_num
  have hxmix := hJ.1 hx hx₀ hh hh hsum
  have hmix : positive (B-energy ((1/2 : ℝ) • x+(1/2 : ℝ) • x₀)) := by
    have hpos := hc.add (hc.add (hc.smul hh hxf) (hc.smul hh hminus))
      (he x hx x₀ hx₀ (1/2) (1/2) hh hh hsum)
    convert hpos using 1
    module
  have hopt := hstar.optimal _ hxmix hmix
  have hj := hJ.2 hx hx₀ hh hh hsum
  simp only [smul_eq_mul] at hj
  linarith

/-- Slater supplies local finiteness; no value derivative or local-value guard is supplied. -/
theorem slater_price_certificate [FiniteDimensional ℝ F]
    {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop} {B : F} {star x₀ : E}
    (hc : ConeLaws positive) (hJ : ConvexOn ℝ A J)
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star) (hx₀ : x₀ ∈ A)
    (hslater : B-energy x₀ ∈ interior {H : F | positive H}) :
    ∃ price : F →L[ℝ] ℝ, DualCertificate A J energy positive B price star :=
  price_certificate hc hJ he hstar (slater_local_finiteness hc hJ he hstar hx₀ hslater)

omit [AddCommGroup E] [Module ℝ E] in
/-- Every constructed certificate supports the actual value at every nonempty budget.
The lower bound itself earns boundedness below; no real fallback infimum is used. -/
theorem certificate_value_support {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B T : F} {star : E} {price : F →L[ℝ] ℝ}
    (h : DualCertificate A J energy positive B price star)
    (hT : (feasibleCosts A J energy positive T).Nonempty) :
    value A J energy positive B-price (T-B) ≤ value A J energy positive T := by
  rw [optimum_value (certificate_primal_optimum h)]
  apply le_csInf hT
  rintro r ⟨x,hx,hf,rfl⟩
  have hh := h.global_minimum x hx
  have hp := h.nonnegative (T-energy x) hf
  have heq : price (T-energy x)=price (T-B)-price (energy x-B) := by
    simp only [map_sub]
    ring
  rw [heq] at hp
  linarith

omit [AddCommGroup E] [Module ℝ E] in
/-- Strict decrease of the actual value earns a strictly positive price evaluation. -/
theorem certificate_strict_price {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B T : F} {star : E} {price : F →L[ℝ] ℝ}
    (h : DualCertificate A J energy positive B price star)
    (hT : (feasibleCosts A J energy positive T).Nonempty)
    (hdecrease : value A J energy positive T < value A J energy positive B) : 0 < price (T-B) := by
  have hh := certificate_value_support h hT
  linarith

omit [AddCommGroup E] [Module ℝ E] in
/-- A strictly lower actual value at any nonempty competing budget excludes a zero price. -/
theorem certificate_nonzero {A : Set E} {J : E → ℝ} {energy : E → F} {positive : F → Prop}
    {B T : F} {star : E} {price : F →L[ℝ] ℝ}
    (h : DualCertificate A J energy positive B price star)
    (hT : (feasibleCosts A J energy positive T).Nonempty)
    (hdecrease : value A J energy positive T < value A J energy positive B) : price ≠ 0 := by
  intro hz
  have hopt := optimum_value (certificate_primal_optimum h)
  obtain ⟨_, ⟨x,hx,_,rfl⟩, hxc⟩ := exists_lt_of_csInf_lt hT (by rwa [hopt] at hdecrease)
  have hh := h.global_minimum x hx
  rw [hz, ContinuousLinearMap.zero_apply, add_zero] at hh
  linarith

end
end SbtCosmo.Derivation.NonsmoothConePrice
