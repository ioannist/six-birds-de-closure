import SbtCosmo.Derivation.ConvexSumSplit
import SbtCosmo.Derivation.NonsmoothMatrixPrice
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! Actual Schur quadratic smoothness and constructed finite-objective split stationarity. -/
namespace SbtCosmo.Derivation.SchurStationarity
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice ConvexSubgradient SchurClosurePrice
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {n m e E : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [DecidableEq m] [DecidableEq e] in
/-- Finite affine probes are genuinely smooth; no derivative hypothesis is supplied. -/
theorem affine_probe_differentiable (D : E →ᵃ[ℝ] Matrix m e ℝ) : Differentiable ℝ D := by
  let Dc : E →ᴬ[ℝ] Matrix m e ℝ := {D with cont := D.continuous_of_finiteDimensional}
  exact Dc.differentiable

omit [DecidableEq m] in
/-- The actual fixed-native support residual trace is a finite quadratic polynomial. -/
theorem schur_energy_differentiable (W : Matrix m m ℝ) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) : Differentiable ℝ (fun x => schurEnergy W L (D x)) := by
  have hD := affine_probe_differentiable D
  have hentry (i : m) (j : e) : Differentiable ℝ (fun x => D x i j) := by
    let p : Matrix m e ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j : (e → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj i : (m → e → ℝ) →L[ℝ] (e → ℝ))
    exact p.differentiable.comp hD
  simp only [schurEnergy,SbtCosmo.Adequacy.Support.residual_gram,Matrix.trace,Matrix.diag_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
  fun_prop

omit [DecidableEq m] [FiniteDimensional ℝ E] in
/-- Actual matrix trace-Lagrangian convexity is earned from the PSD trace pairing. -/
theorem trace_energy_convex {P : Matrix m m ℝ} (hP : P.PosSemidef) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) (B : Symmetric m) :
    ConvexOn ℝ univ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) := by
  have he := (affine_schur_energy_convex hP L D convex_univ).add_const (-trace (P*(B : Matrix m m ℝ)))
  change ConvexOn ℝ univ (fun x => trace (P*(SbtCosmo.Adequacy.Support.residual L (D x)-(B : Matrix m m ℝ))))
  simp only [Matrix.mul_sub,Matrix.trace_sub]
  simpa only [Pi.add_apply,sub_eq_add_neg,schurEnergy] using he

omit [DecidableEq m] in
/-- Subtracting the fixed budget preserves actual Schur smoothness. -/
theorem trace_energy_differentiable (P : Matrix m m ℝ) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) (B : Symmetric m) :
    Differentiable ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) := by
  have he := (schur_energy_differentiable P L D).sub_const (trace (P*(B : Matrix m m ℝ)))
  simpa only [Matrix.mul_sub,Matrix.trace_sub,schurEnergy] using he

/-- Original matrix price plus actual quadratic smoothness earns the full split for
finite ambient convex objectives. No stationarity, normal or objective subgradient is supplied. -/
theorem matrix_stationarity (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → ℝ} {B : Symmetric m} {star x₀ : E}
    (hA : Convex ℝ A) (hJ : ConvexOn ℝ univ J)
    (hstar : ConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef) :
    ∃ (P : Matrix m m ℝ) (q n : E →L[ℝ] ℝ), P.PosSemidef ∧
      RealSubgradient J star q ∧ NormalCone A star n ∧
      q+fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star+n=0 ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      (∀ x ∈ A, J star ≤ J x+trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) := by
  have hJE : Convex ℝ (ExtendedClosurePrice.epigraph A (fun x => (J x : EReal))) := by
    have hj := (hJ.subset (subset_univ A) hA).convex_epigraph
    simpa only [ExtendedClosurePrice.epigraph,EReal.coe_le_coe_iff] using hj
  have hstarE : ExtendedConeClosurePrice.PrimalOptimum A (fun x => (J x : EReal))
      (fun x => residual L (D x)) positive B star :=
    ⟨hstar.member,EReal.coe_ne_top _,hstar.feasible,fun x hx he => EReal.coe_le_coe_iff.mpr (hstar.optimal x hx he)⟩
  obtain ⟨P,hP,hcomp,hglob,_⟩ := NonsmoothMatrixPrice.matrix_price L D
    (fun x _ => EReal.coe_ne_bot (J x)) hJE hstarE hx₀ (EReal.coe_ne_top _) hslater
  let g : E → ℝ := fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))
  have hmin : ∀ x ∈ A, J star+g star ≤ J x+g x := by
    intro x hx
    have hh := hglob x hx
    rw [← EReal.coe_add] at hh
    have hh' := EReal.coe_le_coe_iff.mp hh
    simpa only [g,hcomp,add_zero] using hh'
  obtain ⟨q,n,hq,hn,hstation⟩ := ConvexSumSplit.finite_objective_stationarity hA hJ
    (trace_energy_convex hP L D B) hstar.member hmin ((trace_energy_differentiable P L D B) star).hasFDerivAt
  refine ⟨P,q,n,hP,hq,hn,hstation,hcomp,?_⟩
  intro x hx
  have hh := hglob x hx
  rw [← EReal.coe_add] at hh
  exact EReal.coe_le_coe_iff.mp hh

/-- Strict actual value decrease retains nonzero matrix price in the full finite-objective split. -/
theorem matrix_stationarity_nonzero (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → ℝ} {B : Symmetric m} {star x₀ : E}
    (hA : Convex ℝ A) (hJ : ConvexOn ℝ univ J)
    (hstar : ConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef)
    (hs : ∃ H : Symmetric m, positive H ∧
      ExtendedConeClosurePrice.value A (fun x => (J x : EReal)) (fun x => residual L (D x)) positive (B+H) <
        ExtendedConeClosurePrice.value A (fun x => (J x : EReal)) (fun x => residual L (D x)) positive B) :
    ∃ (P : Matrix m m ℝ) (q n : E →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      RealSubgradient J star q ∧ NormalCone A star n ∧
      q+fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star+n=0 ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := by
  obtain ⟨P,q,n,hP,hq,hn,hstation,hcomp,hglob⟩ := matrix_stationarity L D hA hJ hstar hx₀ hslater
  refine ⟨P,q,n,hP,?_,hq,hn,hstation,hcomp⟩
  intro hz
  obtain ⟨H,_,hdec⟩ := hs
  have hstarE : ExtendedConeClosurePrice.PrimalOptimum A (fun x => (J x : EReal))
      (fun x => residual L (D x)) positive B star :=
    ⟨hstar.member,EReal.coe_ne_top _,hstar.feasible,fun x hx he => EReal.coe_le_coe_iff.mpr (hstar.optimal x hx he)⟩
  rw [ExtendedConeClosurePrice.optimum_value hstarE] at hdec
  obtain ⟨_,⟨x,hx,_,rfl⟩,hcost⟩ := sInf_lt_iff.mp hdec
  have hh := hglob x hx
  rw [hz,zero_mul,trace_zero,add_zero] at hh
  exact (EReal.coe_lt_coe_iff.mp hcost).not_ge hh

/-- For genuinely extended objectives, the earned smooth constraint derivative returns
to the exact restricted-objective subgradient. Splitting ambient J from its normal
cone still requires the separate relative-interior qualification construction. -/
theorem matrix_restricted_stationarity (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (ExtendedClosurePrice.epigraph A J))
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧
      SubgradientOn A J star (-fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star) ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := by
  obtain ⟨P,hP,hcomp,hglob,_⟩ := NonsmoothMatrixPrice.matrix_price L D hbottom hJ hstar hx₀ hfinite₀ hslater
  let g : E → ℝ := fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))
  have hmin : ∀ x ∈ A, J star+(g star : ℝ) ≤ J x+(g x : ℝ) := by
    simpa only [g,hcomp,EReal.coe_zero,add_zero] using hglob
  obtain ⟨d,hd,hgd⟩ := ConvexSumSplit.split_extended hbottom hJ (trace_energy_convex hP L D B)
    hstar.member hstar.finite hmin
  have heq := smooth_real_subgradient_eq hgd ((trace_energy_differentiable P L D B) star).hasFDerivAt
  rw [heq] at hd
  exact ⟨P,hP,hd,hcomp⟩

end
end SbtCosmo.Derivation.SchurStationarity
