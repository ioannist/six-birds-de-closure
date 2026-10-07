import SbtCosmo.Derivation.ExtendedNonsmoothConePrice
import SbtCosmo.Derivation.MatrixSlaterTopology
import SbtCosmo.Derivation.MatrixDifferential

/-! Original extended Slater duality for arbitrary Loewner-convex symmetric
matrix maps. No affine/quadratic or value-derivative restriction is imposed. -/
namespace SbtCosmo.Derivation.GeneralMatrixPrice
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice ExtendedClosurePrice
open scoped Matrix Topology Matrix.Norms.Elementwise
variable {m E : Type*} [Fintype m] [DecidableEq m]

def tracePrice (P : Matrix m m ℝ) : Symmetric m →L[ℝ] ℝ :=
  (MatrixDifferential.tracePair P).toContinuousLinearMap.comp (symmetricSubmodule m).subtypeL

omit [DecidableEq m] in
theorem tracePrice_apply (P : Matrix m m ℝ) (H : Symmetric m) :
    tracePrice P H=trace (P*(H : Matrix m m ℝ)) := rfl

/-- The earned symmetric trace representative represents the whole budget dual,
not just its pairing with the constraint at one optimizer. -/
theorem tracePrice_priceMatrix (price : Symmetric m →L[ℝ] ℝ) :
    tracePrice (priceMatrix price.toLinearMap)=price := by
  apply ContinuousLinearMap.ext
  intro H
  exact trace_representation price.toLinearMap H

variable [AddCommGroup E] [Module ℝ E]

def LoewnerConvexOn (A : Set E) (Xi : E → Symmetric m) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
    positive (a • Xi x+b • Xi y-Xi (a • x+b • y))

/-- Actual PD Slater and ordinary finite attainment construct a PSD trace price
for any Loewner-convex map and original extended objective. -/
theorem matrix_price {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hXi : LoewnerConvexOn A Xi)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊤ ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊥ := by
  have hs : B-Xi x₀ ∈ interior {H : Symmetric m | positive H} :=
    MatrixSlaterTopology.posdef_mem_interior_positive hslater
  obtain ⟨price,hp,hdual,hfinite⟩ := ExtendedNonsmoothConePrice.slater_strong_duality
    cone_laws hbottom hJ hXi hstar hx₀ hfinite₀ hs
  refine ⟨priceMatrix price.toLinearMap,price_matrix_positive price.toLinearMap hp.nonnegative,?_,?_,?_,?_⟩
  · rwa [tracePrice_priceMatrix]
  · rwa [tracePrice_priceMatrix]
  · simpa only [tracePrice_priceMatrix] using hfinite.1
  · simpa only [tracePrice_priceMatrix] using hfinite.2

/-- Strict decrease of the original complete-lattice value supplies nonzero P,
including a possible minus-infinity competing value. -/
theorem matrix_price_nonzero {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hXi : LoewnerConvexOn A Xi)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef)
    (hsensitive : ∃ H : Symmetric m, positive H ∧
      ExtendedConeClosurePrice.value A J Xi positive (B+H) <
        ExtendedConeClosurePrice.value A J Xi positive B) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊤ ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊥ := by
  obtain ⟨P,hP,hc,hdual,hfinite⟩ := matrix_price hbottom hJ hXi hstar hx₀ hfinite₀ hslater
  obtain ⟨H,_,hdec⟩ := hsensitive
  have hpne := ExtendedNonsmoothConePrice.certificate_nonzero hc hdec
  refine ⟨P,hP,?_,hc,hdual,hfinite⟩
  intro hz
  apply hpne
  apply ContinuousLinearMap.ext
  intro M
  simp only [tracePrice_apply,hz,zero_mul,trace_zero,ContinuousLinearMap.zero_apply]

omit [DecidableEq m] in
/-- The actual earned cone-positive certificate makes its trace energy convex
whenever the matrix map has a full ambient Loewner-convex extension. -/
theorem certificate_trace_energy_convex {A : Set E} {J : E → EReal}
    {Xi : E → Symmetric m} {B : Symmetric m} {P : Matrix m m ℝ} {star : E}
    (hXi : LoewnerConvexOn univ Xi)
    (hc : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star) :
    ConvexOn ℝ univ (fun x => trace (P*(Xi x : Matrix m m ℝ))) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.nonnegative _ (hXi x hx y hy a b ha hb hab)
  simp only [map_sub,map_add,map_smul,smul_eq_mul,tracePrice_apply] at hh
  simp only [smul_eq_mul]
  linarith

end
end SbtCosmo.Derivation.GeneralMatrixPrice
