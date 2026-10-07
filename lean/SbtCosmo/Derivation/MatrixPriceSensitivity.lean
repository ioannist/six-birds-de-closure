import SbtCosmo.Derivation.ConePriceSensitivity
import SbtCosmo.Derivation.GeneralMatrixPrice

/-! Actual full matrix-value sensitivity identifies the entire symmetric price.
One directional readout does not identify a matrix; antisymmetric parts remain
invisible to symmetric budgets. -/
namespace SbtCosmo.Derivation.MatrixPriceSensitivity
noncomputable section
open Set Filter Matrix MatrixPriceRepresentation MatrixClosurePrice GeneralMatrixPrice ExtendedClosurePrice
open scoped Matrix Topology Matrix.Norms.Elementwise
variable {m E : Type*} [Fintype m] [DecidableEq m]

/-- Reconstruct a Hermitian matrix from its entire trace dual on symmetric budgets. -/
theorem priceMatrix_tracePrice {P : Matrix m m ℝ} (hP : P.IsHermitian) :
    priceMatrix (tracePrice P).toLinearMap=P := by
  ext i j
  have hs : P j i=P i j := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrArg (fun M => M i j) hP.eq
  change trace (P*((1/2 : ℝ) • (Matrix.single j i 1+(Matrix.single j i 1).transpose)))=P i j
  rw [Matrix.transpose_single,Matrix.mul_smul,Matrix.trace_smul,Matrix.mul_add,
    Matrix.trace_add,Matrix.trace_mul_single,Matrix.trace_mul_single]
  norm_num [hs]
  ring

/-- Equality of whole trace duals is injective on symmetric prices. -/
theorem tracePrice_injective {P Q : Matrix m m ℝ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (heq : tracePrice P=tracePrice Q) : P=Q := by
  rw [← priceMatrix_tracePrice hP,← priceMatrix_tracePrice hQ,heq]

omit [DecidableEq m] in
/-- Every original matrix trace certificate agrees with the actual full budget
derivative, with local finite original values explicitly guarded. -/
theorem certificate_price_identification {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star : E} {P : Matrix m m ℝ} {d : Symmetric m →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star)
    (hfinite : ∀ᶠ T in 𝓝 B, ExtendedConeClosurePrice.value A J Xi positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J Xi positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J Xi positive T).toReal) d B) :
    tracePrice P = -d := ConePriceSensitivity.price_identification hbottom hc hfinite hd

/-- The actual full derivative determines the PSD matrix itself, not merely one
price-weighted slack pairing or one directional readout. -/
theorem certificate_matrix_identification {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star : E} {P : Matrix m m ℝ} {d : Symmetric m →L[ℝ] ℝ}
    (hP : P.PosSemidef) (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star)
    (hfinite : ∀ᶠ T in 𝓝 B, ExtendedConeClosurePrice.value A J Xi positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J Xi positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J Xi positive T).toReal) d B) :
    P=priceMatrix (-d).toLinearMap ∧
      ∀ H : Symmetric m, trace (P*(H : Matrix m m ℝ)) = -d H := by
  have heq := certificate_price_identification hbottom hc hfinite hd
  refine ⟨?_,?_⟩
  · rw [← heq,priceMatrix_tracePrice hP.1]
  · intro H
    exact congrArg (fun p : Symmetric m →L[ℝ] ℝ => p H) heq

/-- Every PSD matrix certificate at the same budget has the same matrix price,
even at a different optimizer. No primal/support uniqueness is claimed. -/
theorem certificate_matrix_unique {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star other : E} {P Q : Matrix m m ℝ} {d : Symmetric m →L[ℝ] ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star)
    (ho : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice Q) other)
    (hfinite : ∀ᶠ T in 𝓝 B, ExtendedConeClosurePrice.value A J Xi positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J Xi positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J Xi positive T).toReal) d B) : P=Q := by
  exact tracePrice_injective hP.1 hQ.1 (ConePriceSensitivity.price_unique hbottom hc ho hfinite hd)

variable [AddCommGroup E] [Module ℝ E]

omit [DecidableEq m] in
/-- PD Slater earns local extended finiteness before the original value
derivative identifies the whole actual trace dual. -/
theorem slater_price_identification {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ : E} {P : Matrix m m ℝ} {d : Symmetric m →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hXi : LoewnerConvexOn A Xi)
    (hc : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J Xi positive T).toReal) d B) :
    tracePrice P=-d :=
  ConePriceSensitivity.slater_price_identification cone_laws hbottom hJ hXi hc hx₀ hfinite₀
    (MatrixSlaterTopology.posdef_mem_interior_positive hslater) hd

end
end SbtCosmo.Derivation.MatrixPriceSensitivity
