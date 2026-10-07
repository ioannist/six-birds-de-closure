import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
T3 receipt for the Xi_cosmo / Schur reconciliation.

This module mechanizes the faithful positive-definite Schur core, the easy
exact-adequacy implication chain, the P-adeq positivity link under an explicit
Schur-realization congruence, and the packaged algebraic projection identity.
This module retains the positive-definite inverse convention. The separate
`SbtCosmo.Adequacy.Support` module constructs the finite real Moore-Penrose
inverse and proves the full exact-adequacy cycle, including singular native
blocks. Minimal-rewrite selection and construction of the legal energy
quotient remain outside this module; see `lean/manifests/coverage_table.md`.
-/

open Matrix
open scoped Matrix

namespace SbtCosmo.Adequacy.Reconciliation

noncomputable section

variable {n m e y z : Type*}

/-- The positive-definite Schur-complement adequacy residual for real finite blocks.

This is the R2 mechanized convention: the native block `KLL` is positive
definite, so `KLL⁻¹` is the genuine matrix inverse. The singular
Moore-Penrose-on-support case is provided separately in `Adequacy.Support`. -/
def adequacyResidual [Fintype n] [Fintype m] [DecidableEq n]
    (KLL : Matrix n n ℝ) (KLD : Matrix n m ℝ) (KDD : Matrix m m ℝ) :
    Matrix m m ℝ :=
  KDD - KLDᴴ * KLL⁻¹ * KLD

/-- Block-currency package for the faithful positive-definite T3 receipt. -/
structure BlockCurrency (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] where
  KLL : Matrix n n ℝ
  KLD : Matrix n m ℝ
  KDD : Matrix m m ℝ
  KLL_posDef : KLL.PosDef
  joint_posSemidef : (Matrix.fromBlocks KLL KLD KLDᴴ KDD).PosSemidef

namespace BlockCurrency

/-- The Schur residual attached to a `BlockCurrency`. -/
def residual [Fintype n] [Fintype m] [DecidableEq n]
    (B : BlockCurrency n m) : Matrix m m ℝ :=
  adequacyResidual B.KLL B.KLD B.KDD

end BlockCurrency

/-- The `C`-inner-product convention used for P-adeq readout operators. -/
def cInner [Fintype n] (C : Matrix n n ℝ) (x y : n → ℝ) : ℝ :=
  x ⬝ᵥ (C *ᵥ y)

/-- The `C`-adjoint of a square real matrix in the positive-definite inverse convention. -/
def cAdjoint [Fintype n] [DecidableEq n]
    (C R : Matrix n n ℝ) : Matrix n n ℝ :=
  C⁻¹ * Rᴴ * C

/-- The `C`-symmetric part of a rewrite/readout operator. -/
def symC [Fintype n] [DecidableEq n]
    (C R : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (R + cAdjoint C R)

/-- Explicit Schur-realization data for the P-adeq positivity link.

The theorem below applies only when the supplied readout symmetrization is
realized in the `C` metric: `C * symC C R = Uᴴ * Xi * U`, with `C` positive
definite and `U` invertible. Ordinary PSD of `symC C R` is not the metric
positivity condition. This is the R1/R6
scope: it is a positivity certificate, not an S-stab/no-growing-mode theorem.
-/
structure PAdeqRealization (n : Type*) [Fintype n] [DecidableEq n] where
  C : Matrix n n ℝ
  C_posDef : C.PosDef
  R : Matrix n n ℝ
  Xi : Matrix n n ℝ
  U : Matrix n n ℝ
  U_isUnit : IsUnit U
  energy_eq_congruence : C * symC C R = Uᴴ * Xi * U

/-- The native-support projector package `P_L = T_L^* (T_L T_L^*)⁻¹ T_L`.

This is only the positive-definite inverse package used in the faithful T3
core. The singular support/Moore-Penrose projector is in `Adequacy.Support`.
-/
def nativeProjector [Fintype n] [Fintype e] [DecidableEq n]
    (TL : Matrix n e ℝ) : Matrix e e ℝ :=
  TLᴴ * (TL * TLᴴ)⁻¹ * TL

/-- T3 faithful core: a PSD joint block with positive-definite native block has PSD Schur residual. -/
theorem schur_complement_psd_of_joint_psd
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {KLL : Matrix n n ℝ} {KLD : Matrix n m ℝ} {KDD : Matrix m m ℝ}
    (hKLL : KLL.PosDef)
    (hJoint : (Matrix.fromBlocks KLL KLD KLDᴴ KDD).PosSemidef) :
    (adequacyResidual KLL KLD KDD).PosSemidef := by
  classical
  letI : Invertible KLL := hKLL.isUnit.invertible
  exact (Matrix.PosDef.fromBlocks₁₁ KLD KDD hKLL).mp hJoint

/-- T3 faithful core, packaged form for block-currency records. -/
theorem adequacy_residual_psd
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (B : BlockCurrency n m) :
    B.residual.PosSemidef := by
  exact schur_complement_psd_of_joint_psd B.KLL_posDef B.joint_posSemidef

/-- R6 P-adeq link: under an explicit Schur-realization congruence, the
`C`-symmetric readout is PSD iff the Schur residual is PSD.

This is faithful only under the carried realization data `A`; it does not
assert P-adeq for arbitrary rewrite operators and it is distinct from S-stab.
-/
theorem p_adeq_iff_xi_psd
    [Fintype n] [DecidableEq n] (A : PAdeqRealization n) :
    (A.C * symC A.C A.R).PosSemidef ↔ A.Xi.PosSemidef := by
  rw [A.energy_eq_congruence]
  simpa [Matrix.star_eq_conjTranspose] using
    (A.U_isUnit.posSemidef_star_left_conjugate_iff (x := A.Xi))

/-- The matrix energy tested by P-adeq is precisely the `C` quadratic form. -/
theorem cInner_symC_eq_energy
    [Fintype n] [DecidableEq n] (C R : Matrix n n ℝ) (x : n → ℝ) :
    cInner C x (symC C R *ᵥ x) = x ⬝ᵥ ((C * symC C R) *ᵥ x) := by
  simp only [cInner, Matrix.mulVec_mulVec]

/-- An actual metric-positivity conclusion under the supplied realization. -/
theorem p_adeq_quadratic_nonneg
    [Fintype n] [DecidableEq n] (A : PAdeqRealization n)
    (hXi : A.Xi.PosSemidef) (x : n → ℝ) :
    0 ≤ cInner A.C x (symC A.C A.R *ᵥ x) := by
  rw [cInner_symC_eq_energy]
  simpa using ((p_adeq_iff_xi_psd A).mpr hXi).dotProduct_mulVec_nonneg x

/-- Packaged positive-definite projection identity:
`Xi = T_D (I - P_L) T_D^*` for the exposed finite matrix realization.

The identity is algebraic and uses the same genuine-inverse convention as
`adequacyResidual`. It does not cover the singular Moore-Penrose support case.
-/
theorem projection_identity_packaged
    [Fintype n] [Fintype m] [Fintype e]
    [DecidableEq n] [DecidableEq m] [DecidableEq e]
    (TL : Matrix n e ℝ) (TD : Matrix m e ℝ) :
    adequacyResidual (TL * TLᴴ) (TL * TDᴴ) (TD * TDᴴ) =
      TD * (1 - nativeProjector TL) * TDᴴ := by
  calc
    adequacyResidual (TL * TLᴴ) (TL * TDᴴ) (TD * TDᴴ)
        = TD * TDᴴ - (((TD * TLᴴ) * (TL * TLᴴ)⁻¹) * TL) * TDᴴ := by
          simp [adequacyResidual, Matrix.mul_assoc]
    _ = TD * (1 - nativeProjector TL) * TDᴴ := by
          simp [nativeProjector, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The joint Gram currency is PSD by construction, without a supplied PSD proof. -/
theorem joint_gram_psd
    [Fintype n] [Fintype m] [Fintype e]
    [DecidableEq n] [DecidableEq m]
    (TL : Matrix n e ℝ) (TD : Matrix m e ℝ) :
    (Matrix.fromBlocks (TL * TLᴴ) (TL * TDᴴ) (TL * TDᴴ)ᴴ
      (TD * TDᴴ)).PosSemidef := by
  let T : Matrix (Sum n m) e ℝ := fun i j => Sum.elim (fun k => TL k j) (fun k => TD k j) i
  have heq : Matrix.fromBlocks (TL * TLᴴ) (TL * TDᴴ) (TL * TDᴴ)ᴴ
      (TD * TDᴴ) = T * Tᴴ := by
    ext i j
    cases i <;> cases j <;> simp [T, Matrix.fromBlocks, Matrix.mul_apply]
  rw [heq]
  exact Matrix.posSemidef_self_mul_conjTranspose T

/-- PSD form of the packaged projection identity. The joint PSD hypothesis
is now derived from the Gram construction; only native positive definiteness
is supplied. -/
theorem projection_identity_packaged_psd
    [Fintype n] [Fintype m] [Fintype e]
    [DecidableEq n] [DecidableEq m] [DecidableEq e]
    (TL : Matrix n e ℝ) (TD : Matrix m e ℝ)
    (hKLL : (TL * TLᴴ).PosDef) :
    (TD * (1 - nativeProjector TL) * TDᴴ).PosSemidef := by
  rw [← projection_identity_packaged TL TD]
  exact schur_complement_psd_of_joint_psd hKLL (joint_gram_psd TL TD)

/-- The easy exact-adequacy chain:
`D₀ = A_* L₀` gives an explicit factorization and hence `Ker L₀ ⊆ Ker D₀`.

This theorem retains the easy implication chain. The full finite real cycle
is now proved independently in `Adequacy.Support.exact_adequacy_full`. -/
theorem exact_adequacy_easy_chain
    [Fintype e] [Fintype y] [Fintype z]
    {L₀ : Matrix y e ℝ} {D₀ : Matrix z e ℝ} {Astar : Matrix z y ℝ}
    (hFactor : D₀ = Astar * L₀) :
    (∃ A : Matrix z y ℝ, D₀ = A * L₀) ∧
      (∀ v : e → ℝ, L₀ *ᵥ v = 0 → D₀ *ᵥ v = 0) := by
  constructor
  · exact ⟨Astar, hFactor⟩
  · intro v hv
    rw [hFactor, ← Matrix.mulVec_mulVec v Astar L₀, hv, Matrix.mulVec_zero]

/-- A 1-by-1 real matrix with the single entry `a`. -/
def oneByOne (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => a

/-- Worked 1+1 block: native currency `1`, cross `1`, dissolving currency `2`.
The Schur residual is `2 - 1 * 1⁻¹ * 1 = 1`, hence nonzero. -/
theorem worked_example_residual_eq_one :
    adequacyResidual (1 : Matrix (Fin 1) (Fin 1) ℝ) (oneByOne 1) (oneByOne 2) = oneByOne 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [adequacyResidual, oneByOne, Matrix.mul_apply]

/-- The worked 1+1 Schur residual is nonzero. -/
theorem worked_example_residual_nonzero :
    adequacyResidual (1 : Matrix (Fin 1) (Fin 1) ℝ) (oneByOne 1) (oneByOne 2) ≠ 0 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [adequacyResidual, oneByOne, Matrix.mul_apply] at h00

end

end SbtCosmo.Adequacy.Reconciliation
