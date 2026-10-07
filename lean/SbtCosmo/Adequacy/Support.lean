import SbtCosmo.Adequacy.Reconciliation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Matrix.Spectrum

/-!
Finite real support calculus without a positive-definite native Gram block.
The generalized inverse is constructed from the Hermitian spectral theorem;
no inverse or zero-residual conclusion is assumed in a structure field.
-/
namespace SbtCosmo.Adequacy.Support

noncomputable section

open Matrix
open scoped Matrix

variable {n m e : Type*} [Fintype n] [Fintype e]
  [DecidableEq n] [DecidableEq e]

def spectralInverse {K : Matrix n n ℝ} (hK : K.IsHermitian) : Matrix n n ℝ :=
  Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hK.eigenvectorUnitary
    (diagonal (fun i => (hK.eigenvalues i)⁻¹))

theorem spectralInverse_inner {K : Matrix n n ℝ} (hK : K.IsHermitian) :
    K * spectralInverse hK * K = K := by
  conv_lhs => lhs; lhs; rw [hK.spectral_theorem]
  conv_lhs => rhs; rw [hK.spectral_theorem]
  conv_rhs => rw [hK.spectral_theorem]
  unfold spectralInverse
  simp only [← map_mul, RCLike.ofReal_real_eq_id, Function.comp_def, id_eq,
    diagonal_mul_diagonal]
  congr 2
  funext i
  by_cases h : hK.eigenvalues i = 0
  · simp [h]
  · field_simp

theorem spectralInverse_hermitian {K : Matrix n n ℝ} (hK : K.IsHermitian) :
    (spectralInverse hK).IsHermitian := by
  change star (spectralInverse hK) = spectralInverse hK
  unfold spectralInverse
  rw [← map_star]
  congr 1
  simp [Matrix.star_eq_conjTranspose]

theorem spectralInverse_outer {K : Matrix n n ℝ} (hK : K.IsHermitian) :
    spectralInverse hK * K * spectralInverse hK = spectralInverse hK := by
  conv_lhs => lhs; rhs; rw [hK.spectral_theorem]
  unfold spectralInverse
  simp only [← map_mul, RCLike.ofReal_real_eq_id, Function.comp_def, id_eq,
    diagonal_mul_diagonal]
  congr 2
  funext i
  by_cases h : hK.eigenvalues i = 0
  · simp [h]
  · field_simp

theorem spectralInverse_commutes {K : Matrix n n ℝ} (hK : K.IsHermitian) :
    K * spectralInverse hK = spectralInverse hK * K := by
  conv_lhs => lhs; rw [hK.spectral_theorem]
  conv_rhs => rhs; rw [hK.spectral_theorem]
  unfold spectralInverse
  simp only [← map_mul, RCLike.ofReal_real_eq_id, Function.comp_def, id_eq,
    diagonal_mul_diagonal]
  congr 2
  funext i
  ring

theorem spectralInverse_penrose {K : Matrix n n ℝ} (hK : K.IsHermitian) :
    K * spectralInverse hK * K = K ∧
      spectralInverse hK * K * spectralInverse hK = spectralInverse hK ∧
      (K * spectralInverse hK).IsHermitian ∧
      (spectralInverse hK * K).IsHermitian := by
  have hprod : (K * spectralInverse hK).IsHermitian := by
    change (K * spectralInverse hK)ᴴ = K * spectralInverse hK
    rw [conjTranspose_mul, (spectralInverse_hermitian hK).eq, hK.eq,
      ← spectralInverse_commutes hK]
  exact ⟨spectralInverse_inner hK, spectralInverse_outer hK, hprod,
    by simpa only [spectralInverse_commutes hK] using hprod⟩

/-- Four Penrose identities uniquely determine the constructed inverse. -/
theorem spectralInverse_unique {K H : Matrix n n ℝ} (hK : K.IsHermitian)
    (hinner : K * H * K = K) (houter : H * K * H = H)
    (hKH : (K * H).IsHermitian) (hHK : (H * K).IsHermitian) :
    H = spectralInverse hK := by
  let G := spectralInverse hK
  obtain ⟨hginner, hgouter, hKG, hGK⟩ := spectralInverse_penrose hK
  have h1 : (K * G) * (K * H) = K * H := by
    simpa only [← Matrix.mul_assoc] using congrArg (fun T => T * H) hginner
  have h2 : (K * H) * (K * G) = K * G := by
    simpa only [← Matrix.mul_assoc] using congrArg (fun T => T * G) hinner
  have h3 : (K * H) * (K * G) = K * H := by
    calc
      (K * H) * (K * G) = ((K * G) * (K * H))ᴴ := by
        rw [conjTranspose_mul, hKH.eq, show (K * G)ᴴ = K * G from hKG.eq]
      _ = K * H := by rw [h1, hKH.eq]
  have heqleft : K * H = K * G := h3.symm.trans h2
  have h4 : (G * K) * (H * K) = G * K := by
    simpa only [Matrix.mul_assoc] using congrArg (fun T => G * T) hinner
  have h5 : (H * K) * (G * K) = H * K := by
    simpa only [Matrix.mul_assoc] using congrArg (fun T => H * T) hginner
  have h6 : (H * K) * (G * K) = G * K := by
    calc
      (H * K) * (G * K) = ((G * K) * (H * K))ᴴ := by
        rw [conjTranspose_mul, hHK.eq, show (G * K)ᴴ = G * K from hGK.eq]
      _ = G * K := by rw [h4, show (G * K)ᴴ = G * K from hGK.eq]
  have heqright : H * K = G * K := h5.symm.trans h6
  calc
    H = (H * K) * H := houter.symm
    _ = (G * K) * H := by rw [heqright]
    _ = G * (K * G) := by rw [Matrix.mul_assoc, heqleft]
    _ = G := by simpa only [← Matrix.mul_assoc] using hgouter

theorem spectralInverse_eq_inverse {K : Matrix n n ℝ} (hK : K.IsHermitian)
    (hu : IsUnit K) : spectralInverse hK = K⁻¹ := by
  letI : Invertible K := hu.invertible
  have h := congrArg (fun T => K⁻¹ * T * K⁻¹) (spectralInverse_inner hK)
  simp only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one] at h
  simpa only [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul] using h

def gramInverse (L : Matrix n e ℝ) : Matrix n n ℝ :=
  spectralInverse (isHermitian_mul_conjTranspose_self L)

def projector (L : Matrix n e ℝ) : Matrix e e ℝ := Lᴴ * gramInverse L * L

def optimalFactor (L : Matrix n e ℝ) (D : Matrix m e ℝ) : Matrix m n ℝ :=
  D * Lᴴ * gramInverse L

def residual (L : Matrix n e ℝ) (D : Matrix m e ℝ) : Matrix m m ℝ :=
  D * Dᴴ - (D * Lᴴ) * gramInverse L * (L * Dᴴ)

omit [DecidableEq e] in
/-- The constructed inverse fixes the actual native range, including singular
Gram blocks. This is derived from KGK=K and the Gram null-space identity. -/
theorem gramInverse_range (L : Matrix n e ℝ) :
    (L * Lᴴ) * gramInverse L * L = L := by
  have hinner : (L * Lᴴ) * gramInverse L * (L * Lᴴ) = L * Lᴴ :=
    spectralInverse_inner (isHermitian_mul_conjTranspose_self L)
  have hz : (L * Lᴴ) * (gramInverse L * (L * Lᴴ) - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hinner, Matrix.mul_one, sub_self]
  have hnull := (Matrix.self_mul_conjTranspose_mul_eq_zero L
    (gramInverse L * (L * Lᴴ) - 1)).mp hz
  have ht := congrArg Matrix.conjTranspose hnull
  have hg : (gramInverse L)ᴴ = gramInverse L :=
    (spectralInverse_hermitian (isHermitian_mul_conjTranspose_self L)).eq
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hg, conjTranspose_zero] at ht
  simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, Matrix.mul_assoc] using ht

omit [DecidableEq e] in
theorem projector_hermitian (L : Matrix n e ℝ) : (projector L).IsHermitian := by
  exact isHermitian_conjTranspose_mul_mul L
    (spectralInverse_hermitian (isHermitian_mul_conjTranspose_self L))

omit [DecidableEq e] in
theorem native_projected (L : Matrix n e ℝ) : L * projector L = L := by
  simpa only [projector, Matrix.mul_assoc] using gramInverse_range L

omit [DecidableEq e] in
theorem projector_idempotent (L : Matrix n e ℝ) :
    projector L * projector L = projector L := by
  calc
    projector L * projector L = (Lᴴ * gramInverse L) * (L * projector L) := by
      simp only [projector, Matrix.mul_assoc]
    _ = projector L := by rw [native_projected]; rfl

theorem complement_hermitian (L : Matrix n e ℝ) : (1 - projector L).IsHermitian := by
  exact Matrix.isHermitian_one.sub (projector_hermitian L)

theorem complement_idempotent (L : Matrix n e ℝ) :
    (1 - projector L) * (1 - projector L) = 1 - projector L := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, projector_idempotent]
  abel

theorem native_complement_zero (L : Matrix n e ℝ) : L * (1 - projector L) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, native_projected, sub_self]

theorem residual_projection (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D = D * (1 - projector L) * Dᴴ := by
  simp only [residual, projector, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

omit [DecidableEq e] in
/-- Exact compatibility with the already mechanized positive-definite block
convention; the support extension changes no nonsingular residual. -/
theorem residual_eq_positiveDefinite [Fintype m] (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (hK : (L * Lᴴ).PosDef) :
    residual L D = SbtCosmo.Adequacy.Reconciliation.adequacyResidual
      (L * Lᴴ) (L * Dᴴ) (D * Dᴴ) := by
  have hinv : gramInverse L = (L * Lᴴ)⁻¹ :=
    spectralInverse_eq_inverse (isHermitian_mul_conjTranspose_self L) hK.isUnit
  simp only [residual, SbtCosmo.Adequacy.Reconciliation.adequacyResidual, hinv,
    conjTranspose_mul, conjTranspose_conjTranspose]

/-- The singular-support Schur residual is a Gram matrix of the actual blind
component, rather than a positivity conclusion carried as a premise. -/
theorem residual_gram (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D = (D * (1 - projector L)) * (D * (1 - projector L))ᴴ := by
  rw [residual_projection]
  calc
    D * (1 - projector L) * Dᴴ =
        D * ((1 - projector L) * (1 - projector L)) * Dᴴ := by
      rw [complement_idempotent]
    _ = (D * (1 - projector L)) * (D * (1 - projector L))ᴴ := by
      simp only [conjTranspose_mul, (complement_hermitian L).eq, Matrix.mul_assoc]

theorem residual_psd [Fintype m] (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    (residual L D).PosSemidef := by
  rw [residual_gram]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem residual_zero_iff_optimal_factor (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D = 0 ↔ D = optimalFactor L D * L := by
  rw [residual_gram, self_mul_conjTranspose_eq_zero, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  simp only [optimalFactor, projector, Matrix.mul_assoc]

theorem residual_zero_iff_kernel (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D = 0 ↔ (∀ v : e → ℝ, L *ᵥ v = 0 → D *ᵥ v = 0) := by
  constructor
  · intro h v hv
    rw [(residual_zero_iff_optimal_factor L D).mp h,
      ← mulVec_mulVec, hv, mulVec_zero]
  · intro h
    have hz : D * (1 - projector L) = 0 := by
      have hvec : ∀ v : e → ℝ, (D * (1 - projector L)) *ᵥ v = 0 := by
        intro v
        rw [← mulVec_mulVec]
        apply h
        rw [mulVec_mulVec, native_complement_zero, zero_mulVec]
      ext i j
      have hij := congrFun (hvec (Pi.single j 1)) i
      simpa only [mulVec_single_one, Pi.zero_apply, Matrix.zero_apply] using hij
    rw [residual_gram, hz, Matrix.zero_mul]

theorem residual_zero_iff_factor (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D = 0 ↔ ∃ A : Matrix m n ℝ, D = A * L := by
  constructor
  · intro h
    exact ⟨optimalFactor L D, (residual_zero_iff_optimal_factor L D).mp h⟩
  · rintro ⟨A, hA⟩
    apply (residual_zero_iff_kernel L D).mpr
    intro v hv
    rw [hA, ← mulVec_mulVec, hv, mulVec_zero]

/-- All four exact-adequacy statements, for arbitrary finite real native rank.
No positive-definite Gram assumption, factorization hypothesis or zero-residual
field is required. Inputs are the actual two whitened probe matrices. -/
theorem exact_adequacy_full (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    (residual L D = 0 ↔ D = optimalFactor L D * L) ∧
      (residual L D = 0 ↔ ∃ A : Matrix m n ℝ, D = A * L) ∧
      (residual L D = 0 ↔ ∀ v : e → ℝ, L *ᵥ v = 0 → D *ᵥ v = 0) := by
  exact ⟨residual_zero_iff_optimal_factor L D, residual_zero_iff_factor L D,
    residual_zero_iff_kernel L D⟩

theorem error_native_orthogonal (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    (D - optimalFactor L D * L) * Lᴴ = 0 := by
  have hp : projector L * Lᴴ = Lᴴ := by
    have ht := congrArg Matrix.conjTranspose (native_projected L)
    simpa only [conjTranspose_mul, (projector_hermitian L).eq] using ht
  have he : D - optimalFactor L D * L = D * (1 - projector L) := by
    simp only [optimalFactor, projector, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  rw [he, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hp, sub_self, Matrix.mul_zero]

theorem residual_error_gram (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D = (D - optimalFactor L D * L) * (D - optimalFactor L D * L)ᴴ := by
  simpa only [Matrix.mul_sub, Matrix.mul_one, optimalFactor, projector, Matrix.mul_assoc]
    using residual_gram L D

/-- The full optimal-residual identity, including singular native blocks.
Every other linear factor adds a positive semidefinite Gram currency. -/
theorem optimal_residual_identity (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (A : Matrix m n ℝ) :
    (D - A * L) * (D - A * L)ᴴ = residual L D +
      (A - optimalFactor L D) * (L * Lᴴ) * (A - optimalFactor L D)ᴴ := by
  let E := D - optimalFactor L D * L
  let F := (A - optimalFactor L D) * L
  have hdecomp : D - A * L = E - F := by
    dsimp [E, F]
    rw [Matrix.sub_mul]
    abel
  have hEF : E * Fᴴ = 0 := by
    dsimp [E, F]
    rw [conjTranspose_mul, ← Matrix.mul_assoc, error_native_orthogonal, Matrix.zero_mul]
  have hFE : F * Eᴴ = 0 := by
    have ht := congrArg Matrix.conjTranspose hEF
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using ht
  have hEE : E * Eᴴ = residual L D := (residual_error_gram L D).symm
  rw [hdecomp]
  calc
    (E - F) * (E - F)ᴴ = E * Eᴴ + F * Fᴴ := by
      rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hEF, hFE]
      abel
    _ = residual L D +
        (A - optimalFactor L D) * (L * Lᴴ) * (A - optimalFactor L D)ᴴ := by
      rw [hEE]
      dsimp [F]
      simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem optimal_residual_loewner [Fintype m] (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (A : Matrix m n ℝ) :
    ((D - A * L) * (D - A * L)ᴴ - residual L D).PosSemidef := by
  rw [optimal_residual_identity, add_sub_cancel_left]
  have hgram : (A - optimalFactor L D) * (L * Lᴴ) * (A - optimalFactor L D)ᴴ =
      ((A - optimalFactor L D) * L) * ((A - optimalFactor L D) * L)ᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hgram]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem residual_nonzero_iff_blind_witness (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    residual L D ≠ 0 ↔ ∃ v : e → ℝ, L *ᵥ v = 0 ∧ D *ᵥ v ≠ 0 := by
  classical
  simp only [ne_eq, residual_zero_iff_kernel, not_forall, exists_prop]

omit [DecidableEq e] in
theorem projector_kernel (L : Matrix n e ℝ) (v : e → ℝ) :
    projector L *ᵥ v = 0 ↔ L *ᵥ v = 0 := by
  constructor
  · intro h
    have he := congrArg (fun P => P *ᵥ v) (native_projected L)
    change (L * projector L) *ᵥ v = L *ᵥ v at he
    rw [← mulVec_mulVec, h, mulVec_zero] at he
    exact he.symm
  · intro h
    simp only [projector, ← mulVec_mulVec, h, mulVec_zero]

omit [DecidableEq e] in
theorem projector_range (L : Matrix n e ℝ) (w : e → ℝ) :
    (∃ v : e → ℝ, projector L *ᵥ v = w) ↔ ∃ y : n → ℝ, Lᴴ *ᵥ y = w := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨gramInverse L *ᵥ (L *ᵥ v), ?_⟩
    simpa only [projector, ← mulVec_mulVec] using hv
  · rintro ⟨y, hy⟩
    refine ⟨Lᴴ *ᵥ y, ?_⟩
    have hp : projector L * Lᴴ = Lᴴ := by
      have ht := congrArg Matrix.conjTranspose (native_projected L)
      simpa only [conjTranspose_mul, (projector_hermitian L).eq] using ht
    rw [mulVec_mulVec, hp, hy]

/-- Whitened exact adequacy returns to the original probes under an actual
invertible whitening map. No invertibility of the native probe is required. -/
theorem whitened_exact_adequacy (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (B : Matrix e e ℝ) (hB : IsUnit B) :
    residual (L * B) (D * B) = 0 ↔ ∃ A : Matrix m n ℝ, D = A * L := by
  letI : Invertible B := hB.invertible
  rw [residual_zero_iff_factor]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    have h := congrArg (fun T => T * B⁻¹) hA
    simpa only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one] using h
  · rintro ⟨A, hA⟩
    exact ⟨A, by rw [hA, Matrix.mul_assoc]⟩

omit [DecidableEq e] in
/-- The weighted block convention when the legal audit inverse is B B*.
This exposes the exact return from whitened matrices to the original probes. -/
theorem weighted_residual_formula (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (B : Matrix e e ℝ) :
    residual (L * B) (D * B) = D * (B * Bᴴ) * Dᴴ -
      (D * (B * Bᴴ) * Lᴴ) * gramInverse (L * B) * (L * (B * Bᴴ) * Dᴴ) := by
  simp only [residual, conjTranspose_mul, Matrix.mul_assoc]

theorem weighted_optimal_residual (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (B : Matrix e e ℝ) (A : Matrix m n ℝ) :
    (D - A * L) * (B * Bᴴ) * (D - A * L)ᴴ = residual (L * B) (D * B) +
      (A - optimalFactor (L * B) (D * B)) * (L * (B * Bᴴ) * Lᴴ) *
        (A - optimalFactor (L * B) (D * B))ᴴ := by
  have h := optimal_residual_identity (L * B) (D * B) A
  have he : D * B - A * (L * B) = (D - A * L) * B := by
    rw [Matrix.sub_mul, Matrix.mul_assoc]
  rw [he] at h
  simpa only [conjTranspose_mul, Matrix.mul_assoc] using h

theorem residual_trace_zero_iff_factor [Fintype m]
    (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    Matrix.trace (residual L D) = 0 ↔ ∃ A : Matrix m n ℝ, D = A * L := by
  classical
  rw [(residual_psd L D).trace_eq_zero_iff, residual_zero_iff_factor]

theorem weighted_gram_trace_zero_iff [Fintype m] (E : Matrix m e ℝ)
    (W : Matrix m m ℝ) (hW : W.PosDef) :
    Matrix.trace (W * (E * Eᴴ)) = 0 ↔ E = 0 := by
  classical
  constructor
  · intro ht
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc] at ht
    have hz : Eᴴ * W * E = 0 :=
      (hW.posSemidef.conjTranspose_mul_mul_same E).trace_eq_zero_iff.mp ht
    have hvec : ∀ v : e → ℝ, E *ᵥ v = 0 := by
      intro v
      by_contra hn
      have hp : 0 < star v ⬝ᵥ ((Eᴴ * W * E) *ᵥ v) := by
        simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
          using hW.dotProduct_mulVec_pos hn
      rw [hz, zero_mulVec, dotProduct_zero] at hp
      linarith
    ext i j
    have he := congrFun (hvec (Pi.single j 1)) i
    simpa only [mulVec_single_one, Pi.zero_apply, Matrix.zero_apply] using he
  · intro h
    simp [h]

theorem weighted_residual_nonnegative [Fintype m]
    (L : Matrix n e ℝ) (D : Matrix m e ℝ) (W : Matrix m m ℝ)
    (hW : W.PosSemidef) : 0 ≤ Matrix.trace (W * residual L D) := by
  rw [residual_gram, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (hW.conjTranspose_mul_mul_same _).trace_nonneg

theorem weighted_residual_zero_iff_factor [Fintype m]
    (L : Matrix n e ℝ) (D : Matrix m e ℝ) (W : Matrix m m ℝ)
    (hW : W.PosDef) :
    Matrix.trace (W * residual L D) = 0 ↔ ∃ A : Matrix m n ℝ, D = A * L := by
  rw [residual_gram, weighted_gram_trace_zero_iff _ _ hW,
    ← self_mul_conjTranspose_eq_zero, ← residual_gram, residual_zero_iff_factor]

omit [DecidableEq e] in
theorem residual_zero_native (D : Matrix m e ℝ) :
    residual (0 : Matrix n e ℝ) D = D * Dᴴ := by
  simp [residual]

/-- A nonfaithful PSD weight can hide a nonzero residual. Zero scalar budget
only detects exact adequacy when the weight actually sees every residual. -/
theorem nonfaithful_weight_counterexample :
    (0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef ∧
      Matrix.trace ((0 : Matrix (Fin 1) (Fin 1) ℝ) *
        residual (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 0 ∧
      residual (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) ≠ 0 := by
  constructor
  · exact Matrix.PosSemidef.zero
  constructor
  · simp
  · rw [residual_zero_native]
    simp

def rankOneNative : Matrix (Fin 2) (Fin 3) ℝ :=
  fun i j => if j.val = 2 then 0 else if i.val = 0 then 1 else 2

def rankOneInverse : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i.val = 0 then (if j.val = 0 then 1/50 else 1/25)
    else (if j.val = 0 then 1/25 else 2/25)

theorem rankOne_native_singular : ¬ IsUnit (rankOneNative * rankOneNativeᴴ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  norm_num [rankOneNative, Matrix.det_fin_two, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem rankOne_gramInverse : gramInverse rankOneNative = rankOneInverse := by
  symm
  apply spectralInverse_unique (isHermitian_mul_conjTranspose_self rankOneNative)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rankOneNative, rankOneInverse, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rankOneNative, rankOneInverse, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  · change (rankOneNative * rankOneNativeᴴ * rankOneInverse)ᴴ =
      rankOneNative * rankOneNativeᴴ * rankOneInverse
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rankOneNative, rankOneInverse, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  · change (rankOneInverse * (rankOneNative * rankOneNativeᴴ))ᴴ =
      rankOneInverse * (rankOneNative * rankOneNativeᴴ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rankOneNative, rankOneInverse, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem rankOne_adequate_zero :
    residual rankOneNative (fun (_ : Fin 1) (j : Fin 3) => if j.val = 2 then 0 else 3) = 0 := by
  simp only [residual, rankOne_gramInverse]
  ext i j
  fin_cases i; fin_cases j;
    norm_num [rankOneNative, rankOneInverse, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem rankOne_blind_residual :
    residual rankOneNative (fun (_ : Fin 1) (j : Fin 3) => if j.val = 2 then 1 else 3) = 1 := by
  simp only [residual, rankOne_gramInverse]
  ext i j
  fin_cases i; fin_cases j;
    norm_num [rankOneNative, rankOneInverse, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

end

end SbtCosmo.Adequacy.Support
