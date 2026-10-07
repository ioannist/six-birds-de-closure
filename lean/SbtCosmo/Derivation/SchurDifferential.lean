import SbtCosmo.Derivation.MatrixDifferential

/-! Explicit derivative and trace-dual adjoint of the actual fixed-native Schur
residual. Singular native blocks and rectangular probes are retained. -/
namespace SbtCosmo.Derivation.SchurDifferential
noncomputable section
open Matrix MatrixDifferential
open scoped Matrix Matrix.Norms.Elementwise
variable {n m e E : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq e]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def complement (L : Matrix n e ℝ) : Matrix e e ℝ := 1-SbtCosmo.Adequacy.Support.projector L

def jacobian (L : Matrix n e ℝ) (Z : Matrix m e ℝ) : Matrix m e ℝ →L[ℝ] Matrix m m ℝ :=
  (mulRight Z.transpose).toContinuousLinearMap.comp (mulRight (complement L)).toContinuousLinearMap +
    (mulLeft (Z*complement L)).toContinuousLinearMap.comp transposeMap.toContinuousLinearMap

theorem jacobian_apply (L : Matrix n e ℝ) (Z H : Matrix m e ℝ) :
    jacobian L Z H=H*complement L*Z.transpose+Z*complement L*H.transpose := rfl

theorem complement_transpose (L : Matrix n e ℝ) : (complement L).transpose=complement L := by
  exact (Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans
    (SbtCosmo.Adequacy.Support.complement_hermitian L).eq

/-- The computed derivative lies in the original symmetric budget directions. -/
theorem jacobian_symmetric (L : Matrix n e ℝ) (Z H : Matrix m e ℝ) :
    (jacobian L Z H).transpose=jacobian L Z H := by
  rw [jacobian_apply]
  simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,
    complement_transpose,Matrix.mul_assoc]
  rw [add_comm]

/-- The actual singular-support Schur residual has this explicit derivative. -/
theorem hasFDerivAt_residual (L : Matrix n e ℝ) (Z : Matrix m e ℝ) :
    HasFDerivAt (SbtCosmo.Adequacy.Support.residual L) (jacobian L Z) Z := by
  have hZ := hasFDerivAt_id (𝕜 := ℝ) Z
  have hR := (mulRight (complement L)).toContinuousLinearMap.hasFDerivAt.comp Z hZ
  have hh := hasFDerivAt_mul hR (hasFDerivAt_transpose hZ)
  convert hh using 1
  · funext X
    rw [SbtCosmo.Adequacy.Support.residual_projection,Matrix.conjTranspose_eq_transpose_of_trivial]
    rfl

theorem fderiv_residual (L : Matrix n e ℝ) (Z : Matrix m e ℝ) :
    fderiv ℝ (SbtCosmo.Adequacy.Support.residual L) Z=jacobian L Z :=
  (hasFDerivAt_residual L Z).fderiv

def traceAdjoint (J : E →L[ℝ] Matrix m m ℝ) : Matrix m m ℝ →ₗ[ℝ] (E →L[ℝ] ℝ) where
  toFun P := (tracePair P).toContinuousLinearMap.comp J
  map_add' P Q := by
    ext v
    change trace ((P+Q)*J v)=trace (P*J v)+trace (Q*J v)
    rw [Matrix.add_mul,Matrix.trace_add]
  map_smul' a P := by
    ext v
    change trace ((a • P)*J v)=a • trace (P*J v)
    rw [Matrix.smul_mul,Matrix.trace_smul]

/-- This adjoint is the actual dual pullback with the trace pairing. -/
theorem traceAdjoint_pairing (J : E →L[ℝ] Matrix m m ℝ) (P : Matrix m m ℝ) (h : E) :
    traceAdjoint J P h=trace (P*J h) := rfl

/-- General real matrix-price formula; the transpose of P cannot be discarded
until symmetry is justified. -/
theorem trace_jacobian_formula (L : Matrix n e ℝ) (Z H : Matrix m e ℝ) (P : Matrix m m ℝ) :
    trace (P*jacobian L Z H)=trace (((P+P.transpose)*Z*complement L)*H.transpose) := by
  have hfirst : trace (P*(H*complement L*Z.transpose))=
      trace (P.transpose*Z*complement L*H.transpose) := by
    calc
      trace (P*(H*complement L*Z.transpose))=
          trace ((P*H*complement L*Z.transpose).transpose) := by
        rw [Matrix.trace_transpose]
        simp only [Matrix.mul_assoc]
      _ = trace (Z*complement L*H.transpose*P.transpose) := by
        simp only [Matrix.transpose_mul,Matrix.transpose_transpose,complement_transpose,Matrix.mul_assoc]
      _ = trace (P.transpose*(Z*complement L*H.transpose)) := Matrix.trace_mul_comm _ _
      _ = trace (P.transpose*Z*complement L*H.transpose) := by simp only [Matrix.mul_assoc]
  rw [jacobian_apply,Matrix.mul_add,Matrix.trace_add,hfirst]
  simp only [Matrix.add_mul,Matrix.trace_add]
  rw [add_comm]
  simp only [Matrix.mul_assoc]

/-- PSD matrix prices are symmetric, earning the factor two in the pullback. -/
theorem trace_jacobian_psd {P : Matrix m m ℝ} (hP : P.PosSemidef)
    (L : Matrix n e ℝ) (Z H : Matrix m e ℝ) :
    trace (P*jacobian L Z H)=2*trace (P*Z*complement L*H.transpose) := by
  have hp : P.transpose=P :=
    (Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans hP.1.eq
  rw [trace_jacobian_formula,hp]
  simp only [Matrix.add_mul,Matrix.trace_add]
  ring

/-- The same actual matrix derivative returns through every genuinely
differentiable probe, without requiring a finite-dimensional primal space. -/
theorem hasFDerivAt_composed_residual (L : Matrix n e ℝ) {D : E → Matrix m e ℝ}
    {D' : E →L[ℝ] Matrix m e ℝ} {x : E} (hD : HasFDerivAt D D' x) :
    HasFDerivAt (fun z => SbtCosmo.Adequacy.Support.residual L (D z))
      ((jacobian L (D x)).comp D') x := (hasFDerivAt_residual L (D x)).comp x hD

/-- General differentiable-probe trace pullback with fixed budget, using the
actual supplied probe derivative rather than supplying a Schur derivative. -/
theorem hasFDerivAt_composed_trace_gap (L : Matrix n e ℝ) {D : E → Matrix m e ℝ}
    {D' : E →L[ℝ] Matrix m e ℝ} {x : E} (hD : HasFDerivAt D D' x) (P B : Matrix m m ℝ) :
    HasFDerivAt (fun z => trace (P*(SbtCosmo.Adequacy.Support.residual L (D z)-B)))
      (traceAdjoint ((jacobian L (D x)).comp D') P) x := by
  have hh := (hasFDerivAt_tracePair P (hasFDerivAt_composed_residual L hD)).sub_const (trace (P*B))
  simpa only [Matrix.mul_sub,Matrix.trace_sub] using hh

variable [FiniteDimensional ℝ E]

def affineLinear (D : E →ᵃ[ℝ] Matrix m e ℝ) : E →L[ℝ] Matrix m e ℝ := D.linear.toContinuousLinearMap

omit [DecidableEq e] in
theorem hasFDerivAt_probe (D : E →ᵃ[ℝ] Matrix m e ℝ) (x : E) :
    HasFDerivAt D (affineLinear D) x := by
  let Dc : E →ᴬ[ℝ] Matrix m e ℝ := {D with cont := D.continuous_of_finiteDimensional}
  exact Dc.hasFDerivAt

theorem hasFDerivAt_affine_residual (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ) (x : E) :
    HasFDerivAt (fun z => SbtCosmo.Adequacy.Support.residual L (D z))
      ((jacobian L (D x)).comp (affineLinear D)) x :=
  (hasFDerivAt_residual L (D x)).comp x (hasFDerivAt_probe D x)

theorem fderiv_affine_residual (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ) (x : E) :
    fderiv ℝ (fun z => SbtCosmo.Adequacy.Support.residual L (D z)) x=
      (jacobian L (D x)).comp (affineLinear D) := (hasFDerivAt_affine_residual L D x).fderiv

def pricePullback (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ) (x : E) (P : Matrix m m ℝ) : E →L[ℝ] ℝ :=
  traceAdjoint ((jacobian L (D x)).comp (affineLinear D)) P

/-- The explicit pullback is the trace-dual adjoint of the actual residual
derivative, not an arbitrarily named stationarity functional. -/
theorem pricePullback_eq_adjoint_fderiv (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    (x : E) (P : Matrix m m ℝ) :
    pricePullback L D x P=
      traceAdjoint (fderiv ℝ (fun z => SbtCosmo.Adequacy.Support.residual L (D z)) x) P := by
  rw [fderiv_affine_residual]
  rfl

/-- The original actual trace-Lagrangian has the computed price pullback as its
derivative; a fixed matrix budget contributes zero. -/
theorem hasFDerivAt_trace_gap (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    (x : E) (P B : Matrix m m ℝ) :
    HasFDerivAt (fun z => trace (P*(SbtCosmo.Adequacy.Support.residual L (D z)-B)))
      (pricePullback L D x P) x := by
  have hh := (hasFDerivAt_tracePair P (hasFDerivAt_affine_residual L D x)).sub_const (trace (P*B))
  simpa only [Matrix.mul_sub,Matrix.trace_sub] using hh

theorem fderiv_trace_gap (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    (x : E) (P B : Matrix m m ℝ) :
    fderiv ℝ (fun z => trace (P*(SbtCosmo.Adequacy.Support.residual L (D z)-B))) x=
      pricePullback L D x P := (hasFDerivAt_trace_gap L D x P B).fderiv

theorem pricePullback_psd {P : Matrix m m ℝ} (hP : P.PosSemidef)
    (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ) (x h : E) :
    pricePullback L D x P h=2*trace (P*D x*complement L*(D.linear h).transpose) := by
  exact trace_jacobian_psd hP L (D x) (D.linear h)

end
end SbtCosmo.Derivation.SchurDifferential
