import SbtCosmo.Derivation.SchurStationarity

/-! Actual finite matrix product/transpose calculus in the existing elementwise
norm. No operator-norm substitution or matrix-derivative premise is needed. -/
namespace SbtCosmo.Derivation.MatrixDifferential
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Elementwise
variable {i j k E : Type*} [Fintype i] [Fintype j] [Fintype k]
  [DecidableEq i] [DecidableEq j] [DecidableEq k]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def entry (a : i) (b : j) : Matrix i j ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj b : (j → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj a : (i → j → ℝ) →L[ℝ] (j → ℝ))

def mulRight (B : Matrix j k ℝ) : Matrix i j ℝ →ₗ[ℝ] Matrix i k ℝ where
  toFun A := A*B
  map_add' A C := Matrix.add_mul A C B
  map_smul' a A := Matrix.smul_mul a A B

def mulLeft (A : Matrix i j ℝ) : Matrix j k ℝ →ₗ[ℝ] Matrix i k ℝ where
  toFun B := A*B
  map_add' B C := Matrix.mul_add A B C
  map_smul' a B := Matrix.mul_smul A a B

def transposeMap : Matrix i j ℝ →ₗ[ℝ] Matrix j i ℝ where
  toFun A := A.transpose
  map_add' A B := Matrix.transpose_add A B
  map_smul' a A := Matrix.transpose_smul a A

omit [DecidableEq i] [DecidableEq j] [DecidableEq k] in
/-- Rectangular matrix product rule, derived entry by entry in the actual norm. -/
theorem hasFDerivAt_mul {f : E → Matrix i j ℝ} {g : E → Matrix j k ℝ}
    {f' : E →L[ℝ] Matrix i j ℝ} {g' : E →L[ℝ] Matrix j k ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun z => f z*g z)
      ((mulRight (g x)).toContinuousLinearMap.comp f' +
        (mulLeft (f x)).toContinuousLinearMap.comp g') x := by
  apply hasFDerivAt_pi''
  intro a
  apply hasFDerivAt_pi''
  intro b
  have hterm (c : j) := ((entry a c).hasFDerivAt.comp x hf).mul
    ((entry c b).hasFDerivAt.comp x hg)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ => hterm c)
  convert hh using 1
  ext v
  simp only [ContinuousLinearMap.sum_apply]
  change (f' v*g x+f x*g' v) a b =
    ∑ c : j, ((f x a c)*(g' v c b)+(g x c b)*(f' v a c))
  simp only [Matrix.add_apply,Matrix.mul_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [DecidableEq i] [DecidableEq j] in
/-- The actual transpose has the constructed transpose linear derivative. -/
theorem hasFDerivAt_transpose {f : E → Matrix i j ℝ} {f' : E →L[ℝ] Matrix i j ℝ} {x : E}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z => (f z).transpose) (transposeMap.toContinuousLinearMap.comp f') x := by
  exact (transposeMap (i := i) (j := j)).toContinuousLinearMap.hasFDerivAt.comp x hf

def tracePair (P : Matrix i i ℝ) : Matrix i i ℝ →ₗ[ℝ] ℝ where
  toFun M := trace (P*M)
  map_add' A B := by rw [Matrix.mul_add,Matrix.trace_add]
  map_smul' a A := by rw [Matrix.mul_smul,Matrix.trace_smul]; rfl

omit [DecidableEq i] in
/-- The price trace pairs with the actual matrix derivative. -/
theorem hasFDerivAt_tracePair {f : E → Matrix i i ℝ} {f' : E →L[ℝ] Matrix i i ℝ} {x : E}
    (P : Matrix i i ℝ) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z => trace (P*f z)) ((tracePair P).toContinuousLinearMap.comp f') x :=
  (tracePair P).toContinuousLinearMap.hasFDerivAt.comp x hf

end
end SbtCosmo.Derivation.MatrixDifferential
