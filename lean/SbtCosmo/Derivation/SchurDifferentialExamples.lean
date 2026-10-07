import SbtCosmo.Derivation.SchurDifferential

/-! Actual rectangular singular-native differentiation, plus controls that
detect a dropped product-rule term and an unjustified symmetric-price formula. -/
namespace SbtCosmo.Derivation.SchurDifferentialExamples
noncomputable section
open Matrix SchurDifferential
open scoped Matrix Matrix.Norms.Elementwise

def singularProbe : ℝ →ᵃ[ℝ] Matrix (Fin 1) (Fin 3) ℝ where
  toFun x := fun _ j => if j.val=2 then x else 3
  linear :=
    { toFun := fun h => fun _ j => if j.val=2 then h else 0
      map_add' := by intro a b; ext i j; by_cases hj : j.val=2 <;> simp [hj]
      map_smul' := by intro a b; ext i j; by_cases hj : j.val=2 <;> simp [hj] }
  map_vadd' x h := by ext i j; by_cases hj : j.val=2 <;> simp [vadd_eq_add,hj]

def nativeComplement : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if i.val=2 then (if j.val=2 then 1 else 0)
  else if j.val=2 then 0 else if i=j then 1/2 else -1/2

theorem singular_native_complement : complement SbtCosmo.Adequacy.Support.rankOneNative=nativeComplement := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complement,SbtCosmo.Adequacy.Support.projector,SbtCosmo.Adequacy.Support.rankOne_gramInverse,
      SbtCosmo.Adequacy.Support.rankOneNative,SbtCosmo.Adequacy.Support.rankOneInverse,nativeComplement,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,Fin.sum_univ_succ]

/-- The actual price pullback works with a singular native Gram and rectangular
probe, and computes the expected derivative of the blind-coordinate square. -/
theorem singular_pricePullback (x h : ℝ) :
    pricePullback SbtCosmo.Adequacy.Support.rankOneNative singularProbe x
      (1 : Matrix (Fin 1) (Fin 1) ℝ) h=2*x*h := by
  rw [pricePullback_psd Matrix.PosSemidef.one]
  rw [Matrix.one_mul,singular_native_complement]
  norm_num [nativeComplement,singularProbe,Matrix.mul_apply,Matrix.transpose_apply,Matrix.trace,Fin.sum_univ_succ]
  ring

theorem singular_trace_derivative (x : ℝ) :
    HasFDerivAt (fun z => trace (SbtCosmo.Adequacy.Support.residual
      SbtCosmo.Adequacy.Support.rankOneNative (singularProbe z)))
      ((2*x) • ContinuousLinearMap.id ℝ ℝ) x := by
  have he : pricePullback SbtCosmo.Adequacy.Support.rankOneNative singularProbe x
      (1 : Matrix (Fin 1) (Fin 1) ℝ)=(2*x) • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro h
    rw [singular_pricePullback]
    rfl
  have hh := hasFDerivAt_trace_gap SbtCosmo.Adequacy.Support.rankOneNative singularProbe x
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
  rw [he] at hh
  simpa only [sub_zero,Matrix.one_mul] using hh

/-- Dropping one of the two derivative terms gives a wrong actual price. -/
theorem missing_second_term_control :
    pricePullback SbtCosmo.Adequacy.Support.rankOneNative singularProbe 1
      (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠
    trace (singularProbe 1*complement SbtCosmo.Adequacy.Support.rankOneNative*
      (singularProbe.linear 1).transpose) := by
  rw [singular_pricePullback]
  rw [singular_native_complement]
  norm_num [nativeComplement,singularProbe,Matrix.mul_apply,Matrix.transpose_apply,Matrix.trace,Fin.sum_univ_succ]

def nonsymmetricPrice : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 0 1 1
def baseProbe : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => if i=0 then 1 else 0
def directionProbe : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => if i=1 then 1 else 0

theorem price_not_hermitian : ¬ nonsymmetricPrice.IsHermitian := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h.eq
  norm_num [nonsymmetricPrice,Matrix.single,Matrix.conjTranspose_apply] at hh

/-- Without a symmetric price the factor-two shortcut is false; the general
P+transpose(P) theorem keeps the omitted contribution. -/
theorem nonsymmetric_price_control :
    trace (nonsymmetricPrice*jacobian (0 : Matrix (Fin 1) (Fin 1) ℝ) baseProbe directionProbe) ≠
      2*trace (nonsymmetricPrice*baseProbe*complement (0 : Matrix (Fin 1) (Fin 1) ℝ)*directionProbe.transpose) := by
  rw [jacobian_apply]
  norm_num [complement,SbtCosmo.Adequacy.Support.projector,nonsymmetricPrice,baseProbe,directionProbe,
    Matrix.single,Matrix.mul_apply,Matrix.transpose_apply,Matrix.trace,Fin.sum_univ_succ]

end
end SbtCosmo.Derivation.SchurDifferentialExamples
