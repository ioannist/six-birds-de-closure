import SbtCosmo.Derivation.GroundBorder

/-! Polynomial normalized eigen equations and their actual full derivative. -/
namespace SbtCosmo.Derivation.GroundEquations
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators ContDiff
open GroundState GroundBorder

abbrev Domain := Field × Point
def equations (p : Domain) : Point :=
  (shifted p.1 p.2.2 p.2.1, (normSq p.2.1 - 1) / 2)

def derivativeLM (p : Domain) : Domain →ₗ[ℝ] Point where
  toFun h := (fun i => h.1 i * p.2.1 i + shifted p.1 p.2.2 h.2.1 i - h.2.2 * p.2.1 i,
    dot p.2.1 h.2.1)
  map_add' a b := by
    apply Prod.ext
    · funext i
      dsimp [shifted, hamiltonian]
      ring
    · simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c h := by
    apply Prod.ext
    · funext i
      simp [shifted, hamiltonian, smul_eq_mul]
      ring
    · simp [dot, Finset.mul_sum, smul_eq_mul, mul_left_comm]

def derivative (p : Domain) : Domain →L[ℝ] Point := (derivativeLM p).toContinuousLinearMap

theorem derivative_apply (p h : Domain) :
    derivative p h = (fun i => h.1 i * p.2.1 i + shifted p.1 p.2.2 h.2.1 i - h.2.2 * p.2.1 i,
      dot p.2.1 h.2.1) := rfl

theorem equations_smooth : ContDiff ℝ ∞ equations := by
  unfold equations shifted hamiltonian normSq
  fun_prop

def potentialEval (i : Fin 8) : Domain →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ Field Point)
def fieldEval (i : Fin 8) : Domain →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ Field ℝ).comp (ContinuousLinearMap.snd ℝ Field Point))
def energyEval : Domain →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ Field ℝ).comp (ContinuousLinearMap.snd ℝ Field Point)

theorem equations_hasFDerivAt (p : Domain) : HasFDerivAt equations (derivative p) p := by
  have hv (i : Fin 8) := (potentialEval i).hasFDerivAt (x := p)
  have hu (i : Fin 8) := (fieldEval i).hasFDerivAt (x := p)
  have he := energyEval.hasFDerivAt (x := p)
  have hh (i : Fin 8) := (((hv i).const_add 1).mul (hu i)).sub
    (((hu (prev i)).add (hu (next i))).mul_const (1 / 2 : ℝ)) |>.sub (he.mul (hu i))
  have hn := ((HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hu i).pow 2)).sub_const 1).mul_const (1 / 2 : ℝ)
  have hf := (hasFDerivAt_pi.mpr hh).prodMk hn
  convert hf using 1
  · funext x
    apply Prod.ext
    · funext i
      dsimp [equations, shifted, hamiltonian, potentialEval, fieldEval, energyEval]
      ring
    · dsimp [equations, normSq, fieldEval]
      ring
  · apply ContinuousLinearMap.ext
    intro h
    apply Prod.ext
    · funext i
      simp [derivative, derivativeLM, potentialEval, fieldEval, energyEval,
        shifted, hamiltonian]
      ring
    · simp [derivative, derivativeLM, dot, fieldEval, energyEval,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem derivative_partial (p : Domain) :
    (derivative p).comp (ContinuousLinearMap.inr ℝ Field Point) = border p.1 p.2.1 p.2.2 := by
  apply ContinuousLinearMap.ext
  intro y
  apply Prod.ext
  · funext i
    simp [derivative, derivativeLM, border, borderLM]
  · rfl

theorem ground_equations (v : Field) : equations (v, groundPair v) = 0 := by
  have hg := (positiveGround_spec v).2
  apply Prod.ext
  · funext i
    simp [equations, shifted, groundPair, hg.2.1 i]
  · simp [equations, groundPair, hg.1]

/-- All implicit-function hypotheses are derived for the existing actual selector. -/
theorem actual_implicit_data (v : Field) :
    IsContDiffImplicitAt ∞ equations (derivative (v, groundPair v)) (v, groundPair v) := by
  refine ⟨equations_hasFDerivAt _, equations_smooth.contDiffAt, ?_, by norm_num⟩
  rw [derivative_partial]
  exact border_bijective (positiveGround_spec v).2

end
end SbtCosmo.Derivation.GroundEquations
