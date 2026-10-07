import SbtCosmo.Derivation.GroundComplexIntervalBudget
import SbtCosmo.Derivation.GroundNativeBox
import SbtCosmo.Derivation.GroundSourceDiagnostics
namespace SbtCosmo.Derivation.GroundComplexFiniteBudget
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundComplexEuclidean GroundComplexResidual
open GroundNativeBox GroundRationalInterval GroundSourceDiagnostics
open scoped BigOperators

def squaredBudget (B : StateBox) : ℚ := ∑ i : Fin 8, ((B.R i).bound^2+(B.I i).bound^2)

theorem box_l2_bound {B : StateBox} {z : ComplexField} {d : ℚ}
    (hz : B.Contains (unpack z)) (hd : 0 ≤ d) (hb : squaredBudget B ≤ d^2) :
    l2 z ≤ (d : ℝ) := by
  have hs : complexNormSq z ≤ ((squaredBudget B : ℚ) : ℝ) := by
    rw [complexNormSq, squaredBudget, Rat.cast_sum]
    apply Finset.sum_le_sum
    intro i _
    have hr := Interval.abs_le_bound (hz i).1
    have hi := Interval.abs_le_bound (hz i).2
    change |(z i).re| ≤ ((B.R i).bound : ℝ) at hr
    change |(z i).im| ≤ ((B.I i).bound : ℝ) at hi
    simp only [Complex.normSq_apply, Rat.cast_add, Rat.cast_pow]
    have har := abs_nonneg (z i).re
    have hai := abs_nonneg (z i).im
    have her := sq_abs (z i).re
    have hei := sq_abs (z i).im
    nlinarith
  have hc : ((squaredBudget B : ℚ) : ℝ) ≤ (d : ℝ)^2 := by exact_mod_cast hb
  have hn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [← l2_sq] at hs
  nlinarith [l2_nonneg z]

theorem tests_of_budgets {τ ε : ℝ} {b : Field} {κ : ℝ} {previous z : ComplexField}
    {d update A B : ℝ}
    (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hz : complexNormSq z = 1)
    (hdistance : l2 (z-(-nativeCandidate b κ z)) ≤ d)
    (hupdate : l2 (z-previous) ≤ update)
    (hstep : nativeUpdate τ b κ (1/2) previous = z)
    (hpotential : ∀ i, A ≤ complexSourcePotential b κ z i ∧ complexSourcePotential b κ z i ≤ B)
    (hphase : 2*d^2 ≤ 1) (hguard : τ < 1-2*d^2)
    (hsmall : update ≤ ε ∧ 4*d ≤ ε ∧ (2+(B-A))*(d+d^2) ≤ ε) :
    MeetsConvergence τ ε b κ (1/2) previous z := by
  let g := -nativeCandidate b κ z
  let V := complexSourcePotential b κ z
  let e := energy V (positiveGround V)
  have hg := (positiveGround_spec V).2
  have hu : complexNormSq g = 1 := by
    rw [show g = -realEmbed (positiveGround V) from rfl, GroundNativeReflection.complexNormSq_neg]
    exact realEmbed_normalized hg.1
  have heig : ∀ i, complexHamiltonian V g i = (e : ℂ)*g i := by
    intro i
    have hn : complexHamiltonian V (-realEmbed (positiveGround V)) i =
        -complexHamiltonian V (realEmbed (positiveGround V)) i := by
      simp [complexHamiltonian]; ring
    change complexHamiltonian V (-realEmbed (positiveGround V)) i = (e : ℂ)*(-realEmbed (positiveGround V) i)
    rw [hn,realEmbed_eigen hg i]
    change -(↑e * realEmbed (positiveGround V) i) = ↑e * -realEmbed (positiveGround V) i
    ring
  have he := GroundComplexIntervalBudget.ground_energy_budget hg hpotential
  have hM : ∀ w, l2 (shifted V e w) ≤ (2+(B-A))*l2 w :=
    GroundComplexIntervalBudget.shifted_l2_bound hpotential he
  have hgap := double_phase_gap hu hz hdistance hd hphase hτ hguard
  have hsign : nativePhase τ (nativeCandidate b κ z) z = nativePhase τ g z := by
    have hc : nativeCandidate b κ z = -g := by simp [g]
    rw [hc, nativePhase_real_sign_invariant hτ hgap.1]
  refine ⟨?_,?_,?_,?_⟩
  · rw [lastUpdateResidual,hstep]; exact hupdate.trans hsmall.1
  · rw [finalFixedGap,hsign]; exact hgap.2.2.trans hsmall.2.1
  · have hres := eigen_residual_bound heig hz hM
    have hAB : A ≤ B := (hpotential 0).1.trans (hpotential 0).2
    have hp : (l2 (z-g))^2 ≤ d^2 := by nlinarith [l2_nonneg (z-g)]
    change l2 (shifted V (complexEnergy V z) z) ≤ ε
    nlinarith [l2_nonneg (z-g),hdistance,hsmall.2.2]
  · rw [sourcing_self_comparison_zero]; exact hε

theorem fails_of_update {τ ε : ℝ} {b : Field} {κ m : ℝ} {previous z : ComplexField}
    (hstep : nativeUpdate τ b κ m previous = z) (hgap : ε < l2 (z-previous)) :
    ¬ MeetsConvergence τ ε b κ m previous z := by
  intro h
  have he := h.1
  rw [lastUpdateResidual,hstep] at he
  exact (not_lt_of_ge he) hgap
end
end SbtCosmo.Derivation.GroundComplexFiniteBudget
