import SbtCosmo.Derivation.GroundComplex

/-! Exact background-shift law for the original sourced potential. -/
namespace SbtCosmo.Derivation.GroundNativeBackgroundShift
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open GroundState

theorem source_uniform_shift (b : Field) (κ s : ℝ) (z : ComplexField) (i : Fin 8) :
    complexSourcePotential (fun j => b j+s) κ z i - complexSourcePotential b κ z i =
      s*(1+κ*Complex.normSq (z i)) := by
  unfold complexSourcePotential BackgroundSelection.potential
  ring

theorem source_shift_site_difference (b : Field) (κ s : ℝ) (z : ComplexField)
    (i j : Fin 8) :
    (complexSourcePotential (fun k => b k+s) κ z i - complexSourcePotential b κ z i) -
      (complexSourcePotential (fun k => b k+s) κ z j - complexSourcePotential b κ z j) =
        s*κ*(Complex.normSq (z i)-Complex.normSq (z j)) := by
  rw [source_uniform_shift, source_uniform_shift]
  ring

/-- A nonzero coupled shift changes the sourced potential by a nonconstant
field whenever two original site densities differ. -/
theorem source_shift_nonconstant (b : Field) {κ s : ℝ} (hκ : κ ≠ 0) (hs : s ≠ 0)
    (z : ComplexField) (i j : Fin 8) (hd : Complex.normSq (z i) ≠ Complex.normSq (z j)) :
    complexSourcePotential (fun k => b k+s) κ z i - complexSourcePotential b κ z i ≠
      complexSourcePotential (fun k => b k+s) κ z j - complexSourcePotential b κ z j := by
  apply sub_ne_zero.mp
  rw [source_shift_site_difference]
  exact mul_ne_zero (mul_ne_zero hs hκ) (sub_ne_zero.mpr hd)
end
end SbtCosmo.Derivation.GroundNativeBackgroundShift
