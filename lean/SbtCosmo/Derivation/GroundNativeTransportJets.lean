import SbtCosmo.Derivation.GroundUncertainNativeBasin
namespace SbtCosmo.Derivation.GroundNativeTransportJets
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundNativeDerivative
open GroundRationalInterval GroundNativeBox GroundNativeDerivativeBox GroundMatrixCoordinates
open GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open scoped BigOperators
/-! Finite transport permits derivative bounds above one; contraction is not assumed. -/
structure RowBounds (c : Certificate) : Prop where
  rate_nonneg : 0 ≤ c.rate
  real_rows : ∀ i : Fin 8,
    (∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).R i).bound+
      ((c.derivativeBox (Fin.natAdd 8 j)).R i).bound)) ≤ c.rate
  imag_rows : ∀ i : Fin 8,
    (∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).I i).bound+
      ((c.derivativeBox (Fin.natAdd 8 j)).I i).bound)) ≤ c.rate

theorem actual_derivative_norm (c : Certificate) (hR : c.ResponseArithmetic)
    (hD : c.ResponseIncluded) (hJ : c.DerivativeIncluded) (hrows : RowBounds c) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {x : State} (hx : c.input.Contains (c.T x)) :
    ‖GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x‖ ≤ (c.rate : ℝ) := by
  have hreal (j : Fin 8) := c.actual_jet_enclosed hR hD hJ hb hx (j.castAdd 8)
  have himag (j : Fin 8) := c.actual_jet_enclosed hR hD hJ hb hx (Fin.natAdd 8 j)
  simp only [column_real] at hreal
  simp only [column_imag] at himag
  apply GroundStateRows.operator_norm_le_rows _ (by exact_mod_cast hrows.rate_nonneg)
  · intro i
    calc
      (∑ j, (|(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (GroundLocalDynamics.column j,0)).1 i|+
        |(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (0,GroundLocalDynamics.column j)).1 i|)) ≤
        ∑ j, ((((c.derivativeBox (j.castAdd 8)).R i).bound : ℝ)+(((c.derivativeBox (Fin.natAdd 8 j)).R i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((hreal j) i).1) (Interval.abs_le_bound ((himag j) i).1)
      _ ≤ (c.rate : ℝ) := by
        have h : ((∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).R i).bound+((c.derivativeBox (Fin.natAdd 8 j)).R i).bound) : ℚ) : ℝ) ≤ (c.rate : ℝ) := Rat.cast_le.mpr (hrows.real_rows i)
        simpa only [Rat.cast_sum, Rat.cast_add] using h
  · intro i
    calc
      (∑ j, (|(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (GroundLocalDynamics.column j,0)).2 i|+
        |(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (0,GroundLocalDynamics.column j)).2 i|)) ≤
        ∑ j, ((((c.derivativeBox (j.castAdd 8)).I i).bound : ℝ)+(((c.derivativeBox (Fin.natAdd 8 j)).I i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((hreal j) i).2) (Interval.abs_le_bound ((himag j) i).2)
      _ ≤ (c.rate : ℝ) := by
        have h : ((∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).I i).bound+((c.derivativeBox (Fin.natAdd 8 j)).I i).bound) : ℚ) : ℝ) ≤ (c.rate : ℝ) := Rat.cast_le.mpr (hrows.imag_rows i)
        simpa only [Rat.cast_sum, Rat.cast_add] using h

end
end SbtCosmo.Derivation.GroundNativeTransportJets
