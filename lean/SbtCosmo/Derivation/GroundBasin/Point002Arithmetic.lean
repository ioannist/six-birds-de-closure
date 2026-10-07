import SbtCosmo.Derivation.GroundBasin.Point002Data

/-! Closed kernel budgets for a whole .3 neighborhood and all16 direction
responses. Data, near-inverse error and all real/imaginary blocks are retained. -/
namespace SbtCosmo.Derivation.GroundBasin.Point002Arithmetic
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundBasin.Point002Data GroundNativeBox GroundRationalInterval
open GroundNativePrefixInitial (κ τ)
open GroundOriginalFirstTube GroundNativeDerivativeBox
open scoped BigOperators

theorem radius_pos : 0 < ρ := by decide +kernel
theorem rate_budget : 0 ≤ rate ∧ rate < 1 := by decide +kernel
theorem basis_rows : ∀ i : Fin 8,
    (∑ j, |GroundCoordinates.Point002.S i j|) ≤ basisBudget ∧
    (∑ j, |GroundCoordinates.Point002.R i j|) ≤ basisBudget := by decide +kernel

theorem ground_arithmetic : GroundBackgroundKernel.Arithmetic (sourceBox originalBackground κ input) z r q a C := by
  constructor <;> decide +kernel

theorem phase_inverse : GroundIntervalReciprocal.Arithmetic (overlapBox input G) K := by
  constructor <;> decide +kernel

theorem normalization_inverse : GroundIntervalReciprocal.Arithmetic (normBox (mixedBox input G K)) L := by
  constructor <;> decide +kernel

theorem native_arithmetic : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q a C K L := by
  constructor
  · exact ground_arithmetic
  · exact phase_inverse
  · exact normalization_inverse
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; constructor <;> exact ⟨le_rfl, le_rfl⟩

theorem real_response : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
    (sourceDerivativeBox originalBackground κ input (realDirection j)) q (yR j) (eR j) := by
  intro j
  fin_cases j <;> constructor <;> decide +kernel

theorem imag_response : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
    (sourceDerivativeBox originalBackground κ input (imagDirection j)) q (yI j) (eI j) := by
  intro j
  fin_cases j <;> constructor <;> decide +kernel

theorem real_response_cache : ∀ j i : Fin 8, included (computedDR j i) (DR j i) := by
  intro j
  fin_cases j <;> unfold included <;> decide +kernel

theorem imag_response_cache : ∀ j i : Fin 8, included (computedDI j i) (DI j i) := by
  intro j
  fin_cases j <;> unfold included <;> decide +kernel

theorem real_jet_cache : ∀ j : Fin 8, (computedJR j).Included (JR j) := by
  intro j
  fin_cases j <;> unfold StateBox.Included included <;> decide +kernel

theorem imag_jet_cache : ∀ j : Fin 8, (computedJI j).Included (JI j) := by
  intro j
  fin_cases j <;> unfold StateBox.Included included <;> decide +kernel

theorem real_rows : ∀ i : Fin 8, (∑ j : Fin 8, (((CR j).R i).bound + ((CI j).R i).bound)) ≤ rate := by
  decide +kernel

theorem imag_rows : ∀ i : Fin 8, (∑ j : Fin 8, (((CR j).I i).bound + ((CI j).I i).bound)) ≤ rate := by
  decide +kernel

theorem selector_rows : ∀ i : Fin 8, (∑ j : Fin 8, ((DR j i).bound + (DI j i).bound)) ≤ 1 := by decide +kernel

theorem endpoint_rows : ∀ i : Fin 8, (entryBox.R i).bound ≤ 1/48000 ∧ (entryBox.I i).bound ≤ 1/48000 := by decide +kernel

theorem source_bounds : ∀ i : Fin 8, 0 ≤ (sourceBox originalBackground κ input i).lo ∧
    (sourceBox originalBackground κ input i).hi ≤ 1/2 := by decide +kernel

theorem zero_contraction_budget_rejected : ¬ ((∑ j : Fin 8, (((CR j).R 0).bound + ((CI j).R 0).bound)) ≤ 0) := by decide +kernel

end
end SbtCosmo.Derivation.GroundBasin.Point002Arithmetic
