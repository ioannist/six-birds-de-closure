import SbtCosmo.Derivation.AccessFork
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
A three-cell invariant block of the source's 54 field records, at density mode
4. The cells (phase,geometry)=(0,0),(0,3),(1,0) have multiplicities 5,1,3.
Their weighted conditional means are actual idempotent operators and do not
commute. This is a new provenance-backed finite carrier, not a repair of the
commuting uniform Boolean pair or a physical quantization/curving theorem.
The source field-to-cell bridge is independently checked with rational arithmetic.
-/
namespace SbtCosmo.Derivation.FieldAccessBlock
open scoped BigOperators

def cellWeight : Fin 3 → ℚ := ![5,1,3]
def phaseAccess : Fin 3 → Bool := ![false,false,true]
def geometryAccess : Fin 3 → ℕ := ![0,3,0]

/-- Full coarse endpoints on this invariant density-sector block. -/
def qmBlock (i : Fin 3) : ℕ × Bool × ℕ := (1,phaseAccess i,4)
def grBlock (i : Fin 3) : ℕ × ℕ × ℕ := (1,4,geometryAccess i)

theorem phase_not_determine_geometry :
    ¬ AccessFork.FactorsThrough phaseAccess geometryAccess := by
  intro h
  have he := (AccessFork.factorsThrough_iff_fiber_constant phaseAccess geometryAccess).mp h
    0 1 (by decide)
  norm_num [geometryAccess] at he

theorem geometry_not_determine_phase :
    ¬ AccessFork.FactorsThrough geometryAccess phaseAccess := by
  intro h
  have he := (AccessFork.factorsThrough_iff_fiber_constant geometryAccess phaseAccess).mp h
    0 2 (by decide)
  norm_num [phaseAccess, Matrix.cons_val_two] at he

/-- Literal weighted conditional expectation over the access fiber. -/
def weightedMean {Y : Type*} [DecidableEq Y] (access : Fin 3 → Y)
    (f : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  (∑ j, if access j = access i then cellWeight j*f j else 0) /
    (∑ j, if access j = access i then cellWeight j else 0)

def phaseMean (f : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  if i.val = 2 then f 2 else (5*f 0+f 1)/6

def geometryMean (f : Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  if i.val = 1 then f 1 else (5*f 0+3*f 2)/8

theorem weights_positive : ∀ i, 0 < cellWeight i := by decide

theorem weights_total : ∑ i, cellWeight i = 9 := by
  norm_num [cellWeight, Fin.sum_univ_three, Matrix.cons_val_two]

theorem fiber_mass_positive {Y : Type*} [DecidableEq Y] (access : Fin 3 → Y) (i : Fin 3) :
    0 < ∑ j, if access j = access i then cellWeight j else 0 := by
  have hn : ∀ j : Fin 3, 0 ≤ if access j = access i then cellWeight j else 0 := by
    intro j
    split_ifs <;> first | exact (weights_positive j).le | exact le_refl _
  have he : cellWeight i ≤ ∑ j, if access j = access i then cellWeight j else 0 := by
    simpa using Finset.single_le_sum (s := Finset.univ) (f := fun j =>
      if access j = access i then cellWeight j else 0) (fun j _ => hn j) (Finset.mem_univ i)
  exact lt_of_lt_of_le (weights_positive i) he

theorem phase_mean_is_conditional : weightedMean phaseAccess = phaseMean := by
  funext f i
  fin_cases i <;> norm_num [weightedMean, phaseAccess, cellWeight, phaseMean, Fin.sum_univ_three, Matrix.cons_val_two]

theorem geometry_mean_is_conditional : weightedMean geometryAccess = geometryMean := by
  funext f i
  fin_cases i <;> norm_num [weightedMean, geometryAccess, cellWeight, geometryMean, Fin.sum_univ_three, Matrix.cons_val_two]

theorem qm_block_conditional : weightedMean qmBlock = phaseMean := by
  rw [← phase_mean_is_conditional]
  funext f i
  simp [weightedMean, qmBlock]

theorem gr_block_conditional : weightedMean grBlock = geometryMean := by
  rw [← geometry_mean_is_conditional]
  funext f i
  simp [weightedMean, grBlock]

theorem phase_mean_idempotent (f : Fin 3 → ℚ) : phaseMean (phaseMean f) = phaseMean f := by
  funext i
  fin_cases i <;> simp [phaseMean] <;> ring

theorem geometry_mean_idempotent (f : Fin 3 → ℚ) : geometryMean (geometryMean f) = geometryMean f := by
  funext i
  fin_cases i <;> simp [geometryMean] <;> ring

def geometryOnlyIndicator : Fin 3 → ℚ := ![0,1,0]

theorem ordered_values :
    phaseMean (geometryMean geometryOnlyIndicator) 0 = 1/6 ∧
      geometryMean (phaseMean geometryOnlyIndicator) 0 = 5/48 := by
  norm_num [phaseMean, geometryMean, geometryOnlyIndicator, Matrix.cons_val_two]

theorem commutator_value :
    phaseMean (geometryMean geometryOnlyIndicator) 0 -
      geometryMean (phaseMean geometryOnlyIndicator) 0 = 1/16 := by
  rw [ordered_values.1, ordered_values.2]
  norm_num

theorem weighted_conditionals_do_not_commute :
    weightedMean phaseAccess (weightedMean geometryAccess geometryOnlyIndicator) ≠
      weightedMean geometryAccess (weightedMean phaseAccess geometryOnlyIndicator) := by
  rw [phase_mean_is_conditional, geometry_mean_is_conditional]
  intro he
  have hz := congrFun he 0
  rw [ordered_values.1, ordered_values.2] at hz
  norm_num at hz

/-- Exact non-commutation uses the inherited full endpoint coordinates. -/
theorem field_block_conditionals_do_not_commute :
    weightedMean qmBlock (weightedMean grBlock geometryOnlyIndicator) ≠
      weightedMean grBlock (weightedMean qmBlock geometryOnlyIndicator) := by
  rw [qm_block_conditional, gr_block_conditional]
  rw [← phase_mean_is_conditional, ← geometry_mean_is_conditional]
  exact weighted_conditionals_do_not_commute

end SbtCosmo.Derivation.FieldAccessBlock
