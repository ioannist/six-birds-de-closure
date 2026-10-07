/-!
Common mathlib-free vocabulary for finite structural Lean receipts.

This module intentionally imports no mathlib.  It provides only the small
finite-carrier and exact rational-defect records used by the T1/T2 receipts.
-/
namespace SbtCosmo.Common

/-- A finite carrier represented by an explicit exhaustive list of states. -/
structure FiniteCarrier where
  X : Type
  decEq : DecidableEq X
  states : List X
  complete : ∀ x : X, x ∈ states

instance (C : FiniteCarrier) : DecidableEq C.X := C.decEq

/-- An exact nonnegative defect separating points. -/
structure Defect (X : Type) [DecidableEq X] where
  d : X → X → Rat
  nonneg : ∀ a b, 0 ≤ d a b
  zero_iff : ∀ a b, d a b = 0 ↔ a = b
  symm : ∀ a b, d a b = d b a

/-- The discrete `0/1` defect on a decidable type. -/
def discreteDefect (X : Type) [DecidableEq X] : Defect X where
  d a b := if a = b then 0 else 1
  nonneg := by
    intro a b
    by_cases h : a = b <;> simp [h] <;> decide
  zero_iff := by
    intro a b
    by_cases h : a = b
    · simp [h]
    · simp [h]
  symm := by
    intro a b
    by_cases h : a = b
    · subst b
      simp
    · have hba : b ≠ a := by
        intro hb
        exact h hb.symm
      simp [h, hba]

/-- A two-state carrier used by E0-style toy receipts. -/
def boolCarrier : FiniteCarrier where
  X := Bool
  decEq := inferInstance
  states := [false, true]
  complete := by
    intro x
    cases x <;> simp

end SbtCosmo.Common
