import SbtCosmo.Common

/-!
T2 route-mismatch receipt.

This module certifies the mathlib-free finite-carrier route-mismatch facts:
nonnegativity, zero iff the package/dynamics square commutes, and one explicit
positive finite toy witness.
-/
namespace SbtCosmo.RouteMismatch

open SbtCosmo.Common

/-- A finite closure package: micro dynamics, packaging, and macro dynamics. -/
structure Package (C : FiniteCarrier) where
  T : C.X → C.X
  E : C.X → C.X
  Tθ : C.X → C.X

/-- Route mismatch at a state: distance between package-then-evolve routes. -/
def RM {C : FiniteCarrier} (K : Package C) (D : Defect C.X) (x : C.X) : Rat :=
  D.d (K.E (K.T x)) (K.Tθ (K.E x))

/-- Route mismatch is always nonnegative. -/
theorem route_mismatch_nonneg {C : FiniteCarrier}
    (K : Package C) (D : Defect C.X) (x : C.X) :
    0 ≤ RM K D x :=
  D.nonneg _ _

/-- Route mismatch vanishes everywhere iff the package/dynamics square commutes. -/
theorem route_mismatch_zero_iff_commutes {C : FiniteCarrier}
    (K : Package C) (D : Defect C.X) :
    (∀ x, RM K D x = 0) ↔ (∀ x, K.E (K.T x) = K.Tθ (K.E x)) := by
  constructor
  · intro hzero x
    exact (D.zero_iff (K.E (K.T x)) (K.Tθ (K.E x))).1 (hzero x)
  · intro hcomm x
    exact (D.zero_iff (K.E (K.T x)) (K.Tθ (K.E x))).2 (hcomm x)

/-- Two-patch heterogeneous toy carrier for a positive route mismatch witness. -/
inductive ToyPatch where
  | native
  | dissolving
  deriving DecidableEq

/-- Explicit two-patch finite carrier. -/
def toyCarrier : FiniteCarrier where
  X := ToyPatch
  decEq := inferInstance
  states := [ToyPatch.native, ToyPatch.dissolving]
  complete := by
    intro x
    cases x <;> simp

/-- A toy package whose macro route disagrees with package-after-micro-evolution. -/
def toyPackage : Package toyCarrier where
  T
    | ToyPatch.native => ToyPatch.dissolving
    | ToyPatch.dissolving => ToyPatch.dissolving
  E _ := ToyPatch.native
  Tθ
    | ToyPatch.native => ToyPatch.dissolving
    | ToyPatch.dissolving => ToyPatch.dissolving

/-- Non-vacuity: the explicit heterogeneous toy has strictly positive route mismatch. -/
theorem route_mismatch_pos_witness :
    ∃ (C : FiniteCarrier) (K : Package C) (D : Defect C.X) (x₀ : C.X),
      0 < RM K D x₀ := by
  refine ⟨toyCarrier, toyPackage, discreteDefect ToyPatch, ToyPatch.native, ?_⟩
  change 0 < (1 : Rat)
  decide

end SbtCosmo.RouteMismatch
