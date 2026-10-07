import SbtCosmo.Common

/-!
T1 idempotent-packaging receipt.

This module certifies the mathlib-free finite-carrier facts used by the
`delta` defect target: the image of an idempotent packaging map is exactly its
fixed-point set, and the idempotence defect vanishes there.
-/
namespace SbtCosmo.Idempotence

open SbtCosmo.Common

/-- An idempotent packaging operator on a finite carrier. -/
structure Packaging (C : FiniteCarrier) where
  E : C.X → C.X
  idem : ∀ x, E (E x) = E x

/-- Fixed points of the packaging operator. -/
def isFixed {C : FiniteCarrier} (P : Packaging C) (x : C.X) : Prop :=
  P.E x = x

/-- The image of an idempotent packaging operator is exactly its fixed-point set. -/
theorem image_eq_fixedSet {C : FiniteCarrier} (P : Packaging C) :
    ∀ x, (∃ y, P.E y = x) ↔ isFixed P x := by
  intro x
  constructor
  · intro hx
    cases hx with
    | intro y hy =>
        calc
          P.E x = P.E (P.E y) := by rw [← hy]
          _ = P.E y := P.idem y
          _ = x := hy
  · intro hx
    exact ⟨x, hx⟩

/-- The idempotence defect vanishes, equivalently the packaged state is fixed. -/
theorem delta_zero_iff_fixed {C : FiniteCarrier} (P : Packaging C) (D : Defect C.X) :
    (∀ x, D.d (P.E (P.E x)) (P.E x) = 0) ∧
      (∀ x, D.d (P.E (P.E x)) (P.E x) = 0 ↔ isFixed P (P.E x)) := by
  constructor
  · intro x
    exact (D.zero_iff (P.E (P.E x)) (P.E x)).2 (P.idem x)
  · intro x
    constructor
    · intro hx
      exact (D.zero_iff (P.E (P.E x)) (P.E x)).1 hx
    · intro hx
      exact (D.zero_iff (P.E (P.E x)) (P.E x)).2 hx

/-- E0 two-state lumping package: both states close to the `false` macro state. -/
def boolLumpingPackaging : Packaging boolCarrier where
  E _ := false
  idem := by
    intro x
    rfl

/-- The E0 two-state lumping package has zero idempotence defect. -/
theorem bool_lumping_delta_zero :
    ∀ x : boolCarrier.X,
      (discreteDefect Bool).d
        (boolLumpingPackaging.E (boolLumpingPackaging.E x))
        (boolLumpingPackaging.E x) = 0 :=
  (delta_zero_iff_fixed boolLumpingPackaging (discreteDefect Bool)).1

end SbtCosmo.Idempotence
