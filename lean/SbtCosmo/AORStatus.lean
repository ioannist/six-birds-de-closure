/-!
T7 no-unstatused-residual well-formedness receipt.

The status vocabulary contains only the 15 valid AOR statuses. An unstatused
residual is represented by `none` from a partial classifier, not by a status
constructor.
-/
namespace SbtCosmo.AORStatus

/-- The canonical 15 valid AOR statuses: 11 base and 4 asymptotic. -/
inductive Status
  | zero
  | budgeted
  | bridged
  | hidden
  | moduli
  | selected
  | probabilistic
  | out_of_scope
  | nonclaim
  | blocked
  | approved_other
  | asymptotic_budgeted
  | summable
  | contractive
  | eventual_zero
  deriving DecidableEq

/-- A formed status package: `none` is the validator error ruled out by F9. -/
structure StatusPackage (R : Type) where
  st : R → Option Status
  discipline : ∀ r : R, (st r).isSome = true

/-- A residual has exactly one status when the classifier returns a single
`some` value for it. -/
def HasUniqueStatus {R : Type} (P : StatusPackage R) (r : R) : Prop :=
  ∃ s : Status, P.st r = some s ∧ ∀ t : Status, P.st r = some t → t = s

/-- T7 / F9: a disciplined status package has no unstatused residuals and every
residual has exactly one valid status. -/
theorem no_unstatused_residual {R : Type} (P : StatusPackage R) :
    (∀ r : R, (P.st r).isSome = true) ∧
      (∀ r : R, HasUniqueStatus P r) := by
  constructor
  · exact P.discipline
  · intro r
    have hsome := P.discipline r
    cases h : P.st r with
    | none =>
        simp [h] at hsome
    | some s =>
        exact ⟨s, h, by
          intro t ht
          rw [h] at ht
          injection ht with hts
          exact hts.symm⟩

/-- E0 ledger residual identifiers, matching the four-row synthetic ledger. -/
inductive E0Residual where
  | dataFree
  | xiToyScope
  | qDiagnostic
  | skeletonPaths
  deriving DecidableEq

/-- The E0 synthetic ledger status package has no `none` entries. -/
def e0StatusPackage : StatusPackage E0Residual where
  st
    | E0Residual.dataFree => some Status.zero
    | E0Residual.xiToyScope => some Status.nonclaim
    | E0Residual.qDiagnostic => some Status.nonclaim
    | E0Residual.skeletonPaths => some Status.approved_other
  discipline := by
    intro r
    cases r <;> rfl

/-- Worked T7 receipt for the E0 synthetic status ledger. -/
theorem e0_no_unstatused :
    (∀ r : E0Residual, (e0StatusPackage.st r).isSome = true) ∧
      (∀ r : E0Residual, HasUniqueStatus e0StatusPackage r) :=
  no_unstatused_residual e0StatusPackage

end SbtCosmo.AORStatus
