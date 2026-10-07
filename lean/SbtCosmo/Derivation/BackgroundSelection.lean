import Mathlib.Tactic

/-!
Exact demarcation lemmas. Two admissible readouts refute a value forced by
that admissibility predicate; they do not forbid additional selectors.
The Step26 background-shift identity exhibits the actual nonconstant term.
No theorem here derives a physical cosmological constant or certifies a
floating-point convergence run.
-/
namespace SbtCosmo.Derivation.BackgroundSelection

/-- The predicate alone forces `v` if every admitted state reads `v`. -/
def ForcesValue {X V : Type*} (admitted : X → Prop) (readout : X → V) (v : V) : Prop :=
  ∀ x, admitted x → readout x = v

theorem two_admitted_values_not_forced {X V : Type*}
    (admitted : X → Prop) (readout : X → V) {x y : X}
    (hx : admitted x) (hy : admitted y) (hne : readout x ≠ readout y) :
    ¬ ∃ v, ForcesValue admitted readout v := by
  rintro ⟨v, h⟩
  exact hne ((h x hx).trans (h y hy).symm)

/-- Equal accessible records and unequal targets obstruct every factorization
through those records. This conclusion needs equal records, not only two
passing Boolean audit outcomes. -/
theorem same_record_different_value_no_factor {X A V : Type*}
    (record : X → A) (readout : X → V) {x y : X}
    (heq : record x = record y) (hne : readout x ≠ readout y) :
    ¬ ∃ f : A → V, ∀ z, f (record z) = readout z := by
  rintro ⟨f, hf⟩
  apply hne
  rw [← hf x, ← hf y, heq]

/-- Sitewise Step26 potential, with density `|psi|²` and gradient energy fixed. -/
def potential (background kappa density gradientEnergy : ℝ) : ℝ :=
  background + kappa * (gradientEnergy + background * density)

theorem background_shift_identity (background kappa density gradientEnergy shift : ℝ) :
    potential (background + shift) kappa density gradientEnergy -
      potential background kappa density gradientEnergy = shift * (1 + kappa * density) := by
  simp only [potential]
  ring

/-- On two sites with distinct densities, a nonzero shift at nonzero coupling
does not act as a scalar identity shift of the Hamiltonian. -/
theorem background_shift_not_scalar {background kappa p q gradientEnergy shift : ℝ}
    (hk : kappa ≠ 0) (hs : shift ≠ 0) (hpq : p ≠ q) :
    potential (background + shift) kappa p gradientEnergy -
        potential background kappa p gradientEnergy ≠
      potential (background + shift) kappa q gradientEnergy -
        potential background kappa q gradientEnergy := by
  rw [background_shift_identity, background_shift_identity]
  intro h
  apply hpq
  have h' : shift * kappa * (p - q) = 0 := by nlinarith [h]
  have : p - q = 0 := (mul_eq_zero.mp h').resolve_left (mul_ne_zero hs hk)
  linarith

end SbtCosmo.Derivation.BackgroundSelection
