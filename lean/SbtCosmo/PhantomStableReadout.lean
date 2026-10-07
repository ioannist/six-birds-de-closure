/-!
T5 finite phantom-crossing stable-readout witness.

This module certifies only the finite P4 witness components in scope here:
P-dens (`rhoEff > 0` on the grid) and S-stab (a rational Gershgorin
no-growing-mode certificate for the continuous-generator Jacobian).  It does
not certify P-adeq, and it makes no ghost-absence claim.
-/
namespace SbtCosmo.PhantomStableReadout

/-- Three-node rational grid mirroring the E0 Toy-3 structure. -/
inductive Grid3 where
  | low
  | cross
  | high
  deriving DecidableEq

/-- Absolute value on rationals, kept local to avoid importing mathlib. -/
def ratAbs (q : Rat) : Rat :=
  if q < 0 then -q else q

/-- A two-by-two rational continuous-generator Jacobian. -/
structure Generator2 where
  j00 : Rat
  j01 : Rat
  j10 : Rat
  j11 : Rat

/-- Gershgorin row-disc upper bounds for a two-by-two real generator. -/
def gershgorinRow0Upper (G : Generator2) : Rat :=
  G.j00 + ratAbs G.j01

/-- Gershgorin row-disc upper bounds for a two-by-two real generator. -/
def gershgorinRow1Upper (G : Generator2) : Rat :=
  G.j11 + ratAbs G.j10

/-- Decidable rational no-growing-mode certificate: every Gershgorin row disc
lies in the closed left half-plane. This is a finite algebraic certificate, not
an abstract spectral theorem. -/
def NoGrowingMode (G : Generator2) : Prop :=
  gershgorinRow0Upper G ≤ 0 ∧ gershgorinRow1Upper G ≤ 0

/-- A finite phantom-crossing witness over a rational redshift grid. `wShift`
stores the exact sampled value of `w_eff + 1`; a sign change of `wShift` is a
crossing through `w_eff = -1`. -/
structure Witness where
  z : Grid3 → Rat
  rhoEff : Grid3 → Rat
  rho_pos : ∀ i : Grid3, 0 < rhoEff i
  wShift : Grid3 → Rat
  gen : Generator2
  stable : NoGrowingMode gen

/-- Effective equation-of-state sample reconstructed from `w_eff + 1`. -/
def wEff (W : Witness) (i : Grid3) : Rat :=
  -1 + W.wShift i

/-- Finite-grid density positivity, equivalent to positive minimum on this
three-node grid. -/
def PDens (W : Witness) : Prop :=
  ∀ i : Grid3, 0 < W.rhoEff i

/-- Two adjacent samples cross `w_eff = -1` exactly when `w_eff + 1` changes sign. -/
def SignChange (a b : Rat) : Prop :=
  (a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a)

instance signChangeDecidable (a b : Rat) : Decidable (SignChange a b) := by
  unfold SignChange
  infer_instance

instance noGrowingModeDecidable (G : Generator2) : Decidable (NoGrowingMode G) := by
  unfold NoGrowingMode
  infer_instance

/-- The adjacent-pair sign-change count for the three-node grid. -/
def signChangeCount (W : Witness) : Nat :=
  (if SignChange (W.wShift Grid3.low) (W.wShift Grid3.cross) then 1 else 0) +
    (if SignChange (W.wShift Grid3.cross) (W.wShift Grid3.high) then 1 else 0)

/-- Toy-3 style diagonal generator: centers are negative and radii are zero. -/
def toy3Generator : Generator2 where
  j00 := -2
  j01 := 0
  j10 := 0
  j11 := -1

/-- The finite rational witness: positive density, one phantom crossing, and
a diagonal no-growing-mode continuous generator. -/
def toy3Witness : Witness where
  z
    | Grid3.low => 0
    | Grid3.cross => 1
    | Grid3.high => 2
  rhoEff
    | Grid3.low => 84
    | Grid3.cross => 72
    | Grid3.high => 92
  rho_pos := by
    intro i
    cases i
    · change (0 : Rat).blt 84 = true
      rfl
    · change (0 : Rat).blt 72 = true
      rfl
    · change (0 : Rat).blt 92 = true
      rfl
  wShift
    | Grid3.low => Rat.mk' (-1) 9 (by decide) (by decide)
    | Grid3.cross => Rat.mk' 1 27 (by decide) (by decide)
    | Grid3.high => Rat.mk' 9 23 (by decide) (by decide)
  gen := toy3Generator
  stable := by
    constructor
    · change (0 : Rat).blt (gershgorinRow0Upper toy3Generator) = false
      simp [gershgorinRow0Upper, toy3Generator, ratAbs]
      rw [Rat.add_def]
      rfl
    · change (0 : Rat).blt (gershgorinRow1Upper toy3Generator) = false
      simp [gershgorinRow1Upper, toy3Generator, ratAbs]
      rw [Rat.add_def]
      rfl

/-- T5 crossing receipt: the finite `w_eff + 1` profile has exactly one
adjacent sign change. -/
theorem toy3_crossing_count_one :
    signChangeCount toy3Witness = 1 := by
  rfl

/-- T5 P-dens receipt: all density samples are strictly positive. -/
theorem toy3_p_dens :
    PDens toy3Witness := by
  intro i
  exact toy3Witness.rho_pos i

/-- T5 S-stab receipt: the continuous generator has the rational Gershgorin
no-growing-mode certificate. -/
theorem toy3_no_growing_mode :
    NoGrowingMode toy3Witness.gen :=
  toy3Witness.stable

/-- The toy witness has an explicit phantom sample, `w_eff < -1`. -/
theorem toy3_has_phantom_sample :
    wEff toy3Witness Grid3.low < -1 := by
  simp [wEff, toy3Witness]
  rw [Rat.add_def]
  rfl

/-- T5 faithful finite P4 witness: P-dens and S-stab hold, and the sampled
readout crosses `w_eff = -1` exactly once with a phantom node. This does not
claim P-adeq and does not claim ghost absence. -/
theorem phantom_stable_readout_witness :
    ∃ (W : Witness) (i : Grid3),
      signChangeCount W = 1 ∧ PDens W ∧ NoGrowingMode W.gen ∧ wEff W i < -1 := by
  exact ⟨toy3Witness, Grid3.low, toy3_crossing_count_one, toy3_p_dens,
    toy3_no_growing_mode, toy3_has_phantom_sample⟩

end SbtCosmo.PhantomStableReadout
