import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
The original uniform four-bit access carrier, with actual conditional-mean
completions. Its endpoints do not determine one another, yet their completions
commute. Every deterministic mediator determining both endpoints is injective
on this carrier. None of these facts establishes a physical QM/GR carrier or
converts a numerical vacuum discrepancy into a commutator.
-/
namespace SbtCosmo.Derivation.AccessFork

@[ext]
structure State where
  d0 : Bool
  d1 : Bool
  d2 : Bool
  d3 : Bool
  deriving DecidableEq, Fintype, Inhabited

abbrev Access := Bool × Bool × Bool

def qmAccess (s : State) : Access := (s.d0, s.d1, s.d2)
def grAccess (s : State) : Access := (s.d0, s.d2, s.d3)
def overlapAccess (s : State) : Bool × Bool := (s.d0, s.d2)

def FactorsThrough {X Y Z : Type*} (source : X → Y) (target : X → Z) : Prop :=
  ∃ returnMap : Y → Z, ∀ x, returnMap (source x) = target x

/-- No finiteness or independence assumption is needed to recover a full mode tuple. -/
theorem overlapping_readouts_iff_full_modes {X Y D0 D1 D2 D3 : Type*}
    (modes : X → D0 × D1 × D2 × D3) (r : X → Y) :
    (FactorsThrough r (fun x => ((modes x).1, (modes x).2.1, (modes x).2.2.1)) ∧
      FactorsThrough r (fun x => ((modes x).1, (modes x).2.2.1, (modes x).2.2.2))) ↔
        FactorsThrough r modes := by
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨g, hg⟩⟩
    refine ⟨fun y => ((q y).1, (q y).2.1, (q y).2.2, (g y).2.2), ?_⟩
    intro x
    change ((q (r x)).1, (q (r x)).2.1, (q (r x)).2.2, (g (r x)).2.2) = modes x
    rw [hq, hg]
  · rintro ⟨decode, hd⟩
    constructor
    · refine ⟨fun y => ((decode y).1, (decode y).2.1, (decode y).2.2.1), ?_⟩
      intro x
      change ((decode (r x)).1, (decode (r x)).2.1, (decode (r x)).2.2.1) = _
      rw [hd]
    · refine ⟨fun y => ((decode y).1, (decode y).2.2.1, (decode y).2.2.2), ?_⟩
      intro x
      change ((decode (r x)).1, (decode (r x)).2.2.1, (decode (r x)).2.2.2) = _
      rw [hd]

/-- Complete fiber criterion; inverse choice only defines a return on the image. -/
theorem factorsThrough_iff_fiber_constant {X Y Z : Type*} [Nonempty X]
    (source : X → Y) (target : X → Z) :
    FactorsThrough source target ↔ ∀ x y, source x = source y → target x = target y := by
  constructor
  · rintro ⟨r, hr⟩ x y he
    rw [← hr x, ← hr y, he]
  · intro hf
    classical
    refine ⟨fun y => target (Function.invFun source y), ?_⟩
    intro x
    exact hf _ x (Function.apply_invFun_apply)

/-- The two endpoints together retain all four declared coordinates. -/
theorem joint_access_injective : Function.Injective (fun s => (qmAccess s, grAccess s)) := by
  intro x y he
  have hq := congrArg Prod.fst he
  have hg := congrArg Prod.snd he
  have h0 := congrArg Prod.fst hq
  have h1 := congrArg (fun a : Access => a.2.1) hq
  have h2 := congrArg (fun a : Access => a.2.2) hq
  have h3 := congrArg (fun a : Access => a.2.2) hg
  exact State.ext h0 h1 h2 h3

/-- Recover a complete state directly from the two endpoint records. -/
def recoverState (qm gr : Access) : State := ⟨qm.1, qm.2.1, qm.2.2, gr.2.2⟩

theorem recover_access (s : State) : recoverState (qmAccess s) (grAccess s) = s := by rfl

/-- Full-state recovery uses only the supplied endpoint decoders and four projections. -/
theorem joint_mediator_iff_full_state {Y : Type*} (r : State → Y) :
    (FactorsThrough r qmAccess ∧ FactorsThrough r grAccess) ↔
      FactorsThrough r (fun s : State => s) := by
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨g, hg⟩⟩
    refine ⟨fun y => recoverState (q y) (g y), ?_⟩
    intro s
    change recoverState (q (r s)) (g (r s)) = s
    rw [hq, hg, recover_access]
  · rintro ⟨decode, hd⟩
    constructor
    · exact ⟨fun y => qmAccess (decode y), fun s => congrArg qmAccess (hd s)⟩
    · exact ⟨fun y => grAccess (decode y), fun s => congrArg grAccess (hd s)⟩

/-- Quantifies over every deterministic mediator, not a finite list of labels. -/
theorem joint_mediator_iff_injective {Y : Type*} (r : State → Y) :
    (FactorsThrough r qmAccess ∧ FactorsThrough r grAccess) ↔ Function.Injective r := by
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨g, hg⟩⟩ x y he
    apply joint_access_injective
    change (qmAccess x, grAccess x) = (qmAccess y, grAccess y)
    apply Prod.ext
    · rw [← hq x, ← hq y, he]
    · rw [← hg x, ← hg y, he]
  · intro hi
    classical
    constructor
    · exact ⟨fun y => qmAccess (Function.invFun r y), fun x =>
        congrArg qmAccess (Function.leftInverse_invFun hi x)⟩
    · exact ⟨fun y => grAccess (Function.invFun r y), fun x =>
        congrArg grAccess (Function.leftInverse_invFun hi x)⟩

theorem joint_mediator_discrete_fibers {Y : Type*} {r : State → Y}
    (h : FactorsThrough r qmAccess ∧ FactorsThrough r grAccess) (x y : State) :
    r x = r y ↔ x = y := by
  exact ⟨fun he => (joint_mediator_iff_injective r).mp h he, congrArg r⟩

theorem state_card : Fintype.card State = 16 := by decide

theorem mediator_card_lower_bound {Y : Type*} [Fintype Y] {r : State → Y}
    (h : FactorsThrough r qmAccess ∧ FactorsThrough r grAccess) :
    16 ≤ Fintype.card Y := by
  rw [← state_card]
  exact Fintype.card_le_of_injective r ((joint_mediator_iff_injective r).mp h)

/-- Even an infinite ambient record type has exactly sixteen realized records. -/
theorem mediator_range_card {Y : Type*} {r : State → Y}
    (h : FactorsThrough r qmAccess ∧ FactorsThrough r grAccess) :
    Nat.card (Set.range r) = 16 := by
  have he := Nat.card_congr (Equiv.ofInjective r ((joint_mediator_iff_injective r).mp h))
  rw [← he, Nat.card_eq_fintype_card, state_card]

/-- The record-count bound is attained by the full-state mediator. -/
theorem identity_mediator_sharp :
    (FactorsThrough (fun s : State => s) qmAccess ∧
      FactorsThrough (fun s : State => s) grAccess) ∧ Fintype.card State = 16 := by
  exact ⟨⟨⟨qmAccess, fun _ => rfl⟩, ⟨grAccess, fun _ => rfl⟩⟩, state_card⟩

/-- A reversible re-encoding can retain all coordinates without copying them literally. -/
def xorMemory (s : State) : State := {s with d3 := Bool.xor s.d1 s.d3}

theorem xorMemory_involutive : Function.Involutive xorMemory := by
  intro s
  apply State.ext <;> simp [xorMemory]

theorem xorMemory_mediator : FactorsThrough xorMemory qmAccess ∧ FactorsThrough xorMemory grAccess := by
  apply (joint_mediator_iff_injective xorMemory).mpr
  exact xorMemory_involutive.injective

def base : State := ⟨false, false, false, false⟩
def phaseSplit : State := ⟨false, true, false, false⟩
def curvatureSplit : State := ⟨false, false, false, true⟩

theorem qm_not_determine_gr : ¬ FactorsThrough qmAccess grAccess := by
  intro h
  have he := (factorsThrough_iff_fiber_constant qmAccess grAccess).mp h
    base curvatureSplit (by rfl)
  have hd := congrArg (fun a : Access => a.2.2) he
  change false = true at hd
  cases hd

theorem gr_not_determine_qm : ¬ FactorsThrough grAccess qmAccess := by
  intro h
  have he := (factorsThrough_iff_fiber_constant grAccess qmAccess).mp h
    base phaseSplit (by rfl)
  have hd := congrArg (fun a : Access => a.2.1) he
  change false = true at hd
  cases hd

/-- Adding only a function of an existing readout cannot split its fibers. -/
theorem redundant_augmentation {X Y Z T : Type*} [Nonempty X]
    (source : X → Y) (auxiliary : Y → Z) (target : X → T) :
    FactorsThrough (fun x => (source x, auxiliary (source x))) target ↔
      FactorsThrough source target := by
  simp only [factorsThrough_iff_fiber_constant, Prod.mk.injEq]
  constructor
  · intro h x y he
    exact h x y ⟨he, congrArg auxiliary he⟩
  · intro h x y he
    exact h x y he.1

theorem qm_augmented_still_not_determine_gr {Y : Type*} (auxiliary : Access → Y) :
    ¬ FactorsThrough (fun s => (qmAccess s, auxiliary (qmAccess s))) grAccess := by
  rw [redundant_augmentation]
  exact qm_not_determine_gr

def flipQM (s : State) : State := {s with d3 := !s.d3}
def flipGR (s : State) : State := {s with d1 := !s.d1}

theorem flipQM_involutive : Function.Involutive flipQM := by
  intro s
  simp [flipQM]

theorem flipGR_involutive : Function.Involutive flipGR := by
  intro s
  simp [flipGR]

theorem flips_commute (s : State) : flipQM (flipGR s) = flipGR (flipQM s) := by rfl

theorem flipQM_ne (s : State) : flipQM s ≠ s := by
  intro h
  have he := congrArg State.d3 h
  cases hd : s.d3 <;> simp [flipQM, hd] at he

theorem flipGR_ne (s : State) : flipGR s ≠ s := by
  intro h
  have he := congrArg State.d1 h
  cases hd : s.d1 <;> simp [flipGR, hd] at he

theorem qm_fiber_iff (s t : State) : qmAccess t = qmAccess s ↔ t = s ∨ t = flipQM s := by
  constructor
  · intro h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg (fun a : Access => a.2.1) h
    have h2 := congrArg (fun a : Access => a.2.2) h
    by_cases he : t.d3 = s.d3
    · exact Or.inl (State.ext h0 h1 h2 he)
    · apply Or.inr
      apply State.ext
      · exact h0
      · exact h1
      · exact h2
      · cases ht : t.d3 <;> cases hs : s.d3 <;> simp_all [flipQM]
  · rintro (rfl | rfl) <;> rfl

theorem gr_fiber_iff (s t : State) : grAccess t = grAccess s ↔ t = s ∨ t = flipGR s := by
  constructor
  · intro h
    have h0 := congrArg Prod.fst h
    have h2 := congrArg (fun a : Access => a.2.1) h
    have h3 := congrArg (fun a : Access => a.2.2) h
    by_cases he : t.d1 = s.d1
    · exact Or.inl (State.ext h0 he h2 h3)
    · apply Or.inr
      apply State.ext
      · exact h0
      · cases ht : t.d1 <;> cases hs : s.d1 <;> simp_all [flipGR]
      · exact h2
      · exact h3
  · rintro (rfl | rfl) <;> rfl

theorem overlap_fiber_iff : ∀ s t : State,
    overlapAccess t = overlapAccess s ↔
      t = s ∨ t = flipQM s ∨ t = flipGR s ∨ t = flipQM (flipGR s) := by decide

noncomputable section
open scoped BigOperators

/-- Literal uniform conditional mean over a finite access fiber. -/
def conditionalMean {Y : Type*} [DecidableEq Y] (access : State → Y) (f : State → ℝ) (s : State) : ℝ :=
  (∑ t ∈ Finset.univ.filter (fun t => access t = access s), f t) /
    (Finset.univ.filter (fun t => access t = access s)).card

def qmCompletion (f : State → ℝ) (s : State) : ℝ := (f s + f (flipQM s))/2
def grCompletion (f : State → ℝ) (s : State) : ℝ := (f s + f (flipGR s))/2

def overlapCompletion (f : State → ℝ) (s : State) : ℝ :=
  (f s + f (flipQM s) + f (flipGR s) + f (flipQM (flipGR s)))/4

theorem overlap_fiber_finset (s : State) :
    Finset.univ.filter (fun t => overlapAccess t = overlapAccess s) =
      {s, flipQM s, flipGR s, flipQM (flipGR s)} := by
  ext t
  simp [overlap_fiber_iff]

theorem qm_fiber_finset (s : State) :
    Finset.univ.filter (fun t => qmAccess t = qmAccess s) = {s, flipQM s} := by
  ext t
  simp [qm_fiber_iff]

theorem gr_fiber_finset (s : State) :
    Finset.univ.filter (fun t => grAccess t = grAccess s) = {s, flipGR s} := by
  ext t
  simp [gr_fiber_iff]

theorem qm_completion_is_conditional_mean : conditionalMean qmAccess = qmCompletion := by
  funext f s
  simp [conditionalMean, qm_fiber_finset, qmCompletion, (flipQM_ne s).symm]

theorem gr_completion_is_conditional_mean : conditionalMean grAccess = grCompletion := by
  funext f s
  simp [conditionalMean, gr_fiber_finset, grCompletion, (flipGR_ne s).symm]

theorem overlap_completion_is_conditional_mean :
    conditionalMean overlapAccess = overlapCompletion := by
  funext f s
  obtain ⟨d0,d1,d2,d3⟩ := s
  cases d0 <;> cases d1 <;> cases d2 <;> cases d3 <;>
    simp [conditionalMean, overlap_fiber_finset, overlapCompletion, flipQM, flipGR, add_assoc]

/-- Sequential coordinate means keep just the overlap {d0,d2}. -/
theorem completion_composition_overlap (f : State → ℝ) :
    qmCompletion (grCompletion f) = overlapCompletion f := by
  funext s
  simp only [qmCompletion, grCompletion, overlapCompletion, flips_commute]
  ring

theorem qm_completion_idempotent : ∀ f, qmCompletion (qmCompletion f) = qmCompletion f := by
  intro f
  funext s
  simp only [qmCompletion, flipQM_involutive s]
  ring

theorem gr_completion_idempotent : ∀ f, grCompletion (grCompletion f) = grCompletion f := by
  intro f
  funext s
  simp only [grCompletion, flipGR_involutive s]
  ring

theorem original_completions_commute (f : State → ℝ) :
    qmCompletion (grCompletion f) = grCompletion (qmCompletion f) := by
  funext s
  simp only [qmCompletion, grCompletion, flips_commute]
  ring

theorem original_conditional_means_commute (f : State → ℝ) :
    conditionalMean qmAccess (conditionalMean grAccess f) =
      conditionalMean grAccess (conditionalMean qmAccess f) := by
  rw [qm_completion_is_conditional_mean, gr_completion_is_conditional_mean]
  exact original_completions_commute f

/-- The pointwise commutator defect on any scalar observable is empty. -/
theorem original_defect_empty (f : State → ℝ) :
    {s | qmCompletion (grCompletion f) s ≠ grCompletion (qmCompletion f) s} = ∅ := by
  ext s
  simp [congrFun (original_completions_commute f) s]

end
end SbtCosmo.Derivation.AccessFork
