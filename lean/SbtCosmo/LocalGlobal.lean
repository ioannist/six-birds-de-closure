import SbtCosmo.Common

/-!
T4 local-global four-status receipt.

This module gives a self-contained finite re-derivation of the F4 normal form:
each local family is overlap-inconsistent, compatible-non-global, globally
ambiguous, or globally exact.  The finite image/fiber calculations use explicit
lists, not mathlib `Fintype`, so the target remains mathlib-free.
-/
namespace SbtCosmo.LocalGlobal

/-- A finite gluing record: global states, local-family data, compatibility,
and a restriction map whose global restrictions are compatible. -/
structure GluingRecord where
  G : Type
  F : Type
  decF : DecidableEq F
  globals : List G
  globals_nodup : globals.Nodup
  globals_complete : ∀ g : G, g ∈ globals
  Comp : F → Prop
  decComp : DecidablePred Comp
  R : G → F
  R_comp : ∀ g : G, Comp (R g)

instance (X : GluingRecord) : DecidableEq X.F := X.decF

instance (X : GluingRecord) : DecidablePred X.Comp := X.decComp

/-- A local family globalizes when it is the restriction of some global state. -/
def globalizes (X : GluingRecord) (a : X.F) : Prop :=
  ∃ g : X.G, X.R g = a

/-- Image membership for the restriction map. -/
def inImage (X : GluingRecord) (a : X.F) : Prop :=
  ∃ g : X.G, X.R g = a

/-- Count the global states in an explicit list whose restriction is `a`. -/
def countFiberList {G F : Type} [DecidableEq F] (R : G → F) (a : F) :
    List G → Nat
  | [] => 0
  | g :: gs => (if R g = a then 1 else 0) + countFiberList R a gs

/-- The explicit-list fiber cardinality of a local family. -/
def fiberCard (X : GluingRecord) (a : X.F) : Nat :=
  countFiberList X.R a X.globals

/-- The four mutually exclusive F4 local-global statuses. -/
inductive Status
  | overlapInconsistent
  | compatibleNonGlobal
  | globallyAmbiguous
  | globallyExact
  deriving DecidableEq

/-- Finite F4 classifier by compatibility, image membership, and fiber count. -/
def classify (X : GluingRecord) (a : X.F) : Status :=
  if X.Comp a then
    if fiberCard X a = 0 then
      Status.compatibleNonGlobal
    else if fiberCard X a = 1 then
      Status.globallyExact
    else
      Status.globallyAmbiguous
  else
    Status.overlapInconsistent

/-- Local-to-global image criterion. Compatibility is the F4 side condition;
the equivalence itself is definitional for this finite restriction map. -/
theorem globalizes_iff_in_image (X : GluingRecord) (a : X.F) (_h : X.Comp a) :
    globalizes X a ↔ inImage X a := by
  rfl

theorem countFiberList_ne_zero_iff_exists {G F : Type} [DecidableEq F]
    (R : G → F) (a : F) :
    ∀ gs : List G,
      countFiberList R a gs ≠ 0 ↔ ∃ g : G, g ∈ gs ∧ R g = a := by
  intro gs
  induction gs with
  | nil =>
      simp [countFiberList]
  | cons g rest ih =>
      by_cases hg : R g = a
      · simp [countFiberList, hg]
      · simp [countFiberList, hg, ih]

/-- Nonzero explicit fiber count is equivalent to globalization. -/
theorem fiberCard_ne_zero_iff_globalizes (X : GluingRecord) (a : X.F) :
    fiberCard X a ≠ 0 ↔ globalizes X a := by
  rw [fiberCard, countFiberList_ne_zero_iff_exists]
  constructor
  · intro h
    cases h with
    | intro g hg =>
        exact ⟨g, hg.right⟩
  · intro h
    cases h with
    | intro g hg =>
        exact ⟨g, X.globals_complete g, hg⟩

/-- Zero explicit fiber count is equivalent to failure to globalize. -/
theorem fiberCard_eq_zero_iff_not_globalizes (X : GluingRecord) (a : X.F) :
    fiberCard X a = 0 ↔ ¬ globalizes X a := by
  constructor
  · intro hzero hglob
    have hne : fiberCard X a ≠ 0 :=
      (fiberCard_ne_zero_iff_globalizes X a).2 hglob
    exact hne hzero
  · intro hnot
    by_cases hzero : fiberCard X a = 0
    · exact hzero
    · have hglob : globalizes X a :=
        (fiberCard_ne_zero_iff_globalizes X a).1 hzero
      exact False.elim (hnot hglob)

/-- On a list without duplicates, a singleton counted fiber is a unique state. -/
theorem countFiberList_eq_one_iff_unique {G F : Type} [DecidableEq F]
    (R : G → F) (a : F) (gs : List G) (hn : gs.Nodup) :
    countFiberList R a gs = 1 ↔
      ∃ g, (g ∈ gs ∧ R g = a) ∧ ∀ y, (y ∈ gs ∧ R y = a) → y = g := by
  induction gs with
  | nil => simp [countFiberList]
  | cons g rest ih =>
    have hnrest : rest.Nodup := (List.nodup_cons.mp hn).2
    have hnot : g ∉ rest := (List.nodup_cons.mp hn).1
    by_cases hg : R g = a
    · constructor
      · intro h
        have hz : countFiberList R a rest = 0 := by
          simpa [countFiberList, hg] using h
        refine ⟨g, ⟨by simp, hg⟩, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy.1 with heq | hmem
        · exact heq
        · have hne := (countFiberList_ne_zero_iff_exists R a rest).2 ⟨y, hmem, hy.2⟩
          exact False.elim (hne hz)
      · rintro ⟨y, hy, hu⟩
        have hgy : g = y := hu g ⟨by simp, hg⟩
        have hz : countFiberList R a rest = 0 := by
          by_cases hz : countFiberList R a rest = 0
          · exact hz
          · rcases (countFiberList_ne_zero_iff_exists R a rest).1 hz with ⟨z, hzmem, hza⟩
            have hzg : z = g := (hu z ⟨by simp [hzmem], hza⟩).trans hgy.symm
            exact False.elim (hnot (hzg ▸ hzmem))
        simp [countFiberList, hg, hz]
    · rw [countFiberList]
      simp only [hg, ↓reduceIte, Nat.zero_add]
      rw [ih hnrest]
      constructor
      · rintro ⟨y, hy, hu⟩
        refine ⟨y, ⟨by simp [hy.1], hy.2⟩, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz.1 with heq | hmem
        · exact False.elim (hg (heq ▸ hz.2))
        · exact hu z ⟨hmem, hz.2⟩
      · rintro ⟨y, hy, hu⟩
        have hymem : y ∈ rest := by
          rcases List.mem_cons.mp hy.1 with heq | hmem
          · exact False.elim (hg (heq ▸ hy.2))
          · exact hmem
        exact ⟨y, ⟨hymem, hy.2⟩, fun z hz => hu z ⟨by simp [hz.1], hz.2⟩⟩

/-- Semantic uniqueness, independent of the exhaustive-list representation. -/
theorem fiberCard_eq_one_iff_unique_global (X : GluingRecord) (a : X.F) :
    fiberCard X a = 1 ↔ ∃ g : X.G, X.R g = a ∧ ∀ y, X.R y = a → y = g := by
  rw [fiberCard, countFiberList_eq_one_iff_unique X.R a X.globals X.globals_nodup]
  constructor
  · rintro ⟨g, hg, hu⟩
    exact ⟨g, hg.2, fun y hy => hu y ⟨X.globals_complete y, hy⟩⟩
  · rintro ⟨g, hg, hu⟩
    exact ⟨g, ⟨X.globals_complete g, hg⟩, fun y hy => hu y hy.2⟩

theorem nat_one_lt_of_ne_zero_ne_one (n : Nat) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    1 < n := by
  cases n with
  | zero =>
      exact False.elim (h0 rfl)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim (h1 rfl)
      | succ n =>
          simp

/-- T4/F4 finite normal form: each local family has exactly the status selected
by compatibility, image membership, and fiber cardinality. -/
theorem four_status_classification (X : GluingRecord) (a : X.F) :
    (classify X a = Status.overlapInconsistent ↔ ¬ X.Comp a) ∧
    (classify X a = Status.compatibleNonGlobal ↔
      (X.Comp a ∧ ¬ globalizes X a)) ∧
    (classify X a = Status.globallyAmbiguous ↔
      (X.Comp a ∧ globalizes X a ∧ 1 < fiberCard X a)) ∧
    (classify X a = Status.globallyExact ↔
      (X.Comp a ∧ globalizes X a ∧ fiberCard X a = 1)) := by
  by_cases hc : X.Comp a
  · by_cases h0 : fiberCard X a = 0
    · have hnotGlob : ¬ globalizes X a :=
        (fiberCard_eq_zero_iff_not_globalizes X a).1 h0
      have hnotNeZero : ¬ fiberCard X a ≠ 0 := by
        intro hne
        exact hne h0
      have hnotGt : ¬ 1 < fiberCard X a := by
        rw [h0]
        decide
      have hnotOne : fiberCard X a ≠ 1 := by
        rw [h0]
        decide
      simp [classify, hc, h0, hnotGlob]
    · by_cases h1 : fiberCard X a = 1
      · have hglob : globalizes X a :=
          (fiberCard_ne_zero_iff_globalizes X a).1 h0
        have hnotGt : ¬ 1 < fiberCard X a := by
          rw [h1]
          decide
        simp [classify, hc, h1, hglob]
      · have hglob : globalizes X a :=
          (fiberCard_ne_zero_iff_globalizes X a).1 h0
        have hgt : 1 < fiberCard X a :=
          nat_one_lt_of_ne_zero_ne_one (fiberCard X a) h0 h1
        have hnotNotGlob : ¬ ¬ globalizes X a := by
          intro hnot
          exact hnot hglob
        simp [classify, hc, h0, h1, hglob, hgt]
  · simp [classify, hc]

/-- Two local SN/BAO distance-duality sections. -/
inductive CDDRLocalFamily
  | etaEqOne
  | etaNeOne
  deriving DecidableEq

/-- One closed FLRW metric-distance object in the toy CDDR chart. -/
inductive FLRWDistance
  | closed

/-- A two-patch CDDR gluing record: the closed FLRW object restricts to
`etaEqOne`; an `etaNeOne` fitted local family is compatible but non-global. -/
def cddrRecord : GluingRecord where
  G := FLRWDistance
  F := CDDRLocalFamily
  decF := inferInstance
  globals := [FLRWDistance.closed]
  globals_nodup := by simp
  globals_complete := by
    intro g
    cases g
    simp
  Comp _ := True
  decComp := by
    intro a
    infer_instance
  R
    | FLRWDistance.closed => CDDRLocalFamily.etaEqOne
  R_comp := by
    intro g
    trivial

/-- Cosmological T4 example: SN/BAO `eta ≠ 1` lands in
compatible-non-global, i.e. a local-global gluing obstruction. -/
theorem cddr_eta_ne_one_compatibleNonGlobal :
    classify cddrRecord CDDRLocalFamily.etaNeOne =
      Status.compatibleNonGlobal := by
  rfl

/-- The same CDDR example stated with the semantic predicates. -/
theorem cddr_eta_ne_one_semantics :
    cddrRecord.Comp CDDRLocalFamily.etaNeOne ∧
      ¬ globalizes cddrRecord CDDRLocalFamily.etaNeOne := by
  constructor
  · trivial
  · intro h
    cases h with
    | intro g hg =>
        cases g
        contradiction

end SbtCosmo.LocalGlobal
