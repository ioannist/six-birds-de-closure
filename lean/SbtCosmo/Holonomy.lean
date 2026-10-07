import SbtCosmo.Common

/-!
T6 finite Hubble-holonomy receipt.

This module certifies a finite route-graph witness for nonzero loop transport
and the Holonomy-with-Memory pattern: the loop is trivial on the current
scalar quotient while nontrivial on a predictive quotient.  It does not measure
the empirical E4 posterior holonomy.
-/
namespace SbtCosmo.Holonomy

open SbtCosmo.Common

/-- A finite route graph with bridge transports acting on readout states. -/
structure RouteGraph where
  Route : Type
  decRoute : DecidableEq Route
  routes : List Route
  routes_complete : ∀ r : Route, r ∈ routes
  S : Type
  decState : DecidableEq S
  states : List S
  states_complete : ∀ s : S, s ∈ states
  bridge : Route → Route → S → S

instance (Γ : RouteGraph) : DecidableEq Γ.Route := Γ.decRoute

instance (Γ : RouteGraph) : DecidableEq Γ.S := Γ.decState

/-- Transport along a listed route path.  A loop is represented by a nonempty
route list whose last route returns to the first route. -/
def loopTransport (Γ : RouteGraph) : List Γ.Route → Γ.S → Γ.S
  | [], s => s
  | [_], s => s
  | r₁ :: r₂ :: rest, s => loopTransport Γ (r₂ :: rest) (Γ.bridge r₁ r₂ s)

/-- A genuine closed path, with at least one bridge and matching endpoints. -/
def IsClosedLoop (Γ : RouteGraph) (path : List Γ.Route) : Prop :=
  ∃ r rest, path = r :: (rest ++ [r])

/-- The canonical E4 route labels used by the finite witness. -/
inductive E4Route
  | cmbBao
  | baoSn
  | cepheidSn
  deriving DecidableEq

/-- Two predictive readout states for an abstract Hubble posterior. -/
inductive E4Readout
  | low
  | high
  deriving DecidableEq

/-- A route disagreement injected into one bridge of the loop. -/
inductive InjectedDisagreement
  | zero
  | nonzero
  deriving DecidableEq

/-- The current scalar quotient intentionally forgets the predictive split. -/
inductive CurrentClass
  | scalar
  deriving DecidableEq

/-- Predictive quotient classes retain the split moved by the route loop. -/
inductive PredictiveClass
  | low
  | high
  deriving DecidableEq

def flipReadout : E4Readout → E4Readout
  | E4Readout.low => E4Readout.high
  | E4Readout.high => E4Readout.low

def disagreementTransport : InjectedDisagreement → E4Readout → E4Readout
  | InjectedDisagreement.zero, s => s
  | InjectedDisagreement.nonzero, s => flipReadout s

/-- The E4 loop uses route labels `CMB→BAO`, `BAO→SN`, `Cepheid→SN`, then
returns to `CMB→BAO`. -/
def e4Loop : List E4Route :=
  [E4Route.cmbBao, E4Route.baoSn, E4Route.cepheidSn, E4Route.cmbBao]

/-- The finite E4 route graph. The injected route disagreement lives in the
`CMB→BAO` to `BAO→SN` bridge; all other bridges are identity for this witness. -/
def e4RouteGraph (d : InjectedDisagreement) : RouteGraph where
  Route := E4Route
  decRoute := inferInstance
  routes := [E4Route.cmbBao, E4Route.baoSn, E4Route.cepheidSn]
  routes_complete := by
    intro r
    cases r <;> simp
  S := E4Readout
  decState := inferInstance
  states := [E4Readout.low, E4Readout.high]
  states_complete := by
    intro s
    cases s <;> simp
  bridge := fun rFrom rTo s =>
    match rFrom, rTo with
    | E4Route.cmbBao, E4Route.baoSn => disagreementTransport d s
    | _, _ => s

/-- The exact loop residue of the finite Hubble readout witness. -/
def hubbleHolonomyResidue (d : InjectedDisagreement) : Rat :=
  (discreteDefect E4Readout).d
    (loopTransport (e4RouteGraph d) e4Loop E4Readout.low)
    E4Readout.low

/-- The injected route disagreement as an exact rational diagnostic. -/
def injectedRouteDisagreement (d : InjectedDisagreement) : Rat :=
  match d with
  | InjectedDisagreement.zero => 0
  | InjectedDisagreement.nonzero => 1

/-- T6 iff receipt: in the finite route loop, nonzero Hubble holonomy residue
is equivalent to nonzero injected route disagreement. -/
theorem hubble_holonomy_nonzero_iff_injected_disagreement_nonzero
    (d : InjectedDisagreement) :
    hubbleHolonomyResidue d ≠ 0 ↔ injectedRouteDisagreement d ≠ 0 := by
  cases d <;>
    simp [hubbleHolonomyResidue, injectedRouteDisagreement, e4Loop, e4RouteGraph,
      loopTransport, disagreementTransport, flipReadout, discreteDefect]

/-- Zero-disagreement control: no injected disagreement gives zero holonomy. -/
theorem zero_disagreement_zero_holonomy :
    hubbleHolonomyResidue InjectedDisagreement.zero = 0 := by
  simp [hubbleHolonomyResidue, e4Loop, e4RouteGraph, loopTransport,
    disagreementTransport, discreteDefect]

/-- Nonzero finite witness: the injected disagreement gives nonzero holonomy. -/
theorem e4_nonzero_holonomy_residue :
    hubbleHolonomyResidue InjectedDisagreement.nonzero ≠ 0 := by
  simp [hubbleHolonomyResidue, e4Loop, e4RouteGraph, loopTransport,
    disagreementTransport, flipReadout, discreteDefect]

/-- T6a: an explicit route graph and loop whose composite transport is not
the identity. -/
theorem route_holonomy_nonzero :
    ∃ (Γ : RouteGraph) (loop : List Γ.Route) (s : Γ.S),
      IsClosedLoop Γ loop ∧ loopTransport Γ loop s ≠ s := by
  refine ⟨e4RouteGraph InjectedDisagreement.nonzero, e4Loop, E4Readout.low,
    ⟨E4Route.cmbBao, [E4Route.baoSn, E4Route.cepheidSn], rfl⟩, ?_⟩
  simp [e4Loop, e4RouteGraph, loopTransport, disagreementTransport, flipReadout]

def toCurrent : E4Readout → CurrentClass
  | _ => CurrentClass.scalar

def toPredictive : E4Readout → PredictiveClass
  | E4Readout.low => PredictiveClass.low
  | E4Readout.high => PredictiveClass.high

/-- T6b: the route loop is trivial on the current scalar quotient but moves a
predictive class, the finite Holonomy-with-Memory asymmetry pattern. -/
theorem holonomy_current_trivial_predictive_nontrivial :
    ∃ (Γ : RouteGraph) (loop : List Γ.Route)
      (toCurrent : Γ.S → CurrentClass) (toPredictive : Γ.S → PredictiveClass),
      IsClosedLoop Γ loop ∧
      (∀ s : Γ.S, toCurrent (loopTransport Γ loop s) = toCurrent s) ∧
      (∃ s : Γ.S, toPredictive (loopTransport Γ loop s) ≠ toPredictive s) := by
  exact ⟨e4RouteGraph InjectedDisagreement.nonzero, e4Loop, toCurrent,
    toPredictive, by
      constructor
      · exact ⟨E4Route.cmbBao, [E4Route.baoSn, E4Route.cepheidSn], rfl⟩
      constructor
      · intro s
        cases s <;> rfl
      · exact ⟨E4Readout.low, by
          simp [e4Loop, e4RouteGraph, loopTransport, disagreementTransport, flipReadout,
            toPredictive]⟩⟩

end SbtCosmo.Holonomy
