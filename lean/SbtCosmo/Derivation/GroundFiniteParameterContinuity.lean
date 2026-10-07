import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Dynamics.FixedPoints.Basic

/-! Continuity of a finite parameterized iteration requires regularity only
along the finite prefix, not an assumed infinite regular orbit. -/
namespace SbtCosmo.Derivation.GroundFiniteParameterContinuity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Filter
open scoped Topology
variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem finite_iterate_parameter_continuous_at {f : P → E → E} {p : P} {a : E}
    (N : ℕ)
    (hc : ∀ n : ℕ, n < N → ContinuousAt (Function.uncurry f) (p,(f p)^[n] a)) :
    ContinuousAt (fun b => (f b)^[N] a) p := by
  revert hc
  induction N with
  | zero =>
    intro _
    simpa only [Function.iterate_zero_apply] using (continuousAt_const (y := a) (x := p))
  | succ n ih =>
    intro hc
    have hprev := ih (fun j hj => hc j (by omega))
    have hp : ContinuousAt (fun b : P => (b,(f b)^[n] a)) p := continuousAt_id.prodMk hprev
    simpa only [Function.iterate_succ_apply',Function.uncurry,Function.comp_def] using
      (ContinuousAt.comp (g := Function.uncurry f) (f := fun b : P => (b,(f b)^[n] a))
        (x := p) (hc n (by omega)) hp)
end SbtCosmo.Derivation.GroundFiniteParameterContinuity
