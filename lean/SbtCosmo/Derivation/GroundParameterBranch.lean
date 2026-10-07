import SbtCosmo.Derivation.GroundParameterEquations

/-! Earned local positive self-consistent branches and local uniqueness.
The Newton defect is an explicit numerical obligation; all analytic branch
and actual-ground returns are proved, not supplied as branch premises. -/
namespace SbtCosmo.Derivation.GroundParameterBranch
noncomputable section
set_option maxHeartbeats 2000000
open Filter GroundState GroundBorder GroundSourceJacobian GroundRootCertificate
open GroundParameterEquations
open scoped Topology ContDiff

def branch (p : Parameter) (x : Point) (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) : Parameter → Point :=
  (actualImplicitData p x C hd).implicitFunction

theorem branch_center (p : Parameter) (x : Point) (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) : branch p x C hd p = x := by
  exact (actualImplicitData p x C hd).eventually_implicitFunction_apply_eq.self_of_nhds rfl

theorem branch_smooth_at (p : Parameter) (x : Point) (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) :
    ContDiffAt ℝ ∞ (branch p x C hd) p :=
  (actualImplicitData p x C hd).contDiffAt_implicitFunction

theorem branch_root_eventually {p : Parameter} {x : Point} (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) (hz : residual p.1 p.2 x = 0) :
    ∀ᶠ q in nhds p, residual q.1 q.2 (branch p x C hd q) = 0 := by
  simpa only [jointResidual, hz] using (actualImplicitData p x C hd).apply_implicitFunction

theorem branch_positive_eventually {p : Parameter} {x : Point} (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) (hp : ∀ i, 0 < x.1 i) :
    ∀ᶠ q in nhds p, ∀ i, 0 < (branch p x C hd q).1 i := by
  have hpos : ∀ᶠ y : Point in nhds x, ∀ i, 0 < y.1 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).comp continuous_fst).continuousAt.eventually (lt_mem_nhds (hp i))
  have hc := (branch_smooth_at p x C hd).continuousAt.tendsto
  rw [branch_center] at hc
  exact hc.eventually hpos

theorem branch_ground_eventually {p : Parameter} {x : Point} (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1)
    (hz : residual p.1 p.2 x = 0) (hp : ∀ i, 0 < x.1 i) :
    ∀ᶠ q in nhds p,
      normSq (branch p x C hd q).1 = 1 ∧
      groundPair (sourcePotential q.1 q.2 (branch p x C hd q).1) = branch p x C hd q ∧
      groundMap q.1 q.2 (branch p x C hd q).1 = (branch p x C hd q).1 := by
  filter_upwards [branch_root_eventually C hd hz, branch_positive_eventually C hd hp] with q hq hpq
  exact ⟨((residual_zero_iff q.1 q.2 _).mp hq).1,
    GroundLocalDynamics.positive_root_groundPair_return hq hpq, (positive_root_return hq hpq).2⟩

/-- Local uniqueness concerns the full nonlinear eigen equation, in a proved
product neighborhood. It is not global uniqueness of all self-consistent roots. -/
theorem branch_unique_neighborhoods {p : Parameter} {x : Point} (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) (hz : residual p.1 p.2 x = 0) :
    ∃ P ∈ nhds p, ∃ U ∈ nhds x, ∀ q ∈ P, ∀ y ∈ U,
      residual q.1 q.2 y = 0 → y = branch p x C hd q := by
  have he := (actualImplicitData p x C hd).eventually_implicitFunction_apply_eq
  change {z : Domain | jointResidual z = jointResidual (p, x) → branch p x C hd z.1 = z.2} ∈ nhds (p, x) at he
  rw [nhds_prod_eq] at he
  obtain ⟨P, hP, U, hU, hsub⟩ := Filter.mem_prod_iff.mp he
  refine ⟨P, hP, U, hU, fun q hq y hy hzy => ?_⟩
  have hh := hsub (show (q, y) ∈ P ×ˢ U from ⟨hq, hy⟩)
  exact (hh (by simpa only [jointResidual, hz] using hzy)).symm

theorem certified_local_positive_branch {p : Parameter} {x : Point}
    (C : Point →L[ℝ] Point) (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1)
    (hz : residual p.1 p.2 x = 0) (hp : ∀ i, 0 < x.1 i) :
    ∃ f : Parameter → Point, f p = x ∧ ContDiffAt ℝ ∞ f p ∧
      (∀ᶠ q in nhds p, residual q.1 q.2 (f q) = 0 ∧ ∀ i, 0 < (f q).1 i) ∧
      ∃ P ∈ nhds p, ∃ U ∈ nhds x, ∀ q ∈ P, ∀ y ∈ U,
        residual q.1 q.2 y = 0 → y = f q := by
  refine ⟨branch p x C hd, branch_center p x C hd, branch_smooth_at p x C hd,
    ?_, branch_unique_neighborhoods C hd hz⟩
  filter_upwards [branch_root_eventually C hd hz, branch_positive_eventually C hd hp] with q hq hpq
  exact ⟨hq, hpq⟩

end
end SbtCosmo.Derivation.GroundParameterBranch
