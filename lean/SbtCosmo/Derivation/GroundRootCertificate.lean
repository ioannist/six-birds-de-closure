import SbtCosmo.Derivation.GroundNormalizedJacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-! A posteriori root certification for the actual nonlinear eigen equations.
The derivative bound, residual bound and positive ball are explicit certificate
inputs. Concrete Python interval checks are not Lean proof terms. -/
namespace SbtCosmo.Derivation.GroundRootCertificate
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSourceJacobian
open NNReal Metric
open scoped ContDiff BigOperators

def residual (b : Field) (κ : ℝ) (x : Point) : Point :=
  GroundEquations.equations (sourcePotential b κ x.1, x)

def chartDerivative (b : Field) (κ : ℝ) (x : Point) :
    Point →L[ℝ] GroundEquations.Domain :=
  ((sourceDerivative b κ x.1).comp (ContinuousLinearMap.fst ℝ Field ℝ)).prod
    (ContinuousLinearMap.id ℝ Point)

def residualDerivative (b : Field) (κ : ℝ) (x : Point) : Point →L[ℝ] Point :=
  (GroundEquations.derivative (sourcePotential b κ x.1, x)).comp
    (chartDerivative b κ x)

theorem residual_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (residual b κ) :=
  GroundEquations.equations_smooth.comp
    (((sourcePotential_smooth b κ).comp contDiff_fst).prodMk contDiff_id)

theorem residual_hasFDerivAt (b : Field) (κ : ℝ) (x : Point) :
    HasFDerivAt (residual b κ) (residualDerivative b κ x) x :=
  (GroundEquations.equations_hasFDerivAt _).comp x
    (((sourcePotential_hasFDerivAt b κ x.1).comp x
      (ContinuousLinearMap.fst ℝ Field ℝ).hasFDerivAt).prodMk (hasFDerivAt_id x))

theorem residualDerivative_apply (b : Field) (κ : ℝ) (x h : Point) :
    residualDerivative b κ x h =
      (fun i => sourceDerivative b κ x.1 h.1 i * x.1 i +
        shifted (sourcePotential b κ x.1) x.2 h.1 i - h.2 * x.1 i,
        dot x.1 h.1) := rfl

theorem residual_zero_iff (b : Field) (κ : ℝ) (x : Point) :
    residual b κ x = 0 ↔ normSq x.1 = 1 ∧
      ∀ i, hamiltonian (sourcePotential b κ x.1) x.1 i = x.2 * x.1 i := by
  constructor
  · intro hz
    have hn := congrArg (fun y : Point => y.2) hz
    have he := congrArg (fun y : Point => y.1) hz
    refine ⟨?_, fun i => ?_⟩
    · dsimp [residual, GroundEquations.equations] at hn
      linarith
    · have hi := congrFun he i
      exact sub_eq_zero.mp hi
  · rintro ⟨hn, he⟩
    apply Prod.ext
    · funext i
      simp [residual, GroundEquations.equations, shifted, he i]
    · simp [residual, GroundEquations.equations, hn]

theorem positive_root_return {b : Field} {κ : ℝ} {x : Point}
    (hz : residual b κ x = 0) (hp : ∀ i, 0 < x.1 i) :
    IsGround (sourcePotential b κ x.1) x.1 x.2 ∧ groundMap b κ x.1 = x.1 := by
  obtain ⟨hn, he⟩ := (residual_zero_iff b κ x).mp hz
  have hg := GroundAlternating.positive_eigen_ground hp hn he
  exact ⟨hg, positive_ground_unique (positiveGround_spec _).2 hg
    (positiveGround_spec _).1 hp⟩

theorem root_half_mixing_derivative {b : Field} {κ : ℝ} {x : Point}
    (hz : residual b κ x = 0) (hp : ∀ i, 0 < x.1 i) :
    HasFDerivAt (normalizedRelaxed (groundMap b κ) (1 / 2))
      (GroundNormalizedJacobian.normalizedJacobian b κ (1 / 2) x.1) x.1 :=
  GroundNormalizedJacobian.normalized_hasFDerivAt
    ((residual_zero_iff b κ x).mp hz).1 (positive_root_return hz hp).2

/-- Full ambient matrix; its range is tangent to the unit sphere. -/
theorem half_mixing_jacobian_apply {b u : Field} {κ : ℝ}
    (hf : groundMap b κ u = u) (h : Field) (i : Fin 8) :
    GroundNormalizedJacobian.normalizedJacobian b κ (1 / 2) u h i =
      (h i - dot u h * u i + jacobian b κ u h i) / 2 := by
  have hj := jacobian_tangent b κ u h
  rw [hf] at hj
  have hd : dot u (GroundNormalizedJacobian.affineJacobian b κ (1 / 2) u h) =
      dot u h / 2 := by
    have he : dot u (GroundNormalizedJacobian.affineJacobian b κ (1 / 2) u h) =
        (1 - 1 / 2) * dot u h + (1 / 2) * dot u (jacobian b κ u h) := by
      simp only [dot, GroundNormalizedJacobian.affineJacobian,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, hj]
    ring
  change GroundNormalizedJacobian.projection u
    (GroundNormalizedJacobian.affineJacobian b κ (1 / 2) u h) i = _
  rw [GroundNormalizedJacobian.projection_apply, hd]
  simp [GroundNormalizedJacobian.affineJacobian]
  ring

def correction (b : Field) (κ : ℝ) (C : Point →L[ℝ] Point) (x : Point) : Point :=
  x - C (residual b κ x)

def correctionDerivative (b : Field) (κ : ℝ) (C : Point →L[ℝ] Point)
    (x : Point) : Point →L[ℝ] Point :=
  ContinuousLinearMap.id ℝ Point - C.comp (residualDerivative b κ x)

theorem correction_hasFDerivAt (b : Field) (κ : ℝ) (C : Point →L[ℝ] Point) (x : Point) :
    HasFDerivAt (correction b κ C) (correctionDerivative b κ C x) x :=
  (hasFDerivAt_id x).sub (C.hasFDerivAt.comp x (residual_hasFDerivAt b κ x))

theorem correction_lipschitz (b : Field) (κ : ℝ) (C : Point →L[ℝ] Point)
    (center : Point) (r : ℝ) (q : ℝ≥0)
    (hd : ∀ x ∈ Metric.closedBall center r, ‖correctionDerivative b κ C x‖ ≤ q) :
    LipschitzOnWith q (correction b κ C) (Metric.closedBall center r) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x _ => (correction_hasFDerivAt b κ C x).hasFDerivWithinAt)
    (fun x hx => hd x hx) (convex_closedBall center r)

theorem correction_invariant (b : Field) (κ : ℝ) (C : Point →L[ℝ] Point)
    (center : Point) (r : ℝ) (q : ℝ≥0) (hr : 0 ≤ r)
    (hl : LipschitzOnWith q (correction b κ C) (Metric.closedBall center r))
    (hy : ‖C (residual b κ center)‖ + q * r ≤ r) :
    Set.MapsTo (correction b κ C) (Metric.closedBall center r) (Metric.closedBall center r) := by
  intro x hx
  have hc : center ∈ Metric.closedBall center r := Metric.mem_closedBall_self hr
  have hd := hl.dist_le_mul x hx center hc
  have hy' : dist (correction b κ C center) center = ‖C (residual b κ center)‖ := by
    simp [correction]
  have ht := dist_triangle (correction b κ C x) (correction b κ C center) center
  have hx' : dist x center ≤ r := hx
  change dist (correction b κ C x) center ≤ r
  rw [hy'] at ht
  have hm := mul_le_mul_of_nonneg_left hx' q.coe_nonneg
  linarith

/-- A checked small ball earns a root and returns it to the actual ground map.
Uniqueness is of the full nonlinear eigen equation INSIDE the certified ball. -/
theorem certified_positive_root (b : Field) (κ : ℝ) (C : Point →L[ℝ] Point)
    (hC : Function.Injective C) (center : Point) (r : ℝ) (q : ℝ≥0)
    (hr : 0 ≤ r) (hq : q < 1)
    (hd : ∀ x ∈ Metric.closedBall center r, ‖correctionDerivative b κ C x‖ ≤ q)
    (hy : ‖C (residual b κ center)‖ + q * r ≤ r)
    (hp : ∀ x ∈ Metric.closedBall center r, ∀ i, 0 < x.1 i) :
    ∃ x ∈ Metric.closedBall center r, residual b κ x = 0 ∧
      IsGround (sourcePotential b κ x.1) x.1 x.2 ∧ groundMap b κ x.1 = x.1 ∧
      ∀ y ∈ Metric.closedBall center r, residual b κ y = 0 → y = x := by
  let f := correction b κ C
  have hl := correction_lipschitz b κ C center r q hd
  have hm := correction_invariant b κ C center r q hr hl hy
  have ht : ContractingWith q (hm.restrict f _ _) :=
    ⟨hq, hm.lipschitzOnWith_iff_restrict.mp hl⟩
  obtain ⟨x, hx, hfix, _, _⟩ := ht.exists_fixedPoint'
    isClosed_closedBall.isComplete hm (Metric.mem_closedBall_self hr) (edist_ne_top center (f center))
  have hz : residual b κ x = 0 := by
    apply hC
    have hh : x - C (residual b κ x) = x := hfix
    simpa using sub_eq_self.mp hh
  obtain ⟨hg, hgmap⟩ := positive_root_return hz (hp x hx)
  refine ⟨x, hx, hz, hg, hgmap, fun y hy hzy => ?_⟩
  have hyfix : correction b κ C y = y := by simp [correction, hzy]
  have hdxy := hl.dist_le_mul y hy x hx
  rw [hyfix, hfix] at hdxy
  have hd0 : dist y x = 0 := by
    have hq' : (q : ℝ) < 1 := hq
    nlinarith [dist_nonneg (x := y) (y := x)]
  exact dist_eq_zero.mp hd0

end
end SbtCosmo.Derivation.GroundRootCertificate
