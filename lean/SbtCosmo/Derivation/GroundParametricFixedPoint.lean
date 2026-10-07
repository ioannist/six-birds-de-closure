import SbtCosmo.Derivation.GroundParametricContraction

/-! Nearby fixed points are constructed from a strict baseline contraction.
The fixed points, invariant balls and common attraction are conclusions. -/
namespace SbtCosmo.Derivation.GroundParametricFixedPoint
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open Filter Metric
open scoped Topology ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem invariant_ball {f : E → E} {u : E} {r : ℝ} {q : NNReal}
    (hr : 0 ≤ r) (hq : q < 1)
    (hl : LipschitzOnWith q f (closedBall u r))
    (he : dist (f u) u ≤ (1 - (q : ℝ)) * r) :
    Set.MapsTo f (closedBall u r) (closedBall u r) := by
  intro x hx
  have hu : u ∈ closedBall u r := mem_closedBall_self hr
  have hxu := mem_closedBall.mp hx
  have hq0 : 0 ≤ (q : ℝ) := q.coe_nonneg
  have hqd : (q : ℝ) < 1 := by exact_mod_cast hq
  apply mem_closedBall.mpr
  calc
    dist (f x) u ≤ dist (f x) (f u) + dist (f u) u := dist_triangle _ _ _
    _ ≤ (q : ℝ) * dist x u + (1 - (q : ℝ)) * r :=
      add_le_add (hl.dist_le_mul x hx u hu) he
    _ ≤ r := by nlinarith

omit [NormedSpace ℝ E] in
theorem ball_return [CompleteSpace E] {f : E → E} {u : E} {r : ℝ} {q : NNReal}
    (hr : 0 < r) (hq : q < 1)
    (hl : LipschitzOnWith q f (closedBall u r))
    (he : dist (f u) u ≤ (1 - (q : ℝ)) * (r / 4)) :
    ∃ v ∈ closedBall u (r / 4), f v = v ∧
      ∀ x ∈ closedBall u r,
        Tendsto (fun n : ℕ => f^[n] x) atTop (nhds v) ∧
        ∀ n : ℕ, f^[n] x ∈ closedBall u r := by
  have hqd : (q : ℝ) < 1 := by exact_mod_cast hq
  have hm : Set.MapsTo f (closedBall u r) (closedBall u r) :=
    invariant_ball hr.le hq hl (he.trans (by nlinarith))
  have hcontract : ContractingWith q (hm.restrict f (closedBall u r) (closedBall u r)) := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    exact hl.dist_le_mul x.1 x.2 y.1 y.2
  have hcomplete := (isClosed_closedBall (x := u) (ε := r)).isComplete
  have hu : u ∈ closedBall u r := mem_closedBall_self hr.le
  obtain ⟨v,hv,hfix,_,_⟩ := hcontract.exists_fixedPoint' hcomplete hm hu (edist_ne_top _ _)
  have hnear : v ∈ closedBall u (r / 4) := by
    have hb : dist v u ≤ (q : ℝ) * dist v u + dist (f u) u := by
      calc
        dist v u = dist (f v) u := by rw [hfix.eq]
        _ ≤ dist (f v) (f u) + dist (f u) u := dist_triangle _ _ _
        _ ≤ (q : ℝ) * dist v u + dist (f u) u :=
          add_le_add (hl.dist_le_mul v hv u hu) le_rfl
    apply mem_closedBall.mpr
    nlinarith
  refine ⟨v,hnear,hfix.eq,fun x hx => ⟨?_, fun n => hm.iterate n hx⟩⟩
  obtain ⟨w,hw,hwfix,hwt,_⟩ := hcontract.exists_fixedPoint' hcomplete hm hx (edist_ne_top _ _)
  have heq : w = v := by
    have hdist := hl.dist_le_mul w hw v hv
    rw [hwfix.eq,hfix.eq] at hdist
    have hn := dist_nonneg (x := w) (y := v)
    apply dist_eq_zero.mp
    nlinarith
  simpa only [heq] using hwt

theorem nearby_fixed_points [CompleteSpace E]
    {f : P → E → E} {p : P} {u : E} {s : Set (P × E)}
    (hc : ContDiffAt ℝ 1 (Function.uncurry f) (p,u))
    (hf : f p u = u) (hd : ‖fderiv ℝ (f p) u‖ < 1)
    (hs : s ∈ nhds (p,u)) :
    ∃ δ > 0, ∃ r > 0, ∀ b ∈ closedBall p δ,
      ∃ v ∈ closedBall u (r / 4), f b v = v ∧
        ∀ x ∈ closedBall u r,
          Tendsto (fun n : ℕ => (f b)^[n] x) atTop (nhds v) ∧
          ∀ n : ℕ, (b,(f b)^[n] x) ∈ s := by
  obtain ⟨δ0,hδ0,r,hr,q,hq,huniform⟩ :=
    GroundParametricContraction.uniform_local_lipschitz hc hd hs
  have hqd : (q : ℝ) < 1 := by exact_mod_cast hq
  have heps : 0 < (1 - (q : ℝ)) * (r / 4) := mul_pos (by linarith) (by linarith)
  have hcenter : ContinuousAt (fun b => f b u) p := by
    simpa only [Function.uncurry, Function.comp_def] using
      ContinuousAt.comp (g := Function.uncurry f) (f := fun b : P => (b,u))
        (x := p) hc.continuousAt (continuousAt_id.prodMk continuousAt_const)
  have hsmall : ∀ᶠ b in nhds p, dist (f b u) u < (1 - (q : ℝ)) * (r / 4) := by
    have hzero : dist (f p u) u < (1 - (q : ℝ)) * (r / 4) := by simpa [hf] using heps
    exact (hcenter.dist continuousAt_const).eventually (gt_mem_nhds hzero)
  obtain ⟨δ1,hδ1,hsmallball⟩ := nhds_basis_closedBall.mem_iff.mp hsmall
  refine ⟨min δ0 δ1,lt_min hδ0 hδ1,r,hr,fun b hb => ?_⟩
  have hb0 : b ∈ closedBall p δ0 :=
    mem_closedBall.mpr ((mem_closedBall.mp hb).trans (min_le_left _ _))
  have hb1 : b ∈ closedBall p δ1 :=
    mem_closedBall.mpr ((mem_closedBall.mp hb).trans (min_le_right _ _))
  obtain ⟨v,hv,hvf,hreturn⟩ := ball_return hr hq (huniform b hb0).1 (hsmallball hb1).le
  refine ⟨v,hv,hvf,fun x hx => ?_⟩
  exact ⟨(hreturn x hx).1,fun n => (huniform b hb0).2 _ ((hreturn x hx).2 n)⟩
end
end SbtCosmo.Derivation.GroundParametricFixedPoint
