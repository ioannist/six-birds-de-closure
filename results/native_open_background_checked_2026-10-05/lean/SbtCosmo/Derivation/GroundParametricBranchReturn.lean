import SbtCosmo.Derivation.GroundParametricSeedReturn

/-! Identification of the constructed attracting fixed point with an
independently earned continuous fixed-point branch. -/
namespace SbtCosmo.Derivation.GroundParametricBranchReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open Filter Metric
open scoped Topology ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem nearby_original_seed_branch_returns
    {f : P → E → E} {p : P} {u a : E} {s : Set (P × E)} {g : P → E}
    (hc : ContDiffAt ℝ 1 (Function.uncurry f) (p,u))
    (hf : f p u = u) (hd : ‖fderiv ℝ (f p) u‖ < 1) (hs : s ∈ nhds (p,u))
    (horbit : ∀ n : ℕ, ContinuousAt (Function.uncurry f) (p,(f p)^[n] a))
    (hguards : ∀ n : ℕ, s ∈ nhds (p,(f p)^[n] a))
    (hlim : Tendsto (fun n : ℕ => (f p)^[n] a) atTop (nhds u))
    (hg : ContinuousAt g p) (hg0 : g p = u)
    (hgfix : ∀ᶠ b in nhds p, f b (g b) = g b) :
    ∃ δ > 0, ∀ b ∈ closedBall p δ,
      Tendsto (fun n : ℕ => (f b)^[n] a) atTop (nhds (g b)) ∧
        ∀ n : ℕ, (b,(f b)^[n] a) ∈ s := by
  obtain ⟨δ0,hδ0,r,hr,hreturns⟩ :=
    GroundParametricFixedPoint.nearby_fixed_points hc hf hd hs
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds u (by linarith : 0 < r / 2))).exists
  have hNr : (f p)^[N] a ∈ ball u r := by
    apply mem_ball.mpr
    have := mem_ball.mp hN
    linarith
  have hentry : ∀ᶠ b in nhds p, (f b)^[N] a ∈ closedBall u r := by
    filter_upwards [(GroundParametricSeedReturn.iterate_parameter_continuous_at horbit N).eventually
      (isOpen_ball.mem_nhds hNr)] with b hb
    exact mem_closedBall.mpr (mem_ball.mp hb).le
  have hbranch : ∀ᶠ b in nhds p, g b ∈ closedBall u r := by
    have hp : g p ∈ ball u r := by simpa [hg0] using (mem_ball_self hr : u ∈ ball u r)
    filter_upwards [hg.eventually (isOpen_ball.mem_nhds hp)] with b hb
    exact mem_closedBall.mpr (mem_ball.mp hb).le
  have hprefix := GroundParametricSeedReturn.finite_prefix_guards_near horbit hguards N
  obtain ⟨δ,hδ,hnear⟩ := nhds_basis_closedBall.mem_iff.mp
    ((((hentry.and hprefix).and hbranch).and hgfix).and (closedBall_mem_nhds p hδ0))
  refine ⟨δ,hδ,fun b hb => ?_⟩
  obtain ⟨⟨⟨⟨hbentry,hbprefix⟩,hbbranch⟩,hbfix⟩,hb0⟩ := hnear hb
  obtain ⟨v,_,_,hball⟩ := hreturns b hb0
  have heq : v = g b := by
    have ht := (hball (g b) hbbranch).1
    have he : (fun n : ℕ => (f b)^[n] (g b)) = (fun _ : ℕ => g b) :=
      funext (Function.iterate_fixed hbfix)
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have htail := hball ((f b)^[N] a) hbentry
  refine ⟨?_,fun n => ?_⟩
  · apply (tendsto_add_atTop_iff_nat N).1
    simpa only [Function.iterate_add_apply,heq] using htail.1
  · by_cases hn : n < N
    · exact hbprefix n hn
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have he : (f b)^[n - N] ((f b)^[N] a) = (f b)^[n] a := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn']
      simpa only [he] using htail.2 (n - N)
end
end SbtCosmo.Derivation.GroundParametricBranchReturn
