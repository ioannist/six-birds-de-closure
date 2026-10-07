import SbtCosmo.Derivation.GroundParametricSeedReturn

/-! Original-seed continuation with an independently open target condition
on the newly constructed fixed point. Finite prefix guards need only the guard
set, and need not already satisfy the eventual target condition. -/
namespace SbtCosmo.Derivation.GroundParametricSeedTargetReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open Filter Metric
open scoped Topology ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nearby_original_seed_target_returns [CompleteSpace E]
    {f : P → E → E} {p : P} {u a : E} {s t : Set (P × E)}
    (hc : ContDiffAt ℝ 1 (Function.uncurry f) (p,u))
    (hf : f p u = u) (hd : ‖fderiv ℝ (f p) u‖ < 1) (hs : s ∈ nhds (p,u))
    (ht : t ∈ nhds (p,u))
    (horbit : ∀ n : ℕ, ContinuousAt (Function.uncurry f) (p,(f p)^[n] a))
    (hguards : ∀ n : ℕ, s ∈ nhds (p,(f p)^[n] a))
    (hlim : Tendsto (fun n : ℕ => (f p)^[n] a) atTop (nhds u)) :
    ∃ δ > 0, ∃ r > 0, ∀ b ∈ closedBall p δ,
      ∃ v ∈ closedBall u (r / 4), f b v = v ∧ (b,v) ∈ t ∧
        Tendsto (fun n : ℕ => (f b)^[n] a) atTop (nhds v) ∧
        ∀ n : ℕ, (b,(f b)^[n] a) ∈ s := by
  obtain ⟨δ0,hδ0,r,hr,hreturns⟩ :=
    GroundParametricFixedPoint.nearby_fixed_points hc hf hd (inter_mem hs ht)
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds u (by linarith : 0 < r / 2))).exists
  have hNr : (f p)^[N] a ∈ ball u r := by
    apply mem_ball.mpr
    have := mem_ball.mp hN
    linarith
  have hentry : ∀ᶠ b in nhds p, (f b)^[N] a ∈ closedBall u r := by
    filter_upwards [(GroundParametricSeedReturn.iterate_parameter_continuous_at horbit N).eventually
      (isOpen_ball.mem_nhds hNr)] with b hb
    exact mem_closedBall.mpr (mem_ball.mp hb).le
  have hprefix := GroundParametricSeedReturn.finite_prefix_guards_near horbit hguards N
  obtain ⟨δ,hδ,hnear⟩ := nhds_basis_closedBall.mem_iff.mp
    ((hentry.and hprefix).and (closedBall_mem_nhds p hδ0))
  refine ⟨δ,hδ,r,hr,fun b hb => ?_⟩
  obtain ⟨⟨hbentry,hbprefix⟩,hb0⟩ := hnear hb
  obtain ⟨v,hv,hvf,hball⟩ := hreturns b hb0
  have htail := hball ((f b)^[N] a) hbentry
  have hvball : v ∈ closedBall u r := mem_closedBall.mpr
    ((mem_closedBall.mp hv).trans (by linarith))
  have hvt : (b,v) ∈ t := by
    simpa only [Function.iterate_zero_apply] using ((hball v hvball).2 0).2
  refine ⟨v,hv,hvf,hvt,?_,fun n => ?_⟩
  · apply (tendsto_add_atTop_iff_nat N).1
    simpa only [Function.iterate_add_apply] using htail.1
  · by_cases hn : n < N
    · exact hbprefix n hn
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have heq : (f b)^[n - N] ((f b)^[N] a) = (f b)^[n] a := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn']
      simpa only [heq] using (htail.2 (n - N)).1
end
end SbtCosmo.Derivation.GroundParametricSeedTargetReturn
