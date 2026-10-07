import SbtCosmo.Derivation.GroundParametricFixedPoint

/-! Original-seed continuation: finite entry and finite guards persist by
continuity, while the constructed invariant contraction ball supplies the tail.
All baseline orbit hypotheses remain explicit here for later native instances. -/
namespace SbtCosmo.Derivation.GroundParametricSeedReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open Filter Metric
open scoped Topology ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem iterate_parameter_continuous_at {f : P → E → E} {p : P} {a : E}
    (hc : ∀ n : ℕ, ContinuousAt (Function.uncurry f) (p,(f p)^[n] a))
    (N : ℕ) : ContinuousAt (fun b => (f b)^[N] a) p := by
  induction N with
  | zero => simpa only [Function.iterate_zero_apply] using (continuousAt_const (y := a) (x := p))
  | succ n ih =>
    have hp : ContinuousAt (fun b : P => (b,(f b)^[n] a)) p := continuousAt_id.prodMk ih
    simpa only [Function.iterate_succ_apply',Function.uncurry,Function.comp_def] using
      (ContinuousAt.comp (g := Function.uncurry f) (f := fun b : P => (b,(f b)^[n] a))
        (x := p) (hc n) hp)

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem finite_prefix_guards_near {f : P → E → E} {p : P} {a : E} {s : Set (P × E)}
    (hc : ∀ n : ℕ, ContinuousAt (Function.uncurry f) (p,(f p)^[n] a))
    (hs : ∀ n : ℕ, s ∈ nhds (p,(f p)^[n] a)) (N : ℕ) :
    ∀ᶠ b in nhds p, ∀ n < N, (b,(f b)^[n] a) ∈ s := by
  have he : ∀ n ∈ Finset.range N, ∀ᶠ b in nhds p, (b,(f b)^[n] a) ∈ s := by
    intro n _
    exact (continuousAt_id.prodMk (iterate_parameter_continuous_at hc n)).eventually (hs n)
  simpa only [Finset.mem_range] using (eventually_all_finset (Finset.range N)).2 he

theorem nearby_original_seed_returns [CompleteSpace E]
    {f : P → E → E} {p : P} {u a : E} {s : Set (P × E)}
    (hc : ContDiffAt ℝ 1 (Function.uncurry f) (p,u))
    (hf : f p u = u) (hd : ‖fderiv ℝ (f p) u‖ < 1) (hs : s ∈ nhds (p,u))
    (horbit : ∀ n : ℕ, ContinuousAt (Function.uncurry f) (p,(f p)^[n] a))
    (hguards : ∀ n : ℕ, s ∈ nhds (p,(f p)^[n] a))
    (hlim : Tendsto (fun n : ℕ => (f p)^[n] a) atTop (nhds u)) :
    ∃ δ > 0, ∃ r > 0, ∀ b ∈ closedBall p δ,
      ∃ v ∈ closedBall u (r / 4), f b v = v ∧
        Tendsto (fun n : ℕ => (f b)^[n] a) atTop (nhds v) ∧
        ∀ n : ℕ, (b,(f b)^[n] a) ∈ s := by
  obtain ⟨δ0,hδ0,r,hr,hreturns⟩ :=
    GroundParametricFixedPoint.nearby_fixed_points hc hf hd hs
  obtain ⟨N,hN⟩ := (hlim.eventually (ball_mem_nhds u (by linarith : 0 < r / 2))).exists
  have hNr : (f p)^[N] a ∈ ball u r := by
    apply mem_ball.mpr
    have := mem_ball.mp hN
    linarith
  have hentry : ∀ᶠ b in nhds p, (f b)^[N] a ∈ closedBall u r := by
    filter_upwards [(iterate_parameter_continuous_at horbit N).eventually
      (isOpen_ball.mem_nhds hNr)] with b hb
    exact mem_closedBall.mpr (mem_ball.mp hb).le
  have hprefix := finite_prefix_guards_near horbit hguards N
  obtain ⟨δ,hδ,hnear⟩ := nhds_basis_closedBall.mem_iff.mp
    ((hentry.and hprefix).and (closedBall_mem_nhds p hδ0))
  refine ⟨δ,hδ,r,hr,fun b hb => ?_⟩
  obtain ⟨⟨hbentry,hbprefix⟩,hb0⟩ := hnear hb
  obtain ⟨v,hv,hvf,hball⟩ := hreturns b hb0
  have htail := hball ((f b)^[N] a) hbentry
  refine ⟨v,hv,hvf,?_,fun n => ?_⟩
  · apply (tendsto_add_atTop_iff_nat N).1
    simpa only [Function.iterate_add_apply] using htail.1
  · by_cases hn : n < N
    · exact hbprefix n hn
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have heq : (f b)^[n - N] ((f b)^[N] a) = (f b)^[n] a := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn']
      simpa only [heq] using htail.2 (n - N)
end
end SbtCosmo.Derivation.GroundParametricSeedReturn
