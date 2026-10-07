import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-! Uniform local state contractions from independently supplied joint C1
regularity and a strict baseline derivative estimate. -/
namespace SbtCosmo.Derivation.GroundParametricContraction
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open Filter Metric
open scoped Topology ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem partial_fderiv_continuous_at {f : P → E → E} {p : P} {u : E}
    (hc : ContDiffAt ℝ 1 (Function.uncurry f) (p,u)) :
    ContinuousAt (fun v : P × E => fderiv ℝ (f v.1) v.2) (p,u) := by
  let g : (P × E) → E → E := fun v x => f v.1 x
  have hproj : ContDiff ℝ 1 (fun z : (P × E) × E => (z.1.1,z.2)) := by fun_prop
  have hg : ContDiffAt ℝ 1 (Function.uncurry g) ((p,u),u) := by
    simpa only [g, Function.uncurry, Function.comp_def] using
      (ContDiffAt.comp (g := Function.uncurry f)
        (f := fun z : (P × E) × E => (z.1.1,z.2)) ((p,u),u) hc hproj.contDiffAt)
  exact (hg.fderiv (g := fun v : P × E => v.2) contDiffAt_snd
    (by simp : (0 : WithTop ℕ∞)+1 ≤ 1)).continuousAt

theorem uniform_local_lipschitz {f : P → E → E} {p : P} {u : E} {s : Set (P × E)}
    (hc : ContDiffAt ℝ 1 (Function.uncurry f) (p,u))
    (hd : ‖fderiv ℝ (f p) u‖ < 1) (hs : s ∈ nhds (p,u)) :
    ∃ δ > 0, ∃ r > 0, ∃ q : NNReal, q < 1 ∧
      ∀ b ∈ closedBall p δ,
        LipschitzOnWith q (f b) (closedBall u r) ∧
          ∀ x ∈ closedBall u r, (b,x) ∈ s := by
  have hd' : ‖fderiv ℝ (f p) u‖₊ < (1 : NNReal) := by exact_mod_cast hd
  obtain ⟨q,hlo,hhi⟩ := exists_between hd'
  have hbound : ∀ᶠ v : P × E in nhds (p,u), ‖fderiv ℝ (f v.1) v.2‖ < (q : ℝ) := by
    have hlow : ‖fderiv ℝ (f p) u‖ < (q : ℝ) := by exact_mod_cast hlo
    exact (partial_fderiv_continuous_at hc).norm.eventually (gt_mem_nhds hlow)
  have hdiff : ∀ᶠ v : P × E in nhds (p,u), DifferentiableAt ℝ (f v.1) v.2 := by
    filter_upwards [hc.eventually (by simp)] with v hv
    have hslice : ContDiffAt ℝ 1 (f v.1) v.2 := by
      simpa only [Function.uncurry, Function.comp_def] using
        (ContDiffAt.comp (g := Function.uncurry f) (f := fun y : E => (v.1,y))
          v.2 hv (contDiffAt_const.prodMk contDiffAt_id))
    exact hslice.differentiableAt (by simp)
  obtain ⟨R,hR,hinside⟩ := nhds_basis_closedBall.mem_iff.mp ((hbound.and hdiff).and hs)
  refine ⟨R,hR,R,hR,q,hhi,fun b hb => ?_⟩
  have hpair (x : E) (hx : x ∈ closedBall u R) : (b,x) ∈ closedBall (p,u) R := by
    rw [mem_closedBall, Prod.dist_eq]
    exact max_le (mem_closedBall.mp hb) (mem_closedBall.mp hx)
  have hstate (x : E) (hx : x ∈ closedBall u R) := hinside (hpair x hx)
  refine ⟨?_,fun x hx => (hstate x hx).2⟩
  apply (convex_closedBall u R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hstate x hx).1.2
  · intro x hx
    have he : ‖fderiv ℝ (f b) x‖ ≤ (q : ℝ) := (hstate x hx).1.1.le
    exact_mod_cast he
end
end SbtCosmo.Derivation.GroundParametricContraction
