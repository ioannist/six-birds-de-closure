import SbtCosmo.Derivation.GroundParameterTube
import Mathlib.Topology.LocallyFinite

/-! Finite closed pasting of roots constructed by quantitative Newton tubes.
Overlap identities come from smaller certified common-root balls. Neither a
global root function nor its continuity or smoothness is an input. -/
namespace SbtCosmo.Derivation.GroundParameterPatch
noncomputable section
set_option maxHeartbeats 2000000
open Filter Metric GroundState GroundBorder GroundRootCertificate GroundSourceJacobian
open GroundParameterEquations GroundParameterBranch GroundParameterTube
open scoped Topology ContDiff

structure TubeCover (b : Field) (ι : Type*) where
  tube : ι → TubeCertificate b
  closed : ∀ i, IsClosed (tube i).interval
  overlap : ∀ i j k, k ∈ (tube i).interval → k ∈ (tube j).interval →
    ∃ a : TubeCertificate b, k ∈ a.interval ∧
      closedBall a.center a.radius ⊆ closedBall (tube i).center (tube i).radius ∧
      closedBall a.center a.radius ⊆ closedBall (tube j).center (tube j).radius

variable {b : Field} {ι : Type*}

def TubeCover.domain (v : TubeCover b ι) : Set ℝ := ⋃ i, (v.tube i).interval

theorem TubeCover.mem_domain (v : TubeCover b ι) {k : ℝ} :
    k ∈ v.domain ↔ ∃ i, k ∈ (v.tube i).interval := Set.mem_iUnion

theorem TubeCover.tube_root_eq (v : TubeCover b ι) {i j : ι} {k : ℝ}
    (hi : k ∈ (v.tube i).interval) (hj : k ∈ (v.tube j).interval) :
    (v.tube i).root k = (v.tube j).root k := by
  obtain ⟨a, ha, hai, haj⟩ := v.overlap i j k hi hj
  have hs := a.root_spec ha
  exact common_root_glues (v.tube i) (v.tube j) hi hj hs.2.1 (hai hs.1) (haj hs.1)

/-- The value outside the certified domain is irrelevant to all conclusions. -/
def TubeCover.root (v : TubeCover b ι) (k : ℝ) : Point :=
  @dite Point (∃ i, k ∈ (v.tube i).interval) (Classical.propDecidable _)
    (fun h => (v.tube h.choose).root k) (fun _ => 0)

theorem TubeCover.root_eq (v : TubeCover b ι) {i : ι} {k : ℝ}
    (hi : k ∈ (v.tube i).interval) : v.root k = (v.tube i).root k := by
  have h : ∃ j, k ∈ (v.tube j).interval := ⟨i, hi⟩
  simp only [TubeCover.root, dif_pos h]
  exact v.tube_root_eq h.choose_spec hi

theorem TubeCover.root_spec (v : TubeCover b ι) {k : ℝ} (hk : k ∈ v.domain) :
    residual b k (v.root k) = 0 ∧ (∀ i, 0 < (v.root k).1 i) ∧
      IsGround (sourcePotential b k (v.root k).1) (v.root k).1 (v.root k).2 ∧
      groundMap b k (v.root k).1 = (v.root k).1 := by
  obtain ⟨i, hi⟩ := v.mem_domain.mp hk
  rw [v.root_eq hi]
  have hs := (v.tube i).root_spec hi
  exact ⟨hs.2.1, (v.tube i).field_positive _ hs.1, hs.2.2.1, hs.2.2.2.1⟩

theorem TubeCover.sample_root_return (v : TubeCover b ι) {i : ι} {k : ℝ}
    (hi : k ∈ (v.tube i).interval) {x : Point} (hz : residual b k x = 0)
    (hx : x ∈ closedBall (v.tube i).center (v.tube i).radius) : x = v.root k := by
  rw [v.root_eq hi]
  exact ((v.tube i).root_spec hi).2.2.2.2 x hx hz

theorem TubeCover.root_continuous_on [Finite ι] (v : TubeCover b ι) :
    ContinuousOn v.root v.domain := by
  apply (locallyFinite_of_finite (fun i => (v.tube i).interval)).continuousOn_iUnion v.closed
  intro i
  exact (v.tube i).root_continuous_on.congr (fun _ hk => v.root_eq hk)

/-- Finite closed pasting earns continuity first; local implicit uniqueness
then earns a single smooth germ through every seam, even when the owning tube
does not itself contain a full relative neighborhood in the union. -/
theorem TubeCover.root_implicit_germ [Finite ι] (v : TubeCover b ι)
    {k : ℝ} (hk : k ∈ v.domain) :
    ∃ g : ℝ → Point, ContDiffAt ℝ ∞ g k ∧ g k = v.root k ∧
      v.root =ᶠ[nhdsWithin k v.domain] g := by
  obtain ⟨i, hi⟩ := v.mem_domain.mp hk
  have hbox : v.root k ∈ closedBall (v.tube i).center (v.tube i).radius := by
    rw [v.root_eq hi]
    exact ((v.tube i).root_spec hi).1
  have hs := v.root_spec hk
  have hd : ‖correctionDerivative b k (v.tube i).preconditioner (v.root k)‖ < 1 :=
    ((v.tube i).defect k hi _ hbox).trans_lt (v.tube i).rate_lt
  let f := branch (b, k) (v.root k) (v.tube i).preconditioner hd
  let g : ℝ → Point := fun s => f (b, s)
  have hparam : ContDiff ℝ ∞ (fun s : ℝ => ((b, s) : Parameter)) :=
    contDiff_const.prodMk contDiff_id
  have hg : ContDiffAt ℝ ∞ g k :=
    (branch_smooth_at (b, k) (v.root k) (v.tube i).preconditioner hd).comp k
      hparam.contDiffAt
  have hgk : g k = v.root k := branch_center (b, k) (v.root k) (v.tube i).preconditioner hd
  obtain ⟨P, hP, U, hU, hu⟩ :=
    branch_unique_neighborhoods (p := (b, k)) (x := v.root k) (v.tube i).preconditioner hd hs.1
  have hp : ∀ᶠ s in nhdsWithin k v.domain, (b, s) ∈ P :=
    hparam.continuous.continuousAt.continuousWithinAt.tendsto.eventually hP
  have hv : ∀ᶠ s in nhdsWithin k v.domain, v.root s ∈ U :=
    (v.root_continuous_on k hk).tendsto.eventually hU
  refine ⟨g, hg, hgk, ?_⟩
  filter_upwards [hp, hv, self_mem_nhdsWithin] with s hsp hsu hsd
  exact hu (b, s) hsp (v.root s) hsu (v.root_spec hsd).1

theorem TubeCover.root_smooth_on [Finite ι] (v : TubeCover b ι) :
    ContDiffOn ℝ ∞ v.root v.domain := by
  intro k hk
  obtain ⟨g, hg, _, he⟩ := v.root_implicit_germ hk
  exact hg.contDiffWithinAt.congr_of_eventuallyEq_of_mem he hk

theorem TubeCover.groundPair_return (v : TubeCover b ι) {k : ℝ} (hk : k ∈ v.domain) :
    normSq (v.root k).1 = 1 ∧
      groundPair (sourcePotential b k (v.root k).1) = v.root k := by
  have hs := v.root_spec hk
  exact ⟨((residual_zero_iff b k _).mp hs.1).1,
    GroundLocalDynamics.positive_root_groundPair_return hs.1 hs.2.1⟩

end
end SbtCosmo.Derivation.GroundParameterPatch
