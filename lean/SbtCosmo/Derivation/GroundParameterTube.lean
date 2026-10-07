import SbtCosmo.Derivation.GroundParameterBranch

/-! A uniform quantitative Newton tube constructs positive actual roots
for every parameter in its interval. Smoothness up to its boundaries is earned
by return to the local implicit branch, not assumed of a selected root. -/
namespace SbtCosmo.Derivation.GroundParameterTube
noncomputable section
set_option maxHeartbeats 2000000
open Filter Metric GroundState GroundBorder GroundRootCertificate GroundSourceJacobian
open GroundParameterEquations GroundParameterBranch
open scoped Topology ContDiff

structure TubeCertificate (b : Field) where
  interval : Set ℝ
  center : Point
  radius : ℝ
  preconditioner : Point →L[ℝ] Point
  rate : NNReal
  radius_pos : 0 < radius
  rate_lt : rate < 1
  defect : ∀ k ∈ interval, ∀ x ∈ closedBall center radius,
    ‖correctionDerivative b k preconditioner x‖ ≤ rate
  residual_strict : ∀ k ∈ interval,
    ‖preconditioner (residual b k center)‖ + rate * radius < radius
  field_positive : ∀ x ∈ closedBall center radius, ∀ i, 0 < x.1 i

variable {b : Field}

theorem TubeCertificate.preconditioner_injective (t : TubeCertificate b) {k : ℝ}
    (hk : k ∈ t.interval) : Function.Injective t.preconditioner := by
  apply (defect_preconditioner_bijective t.preconditioner (residualDerivative b k t.center) ?_).1
  exact (t.defect k hk t.center (mem_closedBall_self t.radius_pos.le)).trans_lt t.rate_lt

theorem TubeCertificate.positive_root_exists (t : TubeCertificate b) {k : ℝ} (hk : k ∈ t.interval) :
    ∃ x ∈ closedBall t.center t.radius, residual b k x = 0 ∧
      IsGround (sourcePotential b k x.1) x.1 x.2 ∧ groundMap b k x.1 = x.1 ∧
      ∀ y ∈ closedBall t.center t.radius, residual b k y = 0 → y = x :=
  certified_positive_root b k t.preconditioner (t.preconditioner_injective hk)
    t.center t.radius t.rate t.radius_pos.le t.rate_lt (t.defect k hk)
    (t.residual_strict k hk).le t.field_positive

def TubeCertificate.root (t : TubeCertificate b) (k : ℝ) : Point :=
  @dite Point (k ∈ t.interval) (Classical.propDecidable _) (fun hk => (t.positive_root_exists hk).choose)
    (fun _ => t.center)

theorem TubeCertificate.root_spec (t : TubeCertificate b) {k : ℝ} (hk : k ∈ t.interval) :
    t.root k ∈ closedBall t.center t.radius ∧ residual b k (t.root k) = 0 ∧
      IsGround (sourcePotential b k (t.root k).1) (t.root k).1 (t.root k).2 ∧
      groundMap b k (t.root k).1 = (t.root k).1 ∧
      ∀ y ∈ closedBall t.center t.radius, residual b k y = 0 → y = t.root k := by
  simpa only [TubeCertificate.root, dif_pos hk] using (t.positive_root_exists hk).choose_spec

theorem TubeCertificate.root_distance_lt (t : TubeCertificate b) {k : ℝ} (hk : k ∈ t.interval) :
    dist (t.root k) t.center < t.radius := by
  have hs := t.root_spec hk
  have hl := correction_lipschitz b k t.preconditioner t.center t.radius t.rate (t.defect k hk)
  have hh := hl.dist_le_mul (t.root k) hs.1 t.center (mem_closedBall_self t.radius_pos.le)
  have hf : correction b k t.preconditioner (t.root k) = t.root k := by simp [correction, hs.2.1]
  have hc : dist (correction b k t.preconditioner t.center) t.center =
      ‖t.preconditioner (residual b k t.center)‖ := by simp [correction]
  rw [hf] at hh
  have ht := dist_triangle (t.root k) (correction b k t.preconditioner t.center) t.center
  rw [hc] at ht
  have hdist : dist (t.root k) t.center ≤ t.radius := hs.1
  have hb := mul_le_mul_of_nonneg_left hdist t.rate.coe_nonneg
  calc
    dist (t.root k) t.center ≤ t.rate * t.radius + ‖t.preconditioner (residual b k t.center)‖ :=
      ht.trans (add_le_add (hh.trans hb) le_rfl)
    _ < t.radius := by simpa only [add_comm] using t.residual_strict k hk

/-- The tube root is the germ of an earned C-infinity branch, including
one-sided interval endpoints. No continuity of a chosen root is a premise. -/
theorem TubeCertificate.root_implicit_germ (t : TubeCertificate b) {k : ℝ} (hk : k ∈ t.interval) :
    ∃ g : ℝ → Point, ContDiffAt ℝ ∞ g k ∧ g k = t.root k ∧
      t.root =ᶠ[nhdsWithin k t.interval] g := by
  have hs := t.root_spec hk
  have hd : ‖correctionDerivative b k t.preconditioner (t.root k)‖ < 1 :=
    (t.defect k hk (t.root k) hs.1).trans_lt t.rate_lt
  let f := branch (b, k) (t.root k) t.preconditioner hd
  let g : ℝ → Point := fun s => f (b, s)
  have hparam : ContDiff ℝ ∞ (fun s : ℝ => ((b, s) : Parameter)) := contDiff_const.prodMk contDiff_id
  have hg : ContDiffAt ℝ ∞ g k :=
    (branch_smooth_at (b, k) (t.root k) t.preconditioner hd).comp k
      hparam.contDiffAt
  have hgk : g k = t.root k := branch_center (b, k) (t.root k) t.preconditioner hd
  have hp : Tendsto (fun s : ℝ => ((b, s) : Parameter)) (nhds k) (nhds (b, k)) :=
    hparam.continuous.continuousAt.tendsto
  have hroot : ∀ᶠ s in nhds k, residual b s (g s) = 0 :=
    hp.eventually (branch_root_eventually (p := (b, k)) (x := t.root k) t.preconditioner hd hs.2.1)
  have ht := hg.continuousAt.tendsto
  rw [hgk] at ht
  have hnb : ball t.center t.radius ∈ nhds (t.root k) :=
    isOpen_ball.mem_nhds (t.root_distance_lt hk)
  have hball : ∀ᶠ s in nhds k, g s ∈ closedBall t.center t.radius :=
    (ht.eventually hnb).mono fun _ hh => ball_subset_closedBall hh
  refine ⟨g, hg, hgk, ?_⟩
  filter_upwards [hroot.filter_mono nhdsWithin_le_nhds, hball.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hsr hsb hsi
  exact ((t.root_spec hsi).2.2.2.2 _ hsb hsr).symm

theorem TubeCertificate.root_smooth_within (t : TubeCertificate b) {k : ℝ} (hk : k ∈ t.interval) :
    ContDiffWithinAt ℝ ∞ t.root t.interval k := by
  obtain ⟨g, hg, _, he⟩ := t.root_implicit_germ hk
  exact hg.contDiffWithinAt.congr_of_eventuallyEq_of_mem he hk

theorem TubeCertificate.root_continuous_on (t : TubeCertificate b) : ContinuousOn t.root t.interval :=
  fun _ hk => (t.root_smooth_within hk).continuousWithinAt

/-- Two uniform tubes share the same root whenever a smaller certified
common root lies in both boxes at the same coupling. Closeness alone is unused. -/
theorem common_root_glues (t v : TubeCertificate b) {k : ℝ}
    (ht : k ∈ t.interval) (hv : k ∈ v.interval) {x : Point}
    (hz : residual b k x = 0) (hxt : x ∈ closedBall t.center t.radius)
    (hxv : x ∈ closedBall v.center v.radius) : t.root k = v.root k := by
  exact ((t.root_spec ht).2.2.2.2 x hxt hz).symm.trans ((v.root_spec hv).2.2.2.2 x hxv hz)

end
end SbtCosmo.Derivation.GroundParameterTube
