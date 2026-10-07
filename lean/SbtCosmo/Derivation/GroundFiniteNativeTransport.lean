import SbtCosmo.Derivation.GroundLocalDynamics
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
namespace SbtCosmo.Derivation.GroundFiniteNativeTransport
open Metric

theorem step {α : Type*} [PseudoMetricSpace α] (f : α → α)
    {c next x : α} {r nextRadius defect : ℝ} {M : NNReal}
    (hr : 0 ≤ r) (hL : LipschitzOnWith M f (closedBall c r))
    (hdefect : dist (f c) next ≤ defect)
    (hbudget : (M : ℝ)*r+defect ≤ nextRadius) (hx : x ∈ closedBall c r) :
    f x ∈ closedBall next nextRadius := by
  rw [mem_closedBall]
  calc
    dist (f x) next ≤ dist (f x) (f c)+dist (f c) next := dist_triangle _ _ _
    _ ≤ (M : ℝ)*dist x c+defect := add_le_add (hL.dist_le_mul _ hx _ (mem_closedBall_self hr)) hdefect
    _ ≤ (M : ℝ)*r+defect := add_le_add (mul_le_mul_of_nonneg_left (mem_closedBall.mp hx) M.property) le_rfl
    _ ≤ nextRadius := hbudget

theorem enclosed {α : Type*} [PseudoMetricSpace α] (f : α → α) {N : ℕ}
    (centres : Fin (N+1) → α) (radii : Fin (N+1) → ℝ)
    (rates : Fin N → NNReal) (defects : Fin N → ℝ) {initial : α}
    (hr : ∀ j, 0 ≤ radii j)
    (hL : ∀ j, LipschitzOnWith (rates j) f (closedBall (centres j.castSucc) (radii j.castSucc)))
    (hdefect : ∀ j, dist (f (centres j.castSucc)) (centres j.succ) ≤ defects j)
    (hbudget : ∀ j, (rates j : ℝ)*radii j.castSucc+defects j ≤ radii j.succ)
    (hi : initial ∈ closedBall (centres 0) (radii 0)) (i : Fin (N+1)) :
    (f^[i.val]) initial ∈ closedBall (centres i) (radii i) := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · exact hi
  · change (f^[j.val+1]) initial ∈ closedBall (centres j.succ) (radii j.succ)
    rw [Function.iterate_succ_apply']
    exact step f (hr j.castSucc) (hL j) (hdefect j) (hbudget j) ih

theorem endpoint_distance {α : Type*} [PseudoMetricSpace α]
    {x c target : α} {r d : ℝ} (hx : x ∈ closedBall c r)
    (hcentre : dist c target ≤ d) : dist x target ≤ r+d :=
  (dist_triangle _ _ _).trans (add_le_add (mem_closedBall.mp hx) hcentre)
end SbtCosmo.Derivation.GroundFiniteNativeTransport
