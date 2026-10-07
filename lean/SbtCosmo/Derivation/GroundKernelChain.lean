import SbtCosmo.Derivation.GroundOriginalFirstTube
import SbtCosmo.Derivation.GroundParameterPatchReturn
import Mathlib.Order.Fin.Basic

/-! Concrete proof-carrying rational tubes and ordered endpoint chains.
The chain constructor earns all overlap obligations from certified endpoint
anchors and coordinate ball containment; no root/continuity premise is added. -/
namespace SbtCosmo.Derivation.GroundKernelChain
noncomputable section
set_option maxHeartbeats 2000000
open Metric GroundState GroundBorder GroundKernelTube GroundPointCoordinates
open GroundParameterTube GroundParameterPatch
open scoped BigOperators ContDiff

structure Data (β : Fin 8 → ℚ) where
  a : ℚ
  c : ℚ
  z : Fin 9 → ℚ
  r : ℚ
  q : ℚ
  y : ℚ
  C : Matrix (Fin 9) (Fin 9) ℚ
  arithmetic : Arithmetic β a c z r q y C

variable {β : Fin 8 → ℚ}

def Data.toTube (d : Data β) : TubeCertificate (background β) := tube d.arithmetic

theorem Data.ball_subset (d e : Data β)
    (h : ∀ j, |d.z j - e.z j| + d.r ≤ e.r) :
    closedBall d.toTube.center d.toTube.radius ⊆ closedBall e.toTube.center e.toTube.radius := by
  intro x hx
  change ‖x - center e.z‖ ≤ (e.r : ℝ)
  have hn : ‖x - center d.z‖ ≤ (d.r : ℝ) := by
    simpa only [Data.toTube, tube, mem_closedBall, dist_eq_norm] using hx
  apply norm_le_coordinates (by exact_mod_cast e.arithmetic.radius_pos.le)
  intro j
  have hc := (coord_norm_le (x - center d.z) j).trans hn
  simp only [coord_sub, center, coord_fromCoord] at hc ⊢
  have hh : |(d.z j : ℝ) - (e.z j : ℝ)| + (d.r : ℝ) ≤ (e.r : ℝ) := by exact_mod_cast h j
  calc
    |coord x j - (e.z j : ℝ)| = |(coord x j - (d.z j : ℝ)) + ((d.z j : ℝ) - (e.z j : ℝ))| := by
      congr 1
      ring
    _ ≤ |coord x j - (d.z j : ℝ)| + |(d.z j : ℝ) - (e.z j : ℝ)| := abs_add_le _ _
    _ ≤ (d.r : ℝ) + |(d.z j : ℝ) - (e.z j : ℝ)| := add_le_add hc le_rfl
    _ ≤ (e.r : ℝ) := by simpa only [add_comm] using hh

structure Chain (β : Fin 8 → ℚ) (n : ℕ) where
  edge : Fin (n+2) → ℚ
  piece : Fin (n+1) → Data β
  anchor : Fin (n+2) → Data β
  increasing : ∀ i : Fin (n+1), edge i.castSucc < edge i.succ
  piece_a : ∀ i, (piece i).a = edge i.castSucc
  piece_c : ∀ i, (piece i).c = edge i.succ
  anchor_a : ∀ i, (anchor i).a = edge i
  anchor_c : ∀ i, (anchor i).c = edge i
  left_inside : ∀ i j, |(anchor i.castSucc).z j - (piece i).z j| + (anchor i.castSucc).r ≤ (piece i).r
  right_inside : ∀ i j, |(anchor i.succ).z j - (piece i).z j| + (anchor i.succ).r ≤ (piece i).r

variable {n : ℕ}

theorem Chain.edge_strictMono (s : Chain β n) : StrictMono (fun i => (s.edge i : ℝ)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact_mod_cast s.increasing i

theorem Chain.piece_interval (s : Chain β n) (i : Fin (n+1)) :
    (s.piece i).toTube.interval = Set.Icc (s.edge i.castSucc : ℝ) (s.edge i.succ : ℝ) := by
  simp only [Data.toTube, tube, s.piece_a, s.piece_c]

theorem Chain.anchor_interval (s : Chain β n) (i : Fin (n+2)) :
    (s.anchor i).toTube.interval = Set.Icc (s.edge i : ℝ) (s.edge i : ℝ) := by
  simp only [Data.toTube, tube, s.anchor_a, s.anchor_c]

theorem Chain.ordered_overlap (s : Chain β n) {i j : Fin (n+1)} {k : ℝ}
    (hij : i < j) (hi : k ∈ (s.piece i).toTube.interval) (hj : k ∈ (s.piece j).toTube.interval) :
    ∃ a : TubeCertificate (background β), k ∈ a.interval ∧
      closedBall a.center a.radius ⊆ closedBall (s.piece i).toTube.center (s.piece i).toTube.radius ∧
      closedBall a.center a.radius ⊆ closedBall (s.piece j).toTube.center (s.piece j).toTube.radius := by
  rw [s.piece_interval] at hi hj
  have he_le : j.castSucc ≤ i.succ := s.edge_strictMono.le_iff_le.mp (hj.1.trans hi.2)
  have he : j.castSucc = i.succ := by
    change j.val ≤ i.val + 1 at he_le
    change i.val < j.val at hij
    apply Fin.ext
    change j.val = i.val + 1
    omega
  have hk : k = (s.edge i.succ : ℝ) := by
    rw [he] at hj
    exact le_antisymm hi.2 hj.1
  refine ⟨(s.anchor i.succ).toTube, ?_, ?_, ?_⟩
  · rw [s.anchor_interval, hk]
    exact ⟨le_rfl, le_rfl⟩
  · exact (s.anchor i.succ).ball_subset (s.piece i) (s.right_inside i)
  · rw [← he]
    exact (s.anchor j.castSucc).ball_subset (s.piece j) (s.left_inside j)

def Chain.cover (s : Chain β n) : TubeCover (background β) (Fin (n+1)) where
  tube := fun i => (s.piece i).toTube
  closed := fun i => by rw [s.piece_interval]; exact isClosed_Icc
  overlap := by
    intro i j k hi hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact s.ordered_overlap hij hi hj
    · subst j
      exact ⟨(s.piece i).toTube, hi, Set.Subset.rfl, Set.Subset.rfl⟩
    · obtain ⟨a, ha, haj, hai⟩ := s.ordered_overlap hij hj hi
      exact ⟨a, ha, hai, haj⟩

end
end SbtCosmo.Derivation.GroundKernelChain
