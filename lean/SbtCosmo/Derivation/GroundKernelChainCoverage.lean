import SbtCosmo.Derivation.GroundKernelChain

/-! Interval coverage for the finite certified endpoint chain. Together with
the earned overlap constructor this returns an actual smooth branch on the
whole interval, including both outer endpoints. -/
namespace SbtCosmo.Derivation.GroundKernelChainCoverage
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundKernelTube GroundKernelChain
open GroundParameterPatch
open scoped ContDiff

theorem finite_interval_union {n : ℕ} (edge : Fin (n+2) → ℝ) (hm : Monotone edge) :
    (⋃ i : Fin (n+1), Set.Icc (edge i.castSucc) (edge i.succ)) =
      Set.Icc (edge 0) (edge (Fin.last (n+1))) := by
  induction n with
  | zero =>
    ext k
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      exact hi
    · intro hk
      exact ⟨0, hk⟩
  | succ n ih =>
    let g : Fin (n+2) → ℝ := fun i => edge i.castSucc
    have hg : Monotone g := hm.comp Fin.strictMono_castSucc.monotone
    have hs : (⋃ i : Fin (n+2), Set.Icc (edge i.castSucc) (edge i.succ)) =
        (⋃ i : Fin (n+1), Set.Icc (g i.castSucc) (g i.succ)) ∪
        Set.Icc (edge (Fin.last (n+1)).castSucc) (edge (Fin.last (n+2))) := by
      ext k
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        revert hi
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro hi
          exact Or.inr hi
        · intro hi
          exact Or.inl ⟨j, hi⟩
      · rintro (⟨i, hi⟩ | hi)
        · exact ⟨i.castSucc, hi⟩
        · exact ⟨Fin.last (n+1), hi⟩
    rw [hs, ih g hg]
    exact Set.Icc_union_Icc_eq_Icc (hm (Fin.zero_le _)) (hm (Fin.le_last _))

variable {β : Fin 8 → ℚ} {n : ℕ}

theorem chain_cover_domain (s : Chain β n) :
    s.cover.domain = Set.Icc (s.edge 0 : ℝ) (s.edge (Fin.last (n+1)) : ℝ) := by
  change (⋃ i, (s.piece i).toTube.interval) = _
  simp_rw [s.piece_interval]
  exact finite_interval_union _ s.edge_strictMono.monotone

theorem chain_whole_branch_smooth (s : Chain β n) :
    ContDiffOn ℝ ∞ s.cover.root (Set.Icc (s.edge 0 : ℝ) (s.edge (Fin.last (n+1)) : ℝ)) := by
  rw [← chain_cover_domain s]
  exact s.cover.root_smooth_on

theorem chain_whole_branch_ground (s : Chain β n) {k : ℝ}
    (hk : k ∈ Set.Icc (s.edge 0 : ℝ) (s.edge (Fin.last (n+1)) : ℝ)) :
    normSq (s.cover.root k).1 = 1 ∧
      groundPair (sourcePotential (background β) k (s.cover.root k).1) = s.cover.root k := by
  exact s.cover.groundPair_return ((chain_cover_domain s).symm ▸ hk)

end
end SbtCosmo.Derivation.GroundKernelChainCoverage
