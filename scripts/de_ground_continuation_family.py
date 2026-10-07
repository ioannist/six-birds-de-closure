"""Render the concrete finite endpoint-chain assembly from immutable witnesses.

This generator writes the assembly module only. It never modifies concrete leaf
modules, allowing assembly work while their independent kernel builds run.
"""
from fractions import Fraction as F
import json
from pathlib import Path

from de_ground_kernel_tube_generate import rational, vector

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT/'lean/SbtCosmo/Derivation/GroundOriginalContinuation.lean'


def render():
    data = json.loads((ROOT/'results/ground_branch_2026-10-03/witnesses.json').read_text())
    assert len(data['tubes']) == 286 and len(data['anchors']) == 287
    edges = [F(data['tubes'][0]['coupling_interval'][0])]+[F(w['coupling_interval'][1]) for w in data['tubes']]
    assert edges[0] == 0 and edges[-1] == 30
    assert [F(w['coupling']) for w in data['anchors']] == edges
    for i, w in enumerate(data['tubes']):
        assert list(map(F,w['coupling_interval'])) == edges[i:i+2]
    imports = 'import SbtCosmo.Derivation.GroundKernelChainCoverage\n'
    imports += ''.join('import SbtCosmo.Derivation.GroundContinuation.'+kind+f'{i:03d}\n'
                       for kind, indices in [('Tube',range(1,286)),('Anchor',range(287))] for i in indices)
    text = imports+'''
/-! All original uniform tubes and endpoint anchors instantiated in the kernel.
Finite geometry and earned overlap/coverage return a single actual positive
C-infinity ground/energy branch throughout the original interval [0,30]. -/
namespace SbtCosmo.Derivation.GroundOriginalContinuation
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundState GroundBorder GroundRootCertificate GroundKernelTube GroundKernelChain
open GroundKernelChainCoverage GroundParameterPatch GroundOriginalFirstTube
open scoped ContDiff

def firstDatum : Data originalBackground :=
  ⟨0, 15/128, originalCenter, 1/256, 1/10, 3/1000, originalPreconditioner, arithmetic⟩

'''
    text += 'def edges : Fin 287 → ℚ := '+vector(edges)+'\n\n'
    pieces = ['firstDatum']+['GroundContinuation.Tube'+f'{i:03d}.datum' for i in range(1,286)]
    anchors = ['GroundContinuation.Anchor'+f'{i:03d}.datum' for i in range(287)]
    text += 'def pieces : Fin 286 → Data originalBackground := ![\n  '+',\n  '.join(pieces)+']\n\n'
    text += 'def anchors : Fin 287 → Data originalBackground := ![\n  '+',\n  '.join(anchors)+']\n\n'
    text += '''theorem increasing : ∀ i : Fin 286, edges i.castSucc < edges i.succ := by
  decide +kernel

theorem piece_bounds : ∀ i : Fin 286,
    (pieces i).a = edges i.castSucc ∧ (pieces i).c = edges i.succ := by
  decide +kernel

theorem anchor_bounds : ∀ i : Fin 287,
    (anchors i).a = edges i ∧ (anchors i).c = edges i := by
  decide +kernel

theorem containment : ∀ i : Fin 286, ∀ j : Fin 9,
    |(anchors i.castSucc).z j - (pieces i).z j| + (anchors i.castSucc).r ≤ (pieces i).r ∧
    |(anchors i.succ).z j - (pieces i).z j| + (anchors i.succ).r ≤ (pieces i).r := by
  decide +kernel

def chain : Chain originalBackground 285 where
  edge := edges
  piece := pieces
  anchor := anchors
  increasing := increasing
  piece_a := fun i => (piece_bounds i).1
  piece_c := fun i => (piece_bounds i).2
  anchor_a := fun i => (anchor_bounds i).1
  anchor_c := fun i => (anchor_bounds i).2
  left_inside := fun i j => (containment i j).1
  right_inside := fun i j => (containment i j).2

def cover : TubeCover (background originalBackground) (Fin 286) := chain.cover

def branch : ℝ → Point := cover.root

theorem domain_eq : cover.domain = Set.Icc (0 : ℝ) 30 := by
  have h := chain_cover_domain chain
  change cover.domain = Set.Icc (edges 0 : ℝ) (edges (Fin.last 286) : ℝ) at h
  have hl : edges 0 = 0 := by decide +kernel
  have hr : edges (Fin.last 286) = 30 := by decide +kernel
  rw [hl, hr] at h
  simpa only [Rat.cast_zero, Rat.cast_ofNat] using h

theorem whole_smooth : ContDiffOn ℝ ∞ branch (Set.Icc (0 : ℝ) 30) := by
  rw [← domain_eq]
  exact cover.root_smooth_on

theorem whole_ground (κ : ℝ) (hk : κ ∈ Set.Icc (0 : ℝ) 30) :
    residual (background originalBackground) κ (branch κ) = 0 ∧
      (∀ i, 0 < (branch κ).1 i) ∧ normSq (branch κ).1 = 1 ∧
      groundPair (sourcePotential (background originalBackground) κ (branch κ).1) = branch κ ∧
      GroundSourceJacobian.groundMap (background originalBackground) κ (branch κ).1 = (branch κ).1 := by
  have hk' : κ ∈ cover.domain := by rw [domain_eq]; exact hk
  have hs := cover.root_spec hk'
  have hg := cover.groundPair_return hk'
  exact ⟨hs.1, hs.2.1, hg.1, hg.2, hs.2.2.2⟩

theorem whole_native_fixed (κ m : ℝ) (hk : κ ∈ Set.Icc (0 : ℝ) 30) :
    GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance
      (background originalBackground) κ m (GroundState.realEmbed (branch κ).1) =
        GroundState.realEmbed (branch κ).1 ∧
      GroundNativeIteration.ActivePhase GroundNativeControls.originalTolerance
        (background originalBackground) κ (GroundState.realEmbed (branch κ).1) ∧
      GroundNativeIteration.NativeLegal GroundNativeControls.originalTolerance
        (background originalBackground) κ m (GroundState.realEmbed (branch κ).1) := by
  have hk' : κ ∈ cover.domain := by rw [domain_eq]; exact hk
  exact GroundParameterPatchReturn.native_fixed_legal cover hk'
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2

end
end SbtCosmo.Derivation.GroundOriginalContinuation
'''
    return text


if __name__ == '__main__':
    TARGET.write_text(render())
    print('Rendered concrete full interval chain; geometric proof obligations must be checked by Lean')
