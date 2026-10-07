"""Reify the first immutable original coupling tube as rational Lean literals.

The generator supplies data only. Lean proves every numeric certificate and
returns it to actual real equations; Python output is not a proof premise.
"""
from fractions import Fraction
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'results/ground_branch_2026-10-03/witnesses.json'
TARGET = ROOT / 'lean/SbtCosmo/Derivation/GroundOriginalFirstTube.lean'


def rational(x):
    q = Fraction(x)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'


def vector(xs):
    return '![' + ', '.join(map(rational, xs)) + ']'


def render():
    data = json.loads(SOURCE.read_text())
    assert data['scale'] == str(2**80)
    w = data['tubes'][0]
    assert w['coupling_interval'] == ['0', '15/128']
    assert w['radius'] == str(2**80 // 256)
    beta = [Fraction.from_float(float.fromhex(t)) for t in data['background_hex']]
    z = [Fraction(int(t), 2**80) for t in w['center']]
    C = [[Fraction(int(t), 2**80) for t in row] for row in w['newton_inverse']]
    assert len(beta) == 8 and len(z) == 9 and len(C) == 9 and all(len(row) == 9 for row in C)
    return '''import SbtCosmo.Derivation.GroundKernelTube

/-! First concrete original-background uniform tube checked inside Lean.
Data are exact rational reifications from the immutable original witness.
All arithmetic and actual-root returns are kernel proofs, without supplied
norm, residual, positivity or root assumptions. -/
namespace SbtCosmo.Derivation.GroundOriginalFirstTube
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundState GroundBorder GroundRootCertificate GroundKernelTube
open GroundParameterTube GroundResidualEnclosure GroundRationalInterval
open scoped ContDiff BigOperators

''' + f'def originalBackground : Fin 8 → ℚ := {vector(beta)}\n\n' + \
        f'def originalCenter : Fin 9 → ℚ := {vector(z)}\n\n' + \
        'def originalPreconditioner : Matrix (Fin 9) (Fin 9) ℚ := ![\n  ' + \
        ',\n  '.join(map(vector, C)) + ']\n\n' + '''theorem arithmetic : Arithmetic originalBackground 0 (15/128) originalCenter
    (1/256) (1/10) (3/1000) originalPreconditioner := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def originalTube : TubeCertificate (background originalBackground) := tube arithmetic

theorem original_positive_root (κ : ℝ) (hk : κ ∈ Set.Icc (0 : ℝ) (15/128)) :
    ∃ x ∈ Metric.closedBall (center originalCenter) (1/256 : ℝ),
      residual (background originalBackground) κ x = 0 ∧
      IsGround (sourcePotential (background originalBackground) κ x.1) x.1 x.2 ∧
      GroundSourceJacobian.groundMap (background originalBackground) κ x.1 = x.1 ∧
      ∀ t ∈ Metric.closedBall (center originalCenter) (1/256 : ℝ),
        residual (background originalBackground) κ t = 0 → t = x :=
by
  have hk' : κ ∈ Set.Icc ((0 : ℚ) : ℝ) ((15/128 : ℚ) : ℝ) := by
    norm_num
    exact hk
  have ht := certified_actual_root (κ := κ) arithmetic hk'
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using ht

theorem original_smooth_branch :
    ContDiffOn ℝ ∞ originalTube.root (Set.Icc (0 : ℝ) (15/128)) := by
  have he : originalTube.interval = Set.Icc (0 : ℝ) (15/128) := by
    simp only [originalTube, tube, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat]
  rw [← he]
  intro κ hk
  exact originalTube.root_smooth_within hk

theorem zero_preconditioner_rejected :
    ¬ Arithmetic originalBackground 0 (15/128) originalCenter
      (1/256) (1/10) (3/1000) (fun _ _ => 0) := by
  intro h
  have hn : ¬ (∑ j : Fin 9,
      ((defectExpr (fun _ _ => 0) 0 j).enclose
        (box originalBackground 0 (15/128) originalCenter (1/256))).bound) ≤ (1/10 : ℚ) := by
    decide +kernel
  exact hn (h.defect_rows 0)

theorem false_residual_budget_rejected :
    ¬ Arithmetic originalBackground 0 (15/128) originalCenter
      (1/256) (1/10) 1 originalPreconditioner := by
  intro h
  have hh := h.strict_invariance
  norm_num at hh

end
end SbtCosmo.Derivation.GroundOriginalFirstTube
'''


if __name__ == '__main__':
    TARGET.write_text(render())
    print('Reified first original uniform tube; arithmetic must be proved by Lean')
