"""Render the proposed .3 neighborhood as closed kernel arithmetic."""
from pathlib import Path
import json
from de_ground_native_prefix_render import q,iv,vec
ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_basin_2026-10-04'

def render(w):
 s='''import SbtCosmo.Derivation.GroundNativeDerivativeBox
import SbtCosmo.Derivation.GroundCoordinates.Point002
import SbtCosmo.Derivation.GroundOriginalNativePrefix

/-! Data for an explicit whole native neighborhood. All proposals require
separate kernel arithmetic; no basin premise is hidden in this data module. -/
namespace SbtCosmo.Derivation.GroundBasin.Point002Data
noncomputable section
open GroundNativeBox GroundNativeDerivativeBox GroundRationalInterval
open GroundNativePrefixInitial (κ τ)
open GroundOriginalFirstTube

def ρ : ℚ := 1/40000
def basisBudget : ℚ := 177/50
def rate : ℚ := 3/5

def input : StateBox := ⟨fun i =>
  ⟨GroundSamples.Point002.z i.castSucc-ρ*basisBudget-GroundSamples.Point002.r,
   GroundSamples.Point002.z i.castSucc+ρ*basisBudget+GroundSamples.Point002.r⟩,
  fun _ => ⟨-(ρ*basisBudget), ρ*basisBudget⟩⟩
'''
 for k,field in [('z','ground_center'),('r','ground_radius'),('q','ground_rate'),('a','ground_residual')]:
  s+=f'def {k} : '+('Fin 9 → ℚ := '+vec(w[field]) if k=='z' else 'ℚ := '+q(w[field]))+'\n'
 s+='def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vec(row) for row in w['preconditioner'])+']\n'
 s+=f'def K : Interval := {iv(w["phase_inverse"])}\ndef L : Interval := {iv(w["normalization_inverse"])}\n'
 for k,field,start in [('yR','response_y',0),('yI','response_y',8),('eR','response_e',0),('eI','response_e',8)]:
  s+=f'def {k} : Fin 8 → ℚ := '+vec(w[field][start:start+8])+'\n'
 s+='''
def G : Fin 8 → Interval := GroundBackgroundKernel.fieldBox z r
def realDirection (j : Fin 8) : StateBox := ⟨fun i => Interval.point (GroundCoordinates.Point002.S i j), fun _ => Interval.point 0⟩
def imagDirection (j : Fin 8) : StateBox := ⟨fun _ => Interval.point 0, fun i => Interval.point (GroundCoordinates.Point002.R i j)⟩
def computedDR (j : Fin 8) : Fin 8 → Interval := GroundBackgroundResponse.responseInterval C G
  (sourceDerivativeBox originalBackground κ input (realDirection j)) (eR j)
def computedDI (j : Fin 8) : Fin 8 → Interval := GroundBackgroundResponse.responseInterval C G
  (sourceDerivativeBox originalBackground κ input (imagDirection j)) (eI j)
'''
 for name,part in [('DR',w['dg_cache'][:8]),('DI',w['dg_cache'][8:])]:
  s+=f'def {name} : Fin 8 → Fin 8 → Interval := ![\n  '+',\n  '.join('!['+', '.join(iv(x) for x in row)+']' for row in part)+']\n'
 s+='''
def output : StateBox := normalizedBox (mixedBox input G K) L
def computedJR (j : Fin 8) : StateBox := fullDerivativeBox input (realDirection j) G (DR j) K L
def computedJI (j : Fin 8) : StateBox := fullDerivativeBox input (imagDirection j) G (DI j) K L

'''
 for name,start in [('JR',0),('JI',8)]:
  rows=[]
  for j in range(start,start+8):
   rows.append('⟨!['+', '.join(iv(x) for x in w['jet_re_cache'][j])+'], !['+', '.join(iv(x) for x in w['jet_im_cache'][j])+']⟩')
  s+=f'def {name} : Fin 8 → StateBox := ![\n  '+',\n  '.join(rows)+']\n'
 s+='''
def coordinateBox (B : StateBox) : StateBox := ⟨
  fun i => sumBox (fun j => (Interval.point (GroundCoordinates.Point002.P i j)).mul (B.R j)),
  fun i => sumBox (fun j => (Interval.point (GroundCoordinates.Point002.Q i j)).mul (B.I j))⟩
def CR (j : Fin 8) : StateBox := coordinateBox (JR j)
def CI (j : Fin 8) : StateBox := coordinateBox (JI j)
def oldPositive : StateBox := ⟨GroundBackgroundKernel.fieldBox GroundSamples.Point002.z GroundSamples.Point002.r,
  fun _ => Interval.point 0⟩
def reflectedEndpoint : StateBox := ⟨fun i => ((GroundOriginalNativePrefix.boxes 16).R i).neg,
  fun i => ((GroundOriginalNativePrefix.boxes 16).I i).neg⟩
def entryBox : StateBox := coordinateBox (GroundOriginalNativePrefix.differenceBox reflectedEndpoint oldPositive)

end
end SbtCosmo.Derivation.GroundBasin.Point002Data
'''
 a='''import SbtCosmo.Derivation.GroundBasin.Point002Data

/-! Closed kernel budgets for a whole .3 neighborhood and all16 direction
responses. Data, near-inverse error and all real/imaginary blocks are retained. -/
namespace SbtCosmo.Derivation.GroundBasin.Point002Arithmetic
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundBasin.Point002Data GroundNativeBox GroundRationalInterval
open GroundNativePrefixInitial (κ τ)
open GroundOriginalFirstTube GroundNativeDerivativeBox
open scoped BigOperators

theorem radius_pos : 0 < ρ := by decide +kernel
theorem rate_budget : 0 ≤ rate ∧ rate < 1 := by decide +kernel
theorem basis_rows : ∀ i : Fin 8,
    (∑ j, |GroundCoordinates.Point002.S i j|) ≤ basisBudget ∧
    (∑ j, |GroundCoordinates.Point002.R i j|) ≤ basisBudget := by decide +kernel

theorem ground_arithmetic : GroundBackgroundKernel.Arithmetic (sourceBox originalBackground κ input) z r q a C := by
  constructor <;> decide +kernel

theorem phase_inverse : GroundIntervalReciprocal.Arithmetic (overlapBox input G) K := by
  constructor <;> decide +kernel

theorem normalization_inverse : GroundIntervalReciprocal.Arithmetic (normBox (mixedBox input G K)) L := by
  constructor <;> decide +kernel

theorem native_arithmetic : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q a C K L := by
  constructor
  · exact ground_arithmetic
  · exact phase_inverse
  · exact normalization_inverse
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; constructor <;> exact ⟨le_rfl, le_rfl⟩

theorem real_response : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
    (sourceDerivativeBox originalBackground κ input (realDirection j)) q (yR j) (eR j) := by
  intro j
  fin_cases j <;> constructor <;> decide +kernel

theorem imag_response : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
    (sourceDerivativeBox originalBackground κ input (imagDirection j)) q (yI j) (eI j) := by
  intro j
  fin_cases j <;> constructor <;> decide +kernel

theorem real_response_cache : ∀ j i : Fin 8, included (computedDR j i) (DR j i) := by
  intro j
  fin_cases j <;> unfold included <;> decide +kernel

theorem imag_response_cache : ∀ j i : Fin 8, included (computedDI j i) (DI j i) := by
  intro j
  fin_cases j <;> unfold included <;> decide +kernel

theorem real_jet_cache : ∀ j : Fin 8, (computedJR j).Included (JR j) := by
  intro j
  fin_cases j <;> unfold StateBox.Included included <;> decide +kernel

theorem imag_jet_cache : ∀ j : Fin 8, (computedJI j).Included (JI j) := by
  intro j
  fin_cases j <;> unfold StateBox.Included included <;> decide +kernel

theorem real_rows : ∀ i : Fin 8, (∑ j : Fin 8, (((CR j).R i).bound + ((CI j).R i).bound)) ≤ rate := by
  decide +kernel

theorem imag_rows : ∀ i : Fin 8, (∑ j : Fin 8, (((CR j).I i).bound + ((CI j).I i).bound)) ≤ rate := by
  decide +kernel

theorem selector_rows : ∀ i : Fin 8, (∑ j : Fin 8, ((DR j i).bound + (DI j i).bound)) ≤ 1 := by decide +kernel

theorem endpoint_rows : ∀ i : Fin 8, (entryBox.R i).bound ≤ 1/48000 ∧ (entryBox.I i).bound ≤ 1/48000 := by decide +kernel

theorem source_bounds : ∀ i : Fin 8, 0 ≤ (sourceBox originalBackground κ input i).lo ∧
    (sourceBox originalBackground κ input i).hi ≤ 1/2 := by decide +kernel

theorem zero_contraction_budget_rejected : ¬ ((∑ j : Fin 8, (((CR j).R 0).bound + ((CI j).R 0).bound)) ≤ 0) := by decide +kernel

end
end SbtCosmo.Derivation.GroundBasin.Point002Arithmetic
'''
 return {'lean/SbtCosmo/Derivation/GroundBasin/Point002Data.lean':s,
         'lean/SbtCosmo/Derivation/GroundBasin/Point002Arithmetic.lean':a}

if __name__=='__main__':
 for p,s in render(json.loads((PACKET/'witnesses.json').read_text())).items():
  t=ROOT/p;t.parent.mkdir(exist_ok=True);t.write_text(s)
