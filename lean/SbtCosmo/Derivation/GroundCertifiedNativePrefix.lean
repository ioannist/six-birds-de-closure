import SbtCosmo.Derivation.GroundUncertainNativeBox
import SbtCosmo.Derivation.GroundOriginalSeed
import SbtCosmo.Derivation.GroundNativeEscape

/-! Actual guarded original-seed prefixes from populated step certificates.
Input-domain membership and every finite seam are retained explicitly. -/
namespace SbtCosmo.Derivation.GroundCertifiedNativePrefix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open Filter
open scoped Topology

structure Step (β : Fin 8 → Interval) (κ τ : ℚ) where
  input : StateBox
  output : StateBox
  z : Fin 9 → ℚ
  r : ℚ
  q : ℚ
  y : ℚ
  C : Matrix (Fin 9) (Fin 9) ℚ
  K : Interval
  L : Interval
  proof : GroundUncertainNativeBox.Arithmetic β κ τ input output z r q y C K L

structure Certificate (β : Fin 8 → Interval) (κ τ : ℚ) (N : ℕ) where
  first : StateBox
  steps : Fin N → Step β κ τ
  initial : first.Contains (unpack GroundOriginalSeed.initial)
  threshold_nonneg : 0 ≤ τ
  seams : ∀ i : Fin N,
    (Fin.cases first (fun j => (steps j).output) i.castSucc) = (steps i).input

namespace Certificate
variable {β : Fin 8 → Interval} {κ τ : ℚ} {N : ℕ}

def boxes (c : Certificate β κ τ N) : Fin (N+1) → StateBox :=
  Fin.cases c.first (fun j => (c.steps j).output)
def f (b : Field) : ComplexField → ComplexField := nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2)
def orbit (b : Field) (n : ℕ) : ComplexField := (f (κ := κ) (τ := τ) b)^[n] GroundOriginalSeed.initial

theorem step (c : Certificate β κ τ N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (i : Fin N) {x : State}
    (hx : (c.steps i).input.Contains x) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (pack x) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack x) ∧
    (c.steps i).output.Contains (unpack (f (κ := κ) (τ := τ) b (pack x))) :=
  GroundUncertainNativeBox.arithmetic_native_step (c.steps i).proof hb hx

theorem enclosed (c : Certificate β κ τ N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (i : Fin (N+1)) :
    (c.boxes i).Contains (unpack (orbit (κ := κ) (τ := τ) b i.val)) := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · exact c.initial
  · have hx : (c.steps j).input.Contains (unpack (orbit (κ := κ) (τ := τ) b j.val)) := by
      rw [← c.seams j]
      exact ih
    have h := (c.step hb j hx).2.2
    have he : pack (unpack (orbit (κ := κ) (τ := τ) b j.val)) = orbit (κ := κ) (τ := τ) b j.val :=
      packCLE.apply_symm_apply _
    rw [he] at h
    change (c.steps j).output.Contains (unpack (orbit (κ := κ) (τ := τ) b (j.val+1)))
    rw [orbit,Function.iterate_succ_apply']
    exact h

theorem guards (c : Certificate β κ τ N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (i : Fin N) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (orbit (κ := κ) (τ := τ) b i.val) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (orbit (κ := κ) (τ := τ) b i.val) := by
  have hx : (c.steps i).input.Contains (unpack (orbit (κ := κ) (τ := τ) b i.val)) := by
    rw [← c.seams i]
    exact c.enclosed hb i.castSucc
  have h := c.step hb i hx
  have he : pack (unpack (orbit (κ := κ) (τ := τ) b i.val)) = orbit (κ := κ) (τ := τ) b i.val :=
    packCLE.apply_symm_apply _
  rw [he] at h
  exact ⟨h.1,h.2.1⟩

theorem unit (c : Certificate β κ τ N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (i : Fin (N+1)) :
    complexNormSq (orbit (κ := κ) (τ := τ) b i.val) = 1 := by
  refine Fin.induction ?_ (fun j _ => ?_) i
  · exact GroundOriginalSeed.initial_unit
  · change complexNormSq (orbit (κ := κ) (τ := τ) b (j.val+1)) = 1
    rw [orbit,Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit (by exact_mod_cast c.threshold_nonneg) (c.guards hb j).2

end Certificate
end
end SbtCosmo.Derivation.GroundCertifiedNativePrefix
