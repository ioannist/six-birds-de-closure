import SbtCosmo.Derivation.GroundBackgroundKernel
import SbtCosmo.Derivation.GroundIntervalReciprocal
import SbtCosmo.Derivation.GroundNativeIteration

/-! Exact interval propagation through the unchanged native complex half update.
Uniform potential-box Newton certificates identify its actual selected ground;
both reciprocal square roots and source guards are earned from rational budgets. -/
namespace SbtCosmo.Derivation.GroundNativeBox
noncomputable section
set_option maxHeartbeats 5000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundKernelTube
open GroundRationalInterval GroundIntervalReciprocal
open scoped BigOperators

structure StateBox where
  R : Fin 8 → Interval
  I : Fin 8 → Interval
  deriving DecidableEq

def StateBox.Contains (B : StateBox) (x : State) : Prop := ∀ i, (B.R i).Contains (x.1 i) ∧ (B.I i).Contains (x.2 i)
def included (A B : Interval) : Prop := B.lo ≤ A.lo ∧ A.hi ≤ B.hi

theorem included_sound {A B : Interval} (h : included A B) {x : ℝ} (hx : A.Contains x) : B.Contains x := by
  have hl : (B.lo : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
  have hh : (A.hi : ℝ) ≤ (B.hi : ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1, hx.2.trans hh⟩

def StateBox.Included (A B : StateBox) : Prop := ∀ i, included (A.R i) (B.R i) ∧ included (A.I i) (B.I i)

theorem StateBox.included_sound {A B : StateBox} (h : A.Included B) {x : State} (hx : A.Contains x) : B.Contains x :=
  fun i => ⟨GroundNativeBox.included_sound (h i).1 (hx i).1, GroundNativeBox.included_sound (h i).2 (hx i).2⟩

def sumBox {n : ℕ} (A : Fin n → Interval) : Interval :=
  (Expr.sum (fun i : Fin n => (Expr.var i : Expr (Fin n)))).enclose A

theorem sumBox_sound {n : ℕ} {A : Fin n → Interval} {x : Fin n → ℝ}
    (h : ∀ i, (A i).Contains (x i)) : (sumBox A).Contains (∑ i, x i) := by
  have hs := (Expr.sum (fun i : Fin n => (Expr.var i : Expr (Fin n)))).enclose_sound h
  simpa only [sumBox, Expr.eval_sum, Expr.eval] using hs

def normBox (B : StateBox) : Interval := sumBox (fun i => ((B.R i).mul (B.R i)).add ((B.I i).mul (B.I i)))

theorem normBox_sound {B : StateBox} {x : State} (hx : B.Contains x) : (normBox B).Contains (stateNormSq x) := by
  have h := sumBox_sound (fun i => Interval.add_sound (Interval.mul_sound (hx i).1 (hx i).1)
    (Interval.mul_sound (hx i).2 (hx i).2))
  simpa only [normBox, stateNormSq, normSq, ← pow_two, Finset.sum_add_distrib] using h

def gradientBox (B : Fin 8 → Interval) (i : Fin 8) : Interval :=
  ((B (next i)).add (B (prev i)).neg).mul (Interval.point (1/2))

theorem gradientBox_sound {B : Fin 8 → Interval} {x : Field} (hx : ∀ i, (B i).Contains (x i)) (i : Fin 8) :
    (gradientBox B i).Contains (GroundState.gradient x i) := by
  have h := Interval.mul_sound (Interval.add_sound (hx (next i)) (Interval.neg_sound (hx (prev i))))
    (Interval.point_sound (1/2))
  have he : GroundState.gradient x i = (x (next i)+-x (prev i))*(((1/2 : ℚ) : ℝ)) := by
    simp only [GroundState.gradient, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; ring
  rw [he]; exact h

def sourceBox (β : Fin 8 → ℚ) (κ : ℚ) (B : StateBox) (i : Fin 8) : Interval :=
  (Interval.point (β i)).add ((Interval.point κ).mul
    ((((gradientBox B.R i).mul (gradientBox B.R i)).add ((gradientBox B.I i).mul (gradientBox B.I i))).add
      ((Interval.point (β i)).mul (((B.R i).mul (B.R i)).add ((B.I i).mul (B.I i))))))

theorem sourceBox_sound (β : Fin 8 → ℚ) (κ : ℚ) {B : StateBox} {x : State} (hx : B.Contains x) (i : Fin 8) :
    (sourceBox β κ B i).Contains (pairSource (background β) (κ : ℝ) x i) := by
  have hr := gradientBox_sound (fun j => (hx j).1) i
  have hi := gradientBox_sound (fun j => (hx j).2) i
  have h := Interval.add_sound (Interval.point_sound (β i))
    (Interval.mul_sound (Interval.point_sound κ)
      (Interval.add_sound (Interval.add_sound (Interval.mul_sound hr hr) (Interval.mul_sound hi hi))
        (Interval.mul_sound (Interval.point_sound (β i))
          (Interval.add_sound (Interval.mul_sound (hx i).1 (hx i).1) (Interval.mul_sound (hx i).2 (hx i).2)))))
  simpa only [sourceBox, pairSource, background, pow_two] using h

def dotBox (G R : Fin 8 → Interval) : Interval := sumBox (fun i => (G i).mul (R i))

theorem dotBox_sound {G R : Fin 8 → Interval} {g u : Field}
    (hg : ∀ i, (G i).Contains (g i)) (hu : ∀ i, (R i).Contains (u i)) :
    (dotBox G R).Contains (GroundBorder.dot g u) := sumBox_sound (fun i => Interval.mul_sound (hg i) (hu i))

def overlapBox (B : StateBox) (G : Fin 8 → Interval) : Interval :=
  ((dotBox G B.R).mul (dotBox G B.R)).add ((dotBox G B.I).mul (dotBox G B.I))

theorem overlapBox_sound {b : Field} {κ : ℝ} {B : StateBox} {G : Fin 8 → Interval} {x : State}
    (hx : B.Contains x) (hg : ∀ i, (G i).Contains (selected b κ x i)) :
    (overlapBox B G).Contains (overlapSq b κ x) := by
  have hr := dotBox_sound hg (fun i => (hx i).1)
  have hi := dotBox_sound hg (fun i => (hx i).2)
  simpa only [overlapBox, overlapSq, realOverlap, imagOverlap, pow_two] using
    Interval.add_sound (Interval.mul_sound hr hr) (Interval.mul_sound hi hi)

def alignedBox (B : StateBox) (G : Fin 8 → Interval) (K : Interval) : StateBox where
  R i := (((dotBox G B.R).mul K).mul (G i))
  I i := (((dotBox G B.I).neg.mul K).mul (G i))

theorem alignedBox_sound {b : Field} {κ : ℝ} {B : StateBox} {G : Fin 8 → Interval} {K : Interval} {x : State}
    (hx : B.Contains x) (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hK : K.Contains (overlapNorm b κ x)⁻¹) : (alignedBox B G K).Contains (aligned b κ x) := by
  have hr := dotBox_sound hg (fun i => (hx i).1)
  have hi := dotBox_sound hg (fun i => (hx i).2)
  intro i
  constructor
  · simpa only [alignedBox, aligned, realOverlap, div_eq_mul_inv] using
      Interval.mul_sound (Interval.mul_sound hr hK) (hg i)
  · simpa only [alignedBox, aligned, imagOverlap, div_eq_mul_inv] using
      Interval.mul_sound (Interval.mul_sound (Interval.neg_sound hi) hK) (hg i)

def mixedBox (B : StateBox) (G : Fin 8 → Interval) (K : Interval) : StateBox where
  R i := ((Interval.point (1/2)).mul (B.R i)).add ((Interval.point (1/2)).mul ((alignedBox B G K).R i))
  I i := ((Interval.point (1/2)).mul (B.I i)).add ((Interval.point (1/2)).mul ((alignedBox B G K).I i))

theorem mixedBox_sound {b : Field} {κ : ℝ} {B : StateBox} {G : Fin 8 → Interval} {K : Interval} {x : State}
    (hx : B.Contains x) (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hK : K.Contains (overlapNorm b κ x)⁻¹) : (mixedBox B G K).Contains (mixed b κ (1/2) x) := by
  have ha := alignedBox_sound hx hg hK
  intro i
  have hr := Interval.add_sound (Interval.mul_sound (Interval.point_sound (1/2)) (hx i).1)
    (Interval.mul_sound (Interval.point_sound (1/2)) (ha i).1)
  have hi := Interval.add_sound (Interval.mul_sound (Interval.point_sound (1/2)) (hx i).2)
    (Interval.mul_sound (Interval.point_sound (1/2)) (ha i).2)
  have he : (1 : ℝ)-1/2 = 1/2 := by norm_num
  simpa only [StateBox.Contains, mixedBox, mixed, he, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using And.intro hr hi

def normalizedBox (B : StateBox) (K : Interval) : StateBox where
  R i := K.mul (B.R i)
  I i := K.mul (B.I i)

theorem normalizedBox_sound {B : StateBox} {K : Interval} {x : State}
    (hx : B.Contains x) (hK : K.Contains (Real.sqrt (stateNormSq x))⁻¹) :
    (normalizedBox B K).Contains (normalizeState x) := by
  intro i
  exact ⟨Interval.mul_sound hK (hx i).1, Interval.mul_sound hK (hx i).2⟩

structure Arithmetic (β : Fin 8 → ℚ) (κ τ : ℚ) (B D : StateBox) (z : Fin 9 → ℚ)
    (r q y : ℚ) (C : Matrix (Fin 9) (Fin 9) ℚ) (K L : Interval) : Prop where
  ground : GroundBackgroundKernel.Arithmetic (sourceBox β κ B) z r q y C
  overlap_inverse : GroundIntervalReciprocal.Arithmetic (overlapBox B (GroundBackgroundKernel.fieldBox z r)) K
  mixed_inverse : GroundIntervalReciprocal.Arithmetic
    (normBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K)) L
  threshold_nonneg : 0 ≤ τ
  phase_margin : τ^2 < (overlapBox B (GroundBackgroundKernel.fieldBox z r)).lo
  normalization_margin : τ^2 < (normBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K)).lo
  output : (normalizedBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K) L).Included D

theorem arithmetic_native_step {β : Fin 8 → ℚ} {κ τ : ℚ} {B D : StateBox} {z : Fin 9 → ℚ}
    {r q y : ℚ} {C : Matrix (Fin 9) (Fin 9) ℚ} {K L : Interval}
    (h : Arithmetic β κ τ B D z r q y C K L) {x : State} (hx : B.Contains x) :
    ActivePhase (τ : ℝ) (background β) (κ : ℝ) (pack x) ∧
    NativeLegal (τ : ℝ) (background β) (κ : ℝ) (1/2) (pack x) ∧
    D.Contains (unpack (nativeUpdate (τ : ℝ) (background β) (κ : ℝ) (1/2) (pack x))) := by
  have hs := sourceBox_sound β κ hx
  have hg := GroundBackgroundKernel.actual_selected_enclosed h.ground hs
  have hr := overlapBox_sound hx hg
  have hk := (inverse_sqrt_sound h.overlap_inverse hr).2
  have hτ : (0 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast h.threshold_nonneg
  have hb : (τ : ℝ)^2 < ((overlapBox B (GroundBackgroundKernel.fieldBox z r)).lo : ℝ) := by
    exact_mod_cast h.phase_margin
  have ho : (τ : ℝ) < overlapNorm (background β) (κ : ℝ) x := threshold_guard hr hτ hb
  have hm := mixedBox_sound hx hg hk
  have hn := normBox_sound hm
  have hl := (inverse_sqrt_sound h.mixed_inverse hn).2
  have hnb : (τ : ℝ)^2 < ((normBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K)).lo : ℝ) := by
    exact_mod_cast h.normalization_margin
  have hnorm := threshold_guard hn hτ hnb
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using ho
  · rw [NativeLegal, ← pack_mixed_native hτ (background β) (κ : ℝ) (1/2) x ho, norm_pack]
    exact hnorm
  · rw [← fullMap_native_return hτ (background β) (κ : ℝ) (1/2) x ho]
    exact StateBox.included_sound h.output (normalizedBox_sound hm hl)

end
end SbtCosmo.Derivation.GroundNativeBox
