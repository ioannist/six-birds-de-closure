import SbtCosmo.Derivation.GroundNativeGeneralDerivative
import SbtCosmo.Derivation.GroundBackgroundResponse

/-! Whole-state-box interval enclosures for the actual sixteen-coordinate native
update derivative. Selector response error is retained before phase and final
normalization differentiation. -/
namespace SbtCosmo.Derivation.GroundNativeDerivativeBox
noncomputable section
set_option maxHeartbeats 3000000
open GroundState GroundBorder GroundSourceJacobian GroundNativePhase GroundNativeDerivative
open GroundNativeIteration GroundRationalInterval GroundNativeBox GroundKernelTube
open scoped BigOperators

def sourceDerivativeBox (β : Fin 8 → ℚ) (κ : ℚ) (B H : StateBox) (i : Fin 8) : Interval :=
  (Interval.point (2*κ)).mul
    ((((gradientBox B.R i).mul (gradientBox H.R i)).add
      (((Interval.point (β i)).mul (B.R i)).mul (H.R i))).add
     (((gradientBox B.I i).mul (gradientBox H.I i)).add
      (((Interval.point (β i)).mul (B.I i)).mul (H.I i))))

theorem sourceDerivativeBox_sound (β : Fin 8 → ℚ) (κ : ℚ) {B H : StateBox} {x h : State}
    (hx : B.Contains x) (hh : H.Contains h) (i : Fin 8) :
    (sourceDerivativeBox β κ B H i).Contains (pairSourceDerivative (background β) (κ : ℝ) x h i) := by
  have hdR := Interval.add_sound
    (Interval.mul_sound (gradientBox_sound (fun j => (hx j).1) i) (gradientBox_sound (fun j => (hh j).1) i))
    (Interval.mul_sound (Interval.mul_sound (Interval.point_sound (β i)) (hx i).1) (hh i).1)
  have hdI := Interval.add_sound
    (Interval.mul_sound (gradientBox_sound (fun j => (hx j).2) i) (gradientBox_sound (fun j => (hh j).2) i))
    (Interval.mul_sound (Interval.mul_sound (Interval.point_sound (β i)) (hx i).2) (hh i).2)
  have hv := Interval.mul_sound (Interval.point_sound (2*κ)) (Interval.add_sound hdR hdI)
  have he : pairSourceDerivative (background β) (κ : ℝ) x h i =
      ((2*κ : ℚ) : ℝ) *
        (GroundState.gradient x.1 i*GroundState.gradient h.1 i+(β i : ℝ)*x.1 i*h.1 i+
         (GroundState.gradient x.2 i*GroundState.gradient h.2 i+(β i : ℝ)*x.2 i*h.2 i)) := by
    simp [pairSourceDerivative, sourceDerivative_apply, background]
    ring
  rw [he]
  exact hv

theorem selectedDerivative_enclosed {β : Fin 8 → ℚ} {κ : ℚ} {B H : StateBox} {z : Fin 9 → ℚ}
    {r q a y e : ℚ} {C : Matrix (Fin 9) (Fin 9) ℚ}
    (hg : GroundBackgroundKernel.Arithmetic (sourceBox β κ B) z r q a C)
    (hr : GroundBackgroundResponse.ResponseArithmetic C (GroundBackgroundKernel.fieldBox z r)
      (sourceDerivativeBox β κ B H) q y e) {x h : State} (hx : B.Contains x) (hh : H.Contains h) (i : Fin 8) :
    (GroundBackgroundResponse.responseInterval C (GroundBackgroundKernel.fieldBox z r)
      (sourceDerivativeBox β κ B H) e i).Contains (selectedDerivative (background β) (κ : ℝ) x h i) :=
  GroundBackgroundResponse.actual_selector_response_enclosed hg hr (sourceBox_sound β κ hx)
    (sourceDerivativeBox_sound β κ hx hh) i

def realOverlapDerivativeBox (B H : StateBox) (G D : Fin 8 → Interval) : Interval :=
  (dotBox B.R D).add (dotBox G H.R)
def imagOverlapDerivativeBox (B H : StateBox) (G D : Fin 8 → Interval) : Interval :=
  (dotBox B.I D).add (dotBox G H.I)

theorem realOverlapDerivativeBox_sound {b : Field} {κ : ℝ} {B H : StateBox}
    {G D : Fin 8 → Interval} {x h : State} (hx : B.Contains x) (hh : H.Contains h)
    (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hd : ∀ i, (D i).Contains (selectedDerivative b κ x h i)) :
    (realOverlapDerivativeBox B H G D).Contains (GroundNativeGeneralDerivative.realOverlapDerivative b κ x h) := by
  have ha := Interval.add_sound (dotBox_sound (fun i => (hx i).1) hd) (dotBox_sound hg (fun i => (hh i).1))
  rw [GroundNativeGeneralDerivative.realOverlapDerivative_apply]
  simpa only [realOverlapDerivativeBox] using ha

theorem imagOverlapDerivativeBox_sound {b : Field} {κ : ℝ} {B H : StateBox}
    {G D : Fin 8 → Interval} {x h : State} (hx : B.Contains x) (hh : H.Contains h)
    (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hd : ∀ i, (D i).Contains (selectedDerivative b κ x h i)) :
    (imagOverlapDerivativeBox B H G D).Contains (GroundNativeGeneralDerivative.imagOverlapDerivative b κ x h) := by
  have ha := Interval.add_sound (dotBox_sound (fun i => (hx i).2) hd) (dotBox_sound hg (fun i => (hh i).2))
  rw [GroundNativeGeneralDerivative.imagOverlapDerivative_apply]
  simpa only [imagOverlapDerivativeBox] using ha

def negativeCube (K : Interval) : Interval := ((K.mul K).mul K).neg

theorem negativeCube_sound {K : Interval} {k : ℝ} (hk : K.Contains k) : (negativeCube K).Contains (-k^3) := by
  simpa only [negativeCube, pow_succ, pow_zero, mul_one, one_mul] using
    Interval.neg_sound (Interval.mul_sound (Interval.mul_sound hk hk) hk)

def overlapInverseDerivativeBox (B H : StateBox) (G D : Fin 8 → Interval) (K : Interval) : Interval :=
  (negativeCube K).mul
    (((dotBox G B.R).mul (realOverlapDerivativeBox B H G D)).add
      ((dotBox G B.I).mul (imagOverlapDerivativeBox B H G D)))

theorem overlapInverseDerivativeBox_sound {b : Field} {κ : ℝ} {B H : StateBox}
    {G D : Fin 8 → Interval} {K : Interval} {x h : State} (hx : B.Contains x) (hh : H.Contains h)
    (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hd : ∀ i, (D i).Contains (selectedDerivative b κ x h i))
    (hk : K.Contains (overlapNorm b κ x)⁻¹) :
    (overlapInverseDerivativeBox B H G D K).Contains (GroundNativeGeneralDerivative.overlapInverseDerivative b κ x h) := by
  rw [GroundNativeGeneralDerivative.overlapInverseDerivative_apply]
  exact Interval.mul_sound (negativeCube_sound hk)
    (Interval.add_sound
      (Interval.mul_sound (dotBox_sound hg (fun i => (hx i).1)) (realOverlapDerivativeBox_sound hx hh hg hd))
      (Interval.mul_sound (dotBox_sound hg (fun i => (hx i).2)) (imagOverlapDerivativeBox_sound hx hh hg hd)))

def alignedDerivativeBox (B H : StateBox) (G D : Fin 8 → Interval) (K : Interval) : StateBox where
  R i := ((((realOverlapDerivativeBox B H G D).mul K).add
    ((dotBox G B.R).mul (overlapInverseDerivativeBox B H G D K))).mul (G i)).add
      (((dotBox G B.R).mul K).mul (D i))
  I i := ((((imagOverlapDerivativeBox B H G D).neg.mul K).add
    ((dotBox G B.I).neg.mul (overlapInverseDerivativeBox B H G D K))).mul (G i)).add
      (((dotBox G B.I).neg.mul K).mul (D i))

theorem alignedDerivativeBox_sound {b : Field} {κ : ℝ} {B H : StateBox}
    {G D : Fin 8 → Interval} {K : Interval} {x h : State} (hx : B.Contains x) (hh : H.Contains h)
    (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hd : ∀ i, (D i).Contains (selectedDerivative b κ x h i))
    (hk : K.Contains (overlapNorm b κ x)⁻¹) :
    (alignedDerivativeBox B H G D K).Contains (GroundNativeGeneralDerivative.alignedDerivative b κ x h) := by
  have ha := dotBox_sound hg (fun i => (hx i).1)
  have hb := dotBox_sound hg (fun i => (hx i).2)
  have hda := realOverlapDerivativeBox_sound hx hh hg hd
  have hdb := imagOverlapDerivativeBox_sound hx hh hg hd
  have hdk := overlapInverseDerivativeBox_sound hx hh hg hd hk
  intro i
  constructor
  · have hv := Interval.add_sound
      (Interval.mul_sound (Interval.add_sound (Interval.mul_sound hda hk) (Interval.mul_sound ha hdk)) (hg i))
      (Interval.mul_sound (Interval.mul_sound ha hk) (hd i))
    simpa only [alignedDerivativeBox, GroundNativeGeneralDerivative.alignedDerivative_real_apply,
      realOverlap] using hv
  · have hv := Interval.add_sound
      (Interval.mul_sound (Interval.add_sound (Interval.mul_sound (Interval.neg_sound hdb) hk)
        (Interval.mul_sound (Interval.neg_sound hb) hdk)) (hg i))
      (Interval.mul_sound (Interval.mul_sound (Interval.neg_sound hb) hk) (hd i))
    simpa only [alignedDerivativeBox, GroundNativeGeneralDerivative.alignedDerivative_imag_apply,
      imagOverlap, sub_eq_add_neg, neg_mul] using hv


def mixedDerivativeBox (B H : StateBox) (G D : Fin 8 → Interval) (K : Interval) : StateBox :=
  ⟨fun i => ((Interval.point (1/2)).mul (H.R i)).add
      ((Interval.point (1/2)).mul ((alignedDerivativeBox B H G D K).R i)),
   fun i => ((Interval.point (1/2)).mul (H.I i)).add
      ((Interval.point (1/2)).mul ((alignedDerivativeBox B H G D K).I i))⟩


theorem mixedDerivativeBox_sound {b : Field} {κ : ℝ} {B H : StateBox}
    {G D : Fin 8 → Interval} {K : Interval} {x h : State} (hx : B.Contains x) (hh : H.Contains h)
    (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hd : ∀ i, (D i).Contains (selectedDerivative b κ x h i))
    (hk : K.Contains (overlapNorm b κ x)⁻¹) :
    (mixedDerivativeBox B H G D K).Contains (GroundNativeGeneralDerivative.mixedDerivative b κ (1/2) x h) := by
  have ha := alignedDerivativeBox_sound hx hh hg hd hk
  intro i
  have hr := Interval.add_sound (Interval.mul_sound (Interval.point_sound (1/2)) (hh i).1)
    (Interval.mul_sound (Interval.point_sound (1/2)) (ha i).1)
  have hi := Interval.add_sound (Interval.mul_sound (Interval.point_sound (1/2)) (hh i).2)
    (Interval.mul_sound (Interval.point_sound (1/2)) (ha i).2)
  have he : (1 : ℝ)-1/2 = 1/2 := by norm_num
  simpa only [mixedDerivativeBox, GroundNativeGeneralDerivative.mixedDerivative, he,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using And.intro hr hi

def normalizationInverseDerivativeBox (B H : StateBox) (L : Interval) : Interval :=
  (negativeCube L).mul ((dotBox B.R H.R).add (dotBox B.I H.I))

def normalizedDerivativeBox (B H : StateBox) (L : Interval) : StateBox where
  R i := (L.mul (H.R i)).add ((normalizationInverseDerivativeBox B H L).mul (B.R i))
  I i := (L.mul (H.I i)).add ((normalizationInverseDerivativeBox B H L).mul (B.I i))

theorem normalizedDerivativeBox_sound {B H : StateBox} {L : Interval} {x h : State}
    (hx : B.Contains x) (hh : H.Contains h) (hL : L.Contains (Real.sqrt (stateNormSq x))⁻¹) :
    (normalizedDerivativeBox B H L).Contains (GroundNativeGeneralDerivative.normalizationDerivative x h) := by
  have hdot := Interval.add_sound (dotBox_sound (fun i => (hx i).1) (fun i => (hh i).1))
    (dotBox_sound (fun i => (hx i).2) (fun i => (hh i).2))
  have hdl := Interval.mul_sound (negativeCube_sound hL) hdot
  rw [GroundNativeGeneralDerivative.normalizationDerivative_apply]
  intro i
  have hr := Interval.add_sound (Interval.mul_sound hL (hh i).1) (Interval.mul_sound hdl (hx i).1)
  have hi := Interval.add_sound (Interval.mul_sound hL (hh i).2) (Interval.mul_sound hdl (hx i).2)
  simpa only [normalizedDerivativeBox, normalizationInverseDerivativeBox, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using And.intro hr hi

def fullDerivativeBox (B H : StateBox) (G D : Fin 8 → Interval) (K L : Interval) : StateBox :=
  normalizedDerivativeBox (mixedBox B G K) (mixedDerivativeBox B H G D K) L

theorem fullDerivativeBox_sound {b : Field} {κ : ℝ} {B H : StateBox}
    {G D : Fin 8 → Interval} {K L : Interval} {x h : State} (hx : B.Contains x) (hh : H.Contains h)
    (hg : ∀ i, (G i).Contains (selected b κ x i))
    (hd : ∀ i, (D i).Contains (selectedDerivative b κ x h i))
    (hk : K.Contains (overlapNorm b κ x)⁻¹)
    (hl : L.Contains (Real.sqrt (stateNormSq (mixed b κ (1/2) x)))⁻¹) :
    (fullDerivativeBox B H G D K L).Contains (GroundNativeGeneralDerivative.fullDerivative b κ (1/2) x h) :=
  normalizedDerivativeBox_sound (mixedBox_sound hx hg hk) (mixedDerivativeBox_sound hx hh hg hd hk) hl


end
end SbtCosmo.Derivation.GroundNativeDerivativeBox
