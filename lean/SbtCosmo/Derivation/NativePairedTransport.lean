import SbtCosmo.Derivation.GroundCertifiedNativeTransportStep
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
namespace StateBoxComposition
noncomputable section
open SbtCosmo.Derivation
open GroundState GroundNativePhase GroundRationalInterval GroundNativeBox
open GroundUncertainNativeBasin.Certificate
open scoped BigOperators

abbrev MatrixBox := Fin 16 → StateBox

def Contains (A : MatrixBox) (L : State →L[ℝ] State) : Prop :=
  ∀ j, (A j).Contains (L (column j))

def applyBox (A : MatrixBox) (H : StateBox) : StateBox where
  R i := (sumBox (fun j : Fin 8 => ((A (j.castAdd 8)).R i).mul (H.R j))).add
    (sumBox (fun j : Fin 8 => ((A (Fin.natAdd 8 j)).R i).mul (H.I j)))
  I i := (sumBox (fun j : Fin 8 => ((A (j.castAdd 8)).I i).mul (H.R j))).add
    (sumBox (fun j : Fin 8 => ((A (Fin.natAdd 8 j)).I i).mul (H.I j)))

theorem applyBox_sound {A : MatrixBox} {L : State →L[ℝ] State} (hA : Contains A L)
    {H : StateBox} {x : State} (hx : H.Contains x) : (applyBox A H).Contains (L x) := by
  intro i
  constructor
  · rw [GroundStateRows.real_action_entries]
    have hR (j : Fin 8) := (hA (j.castAdd 8) i).1
    have hI (j : Fin 8) := (hA (Fin.natAdd 8 j) i).1
    simp only [column_real] at hR
    simp only [column_imag] at hI
    exact Interval.add_sound (sumBox_sound (fun j => Interval.mul_sound (hR j) (hx j).1))
      (sumBox_sound (fun j => Interval.mul_sound (hI j) (hx j).2))
  · rw [GroundStateRows.imag_action_entries]
    have hR (j : Fin 8) := (hA (j.castAdd 8) i).2
    have hI (j : Fin 8) := (hA (Fin.natAdd 8 j) i).2
    simp only [column_real] at hR
    simp only [column_imag] at hI
    exact Interval.add_sound (sumBox_sound (fun j => Interval.mul_sound (hR j) (hx j).1))
      (sumBox_sound (fun j => Interval.mul_sound (hI j) (hx j).2))

def compose (A B : MatrixBox) : MatrixBox := fun j => applyBox A (B j)

theorem compose_sound {A B : MatrixBox} {L M : State →L[ℝ] State}
    (hA : Contains A L) (hB : Contains B M) : Contains (compose A B) (L.comp M) := by
  intro j
  exact applyBox_sound hA (hB j)

def Included (A B : MatrixBox) : Prop := ∀ j, (A j).Included (B j)

theorem included_sound {A B : MatrixBox} {L : State →L[ℝ] State}
    (h : Included A B) (hA : Contains A L) : Contains B L :=
  fun j => StateBox.included_sound (h j) (hA j)

def identityBox : MatrixBox := fun j =>
  ⟨fun i => Interval.point (if j = i.castAdd 8 then 1 else 0),
   fun i => Interval.point (if j = Fin.natAdd 8 i then 1 else 0)⟩

theorem identity_sound : Contains identityBox (ContinuousLinearMap.id ℝ State) := by
  intro j
  by_cases h : j.val < 8
  · let k : Fin 8 := ⟨j.val,h⟩
    have hj : j = k.castAdd 8 := by apply Fin.ext;rfl
    rw [hj,column_real]
    intro i
    simp only [ContinuousLinearMap.id_apply,identityBox,GroundLocalDynamics.column,Pi.single_apply]
    constructor
    · by_cases hi : i = k
      · simpa [hi,Fin.castAdd] using Interval.point_sound (1 : ℚ)
      · simpa [hi,Ne.symm hi,Fin.castAdd] using Interval.point_sound (0 : ℚ)
    · simpa [Fin.natAdd,Fin.ext_iff,Pi.zero_apply,k.isLt,show ¬ k.val = 8+i.val by omega] using Interval.point_sound 0
  · let k : Fin 8 := ⟨j.val-8,by omega⟩
    have hj : j = Fin.natAdd 8 k := by apply Fin.ext;dsimp [k];omega
    rw [hj,column_imag]
    intro i
    simp only [ContinuousLinearMap.id_apply,identityBox,GroundLocalDynamics.column,Pi.single_apply]
    constructor
    · simpa [Fin.castAdd,Fin.natAdd,Fin.ext_iff,Pi.zero_apply,i.isLt,show ¬ 8+k.val = i.val by omega] using Interval.point_sound 0
    · by_cases hi : i = k
      · simpa [hi,Fin.natAdd,Fin.ext_iff] using Interval.point_sound (1 : ℚ)
      · have hv : i.val ≠ k.val := by intro hv;exact hi (Fin.ext hv)
        simpa [Fin.natAdd,Fin.ext_iff,hi,hv,Ne.symm hv] using Interval.point_sound (0 : ℚ)

/-- The derivative product uses the actual orbit points, not a product frozen
at the reference center. -/
def derivativePower (f : State → State) (D : State → State →L[ℝ] State) : ℕ → State → State →L[ℝ] State
  | 0, _ => ContinuousLinearMap.id ℝ State
  | n+1, x => (D ((f^[n]) x)).comp (derivativePower f D n x)

theorem derivativePower_return (f : State → State) (D : State → State →L[ℝ] State)
    (N : ℕ) (x : State) (hD : ∀ j : Fin N, HasFDerivAt f (D ((f^[j.val]) x)) ((f^[j.val]) x)) :
    HasFDerivAt (f^[N]) (derivativePower f D N x) x := by
  induction N with
  | zero => simpa only [Function.iterate_zero,derivativePower] using hasFDerivAt_id x
  | succ n ih =>
    have hp := ih (fun j => hD ⟨j.val,by omega⟩)
    have hl := hD ⟨n,by omega⟩
    simpa only [Function.iterate_succ',derivativePower] using hl.comp x hp

theorem derivativePower_enclosed (f : State → State) (D : State → State →L[ℝ] State)
    (N : ℕ) (x : State) (steps : Fin N → MatrixBox) (products : Fin (N+1) → MatrixBox)
    (hzero : Included identityBox (products 0))
    (hsteps : ∀ j : Fin N, Contains (steps j) (D ((f^[j.val]) x)))
    (hproducts : ∀ j : Fin N, Included (compose (steps j) (products j.castSucc)) (products j.succ)) :
    Contains (products (Fin.last N)) (derivativePower f D N x) := by
  have hall (j : Fin (N+1)) : Contains (products j) (derivativePower f D j.val x) := by
    refine Fin.induction ?_ (fun i ih => ?_) j
    · exact included_sound hzero identity_sound
    · exact included_sound (hproducts i) (compose_sound (hsteps i) ih)
  exact hall (Fin.last N)
open GroundMatrixCoordinates

def frame {S P R Q : QMatrix} (hS : InverseArithmetic S P) (hR : InverseArithmetic R Q) :
    State ≃L[ℝ] State := (basis hS).prodCongr (basis hR)

def coordinateBox (P Q : QMatrix) (B : StateBox) : StateBox where
  R i := sumBox (fun j => (Interval.point (P i j)).mul (B.R j))
  I i := sumBox (fun j => (Interval.point (Q i j)).mul (B.I j))

theorem coordinateBox_sound {S P R Q : QMatrix} (hS : InverseArithmetic S P) (hR : InverseArithmetic R Q)
    {B : StateBox} {x : State} (hx : B.Contains x) :
    (coordinateBox P Q B).Contains ((frame hS hR).symm x) := by
  intro i
  constructor
  · change (sumBox (fun j => (Interval.point (P i j)).mul (B.R j))).Contains ((basis hS).symm x.1 i)
    rw [basis_symm_apply]
    exact sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound _) (hx j).1)
  · change (sumBox (fun j => (Interval.point (Q i j)).mul (B.I j))).Contains ((basis hR).symm x.2 i)
    rw [basis_symm_apply]
    exact sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound _) (hx j).2)

def directionBox (S R : QMatrix) (j : Fin 16) : StateBox where
  R i := Interval.point (if h : j.val < 8 then S i ⟨j.val,h⟩ else 0)
  I i := Interval.point (if h : j.val < 8 then 0 else R i ⟨j.val-8,by omega⟩)

theorem directionBox_sound {S P R Q : QMatrix} (hS : InverseArithmetic S P) (hR : InverseArithmetic R Q)
    (j : Fin 16) : (directionBox S R j).Contains (frame hS hR (column j)) := by
  intro i
  by_cases h : j.val < 8
  · constructor
    · change (Interval.point (if hj : j.val < 8 then S i ⟨j.val,hj⟩ else 0)).Contains
        ((basis hS) (column j).1 i)
      simp only [h,dite_true,column]
      rw [basis_apply]
      simpa [GroundLocalDynamics.column,Pi.single_apply] using Interval.point_sound (S i ⟨j.val,h⟩)
    · change (Interval.point (if hj : j.val < 8 then 0 else R i ⟨j.val-8,by omega⟩)).Contains
        ((basis hR) (column j).2 i)
      simp only [h,dite_true,column,map_zero,Pi.zero_apply]
      simpa only [Rat.cast_zero] using Interval.point_sound 0
  · constructor
    · change (Interval.point (if hj : j.val < 8 then S i ⟨j.val,hj⟩ else 0)).Contains
        ((basis hS) (column j).1 i)
      simp only [h,dite_false,column,map_zero,Pi.zero_apply]
      simpa only [Rat.cast_zero] using Interval.point_sound 0
    · change (Interval.point (if hj : j.val < 8 then 0 else R i ⟨j.val-8,by omega⟩)).Contains
        ((basis hR) (column j).2 i)
      simp only [h,dite_false,column]
      rw [basis_apply]
      simpa [GroundLocalDynamics.column,Pi.single_apply] using Interval.point_sound (R i ⟨j.val-8,by omega⟩)

def conjugate (T : State ≃L[ℝ] State) (L : State →L[ℝ] State) : State →L[ℝ] State :=
  T.symm.toContinuousLinearMap.comp (L.comp T.toContinuousLinearMap)

/-- Separate cached left/right multiplications retain both cross blocks and
all rounding inclusions before the operator-norm bound is read out. -/
theorem conjugate_enclosed {S P R Q : QMatrix} (hS : InverseArithmetic S P) (hR : InverseArithmetic R Q)
    {A leftCache finalCache : MatrixBox} {L : State →L[ℝ] State}
    (hA : Contains A L)
    (hleft : Included (fun j => coordinateBox P Q (A j)) leftCache)
    (hright : Included (fun j => applyBox leftCache (directionBox S R j)) finalCache) :
    Contains finalCache (conjugate (frame hS hR) L) := by
  have hl : Contains leftCache ((frame hS hR).symm.toContinuousLinearMap.comp L) :=
    included_sound hleft (fun j => coordinateBox_sound hS hR (hA j))
  intro j
  exact StateBox.included_sound (hright j) (applyBox_sound hl (directionBox_sound hS hR j))

theorem norm_le_rows {A : MatrixBox} {L : State →L[ℝ] State} (hA : Contains A L)
    {q : ℚ} (hq : 0 ≤ q)
    (hR : ∀ i : Fin 8, (∑ j : Fin 8, (((A (j.castAdd 8)).R i).bound+
      ((A (Fin.natAdd 8 j)).R i).bound)) ≤ q)
    (hI : ∀ i : Fin 8, (∑ j : Fin 8, (((A (j.castAdd 8)).I i).bound+
      ((A (Fin.natAdd 8 j)).I i).bound)) ≤ q) : ‖L‖ ≤ (q : ℝ) := by
  have hreal (j : Fin 8) := hA (j.castAdd 8)
  have himag (j : Fin 8) := hA (Fin.natAdd 8 j)
  simp only [column_real] at hreal
  simp only [column_imag] at himag
  apply GroundStateRows.operator_norm_le_rows _ (by exact_mod_cast hq)
  · intro i
    calc
      _ ≤ ∑ j : Fin 8, ((((A (j.castAdd 8)).R i).bound : ℝ)+(((A (Fin.natAdd 8 j)).R i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((hreal j) i).1) (Interval.abs_le_bound ((himag j) i).1)
      _ ≤ (q : ℝ) := by exact_mod_cast hR i
  · intro i
    calc
      _ ≤ ∑ j : Fin 8, ((((A (j.castAdd 8)).I i).bound : ℝ)+(((A (Fin.natAdd 8 j)).I i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((hreal j) i).2) (Interval.abs_le_bound ((himag j) i).2)
      _ ≤ (q : ℝ) := by exact_mod_cast hI i
end
end StateBoxComposition
namespace NativeTransportPowers
noncomputable section
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundNativeQuantitativeBall Metric StateBoxComposition
open scoped BigOperators

variable {β : Fin 8 → GroundRationalInterval.Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State}

theorem native_derivative (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall d.center (d.radius : ℝ)) :
    HasFDerivAt (Data.f (T := T) (κ := κ) (τ := τ) b)
      (derivative T b (κ : ℝ) (1/2) x) x := by
  have hg := d.pair_guards hb hx
  exact coordinate_hasFDerivAt T b (κ : ℝ) (1/2) (τ : ℝ) x
    (by exact_mod_cast d.pointStep.proof.threshold_nonneg) hg.1 hg.2

theorem native_matrix (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall d.center (d.radius : ℝ)) :
    Contains d.jet.derivativeBox (derivative T b (κ : ℝ) (1/2) x) := by
  intro j
  have h := d.jet.actual_jet_enclosed d.responses d.response_included d.derivative_included
    (by simpa only [d.inputs] using hb) (d.input_on_ball hx) j
  rw [d.frame,d.coupling] at h
  exact h

theorem advance_smaller (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {E nextE : ℚ}
    (hE : 0 ≤ E) (hER : E ≤ d.radius)
    (hbudget : d.jet.rate*E+d.defect ≤ nextE) {x : State}
    (hx : x ∈ closedBall d.center (E : ℝ)) :
    Data.f (T := T) (κ := κ) (τ := τ) b x ∈ closedBall d.nextCenter (nextE : ℝ) := by
  apply GroundFiniteNativeTransport.step _ (by exact_mod_cast hE)
    ((d.lipschitz hb).mono (closedBall_subset_closedBall (Rat.cast_le.mpr hER)))
    (d.center_defect hb) ?_ hx
  change (d.jet.rate : ℝ)*(E : ℝ)+(d.defect : ℝ) ≤ (nextE : ℝ)
  exact_mod_cast hbudget

theorem next_on_ball (d₀ d₁ : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i))
    (hseam : d₀.nextCenter = d₁.center) (hR : d₀.next_radius ≤ d₁.radius)
    {x : State} (hx : x ∈ closedBall d₀.center (d₀.radius : ℝ)) :
    Data.f (T := T) (κ := κ) (τ := τ) b x ∈ closedBall d₁.center (d₁.radius : ℝ) := by
  have h := d₀.advance hb hx
  rw [hseam] at h
  exact closedBall_subset_closedBall (Rat.cast_le.mpr hR) h

/-- All intermediate jets are evaluated at the actual first iterate.
A two-step rate above one is allowed. -/
theorem pair_lipschitz (d₀ d₁ : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i))
    (hseam : d₀.nextCenter = d₁.center) (hR : d₀.next_radius ≤ d₁.radius)
    {A₀ A₁ B : MatrixBox} {q : ℚ} (hq : 0 ≤ q)
    (hA₀ : Included d₀.jet.derivativeBox A₀) (hA₁ : Included d₁.jet.derivativeBox A₁)
    (hB : Included (compose A₁ A₀) B)
    (hrowsR : ∀ i : Fin 8, (∑ j : Fin 8, (((B (j.castAdd 8)).R i).bound+
      ((B (Fin.natAdd 8 j)).R i).bound)) ≤ q)
    (hrowsI : ∀ i : Fin 8, (∑ j : Fin 8, (((B (j.castAdd 8)).I i).bound+
      ((B (Fin.natAdd 8 j)).I i).bound)) ≤ q) :
    LipschitzOnWith (⟨(q : ℝ),by exact_mod_cast hq⟩ : NNReal)
      ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) (closedBall d₀.center (d₀.radius : ℝ)) := by
  let f := Data.f (T := T) (κ := κ) (τ := τ) b
  let D := derivative T b (κ : ℝ) (1/2)
  have hjet (x : State) (hx : x ∈ closedBall d₀.center (d₀.radius : ℝ)) :
      Contains B ((D (f x)).comp (D x)) := by
    have hi := next_on_ball d₀ d₁ hb hseam hR hx
    exact included_sound hB (compose_sound
      (included_sound hA₁ (native_matrix d₁ hb hi)) (included_sound hA₀ (native_matrix d₀ hb hx)))
  have hdiff (x : State) (hx : x ∈ closedBall d₀.center (d₀.radius : ℝ)) :
      HasFDerivAt (f^[2]) ((D (f x)).comp (D x)) x := by
    have hi := next_on_ball d₀ d₁ hb hseam hR hx
    have h := (native_derivative d₁ hb hi).comp x (native_derivative d₀ hb hx)
    simpa only [Function.iterate_succ',Function.iterate_zero,Function.comp_id] using h
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hdiff x hx).hasFDerivWithinAt)
    (fun x hx => ?_) (convex_closedBall d₀.center (d₀.radius : ℝ))
  exact_mod_cast norm_le_rows (hjet x hx) hq hrowsR hrowsI

/-- This center bound uses the independently earned point defects. -/
theorem pair_center_defect (d₀ d₁ : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (hseam : d₀.nextCenter = d₁.center)
    (hsmall : d₀.defect ≤ d₁.radius) {d : ℚ}
    (hbudget : d₁.jet.rate*d₀.defect+d₁.defect ≤ d) :
    dist (((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) d₀.center) d₁.nextCenter ≤ (d : ℝ) := by
  have hx : Data.f (T := T) (κ := κ) (τ := τ) b d₀.center ∈
      closedBall d₁.center (d₀.defect : ℝ) := by
    rw [mem_closedBall,← hseam]
    exact d₀.center_defect hb
  have hn := advance_smaller d₁ hb d₀.defect_nonneg hsmall hbudget hx
  simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using mem_closedBall.mp hn

/-- The endpoint radius comes from the earned two-step derivative product;
it need not equal the looser product of the one-step norm bounds. -/
theorem pair_advance (d₀ d₁ : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (hseam : d₀.nextCenter = d₁.center)
    (hsmall : d₀.defect ≤ d₁.radius) {d nextR : ℚ} {q : NNReal}
    (hdefect : d₁.jet.rate*d₀.defect+d₁.defect ≤ d)
    (hL : LipschitzOnWith q ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2])
      (closedBall d₀.center (d₀.radius : ℝ)))
    (hbudget : (q : ℝ)*(d₀.radius : ℝ)+(d : ℝ) ≤ (nextR : ℝ)) {x : State}
    (hx : x ∈ closedBall d₀.center (d₀.radius : ℝ)) :
    ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) x ∈ closedBall d₁.nextCenter (nextR : ℝ) :=
  GroundFiniteNativeTransport.step _ (by exact_mod_cast d₀.radius_nonneg) hL
    (pair_center_defect d₀ d₁ hb hseam hsmall hdefect) hbudget hx
end
end NativeTransportPowers
