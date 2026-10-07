import SbtCosmo.Derivation.GroundOffsets.Point000
import SbtCosmo.Derivation.GroundOffsets.Point001
import SbtCosmo.Derivation.GroundOffsets.Point002
import SbtCosmo.Derivation.GroundOffsets.Point003
import SbtCosmo.Derivation.GroundOffsets.Point004
import SbtCosmo.Derivation.GroundOffsets.Point005
import SbtCosmo.Derivation.GroundOffsets.Point006
import SbtCosmo.Derivation.GroundOffsets.Point007
import SbtCosmo.Derivation.GroundOffsets.Point008
import SbtCosmo.Derivation.GroundOffsets.Point009
import SbtCosmo.Derivation.GroundOffsets.Point010
import SbtCosmo.Derivation.GroundOffsets.Point011
import SbtCosmo.Derivation.GroundOffsets.Point012
import SbtCosmo.Derivation.GroundOffsets.Point013
import SbtCosmo.Derivation.GroundOffsets.Point014
import SbtCosmo.Derivation.GroundOffsets.Point015
import SbtCosmo.Derivation.GroundOffsets.Point016
import SbtCosmo.Derivation.GroundOffsets.Point017
import SbtCosmo.Derivation.GroundNativeControls
import SbtCosmo.Derivation.GroundOriginalSamples

/-! Eighteen actual shifted backgrounds and their kernel-earned positive
self-consistent roots. Exact and rounded shifted inputs are distinct models,
both covered by the same whole-background-box certificate. Uniqueness is local
in the certified ball; no frozen-seed basin or finite stopping verdict is added. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsets
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open Metric GroundState GroundBorder GroundRootCertificate GroundSourceJacobian
open GroundParameterTube GroundOriginalFirstTube GroundRationalInterval
open GroundNativePhase GroundNativeIteration
open scoped BigOperators

structure Certificate where
  offset : ℚ
  κ : ℚ
  roundedBackground : Fin 8 → ℚ
  B : Fin 8 → Interval
  z : Fin 9 → ℚ
  r : ℚ
  q : ℚ
  y : ℚ
  C : Matrix (Fin 9) (Fin 9) ℚ
  inputs : ∀ i : Fin 8,
    (B i).lo ≤ originalBackground i+offset ∧ originalBackground i+offset ≤ (B i).hi ∧
    (B i).lo ≤ roundedBackground i ∧ roundedBackground i ≤ (B i).hi
  arithmetic : GroundUncertainBackgroundTube.Arithmetic B κ κ z r q y C

def certificates : Fin 18 → Certificate :=
  Fin.cases ⟨GroundOffsets.Point000.offset, GroundOffsets.Point000.κ, GroundOffsets.Point000.roundedBackground, GroundOffsets.Point000.B, GroundOffsets.Point000.z, GroundOffsets.Point000.r, GroundOffsets.Point000.q, GroundOffsets.Point000.y, GroundOffsets.Point000.C, GroundOffsets.Point000.backgrounds_arithmetic, GroundOffsets.Point000.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point001.offset, GroundOffsets.Point001.κ, GroundOffsets.Point001.roundedBackground, GroundOffsets.Point001.B, GroundOffsets.Point001.z, GroundOffsets.Point001.r, GroundOffsets.Point001.q, GroundOffsets.Point001.y, GroundOffsets.Point001.C, GroundOffsets.Point001.backgrounds_arithmetic, GroundOffsets.Point001.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point002.offset, GroundOffsets.Point002.κ, GroundOffsets.Point002.roundedBackground, GroundOffsets.Point002.B, GroundOffsets.Point002.z, GroundOffsets.Point002.r, GroundOffsets.Point002.q, GroundOffsets.Point002.y, GroundOffsets.Point002.C, GroundOffsets.Point002.backgrounds_arithmetic, GroundOffsets.Point002.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point003.offset, GroundOffsets.Point003.κ, GroundOffsets.Point003.roundedBackground, GroundOffsets.Point003.B, GroundOffsets.Point003.z, GroundOffsets.Point003.r, GroundOffsets.Point003.q, GroundOffsets.Point003.y, GroundOffsets.Point003.C, GroundOffsets.Point003.backgrounds_arithmetic, GroundOffsets.Point003.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point004.offset, GroundOffsets.Point004.κ, GroundOffsets.Point004.roundedBackground, GroundOffsets.Point004.B, GroundOffsets.Point004.z, GroundOffsets.Point004.r, GroundOffsets.Point004.q, GroundOffsets.Point004.y, GroundOffsets.Point004.C, GroundOffsets.Point004.backgrounds_arithmetic, GroundOffsets.Point004.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point005.offset, GroundOffsets.Point005.κ, GroundOffsets.Point005.roundedBackground, GroundOffsets.Point005.B, GroundOffsets.Point005.z, GroundOffsets.Point005.r, GroundOffsets.Point005.q, GroundOffsets.Point005.y, GroundOffsets.Point005.C, GroundOffsets.Point005.backgrounds_arithmetic, GroundOffsets.Point005.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point006.offset, GroundOffsets.Point006.κ, GroundOffsets.Point006.roundedBackground, GroundOffsets.Point006.B, GroundOffsets.Point006.z, GroundOffsets.Point006.r, GroundOffsets.Point006.q, GroundOffsets.Point006.y, GroundOffsets.Point006.C, GroundOffsets.Point006.backgrounds_arithmetic, GroundOffsets.Point006.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point007.offset, GroundOffsets.Point007.κ, GroundOffsets.Point007.roundedBackground, GroundOffsets.Point007.B, GroundOffsets.Point007.z, GroundOffsets.Point007.r, GroundOffsets.Point007.q, GroundOffsets.Point007.y, GroundOffsets.Point007.C, GroundOffsets.Point007.backgrounds_arithmetic, GroundOffsets.Point007.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point008.offset, GroundOffsets.Point008.κ, GroundOffsets.Point008.roundedBackground, GroundOffsets.Point008.B, GroundOffsets.Point008.z, GroundOffsets.Point008.r, GroundOffsets.Point008.q, GroundOffsets.Point008.y, GroundOffsets.Point008.C, GroundOffsets.Point008.backgrounds_arithmetic, GroundOffsets.Point008.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point009.offset, GroundOffsets.Point009.κ, GroundOffsets.Point009.roundedBackground, GroundOffsets.Point009.B, GroundOffsets.Point009.z, GroundOffsets.Point009.r, GroundOffsets.Point009.q, GroundOffsets.Point009.y, GroundOffsets.Point009.C, GroundOffsets.Point009.backgrounds_arithmetic, GroundOffsets.Point009.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point010.offset, GroundOffsets.Point010.κ, GroundOffsets.Point010.roundedBackground, GroundOffsets.Point010.B, GroundOffsets.Point010.z, GroundOffsets.Point010.r, GroundOffsets.Point010.q, GroundOffsets.Point010.y, GroundOffsets.Point010.C, GroundOffsets.Point010.backgrounds_arithmetic, GroundOffsets.Point010.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point011.offset, GroundOffsets.Point011.κ, GroundOffsets.Point011.roundedBackground, GroundOffsets.Point011.B, GroundOffsets.Point011.z, GroundOffsets.Point011.r, GroundOffsets.Point011.q, GroundOffsets.Point011.y, GroundOffsets.Point011.C, GroundOffsets.Point011.backgrounds_arithmetic, GroundOffsets.Point011.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point012.offset, GroundOffsets.Point012.κ, GroundOffsets.Point012.roundedBackground, GroundOffsets.Point012.B, GroundOffsets.Point012.z, GroundOffsets.Point012.r, GroundOffsets.Point012.q, GroundOffsets.Point012.y, GroundOffsets.Point012.C, GroundOffsets.Point012.backgrounds_arithmetic, GroundOffsets.Point012.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point013.offset, GroundOffsets.Point013.κ, GroundOffsets.Point013.roundedBackground, GroundOffsets.Point013.B, GroundOffsets.Point013.z, GroundOffsets.Point013.r, GroundOffsets.Point013.q, GroundOffsets.Point013.y, GroundOffsets.Point013.C, GroundOffsets.Point013.backgrounds_arithmetic, GroundOffsets.Point013.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point014.offset, GroundOffsets.Point014.κ, GroundOffsets.Point014.roundedBackground, GroundOffsets.Point014.B, GroundOffsets.Point014.z, GroundOffsets.Point014.r, GroundOffsets.Point014.q, GroundOffsets.Point014.y, GroundOffsets.Point014.C, GroundOffsets.Point014.backgrounds_arithmetic, GroundOffsets.Point014.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point015.offset, GroundOffsets.Point015.κ, GroundOffsets.Point015.roundedBackground, GroundOffsets.Point015.B, GroundOffsets.Point015.z, GroundOffsets.Point015.r, GroundOffsets.Point015.q, GroundOffsets.Point015.y, GroundOffsets.Point015.C, GroundOffsets.Point015.backgrounds_arithmetic, GroundOffsets.Point015.arithmetic⟩ (
  Fin.cases ⟨GroundOffsets.Point016.offset, GroundOffsets.Point016.κ, GroundOffsets.Point016.roundedBackground, GroundOffsets.Point016.B, GroundOffsets.Point016.z, GroundOffsets.Point016.r, GroundOffsets.Point016.q, GroundOffsets.Point016.y, GroundOffsets.Point016.C, GroundOffsets.Point016.backgrounds_arithmetic, GroundOffsets.Point016.arithmetic⟩ (
  fun _ => ⟨GroundOffsets.Point017.offset, GroundOffsets.Point017.κ, GroundOffsets.Point017.roundedBackground, GroundOffsets.Point017.B, GroundOffsets.Point017.z, GroundOffsets.Point017.r, GroundOffsets.Point017.q, GroundOffsets.Point017.y, GroundOffsets.Point017.C, GroundOffsets.Point017.backgrounds_arithmetic, GroundOffsets.Point017.arithmetic⟩)))))))))))))))))

def b (i : Fin 18) : Field := fun j => ((originalBackground j+(certificates i).offset : ℚ) : ℝ)
def rounded_b (i : Fin 18) : Field := GroundKernelTube.background (certificates i).roundedBackground

theorem exact_inputs_sound (i : Fin 18) : ∀ j, ((certificates i).B j).Contains (b i j) := by
  intro j
  change ((certificates i).B j).lo ≤ (b i j) ∧ (b i j) ≤ ((certificates i).B j).hi
  dsimp only [b]
  exact ⟨Rat.cast_le.mpr ((certificates i).inputs j).1,
    Rat.cast_le.mpr ((certificates i).inputs j).2.1⟩

theorem rounded_inputs_sound (i : Fin 18) : ∀ j, ((certificates i).B j).Contains (rounded_b i j) := by
  intro j
  dsimp only [rounded_b, GroundKernelTube.background]
  exact ⟨Rat.cast_le.mpr ((certificates i).inputs j).2.2.1,
    Rat.cast_le.mpr ((certificates i).inputs j).2.2.2⟩

def exactTube (i : Fin 18) : TubeCertificate (b i) :=
  GroundUncertainBackgroundTube.tube (certificates i).arithmetic (exact_inputs_sound i)
def roundedTube (i : Fin 18) : TubeCertificate (rounded_b i) :=
  GroundUncertainBackgroundTube.tube (certificates i).arithmetic (rounded_inputs_sound i)
def root (i : Fin 18) : Point := (exactTube i).root (certificates i).κ
def roundedRoot (i : Fin 18) : Point := (roundedTube i).root (certificates i).κ

theorem exact_interval (i : Fin 18) : ((certificates i).κ : ℝ) ∈ (exactTube i).interval := ⟨le_rfl, le_rfl⟩
theorem rounded_interval (i : Fin 18) : ((certificates i).κ : ℝ) ∈ (roundedTube i).interval := ⟨le_rfl, le_rfl⟩

theorem exact_root_spec (i : Fin 18) :
    root i ∈ closedBall (GroundKernelTube.center (certificates i).z) ((certificates i).r : ℝ) ∧
    residual (b i) (certificates i).κ (root i) = 0 ∧
    IsGround (sourcePotential (b i) (certificates i).κ (root i).1) (root i).1 (root i).2 ∧
    groundMap (b i) (certificates i).κ (root i).1 = (root i).1 ∧
    ∀ x ∈ closedBall (GroundKernelTube.center (certificates i).z) ((certificates i).r : ℝ),
      residual (b i) (certificates i).κ x = 0 → x = root i :=
  (exactTube i).root_spec (exact_interval i)

theorem rounded_root_spec (i : Fin 18) :
    roundedRoot i ∈ closedBall (GroundKernelTube.center (certificates i).z) ((certificates i).r : ℝ) ∧
    residual (rounded_b i) (certificates i).κ (roundedRoot i) = 0 ∧
    IsGround (sourcePotential (rounded_b i) (certificates i).κ (roundedRoot i).1) (roundedRoot i).1 (roundedRoot i).2 ∧
    groundMap (rounded_b i) (certificates i).κ (roundedRoot i).1 = (roundedRoot i).1 ∧
    ∀ x ∈ closedBall (GroundKernelTube.center (certificates i).z) ((certificates i).r : ℝ),
      residual (rounded_b i) (certificates i).κ x = 0 → x = roundedRoot i :=
  (roundedTube i).root_spec (rounded_interval i)

theorem exact_root_positive (i : Fin 18) : ∀ j, 0 < (root i).1 j :=
  (exactTube i).field_positive _ (exact_root_spec i).1

theorem rounded_root_positive (i : Fin 18) : ∀ j, 0 < (roundedRoot i).1 j :=
  (roundedTube i).field_positive _ (rounded_root_spec i).1

theorem ground_pair_return {β : Field} {x : Point}
    (hg : IsGround β x.1 x.2) (hp : ∀ j, 0 < x.1 j) : groundPair β = x := by
  have he : positiveGround β = x.1 :=
    positive_ground_unique (positiveGround_spec β).2 hg (positiveGround_spec β).1 hp
  change (positiveGround β, energy β (positiveGround β)) = x
  rw [he, ground_energy hg]

theorem exact_ground_return (i : Fin 18) : normSq (root i).1 = 1 ∧
    groundPair (sourcePotential (b i) (certificates i).κ (root i).1) = root i :=
  ⟨(exact_root_spec i).2.2.1.1,
    ground_pair_return (exact_root_spec i).2.2.1 (exact_root_positive i)⟩

theorem rounded_ground_return (i : Fin 18) : normSq (roundedRoot i).1 = 1 ∧
    groundPair (sourcePotential (rounded_b i) (certificates i).κ (roundedRoot i).1) = roundedRoot i :=
  ⟨(rounded_root_spec i).2.2.1.1,
    ground_pair_return (rounded_root_spec i).2.2.1 (rounded_root_positive i)⟩

theorem exact_point_box (i : Fin 18) (j : Fin 9) :
    (⟨(certificates i).z j-(certificates i).r, (certificates i).z j+(certificates i).r⟩ : Interval).Contains
      (GroundPointCoordinates.coord (root i) j) := by
  have h := GroundUncertainBackgroundTube.box_sound (certificates i).B (certificates i).κ
    (certificates i).κ (certificates i).z (certificates i).r (exact_inputs_sound i)
    (κ := ((certificates i).κ : ℝ)) ⟨le_rfl, le_rfl⟩ (exact_root_spec i).1 (.state j)
  exact h

theorem rounded_point_box (i : Fin 18) (j : Fin 9) :
    (⟨(certificates i).z j-(certificates i).r, (certificates i).z j+(certificates i).r⟩ : Interval).Contains
      (GroundPointCoordinates.coord (roundedRoot i) j) := by
  have h := GroundUncertainBackgroundTube.box_sound (certificates i).B (certificates i).κ
    (certificates i).κ (certificates i).z (certificates i).r (rounded_inputs_sound i)
    (κ := ((certificates i).κ : ℝ)) ⟨le_rfl, le_rfl⟩ (rounded_root_spec i).1 (.state j)
  exact h

def offsets : Fin 18 → ℚ := ![-8, -5, -3, -2, -1, -(1/2),
  -(3602879701896397/18014398509481984), -(3602879701896397/36028797018963968),
  0, (3602879701896397/36028797018963968), (3602879701896397/18014398509481984),
  (1/2), 1, 2, 3, 5, 8, 10]
def originalCoupling : ℚ := 5404319552844595/18014398509481984

theorem parameters_arithmetic : ∀ i : Fin 18, (certificates i).offset = offsets i ∧
    (certificates i).κ = originalCoupling ∧ (certificates i).r = 1/2^32 := by decide +kernel

theorem uniform_background_return (i : Fin 18) (j : Fin 8) :
    b i j = (originalBackground j : ℝ)+(offsets i : ℝ) := by
  simp only [b, (parameters_arithmetic i).1, Rat.cast_add]

theorem model_root_proximity (i : Fin 18) : dist (root i) (roundedRoot i) ≤ 2*((certificates i).r : ℝ) := by
  have h0 : dist (root i) (GroundKernelTube.center (certificates i).z) ≤ ((certificates i).r : ℝ) := (exact_root_spec i).1
  have h1 : dist (GroundKernelTube.center (certificates i).z) (roundedRoot i) ≤ ((certificates i).r : ℝ) := by
    rw [dist_comm]; exact (rounded_root_spec i).1
  linarith [dist_triangle (root i) (GroundKernelTube.center (certificates i).z) (roundedRoot i)]

theorem native_fixed_return {β v : Field} {k m τ : ℝ}
    (hu : normSq v = 1) (hf : groundMap β k v = v) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    nativeUpdate τ β k m (realEmbed v) = realEmbed v ∧
    ActivePhase τ β k (realEmbed v) ∧ NativeLegal τ β k m (realEmbed v) := by
  have hn := (nativeUpdate_near_fixed (m := m) hu hf hτ0 hτ1).self_of_nhds
  refine ⟨?_, hn.2⟩
  change nativeUpdate τ β k m (pack (v, 0)) = pack (v, 0)
  rw [← hn.1, fullMap_fixed hu hf]

theorem exact_native_fixed (i : Fin 18) (m : ℝ) :
    nativeUpdate GroundNativeControls.originalTolerance (b i) (certificates i).κ m (realEmbed (root i).1) = realEmbed (root i).1 ∧
    ActivePhase GroundNativeControls.originalTolerance (b i) (certificates i).κ (realEmbed (root i).1) ∧
    NativeLegal GroundNativeControls.originalTolerance (b i) (certificates i).κ m (realEmbed (root i).1) :=
  native_fixed_return (exact_ground_return i).1 (exact_root_spec i).2.2.2.1
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2

theorem rounded_native_fixed (i : Fin 18) (m : ℝ) :
    nativeUpdate GroundNativeControls.originalTolerance (rounded_b i) (certificates i).κ m (realEmbed (roundedRoot i).1) = realEmbed (roundedRoot i).1 ∧
    ActivePhase GroundNativeControls.originalTolerance (rounded_b i) (certificates i).κ (realEmbed (roundedRoot i).1) ∧
    NativeLegal GroundNativeControls.originalTolerance (rounded_b i) (certificates i).κ m (realEmbed (roundedRoot i).1) :=
  native_fixed_return (rounded_ground_return i).1 (rounded_root_spec i).2.2.2.1
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2

theorem separation_arithmetic :
    (certificates 0).z 0+(certificates 0).r+3/10 < (certificates 17).z 0-(certificates 17).r := by decide +kernel

theorem field_coordinate_separation {x y : Point}
    (hx : (⟨(certificates 0).z 0-(certificates 0).r, (certificates 0).z 0+(certificates 0).r⟩ : Interval).Contains (x.1 0))
    (hy : (⟨(certificates 17).z 0-(certificates 17).r, (certificates 17).z 0+(certificates 17).r⟩ : Interval).Contains (y.1 0)) :
    x.1 0+3/10 < y.1 0 := by
  have hc : ((certificates 0).z 0 : ℝ)+((certificates 0).r : ℝ)+3/10 <
      ((certificates 17).z 0 : ℝ)-((certificates 17).r : ℝ) := by
    have h : (((certificates 0).z 0+(certificates 0).r+3/10 : ℚ) : ℝ) <
        (((certificates 17).z 0-(certificates 17).r : ℚ) : ℝ) := Rat.cast_lt.mpr separation_arithmetic
    norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  simp only [Interval.Contains, Rat.cast_sub, Rat.cast_add] at hx hy
  linarith

theorem actual_exact_fields_separated : (root 0).1 0+3/10 < (root 17).1 0 :=
  field_coordinate_separation (exact_point_box 0 (0 : Fin 8).castSucc) (exact_point_box 17 (0 : Fin 8).castSucc)

theorem actual_rounded_fields_separated : (roundedRoot 0).1 0+3/10 < (roundedRoot 17).1 0 :=
  field_coordinate_separation (rounded_point_box 0 (0 : Fin 8).castSucc) (rounded_point_box 17 (0 : Fin 8).castSucc)



theorem zero_preconditioner_rejected : ¬ GroundUncertainBackgroundTube.Arithmetic
    (certificates 0).B (certificates 0).κ (certificates 0).κ (certificates 0).z
    (certificates 0).r (certificates 0).q (certificates 0).y (fun _ _ => 0) := by
  intro h
  have hn : ¬ (∑ j : Fin 9, ((GroundResidualEnclosure.defectExpr (fun _ _ => 0) 0 j).enclose
    (GroundUncertainBackgroundTube.box (certificates 0).B (certificates 0).κ (certificates 0).κ
      (certificates 0).z (certificates 0).r)).bound) ≤ (certificates 0).q := by decide +kernel
  exact hn (h.defect_rows 0)


theorem whole_background_box_root (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((certificates i).B j).Contains (β j)) :
    ∃ x ∈ closedBall (GroundKernelTube.center (certificates i).z) ((certificates i).r : ℝ),
      residual β (certificates i).κ x = 0 ∧ (∀ j, 0 < x.1 j) ∧
      IsGround (sourcePotential β (certificates i).κ x.1) x.1 x.2 ∧
      groundMap β (certificates i).κ x.1 = x.1 ∧
      ∀ y ∈ closedBall (GroundKernelTube.center (certificates i).z) ((certificates i).r : ℝ),
        residual β (certificates i).κ y = 0 → y = x := by
  obtain ⟨x, hx, hr, hg, hf, hu⟩ := GroundUncertainBackgroundTube.certified_actual_root
    (certificates i).arithmetic hβ (κ := ((certificates i).κ : ℝ)) ⟨le_rfl, le_rfl⟩
  exact ⟨x, hx, hr, (GroundUncertainBackgroundTube.tube (certificates i).arithmetic hβ).field_positive x hx, hg, hf, hu⟩

theorem zero_offset_arithmetic :
    (certificates 8).offset = 0 ∧ (certificates 8).κ = GroundOriginalSamples.couplings 2 ∧
    (certificates 8).r = GroundSamples.Point002.r ∧
    (∀ j, (certificates 8).z j = GroundSamples.Point002.z j) ∧
    (∀ j, (certificates 8).roundedBackground j = originalBackground j) := by decide +kernel

theorem zero_exact_background : b 8 = GroundKernelTube.background originalBackground := by
  funext j
  simp only [b, zero_offset_arithmetic.1, add_zero, GroundKernelTube.background]

theorem zero_rounded_background : rounded_b 8 = GroundKernelTube.background originalBackground := by
  funext j
  change ((certificates 8).roundedBackground j : ℝ) = (originalBackground j : ℝ)
  rw [zero_offset_arithmetic.2.2.2.2 j]

theorem zero_exact_root_eq_original : root 8 = GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2) := by
  have hz : (certificates 8).z = GroundSamples.Point002.z := funext zero_offset_arithmetic.2.2.2.1
  have hx := GroundOriginalSamples.branch_in_sample_ball 2
  change GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2) ∈
    closedBall (GroundKernelTube.center GroundSamples.Point002.z) (GroundSamples.Point002.r : ℝ) at hx
  have hball : GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2) ∈
      closedBall (GroundKernelTube.center (certificates 8).z) ((certificates 8).r : ℝ) := by
    rw [hz, zero_offset_arithmetic.2.2.1]; exact hx
  have hr : residual (b 8) (certificates 8).κ
      (GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2)) = 0 := by
    rw [zero_exact_background, zero_offset_arithmetic.2.1]
    exact (GroundOriginalSamples.sample_ground_return 2).1
  exact ((exact_root_spec 8).2.2.2.2 _ hball hr).symm

theorem zero_rounded_root_eq_original : roundedRoot 8 = GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2) := by
  have hz : (certificates 8).z = GroundSamples.Point002.z := funext zero_offset_arithmetic.2.2.2.1
  have hx := GroundOriginalSamples.branch_in_sample_ball 2
  change GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2) ∈
    closedBall (GroundKernelTube.center GroundSamples.Point002.z) (GroundSamples.Point002.r : ℝ) at hx
  have hball : GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2) ∈
      closedBall (GroundKernelTube.center (certificates 8).z) ((certificates 8).r : ℝ) := by
    rw [hz, zero_offset_arithmetic.2.2.1]; exact hx
  have hr : residual (rounded_b 8) (certificates 8).κ
      (GroundOriginalContinuation.branch (GroundOriginalSamples.couplings 2)) = 0 := by
    rw [zero_rounded_background, zero_offset_arithmetic.2.1]
    exact (GroundOriginalSamples.sample_ground_return 2).1
  exact ((rounded_root_spec 8).2.2.2.2 _ hball hr).symm


theorem density_separation_of_positive {x y : ℝ} (hx : 0 < x) (hxy : x+3/10 < y) :
    x^2+9/100 < y^2 := by
  have hp : 0 < x*(y-x) := mul_pos hx (by linarith)
  nlinarith [sq_nonneg (y-x-3/10)]

theorem actual_exact_densities_separated :
    Complex.normSq (realEmbed (root 0).1 0)+9/100 < Complex.normSq (realEmbed (root 17).1 0) := by
  simp only [realEmbed, Complex.normSq_ofReal, ← pow_two]
  exact density_separation_of_positive (exact_root_positive 0 0) actual_exact_fields_separated

theorem actual_rounded_densities_separated :
    Complex.normSq (realEmbed (roundedRoot 0).1 0)+9/100 < Complex.normSq (realEmbed (roundedRoot 17).1 0) := by
  simp only [realEmbed, Complex.normSq_ofReal, ← pow_two]
  exact density_separation_of_positive (rounded_root_positive 0 0) actual_rounded_fields_separated


end
end SbtCosmo.Derivation.GroundOriginalOffsets
