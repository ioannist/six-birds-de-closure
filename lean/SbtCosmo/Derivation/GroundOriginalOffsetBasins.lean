import SbtCosmo.Derivation.GroundOffsetBasins.Point000
import SbtCosmo.Derivation.GroundOffsetBasins.Point001
import SbtCosmo.Derivation.GroundOffsetBasins.Point002
import SbtCosmo.Derivation.GroundOffsetBasins.Point003
import SbtCosmo.Derivation.GroundOffsetBasins.Point004
import SbtCosmo.Derivation.GroundOffsetBasins.Point005
import SbtCosmo.Derivation.GroundOffsetBasins.Point006
import SbtCosmo.Derivation.GroundOffsetBasins.Point007
import SbtCosmo.Derivation.GroundOffsetBasins.Point008
import SbtCosmo.Derivation.GroundOffsetBasins.Point009
import SbtCosmo.Derivation.GroundOffsetBasins.Point010
import SbtCosmo.Derivation.GroundOffsetBasins.Point011
import SbtCosmo.Derivation.GroundOffsetBasins.Point012
import SbtCosmo.Derivation.GroundOffsetBasins.Point013
import SbtCosmo.Derivation.GroundOffsetBasins.Point014
import SbtCosmo.Derivation.GroundOffsetBasins.Point015
import SbtCosmo.Derivation.GroundOffsetBasins.Point016
import SbtCosmo.Derivation.GroundOffsetBasins.Point017
import SbtCosmo.Derivation.GroundOriginalOffsetStability

/-! Explicit quantitative native basins for all18 original background offsets.
The same arithmetic covers every background in each exact/rounded input hull.
Frozen-seed entry remains a separate obligation. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsetBasins
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundRationalInterval
open GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open Filter Metric
open scoped Topology BigOperators

structure Data (i : Fin 18) where
  c : GroundUncertainNativeBasin.Certificate
  ρ : ℚ
  s : ℚ
  inputs : c.β = (GroundOriginalOffsets.certificates i).B
  coupling : c.κ = (GroundOriginalOffsets.certificates i).κ
  threshold : c.τ = GroundNativePrefixInitial.τ
  responses : c.ResponseArithmetic
  response_included : c.ResponseIncluded
  derivative_included : c.DerivativeIncluded
  rows : c.RowArithmetic
  basis_rows : ∀ a : Fin 8, (∑ b, |c.S a b|) ≤ s ∧ (∑ b, |c.R a b|) ≤ s
  radius_pos : 0 < ρ
  basis_nonneg : 0 ≤ s
  input_geometry : (aroundBox (GroundOriginalOffsets.certificates i).z
    (GroundOriginalOffsets.certificates i).r ρ s).Included c.input

def data : (i : Fin 18) → Data i :=
  Fin.cases ⟨GroundOffsetBasins.Point000.certificate, GroundOffsetBasins.Point000.ρ, GroundOffsetBasins.Point000.s, rfl, rfl, rfl, GroundOffsetBasins.Point000.responses, GroundOffsetBasins.Point000.response_included, GroundOffsetBasins.Point000.derivative_included, GroundOffsetBasins.Point000.rows, GroundOffsetBasins.Point000.basis_rows, GroundOffsetBasins.Point000.radius_pos, GroundOffsetBasins.Point000.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point001.certificate, GroundOffsetBasins.Point001.ρ, GroundOffsetBasins.Point001.s, rfl, rfl, rfl, GroundOffsetBasins.Point001.responses, GroundOffsetBasins.Point001.response_included, GroundOffsetBasins.Point001.derivative_included, GroundOffsetBasins.Point001.rows, GroundOffsetBasins.Point001.basis_rows, GroundOffsetBasins.Point001.radius_pos, GroundOffsetBasins.Point001.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point002.certificate, GroundOffsetBasins.Point002.ρ, GroundOffsetBasins.Point002.s, rfl, rfl, rfl, GroundOffsetBasins.Point002.responses, GroundOffsetBasins.Point002.response_included, GroundOffsetBasins.Point002.derivative_included, GroundOffsetBasins.Point002.rows, GroundOffsetBasins.Point002.basis_rows, GroundOffsetBasins.Point002.radius_pos, GroundOffsetBasins.Point002.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point003.certificate, GroundOffsetBasins.Point003.ρ, GroundOffsetBasins.Point003.s, rfl, rfl, rfl, GroundOffsetBasins.Point003.responses, GroundOffsetBasins.Point003.response_included, GroundOffsetBasins.Point003.derivative_included, GroundOffsetBasins.Point003.rows, GroundOffsetBasins.Point003.basis_rows, GroundOffsetBasins.Point003.radius_pos, GroundOffsetBasins.Point003.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point004.certificate, GroundOffsetBasins.Point004.ρ, GroundOffsetBasins.Point004.s, rfl, rfl, rfl, GroundOffsetBasins.Point004.responses, GroundOffsetBasins.Point004.response_included, GroundOffsetBasins.Point004.derivative_included, GroundOffsetBasins.Point004.rows, GroundOffsetBasins.Point004.basis_rows, GroundOffsetBasins.Point004.radius_pos, GroundOffsetBasins.Point004.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point005.certificate, GroundOffsetBasins.Point005.ρ, GroundOffsetBasins.Point005.s, rfl, rfl, rfl, GroundOffsetBasins.Point005.responses, GroundOffsetBasins.Point005.response_included, GroundOffsetBasins.Point005.derivative_included, GroundOffsetBasins.Point005.rows, GroundOffsetBasins.Point005.basis_rows, GroundOffsetBasins.Point005.radius_pos, GroundOffsetBasins.Point005.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point006.certificate, GroundOffsetBasins.Point006.ρ, GroundOffsetBasins.Point006.s, rfl, rfl, rfl, GroundOffsetBasins.Point006.responses, GroundOffsetBasins.Point006.response_included, GroundOffsetBasins.Point006.derivative_included, GroundOffsetBasins.Point006.rows, GroundOffsetBasins.Point006.basis_rows, GroundOffsetBasins.Point006.radius_pos, GroundOffsetBasins.Point006.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point007.certificate, GroundOffsetBasins.Point007.ρ, GroundOffsetBasins.Point007.s, rfl, rfl, rfl, GroundOffsetBasins.Point007.responses, GroundOffsetBasins.Point007.response_included, GroundOffsetBasins.Point007.derivative_included, GroundOffsetBasins.Point007.rows, GroundOffsetBasins.Point007.basis_rows, GroundOffsetBasins.Point007.radius_pos, GroundOffsetBasins.Point007.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point008.certificate, GroundOffsetBasins.Point008.ρ, GroundOffsetBasins.Point008.s, rfl, rfl, rfl, GroundOffsetBasins.Point008.responses, GroundOffsetBasins.Point008.response_included, GroundOffsetBasins.Point008.derivative_included, GroundOffsetBasins.Point008.rows, GroundOffsetBasins.Point008.basis_rows, GroundOffsetBasins.Point008.radius_pos, GroundOffsetBasins.Point008.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point009.certificate, GroundOffsetBasins.Point009.ρ, GroundOffsetBasins.Point009.s, rfl, rfl, rfl, GroundOffsetBasins.Point009.responses, GroundOffsetBasins.Point009.response_included, GroundOffsetBasins.Point009.derivative_included, GroundOffsetBasins.Point009.rows, GroundOffsetBasins.Point009.basis_rows, GroundOffsetBasins.Point009.radius_pos, GroundOffsetBasins.Point009.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point010.certificate, GroundOffsetBasins.Point010.ρ, GroundOffsetBasins.Point010.s, rfl, rfl, rfl, GroundOffsetBasins.Point010.responses, GroundOffsetBasins.Point010.response_included, GroundOffsetBasins.Point010.derivative_included, GroundOffsetBasins.Point010.rows, GroundOffsetBasins.Point010.basis_rows, GroundOffsetBasins.Point010.radius_pos, GroundOffsetBasins.Point010.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point011.certificate, GroundOffsetBasins.Point011.ρ, GroundOffsetBasins.Point011.s, rfl, rfl, rfl, GroundOffsetBasins.Point011.responses, GroundOffsetBasins.Point011.response_included, GroundOffsetBasins.Point011.derivative_included, GroundOffsetBasins.Point011.rows, GroundOffsetBasins.Point011.basis_rows, GroundOffsetBasins.Point011.radius_pos, GroundOffsetBasins.Point011.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point012.certificate, GroundOffsetBasins.Point012.ρ, GroundOffsetBasins.Point012.s, rfl, rfl, rfl, GroundOffsetBasins.Point012.responses, GroundOffsetBasins.Point012.response_included, GroundOffsetBasins.Point012.derivative_included, GroundOffsetBasins.Point012.rows, GroundOffsetBasins.Point012.basis_rows, GroundOffsetBasins.Point012.radius_pos, GroundOffsetBasins.Point012.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point013.certificate, GroundOffsetBasins.Point013.ρ, GroundOffsetBasins.Point013.s, rfl, rfl, rfl, GroundOffsetBasins.Point013.responses, GroundOffsetBasins.Point013.response_included, GroundOffsetBasins.Point013.derivative_included, GroundOffsetBasins.Point013.rows, GroundOffsetBasins.Point013.basis_rows, GroundOffsetBasins.Point013.radius_pos, GroundOffsetBasins.Point013.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point014.certificate, GroundOffsetBasins.Point014.ρ, GroundOffsetBasins.Point014.s, rfl, rfl, rfl, GroundOffsetBasins.Point014.responses, GroundOffsetBasins.Point014.response_included, GroundOffsetBasins.Point014.derivative_included, GroundOffsetBasins.Point014.rows, GroundOffsetBasins.Point014.basis_rows, GroundOffsetBasins.Point014.radius_pos, GroundOffsetBasins.Point014.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point015.certificate, GroundOffsetBasins.Point015.ρ, GroundOffsetBasins.Point015.s, rfl, rfl, rfl, GroundOffsetBasins.Point015.responses, GroundOffsetBasins.Point015.response_included, GroundOffsetBasins.Point015.derivative_included, GroundOffsetBasins.Point015.rows, GroundOffsetBasins.Point015.basis_rows, GroundOffsetBasins.Point015.radius_pos, GroundOffsetBasins.Point015.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  Fin.cases ⟨GroundOffsetBasins.Point016.certificate, GroundOffsetBasins.Point016.ρ, GroundOffsetBasins.Point016.s, rfl, rfl, rfl, GroundOffsetBasins.Point016.responses, GroundOffsetBasins.Point016.response_included, GroundOffsetBasins.Point016.derivative_included, GroundOffsetBasins.Point016.rows, GroundOffsetBasins.Point016.basis_rows, GroundOffsetBasins.Point016.radius_pos, GroundOffsetBasins.Point016.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩ (
  fun _ => ⟨GroundOffsetBasins.Point017.certificate, GroundOffsetBasins.Point017.ρ, GroundOffsetBasins.Point017.s, rfl, rfl, rfl, GroundOffsetBasins.Point017.responses, GroundOffsetBasins.Point017.response_included, GroundOffsetBasins.Point017.derivative_included, GroundOffsetBasins.Point017.rows, GroundOffsetBasins.Point017.basis_rows, GroundOffsetBasins.Point017.radius_pos, GroundOffsetBasins.Point017.basis_nonneg, (by intro a; exact ⟨⟨le_rfl,le_rfl⟩,⟨le_rfl,le_rfl⟩⟩)⟩)))))))))))))))))

def T (i : Fin 18) := (data i).c.T
def rate (i : Fin 18) := (data i).c.contractionRate (data i).rows

theorem root_field_box (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) (a : Fin 8) :
    (GroundBackgroundKernel.fieldBox (GroundOriginalOffsets.certificates i).z
      (GroundOriginalOffsets.certificates i).r a).Contains
      ((GroundOriginalOffsetStability.wholeRoot i hβ).1 a) := by
  have h := GroundUncertainBackgroundTube.box_sound (GroundOriginalOffsets.certificates i).B
    (GroundOriginalOffsets.certificates i).κ (GroundOriginalOffsets.certificates i).κ
    (GroundOriginalOffsets.certificates i).z (GroundOriginalOffsets.certificates i).r hβ
    (κ := ((GroundOriginalOffsets.certificates i).κ : ℝ)) ⟨le_rfl,le_rfl⟩
    (GroundOriginalOffsetStability.whole_root_return i hβ).1 (.state a.castSucc)
  simpa only [GroundBackgroundKernel.fieldBox,GroundUncertainBackgroundTube.box,GroundResidualEnclosure.valuation,GroundPointCoordinates.coord,Fin.lastCases_castSucc] using h

theorem whole_background_box_explicit_native_basin (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) {z : ComplexField}
    (hz : (T i).symm (unpack z) ∈ closedBall
      ((T i).symm ((GroundOriginalOffsetStability.wholeRoot i hβ).1,0)) ((data i).ρ : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
      atTop (nhds (realEmbed (GroundOriginalOffsetStability.wholeRoot i hβ).1)) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ
      ((nativeUpdate GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      dist ((T i).symm (unpack ((nativeUpdate GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)))
        ((T i).symm ((GroundOriginalOffsetStability.wholeRoot i hβ).1,0)) ≤
        ((rate i : ℝ)^n)*dist ((T i).symm (unpack z))
          ((T i).symm ((GroundOriginalOffsetStability.wholeRoot i hβ).1,0)) := by
  have hb : ∀ j, ((data i).c.β j).Contains (β j) := by rw [(data i).inputs]; exact hβ
  have hs := GroundOriginalOffsetStability.whole_root_return i hβ
  have hf : GroundSourceJacobian.groundMap β ((data i).c.κ : ℝ)
      (GroundOriginalOffsetStability.wholeRoot i hβ).1 = (GroundOriginalOffsetStability.wholeRoot i hβ).1 := by
    rw [(data i).coupling];exact hs.2.2.2
  have hτ : ((data i).c.τ : ℝ) = GroundNativeControls.originalTolerance := by
    rw [(data i).threshold,GroundNativePrefixInitial.tolerance_return]
  have h := (data i).c.actual_ball_convergence (data i).responses (data i).response_included
    (data i).derivative_included (data i).rows hb hs.2.1 hf
    (by rw [hτ];exact GroundNativeControls.originalTolerance_guard.2) (data i).radius_pos.le
    (data i).basis_nonneg ((data i).c.basis_norm (data i).basis_nonneg (data i).basis_rows)
    (root_field_box i hβ) (data i).input_geometry hz
  simpa only [(data i).coupling,hτ,T,rate] using h
theorem whole_background_box_explicit_negative_native_basin (i : Fin 18) {β : Field}
    (hβ : ∀ j, ((GroundOriginalOffsets.certificates i).B j).Contains (β j)) {z : ComplexField}
    (hz : (T i).symm (unpack z) ∈ closedBall
      ((T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hβ).1,0)) ((data i).ρ : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
      atTop (nhds (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hβ).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ
      ((nativeUpdate GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      dist ((T i).symm (unpack ((nativeUpdate GroundNativeControls.originalTolerance
        β (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)))
        ((T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hβ).1,0)) ≤
        ((rate i : ℝ)^n)*dist ((T i).symm (unpack z))
          ((T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hβ).1,0)) := by
  have hb : ∀ j, ((data i).c.β j).Contains (β j) := by rw [(data i).inputs]; exact hβ
  have hs := GroundOriginalOffsetStability.whole_root_return i hβ
  have hf : GroundSourceJacobian.groundMap β ((data i).c.κ : ℝ)
      (GroundOriginalOffsetStability.wholeRoot i hβ).1 = (GroundOriginalOffsetStability.wholeRoot i hβ).1 := by
    rw [(data i).coupling];exact hs.2.2.2
  have hτ : ((data i).c.τ : ℝ) = GroundNativeControls.originalTolerance := by
    rw [(data i).threshold,GroundNativePrefixInitial.tolerance_return]
  have h := (data i).c.actual_negative_ball_convergence (data i).responses (data i).response_included
    (data i).derivative_included (data i).rows hb hs.2.1 hf
    (by rw [hτ];exact GroundNativeControls.originalTolerance_guard.2) (data i).radius_pos.le
    (data i).basis_nonneg ((data i).c.basis_norm (data i).basis_nonneg (data i).basis_rows)
    (root_field_box i hβ) (data i).input_geometry hz
  simpa only [(data i).coupling,hτ,T,rate] using h

def commonRadius : ℚ := 1/400000

theorem radii_arithmetic : ∀ i : Fin 18, commonRadius ≤ (data i).ρ ∧
    ((data i).ρ = 1/40000 ∨ (data i).ρ = 1/400000) := by decide +kernel

theorem common_ball_entry (i : Fin 18) {u : Field} {x : State}
    (hx : x ∈ closedBall ((T i).symm (u,0)) (commonRadius : ℝ)) :
    x ∈ closedBall ((T i).symm (u,0)) ((data i).ρ : ℝ) := by
  rw [mem_closedBall] at hx ⊢
  exact hx.trans (Rat.cast_le.mpr (radii_arithmetic i).1)

theorem actual_exact_explicit_basin (i : Fin 18) {z : ComplexField}
    (hz : (T i).symm (unpack z) ∈ closedBall
      ((T i).symm ((GroundOriginalOffsets.root i).1,0)) (commonRadius : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
      atTop (nhds (realEmbed ((GroundOriginalOffsets.root i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ
      ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i)
        (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i)
        (GroundOriginalOffsets.certificates i).κ (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i)
          (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      dist ((T i).symm (unpack ((nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)))
        ((T i).symm ((GroundOriginalOffsets.root i).1,0)) ≤
        ((rate i : ℝ)^n)*dist ((T i).symm (unpack z))
          ((T i).symm ((GroundOriginalOffsets.root i).1,0)) :=
  whole_background_box_explicit_native_basin i (GroundOriginalOffsets.exact_inputs_sound i)
    (common_ball_entry i hz)

theorem actual_exact_negative_explicit_basin (i : Fin 18) {z : ComplexField}
    (hz : (T i).symm (unpack z) ∈ closedBall
      ((T i).symm (-(GroundOriginalOffsets.root i).1,0)) (commonRadius : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
      atTop (nhds (realEmbed (-(GroundOriginalOffsets.root i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ
      ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i)
        (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i)
        (GroundOriginalOffsets.certificates i).κ (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i)
          (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      dist ((T i).symm (unpack ((nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)))
        ((T i).symm (-(GroundOriginalOffsets.root i).1,0)) ≤
        ((rate i : ℝ)^n)*dist ((T i).symm (unpack z))
          ((T i).symm (-(GroundOriginalOffsets.root i).1,0)) :=
  whole_background_box_explicit_negative_native_basin i (GroundOriginalOffsets.exact_inputs_sound i)
    (common_ball_entry i hz)

theorem actual_rounded_explicit_basin (i : Fin 18) {z : ComplexField}
    (hz : (T i).symm (unpack z) ∈ closedBall
      ((T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0)) (commonRadius : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
      atTop (nhds (realEmbed ((GroundOriginalOffsets.roundedRoot i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ
      ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        (GroundOriginalOffsets.certificates i).κ (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
          (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      dist ((T i).symm (unpack ((nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)))
        ((T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0)) ≤
        ((rate i : ℝ)^n)*dist ((T i).symm (unpack z))
          ((T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0)) :=
  whole_background_box_explicit_native_basin i (GroundOriginalOffsets.rounded_inputs_sound i)
    (common_ball_entry i hz)

theorem actual_rounded_negative_explicit_basin (i : Fin 18) {z : ComplexField}
    (hz : (T i).symm (unpack z) ∈ closedBall
      ((T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) (commonRadius : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)
      atTop (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ
      ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        (GroundOriginalOffsets.certificates i).κ (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
          (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z) ∧
      dist ((T i).symm (unpack ((nativeUpdate GroundNativeControls.originalTolerance
        (GroundOriginalOffsets.rounded_b i) (GroundOriginalOffsets.certificates i).κ (1/2))^[n] z)))
        ((T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤
        ((rate i : ℝ)^n)*dist ((T i).symm (unpack z))
          ((T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) :=
  whole_background_box_explicit_negative_native_basin i (GroundOriginalOffsets.rounded_inputs_sound i)
    (common_ball_entry i hz)

theorem zero_native_row_budget_rejected : ¬
    (∑ j : Fin 8, ((((data 0).c.derivativeBox (j.castAdd 8)).R 0).bound+
      (((data 0).c.derivativeBox (Fin.natAdd 8 j)).R 0).bound)) ≤ 0 := by decide +kernel

end
end SbtCosmo.Derivation.GroundOriginalOffsetBasins
