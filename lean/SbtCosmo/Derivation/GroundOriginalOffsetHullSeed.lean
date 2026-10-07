import SbtCosmo.Derivation.GroundOffsetTransport.Point000
import SbtCosmo.Derivation.GroundOffsetTransport.Point001
import SbtCosmo.Derivation.GroundOffsetTransport.Point002
import SbtCosmo.Derivation.GroundOffsetTransport.Point003
import SbtCosmo.Derivation.GroundOffsetTransport.Point004
import SbtCosmo.Derivation.GroundOffsetTransport.Point005
import SbtCosmo.Derivation.GroundOffsetTransport.Point006
import SbtCosmo.Derivation.GroundOffsetTransport.Point007
import SbtCosmo.Derivation.GroundOffsetTransport.Point008
import SbtCosmo.Derivation.GroundOffsetTransport.Point009
import SbtCosmo.Derivation.GroundOffsetTransport.Point010
import SbtCosmo.Derivation.GroundOffsetTransport.Point011
import SbtCosmo.Derivation.GroundOffsetTransport.Point012
import SbtCosmo.Derivation.GroundOffsetTransport.Point013
import SbtCosmo.Derivation.GroundOffsetTransport.Point014
import SbtCosmo.Derivation.GroundOffsetTransport.Point015
import SbtCosmo.Derivation.GroundOffsetTransport.Point016
import SbtCosmo.Derivation.GroundOffsetTransport.Point017

/-! Original-seed returns for every fixed background in all eighteen certified
boxes. This includes the exact uniform-offset and saved rounded-input models. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsetHullSeed
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundOffsetTransportReturn
open Filter Metric
open scoped Topology

structure Data (i : Fin 18) where
  N : ℕ
  δ : ℚ
  c : Prefix i N
  nonneg : 0 ≤ δ
  distance : ∀ {b : Field} (hb : ∀ j, (β i j).Contains (b j)),
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤ (δ : ℝ)
  entry : ∀ {b : Field} (hb : ∀ j, (β i j).Contains (b j)),
    (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)

def data : (i : Fin 18) → Data i :=
  Fin.cases ⟨GroundOffsetTransport.Point000.N, GroundOffsetTransport.Point000.δ, GroundOffsetTransport.Point000.certificate, GroundOffsetTransport.Point000.entry_arithmetic.1, GroundOffsetTransport.Point000.distance, GroundOffsetTransport.Point000.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point001.N, GroundOffsetTransport.Point001.δ, GroundOffsetTransport.Point001.certificate, GroundOffsetTransport.Point001.entry_arithmetic.1, GroundOffsetTransport.Point001.distance, GroundOffsetTransport.Point001.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point002.N, GroundOffsetTransport.Point002.δ, GroundOffsetTransport.Point002.certificate, GroundOffsetTransport.Point002.entry_arithmetic.1, GroundOffsetTransport.Point002.distance, GroundOffsetTransport.Point002.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point003.N, GroundOffsetTransport.Point003.δ, GroundOffsetTransport.Point003.certificate, GroundOffsetTransport.Point003.entry_arithmetic.1, GroundOffsetTransport.Point003.distance, GroundOffsetTransport.Point003.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point004.N, GroundOffsetTransport.Point004.δ, GroundOffsetTransport.Point004.certificate, GroundOffsetTransport.Point004.entry_arithmetic.1, GroundOffsetTransport.Point004.distance, GroundOffsetTransport.Point004.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point005.N, GroundOffsetTransport.Point005.δ, GroundOffsetTransport.Point005.certificate, GroundOffsetTransport.Point005.entry_arithmetic.1, GroundOffsetTransport.Point005.distance, GroundOffsetTransport.Point005.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point006.N, GroundOffsetTransport.Point006.δ, GroundOffsetTransport.Point006.certificate, GroundOffsetTransport.Point006.entry_arithmetic.1, GroundOffsetTransport.Point006.distance, GroundOffsetTransport.Point006.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point007.N, GroundOffsetTransport.Point007.δ, GroundOffsetTransport.Point007.certificate, GroundOffsetTransport.Point007.entry_arithmetic.1, GroundOffsetTransport.Point007.distance, GroundOffsetTransport.Point007.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point008.N, GroundOffsetTransport.Point008.δ, GroundOffsetTransport.Point008.certificate, GroundOffsetTransport.Point008.entry_arithmetic.1, GroundOffsetTransport.Point008.distance, GroundOffsetTransport.Point008.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point009.N, GroundOffsetTransport.Point009.δ, GroundOffsetTransport.Point009.certificate, GroundOffsetTransport.Point009.entry_arithmetic.1, GroundOffsetTransport.Point009.distance, GroundOffsetTransport.Point009.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point010.N, GroundOffsetTransport.Point010.δ, GroundOffsetTransport.Point010.certificate, GroundOffsetTransport.Point010.entry_arithmetic.1, GroundOffsetTransport.Point010.distance, GroundOffsetTransport.Point010.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point011.N, GroundOffsetTransport.Point011.δ, GroundOffsetTransport.Point011.certificate, GroundOffsetTransport.Point011.entry_arithmetic.1, GroundOffsetTransport.Point011.distance, GroundOffsetTransport.Point011.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point012.N, GroundOffsetTransport.Point012.δ, GroundOffsetTransport.Point012.certificate, GroundOffsetTransport.Point012.entry_arithmetic.1, GroundOffsetTransport.Point012.distance, GroundOffsetTransport.Point012.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point013.N, GroundOffsetTransport.Point013.δ, GroundOffsetTransport.Point013.certificate, GroundOffsetTransport.Point013.entry_arithmetic.1, GroundOffsetTransport.Point013.distance, GroundOffsetTransport.Point013.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point014.N, GroundOffsetTransport.Point014.δ, GroundOffsetTransport.Point014.certificate, GroundOffsetTransport.Point014.entry_arithmetic.1, GroundOffsetTransport.Point014.distance, GroundOffsetTransport.Point014.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point015.N, GroundOffsetTransport.Point015.δ, GroundOffsetTransport.Point015.certificate, GroundOffsetTransport.Point015.entry_arithmetic.1, GroundOffsetTransport.Point015.distance, GroundOffsetTransport.Point015.entry⟩ (
  Fin.cases ⟨GroundOffsetTransport.Point016.N, GroundOffsetTransport.Point016.δ, GroundOffsetTransport.Point016.certificate, GroundOffsetTransport.Point016.entry_arithmetic.1, GroundOffsetTransport.Point016.distance, GroundOffsetTransport.Point016.entry⟩ (
  fun _ => ⟨GroundOffsetTransport.Point017.N, GroundOffsetTransport.Point017.δ, GroundOffsetTransport.Point017.certificate, GroundOffsetTransport.Point017.entry_arithmetic.1, GroundOffsetTransport.Point017.distance, GroundOffsetTransport.Point017.entry⟩)))))))))))))))))

theorem entry_times : ∀ i : Fin 18, 15 ≤ (data i).N ∧ (data i).N ≤ 65 := by decide +kernel

theorem whole_background_box_original_seed_return (i : Fin 18) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) :
    Tendsto (orbit i b) atTop (nhds (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hb).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) (orbit i b n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) (orbit i b n) ∧
      complexNormSq (orbit i b n) = 1 :=
  whole_seed_return i (data i).c hb ((data i).entry hb)

theorem whole_background_box_original_geometric_tail (i : Fin 18) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) (n : ℕ) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b (n+(data i).N))))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤
      (GroundOriginalOffsetBasins.rate i : ℝ)^n * ((data i).δ : ℝ) := by
  exact (whole_seed_geometric_tail i hb ((data i).entry hb) n).trans
    (mul_le_mul_of_nonneg_left ((data i).distance hb) (pow_nonneg (GroundOriginalOffsetBasins.rate i).property n))

theorem exact_root_identity (i : Fin 18) :
    GroundOriginalOffsetStability.wholeRoot i (GroundOriginalOffsets.exact_inputs_sound i) =
      GroundOriginalOffsets.root i := rfl

theorem rounded_root_identity (i : Fin 18) :
    GroundOriginalOffsetStability.wholeRoot i (GroundOriginalOffsets.rounded_inputs_sound i) =
      GroundOriginalOffsets.roundedRoot i := rfl

theorem exact_uniform_offset_original_seed_return (i : Fin 18) :
    Tendsto (orbit i (GroundOriginalOffsets.b i)) atTop
      (nhds (realEmbed (-(GroundOriginalOffsets.root i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i) (κ i : ℝ)
        (orbit i (GroundOriginalOffsets.b i) n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i) (κ i : ℝ) (1/2)
        (orbit i (GroundOriginalOffsets.b i) n) ∧
      complexNormSq (orbit i (GroundOriginalOffsets.b i) n) = 1 := by
  simpa only [exact_root_identity] using
    whole_background_box_original_seed_return i (GroundOriginalOffsets.exact_inputs_sound i)

theorem rounded_original_seed_return (i : Fin 18) :
    Tendsto (orbit i (GroundOriginalOffsets.rounded_b i)) atTop
      (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ)
        (orbit i (GroundOriginalOffsets.rounded_b i) n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2)
        (orbit i (GroundOriginalOffsets.rounded_b i) n) ∧
      complexNormSq (orbit i (GroundOriginalOffsets.rounded_b i) n) = 1 := by
  simpa only [rounded_root_identity] using
    whole_background_box_original_seed_return i (GroundOriginalOffsets.rounded_inputs_sound i)

theorem whole_background_box_original_density_limit (i : Fin 18) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) (j : Fin 8) :
    Tendsto (fun n : ℕ => Complex.normSq (orbit i b n j)) atTop
      (nhds (Complex.normSq (realEmbed (GroundOriginalOffsetStability.wholeRoot i hb).1 j))) := by
  have hc : Continuous (fun x : ComplexField => Complex.normSq (x j)) := by fun_prop
  have ht := (hc.tendsto (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hb).1))).comp
    (whole_background_box_original_seed_return i hb).1
  simpa only [realEmbed,Pi.neg_apply,Complex.normSq_ofReal,mul_neg,neg_mul,neg_neg] using ht

theorem whole_background_box_eventual_density_separation {b₀ b₁ : Field}
    (h₀ : ∀ j, (β 0 j).Contains (b₀ j)) (h₁ : ∀ j, (β 17 j).Contains (b₁ j)) :
    ∀ᶠ n : ℕ in atTop, Complex.normSq (orbit 0 b₀ n 0)+9/100 < Complex.normSq (orbit 17 b₁ n 0) := by
  have h0 := whole_background_box_original_density_limit 0 h₀ 0
  have h17 := whole_background_box_original_density_limit 17 h₁ 0
  have hp : 0 < (GroundOriginalOffsetStability.wholeRoot 0 h₀).1 0 :=
    (GroundOriginalOffsetStability.tube 0 h₀).field_positive _
      (GroundOriginalOffsetStability.whole_root_return 0 h₀).1 0
  have hf := GroundOriginalOffsets.field_coordinate_separation
    (GroundOriginalOffsetBasins.root_field_box 0 h₀ 0) (GroundOriginalOffsetBasins.root_field_box 17 h₁ 0)
  have hg : Complex.normSq (realEmbed (GroundOriginalOffsetStability.wholeRoot 0 h₀).1 0)+9/100 <
      Complex.normSq (realEmbed (GroundOriginalOffsetStability.wholeRoot 17 h₁).1 0) := by
    simp only [realEmbed,Complex.normSq_ofReal,← pow_two]
    exact GroundOriginalOffsets.density_separation_of_positive hp hf
  have he := (tendsto_order.mp (h17.sub h0)).1 (9/100) (by linarith)
  filter_upwards [he] with n hn
  linarith
end
end SbtCosmo.Derivation.GroundOriginalOffsetHullSeed
