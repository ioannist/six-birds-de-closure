import SbtCosmo.Derivation.GroundOffsetPrefix.Point000
import SbtCosmo.Derivation.GroundOffsetPrefix.Point001
import SbtCosmo.Derivation.GroundOffsetPrefix.Point002
import SbtCosmo.Derivation.GroundOffsetPrefix.Point003
import SbtCosmo.Derivation.GroundOffsetPrefix.Point004
import SbtCosmo.Derivation.GroundOffsetPrefix.Point005
import SbtCosmo.Derivation.GroundOffsetPrefix.Point006
import SbtCosmo.Derivation.GroundOffsetPrefix.Point007
import SbtCosmo.Derivation.GroundOffsetPrefix.Point008
import SbtCosmo.Derivation.GroundOffsetPrefix.Point009
import SbtCosmo.Derivation.GroundOffsetPrefix.Point010
import SbtCosmo.Derivation.GroundOffsetPrefix.Point011
import SbtCosmo.Derivation.GroundOffsetPrefix.Point012
import SbtCosmo.Derivation.GroundOffsetPrefix.Point013
import SbtCosmo.Derivation.GroundOffsetPrefix.Point014
import SbtCosmo.Derivation.GroundOffsetPrefix.Point015
import SbtCosmo.Derivation.GroundOffsetPrefix.Point016
import SbtCosmo.Derivation.GroundOffsetPrefix.Point017

/-! Closed original-seed infinite returns for all eighteen rounded offset inputs.
The source threshold/phase rule and both initialization normalizations are retained.
Finite sixty-update verdicts and the exact uniform-offset model are separate. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsetSeed
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundOffsetSeedReturn
open Filter Metric
open scoped Topology

structure Data (i : Fin 18) where
  N : ℕ
  δ : ℚ
  c : Prefix i N
  nonneg : 0 ≤ δ
  entry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
    ((GroundOriginalOffsetBasins.data i).ρ : ℝ)
  distance : dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
    ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤ (δ : ℝ)

def data : (i : Fin 18) → Data i :=
  Fin.cases ⟨GroundOffsetPrefix.Point000.N, GroundOffsetPrefix.Point000.δ, GroundOffsetPrefix.Point000.certificate, GroundOffsetPrefix.Point000.entry_margin.1, GroundOffsetPrefix.Point000.entry, GroundOffsetPrefix.Point000.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point001.N, GroundOffsetPrefix.Point001.δ, GroundOffsetPrefix.Point001.certificate, GroundOffsetPrefix.Point001.entry_margin.1, GroundOffsetPrefix.Point001.entry, GroundOffsetPrefix.Point001.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point002.N, GroundOffsetPrefix.Point002.δ, GroundOffsetPrefix.Point002.certificate, GroundOffsetPrefix.Point002.entry_margin.1, GroundOffsetPrefix.Point002.entry, GroundOffsetPrefix.Point002.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point003.N, GroundOffsetPrefix.Point003.δ, GroundOffsetPrefix.Point003.certificate, GroundOffsetPrefix.Point003.entry_margin.1, GroundOffsetPrefix.Point003.entry, GroundOffsetPrefix.Point003.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point004.N, GroundOffsetPrefix.Point004.δ, GroundOffsetPrefix.Point004.certificate, GroundOffsetPrefix.Point004.entry_margin.1, GroundOffsetPrefix.Point004.entry, GroundOffsetPrefix.Point004.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point005.N, GroundOffsetPrefix.Point005.δ, GroundOffsetPrefix.Point005.certificate, GroundOffsetPrefix.Point005.entry_margin.1, GroundOffsetPrefix.Point005.entry, GroundOffsetPrefix.Point005.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point006.N, GroundOffsetPrefix.Point006.δ, GroundOffsetPrefix.Point006.certificate, GroundOffsetPrefix.Point006.entry_margin.1, GroundOffsetPrefix.Point006.entry, GroundOffsetPrefix.Point006.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point007.N, GroundOffsetPrefix.Point007.δ, GroundOffsetPrefix.Point007.certificate, GroundOffsetPrefix.Point007.entry_margin.1, GroundOffsetPrefix.Point007.entry, GroundOffsetPrefix.Point007.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point008.N, GroundOffsetPrefix.Point008.δ, GroundOffsetPrefix.Point008.certificate, GroundOffsetPrefix.Point008.entry_margin.1, GroundOffsetPrefix.Point008.entry, GroundOffsetPrefix.Point008.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point009.N, GroundOffsetPrefix.Point009.δ, GroundOffsetPrefix.Point009.certificate, GroundOffsetPrefix.Point009.entry_margin.1, GroundOffsetPrefix.Point009.entry, GroundOffsetPrefix.Point009.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point010.N, GroundOffsetPrefix.Point010.δ, GroundOffsetPrefix.Point010.certificate, GroundOffsetPrefix.Point010.entry_margin.1, GroundOffsetPrefix.Point010.entry, GroundOffsetPrefix.Point010.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point011.N, GroundOffsetPrefix.Point011.δ, GroundOffsetPrefix.Point011.certificate, GroundOffsetPrefix.Point011.entry_margin.1, GroundOffsetPrefix.Point011.entry, GroundOffsetPrefix.Point011.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point012.N, GroundOffsetPrefix.Point012.δ, GroundOffsetPrefix.Point012.certificate, GroundOffsetPrefix.Point012.entry_margin.1, GroundOffsetPrefix.Point012.entry, GroundOffsetPrefix.Point012.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point013.N, GroundOffsetPrefix.Point013.δ, GroundOffsetPrefix.Point013.certificate, GroundOffsetPrefix.Point013.entry_margin.1, GroundOffsetPrefix.Point013.entry, GroundOffsetPrefix.Point013.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point014.N, GroundOffsetPrefix.Point014.δ, GroundOffsetPrefix.Point014.certificate, GroundOffsetPrefix.Point014.entry_margin.1, GroundOffsetPrefix.Point014.entry, GroundOffsetPrefix.Point014.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point015.N, GroundOffsetPrefix.Point015.δ, GroundOffsetPrefix.Point015.certificate, GroundOffsetPrefix.Point015.entry_margin.1, GroundOffsetPrefix.Point015.entry, GroundOffsetPrefix.Point015.distance⟩ (
  Fin.cases ⟨GroundOffsetPrefix.Point016.N, GroundOffsetPrefix.Point016.δ, GroundOffsetPrefix.Point016.certificate, GroundOffsetPrefix.Point016.entry_margin.1, GroundOffsetPrefix.Point016.entry, GroundOffsetPrefix.Point016.distance⟩ (
  fun _ => ⟨GroundOffsetPrefix.Point017.N, GroundOffsetPrefix.Point017.δ, GroundOffsetPrefix.Point017.certificate, GroundOffsetPrefix.Point017.entry_margin.1, GroundOffsetPrefix.Point017.entry, GroundOffsetPrefix.Point017.distance⟩)))))))))))))))))

theorem entry_times : ∀ i : Fin 18, 15 ≤ (data i).N ∧ (data i).N ≤ 65 := by decide +kernel

theorem rounded_original_seed_return (i : Fin 18) :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b i) ((GroundOriginalOffsets.certificates i).κ : ℝ) (1/2))^[n]
        GroundOriginalSeed.initial) atTop (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        ((GroundOriginalOffsets.certificates i).κ : ℝ)
        ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
          ((GroundOriginalOffsets.certificates i).κ : ℝ) (1/2))^[n] GroundOriginalSeed.initial) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        ((GroundOriginalOffsets.certificates i).κ : ℝ) (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
          ((GroundOriginalOffsets.certificates i).κ : ℝ) (1/2))^[n] GroundOriginalSeed.initial) ∧
      complexNormSq ((nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i)
        ((GroundOriginalOffsets.certificates i).κ : ℝ) (1/2))^[n] GroundOriginalSeed.initial) = 1 :=
  rounded_seed_return i (data i).c (data i).entry

theorem rounded_original_geometric_tail (i : Fin 18) (n : ℕ) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i (n+(data i).N))))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤
      (GroundOriginalOffsetBasins.rate i : ℝ)^n * ((data i).δ : ℝ) := by
  exact (rounded_seed_geometric_tail i (data i).entry n).trans
    (mul_le_mul_of_nonneg_left (data i).distance (pow_nonneg (GroundOriginalOffsetBasins.rate i).property n))

theorem all_original_prefix_enclosed (i : Fin 18) (j : Fin ((data i).N+1)) :
    ((data i).c.boxes j).Contains (unpack (orbit i j.val)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      (data i).c.enclosed (background_sound i) j

theorem rounded_original_density_limit (i : Fin 18) (j : Fin 8) :
    Tendsto (fun n : ℕ => Complex.normSq (orbit i n j)) atTop
      (nhds (Complex.normSq (realEmbed (GroundOriginalOffsets.roundedRoot i).1 j))) := by
  have hc : Continuous (fun x : ComplexField => Complex.normSq (x j)) := by fun_prop
  have ht := (hc.tendsto (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))).comp
    (rounded_original_seed_return i).1
  simpa only [realEmbed,Pi.neg_apply,Complex.normSq_ofReal,mul_neg,neg_mul,neg_neg] using ht

theorem eventual_original_density_separation : ∀ᶠ n : ℕ in atTop,
    Complex.normSq (orbit 0 n 0)+9/100 < Complex.normSq (orbit 17 n 0) := by
  have h0 := rounded_original_density_limit 0 0
  have h17 := rounded_original_density_limit 17 0
  have hgap := GroundOriginalOffsets.actual_rounded_densities_separated
  have he := (tendsto_order.mp (h17.sub h0)).1 (9/100) (by linarith)
  filter_upwards [he] with n hn
  linarith

theorem zero_entry_budget_rejected : ¬
    (((((GroundOriginalOffsetBasins.data 0).c).coordinateBox
      (GroundCertifiedNativeEntry.differenceBox GroundOffsetPrefix.Point000.entryBox
        GroundOffsetPrefix.Point000.targetBox)).R 0).bound) ≤ 0 := by decide +kernel

end
end SbtCosmo.Derivation.GroundOriginalOffsetSeed
