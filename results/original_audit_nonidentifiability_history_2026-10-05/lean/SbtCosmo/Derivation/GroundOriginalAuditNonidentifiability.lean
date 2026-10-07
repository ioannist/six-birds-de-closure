import SbtCosmo.Derivation.GroundOriginalOffsetSixty
import SbtCosmo.Derivation.GroundOriginalOffsetSeed

/-! The actual original audit verdict does not determine its offset control.
The lower interface is only the Boolean diagnostic or limit-existence readout.
This says nothing about recovery from numerical traces or the complete source,
physical Lambda, background independence, or unrestricted value-law absence. -/
namespace SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState Filter
open scoped Topology

def finiteReadout (i : Fin 18) : Bool := by
  classical
  exact decide (GroundOriginalOffsetSixty.Tests i)

def HasLimit (i : Fin 18) : Prop :=
  ∃ l : ComplexField, Tendsto (GroundOffsetSeedReturn.orbit i) atTop (nhds l)

def limitReadout (i : Fin 18) : Bool := by
  classical
  exact decide (HasLimit i)

theorem offsets_injective : Function.Injective GroundOriginalOffsets.offsets := by
  decide +kernel

theorem finite_readout_eq_verdict (i : Fin 18) :
    finiteReadout i = GroundOriginalOffsetSixty.verdict i := by
  classical
  cases hv : GroundOriginalOffsetSixty.verdict i with
  | false =>
    have hn : ¬ GroundOriginalOffsetSixty.Tests i := by
      intro h
      have hc := (GroundOriginalOffsetSixty.original_sixty_verdict i).mp h
      simp [hv] at hc
    simp [finiteReadout, hn, hv]
  | true =>
    have hp := (GroundOriginalOffsetSixty.original_sixty_verdict i).mpr hv
    simp [finiteReadout, hp, hv]

theorem actual_passing_split_pair :
    GroundOriginalOffsetSixty.Tests 0 ∧ GroundOriginalOffsetSixty.Tests 3 ∧
      finiteReadout 0 = finiteReadout 3 ∧
      GroundOriginalOffsets.offsets 0 ≠ GroundOriginalOffsets.offsets 3 := by
  refine ⟨(GroundOriginalOffsetSixty.original_sixty_verdict 0).mpr (by decide),
    (GroundOriginalOffsetSixty.original_sixty_verdict 3).mpr (by decide), ?_, ?_⟩
  · rw [finite_readout_eq_verdict, finite_readout_eq_verdict]
    decide
  · norm_num [GroundOriginalOffsets.offsets]

theorem finite_admitted_offset_count :
    ((Finset.univ.filter (fun i : Fin 18 => finiteReadout i = true)).image
      GroundOriginalOffsets.offsets).card = 15 := by
  simp only [finite_readout_eq_verdict]
  rw [Finset.card_image_of_injective _ offsets_injective]
  exact GroundOriginalOffsetSixty.passing_count

theorem no_finite_readout_decoder :
    ¬ ∃ decode : Bool → ℚ, ∀ i : Fin 18,
      decode (finiteReadout i) = GroundOriginalOffsets.offsets i := by
  rintro ⟨decode, hd⟩
  have hc : GroundOriginalOffsets.offsets 0 = GroundOriginalOffsets.offsets 3 :=
    (hd 0).symm.trans ((congrArg decode actual_passing_split_pair.2.2.1).trans (hd 3))
  exact actual_passing_split_pair.2.2.2 hc

theorem all_original_has_limit (i : Fin 18) : HasLimit i := by
  refine ⟨realEmbed (-(GroundOriginalOffsets.roundedRoot i).1), ?_⟩
  simpa [GroundOffsetSeedReturn.orbit, GroundOffsetSeedReturn.g,
    GroundOffsetSeedReturn.b, GroundOffsetSeedReturn.κ] using
      (GroundOriginalOffsetSeed.rounded_original_seed_return i).1

theorem limit_readout_true (i : Fin 18) : limitReadout i = true := by
  classical
  simp [limitReadout, all_original_has_limit i]

theorem infinite_admitted_offset_count :
    ((Finset.univ.filter (fun i : Fin 18 => limitReadout i = true)).image
      GroundOriginalOffsets.offsets).card = 18 := by
  have hf : Finset.univ.filter (fun i : Fin 18 => limitReadout i = true) = Finset.univ := by
    ext i
    simp [limit_readout_true]
  rw [hf, Finset.card_image_of_injective _ offsets_injective]
  simp

theorem no_limit_readout_decoder :
    ¬ ∃ decode : Bool → ℚ, ∀ i : Fin 18,
      decode (limitReadout i) = GroundOriginalOffsets.offsets i := by
  rintro ⟨decode, hd⟩
  have hc : GroundOriginalOffsets.offsets 0 = GroundOriginalOffsets.offsets 3 := by
    simpa [limit_readout_true] using (hd 0).symm.trans (hd 3)
  exact actual_passing_split_pair.2.2.2 hc

end
end SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability
