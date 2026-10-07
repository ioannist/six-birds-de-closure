import SbtCosmo.Derivation.GroundOriginalOffsetBasins
import SbtCosmo.Derivation.GroundComplexNormBridge
import SbtCosmo.Derivation.GroundOffsetSeedReturn
namespace SbtCosmo.Derivation.GroundOffsetSelectorBudget
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundBorder GroundSourceJacobian GroundNativePhase
open GroundNativeIteration GroundNativeDerivative GroundNativeBox GroundRationalInterval
open GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open Metric
open scoped BigOperators

theorem response_enclosed (c : GroundUncertainNativeBasin.Certificate)
    (hR : c.ResponseArithmetic) (hD : c.ResponseIncluded) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {x : State} (hx : c.input.Contains x)
    (j : Fin 16) (i : Fin 8) :
    (c.DG j i).Contains (selectedDerivative b (c.κ : ℝ) x (c.T (column j)) i) := by
  have hd := GroundUncertainNativeBox.selectedDerivative_enclosed c.ground (hR j) hb hx (c.direction_sound j)
  exact GroundNativeBox.included_sound (hD j i) (hd i)

theorem selector_derivative_bound (c : GroundUncertainNativeBasin.Certificate)
    (hR : c.ResponseArithmetic) (hD : c.ResponseIncluded) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {x : State} (hx : c.input.Contains (c.T x))
    {a : ℚ} (ha : 0 ≤ a)
    (hrows : ∀ i : Fin 8, (∑ j : Fin 8,
      ((c.DG (j.castAdd 8) i).bound+(c.DG (Fin.natAdd 8 j) i).bound)) ≤ a) :
    ‖(selectedDerivative b (c.κ : ℝ) (c.T x)).comp c.T.toContinuousLinearMap‖ ≤ (a : ℝ) := by
  apply GroundStateRows.field_operator_norm_le_rows _ (by exact_mod_cast ha)
  intro i
  calc
    (∑ j, (|((selectedDerivative b (c.κ : ℝ) (c.T x)).comp c.T.toContinuousLinearMap)
        (GroundLocalDynamics.column j,0) i|+
      |((selectedDerivative b (c.κ : ℝ) (c.T x)).comp c.T.toContinuousLinearMap)
        (0,GroundLocalDynamics.column j) i|)) ≤
      ∑ j : Fin 8, (((c.DG (j.castAdd 8) i).bound : ℝ)+((c.DG (Fin.natAdd 8 j) i).bound : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      have hr := Interval.abs_le_bound (response_enclosed c hR hD hb hx (j.castAdd 8) i)
      have hi := Interval.abs_le_bound (response_enclosed c hR hD hb hx (Fin.natAdd 8 j) i)
      rw [column_real] at hr
      rw [column_imag] at hi
      exact add_le_add hr hi
    _ ≤ (a : ℝ) := by
      have hc : ((∑ j : Fin 8, ((c.DG (j.castAdd 8) i).bound+(c.DG (Fin.natAdd 8 j) i).bound) : ℚ) : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast hrows i
      simpa only [Rat.cast_sum,Rat.cast_add] using hc

theorem selector_lipschitz (c : GroundUncertainNativeBasin.Certificate)
    (hR : c.ResponseArithmetic) (hD : c.ResponseIncluded) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {u : Field} {ρ : ℝ}
    (hinput : ∀ x ∈ closedBall (c.T.symm (u,0)) ρ, c.input.Contains (c.T x))
    {a : ℚ} (ha : 0 ≤ a)
    (hrows : ∀ i : Fin 8, (∑ j : Fin 8,
      ((c.DG (j.castAdd 8) i).bound+(c.DG (Fin.natAdd 8 j) i).bound)) ≤ a) :
    LipschitzOnWith ⟨(a : ℝ), by exact_mod_cast ha⟩
      (fun x : State => selected b (c.κ : ℝ) (c.T x)) (closedBall (c.T.symm (u,0)) ρ) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x _ => ((selected_hasFDerivAt b (c.κ : ℝ) (c.T x)).comp x c.T.toContinuousLinearMap.hasFDerivAt).hasFDerivWithinAt)
    (fun x hx => by exact_mod_cast selector_derivative_bound c hR hD hb (hinput x hx) ha hrows)
    (convex_closedBall _ _)

open GroundOffsetSeedReturn GroundComplexEuclidean GroundComplexNormBridge

theorem reflected_tail_in_ball (i : Fin 18) {N : ℕ}
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)) (n : ℕ) :
    (GroundOriginalOffsetBasins.T i).symm (unpack (-orbit i (n+N))) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ) := by
  have h := rounded_seed_geometric_tail i hentry n
  have hq : (GroundOriginalOffsetBasins.rate i : ℝ) ≤ 1 := by
    change ((GroundOriginalOffsetBasins.data i).c.rate : ℝ) ≤ 1
    exact_mod_cast (GroundOriginalOffsetBasins.data i).rows.rate_lt.le
  have hp : (GroundOriginalOffsetBasins.rate i : ℝ)^n ≤ 1 :=
    pow_le_one₀ (GroundOriginalOffsetBasins.rate i).property hq
  have hn := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ dist
    ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
    ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) from dist_nonneg)
  rw [one_mul] at hn
  have he : (GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0) =
      -(GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0) := by
    rw [← map_neg];simp only [Prod.neg_mk,neg_zero]
  rw [mem_closedBall,GroundNativeReflection.unpack_neg,map_neg]
  rw [mem_closedBall] at hentry
  rw [he] at h hentry hn
  have heq := dist_neg_neg ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i (n+N))))
    (-(GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0))
  simp only [neg_neg] at heq
  rw [heq]
  exact h.trans (hn.trans hentry)

theorem euclidean_tail_bound (i : Fin 18) {N : ℕ} {δ : ℚ}
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ))
    (hd : dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤ (δ : ℝ))
    (n : ℕ) : l2 (orbit i (n+N)-realEmbed (-(GroundOriginalOffsets.roundedRoot i).1)) ≤
      4*((GroundOriginalOffsetBasins.data i).s : ℝ)*((GroundOriginalOffsetBasins.rate i : ℝ)^n*(δ : ℝ)) := by
  let T := GroundOriginalOffsetBasins.T i
  let u := (GroundOriginalOffsets.roundedRoot i).1
  have hs := (GroundOriginalOffsetBasins.data i).c.basis_norm
    (GroundOriginalOffsetBasins.data i).basis_nonneg (GroundOriginalOffsetBasins.data i).basis_rows
  have h := T.toContinuousLinearMap.le_opNorm (T.symm (unpack (orbit i (n+N)))-T.symm (-u,0))
  change ‖T (T.symm (unpack (orbit i (n+N)))-T.symm (-u,0))‖ ≤ _ at h
  rw [map_sub,T.apply_symm_apply,T.apply_symm_apply] at h
  have hn : ‖unpack (orbit i (n+N))-(-u,0)‖ ≤
      ((GroundOriginalOffsetBasins.data i).s : ℝ)*((GroundOriginalOffsetBasins.rate i : ℝ)^n*(δ : ℝ)) := by
    have hd' := (rounded_seed_geometric_tail i hentry n).trans
      (mul_le_mul_of_nonneg_left hd (pow_nonneg (GroundOriginalOffsetBasins.rate i).property n))
    rw [dist_eq_norm] at hd'
    exact h.trans (mul_le_mul hs hd' (norm_nonneg _) (by exact_mod_cast (GroundOriginalOffsetBasins.data i).basis_nonneg))
  have he : orbit i (n+N)-realEmbed (-u) = pack (unpack (orbit i (n+N))-(-u,0)) := by
    rw [← packCLE_apply,map_sub,packCLE_apply,packCLE_apply]
    rw [show pack (unpack (orbit i (n+N))) = orbit i (n+N) from packCLE.apply_symm_apply _]
    rfl
  rw [he]
  exact (l2_pack_le _).trans (by nlinarith [hn])

theorem input_on_ball (i : Fin 18) {x : State}
    (hx : x ∈ closedBall ((GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)) :
    (GroundOriginalOffsetBasins.data i).c.input.Contains ((GroundOriginalOffsetBasins.T i) x) := by
  exact (GroundOriginalOffsetBasins.data i).c.input_box_on_ball
    (GroundOriginalOffsetBasins.data i).basis_nonneg
    ((GroundOriginalOffsetBasins.data i).c.basis_norm (GroundOriginalOffsetBasins.data i).basis_nonneg
      (GroundOriginalOffsetBasins.data i).basis_rows)
    (GroundOriginalOffsetBasins.root_field_box i (GroundOriginalOffsets.rounded_inputs_sound i))
    (GroundOriginalOffsetBasins.data i).input_geometry hx

theorem selector_tail_bound (i : Fin 18) {N : ℕ} {δ a : ℚ}
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ))
    (hd : dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤ (δ : ℝ))
    (ha : 0 ≤ a)
    (hrows : ∀ j : Fin 8, (∑ k : Fin 8,
      (((GroundOriginalOffsetBasins.data i).c.DG (k.castAdd 8) j).bound+
       ((GroundOriginalOffsetBasins.data i).c.DG (Fin.natAdd 8 k) j).bound)) ≤ a) (n : ℕ) :
    ‖selected (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (unpack (-orbit i (n+N)))-
      (GroundOriginalOffsets.roundedRoot i).1‖ ≤
      (a : ℝ)*((GroundOriginalOffsetBasins.rate i : ℝ)^n*(δ : ℝ)) := by
  have hb : ∀ j, ((GroundOriginalOffsetBasins.data i).c.β j).Contains (GroundOriginalOffsets.rounded_b i j) := by
    rw [(GroundOriginalOffsetBasins.data i).inputs]
    exact GroundOriginalOffsets.rounded_inputs_sound i
  have hL := selector_lipschitz (GroundOriginalOffsetBasins.data i).c
    (GroundOriginalOffsetBasins.data i).responses (GroundOriginalOffsetBasins.data i).response_included
    hb (fun x hx => input_on_ball i hx) ha hrows
  have hs := GroundOriginalOffsetStability.whole_root_return i (GroundOriginalOffsets.rounded_inputs_sound i)
  have hf : groundMap (GroundOriginalOffsets.rounded_b i) (κ i : ℝ)
      (GroundOriginalOffsets.roundedRoot i).1 = (GroundOriginalOffsets.roundedRoot i).1 := hs.2.2.2
  change groundMap (GroundOriginalOffsets.rounded_b i) ((GroundOriginalOffsets.certificates i).κ : ℝ)
    (GroundOriginalOffsets.roundedRoot i).1 = (GroundOriginalOffsets.roundedRoot i).1 at hf
  have h := hL.dist_le_mul _ (reflected_tail_in_ball i hentry n) _
    (mem_closedBall_self (by exact_mod_cast (GroundOriginalOffsetBasins.data i).radius_pos.le))
  simp only [GroundOriginalOffsetBasins.T,ContinuousLinearEquiv.apply_symm_apply,
    (GroundOriginalOffsetBasins.data i).coupling,selected_real,hf] at h
  have he : (GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0) =
      -(GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0) := by
    rw [← map_neg];simp only [Prod.neg_mk,neg_zero]
  have ht := (rounded_seed_geometric_tail i hentry n).trans
    (mul_le_mul_of_nonneg_left hd (pow_nonneg (GroundOriginalOffsetBasins.rate i).property n))
  rw [he] at ht
  have heq := dist_neg_neg ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i (n+N))))
    (-(GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0))
  simp only [neg_neg] at heq
  rw [← GroundOriginalOffsetBasins.T,GroundNativeReflection.unpack_neg,map_neg,heq] at h
  exact (show ‖selected (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (unpack (-orbit i (n+N)))-
      (GroundOriginalOffsets.roundedRoot i).1‖ ≤ (a : ℝ)*dist
        ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i (n+N))))
        (-(GroundOriginalOffsetBasins.T i).symm ((GroundOriginalOffsets.roundedRoot i).1,0)) from by simpa only [GroundOffsetSeedReturn.κ,GroundNativeReflection.unpack_neg,dist_eq_norm,NNReal.coe_mk] using h).trans
    (mul_le_mul_of_nonneg_left ht (by exact_mod_cast ha))

theorem candidate_distance (i : Fin 18) {N : ℕ} {δ a : ℚ}
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ))
    (hd : dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤ (δ : ℝ))
    (ha : 0 ≤ a)
    (hrows : ∀ j : Fin 8, (∑ k : Fin 8,
      (((GroundOriginalOffsetBasins.data i).c.DG (k.castAdd 8) j).bound+
       ((GroundOriginalOffsetBasins.data i).c.DG (Fin.natAdd 8 k) j).bound)) ≤ a) (n : ℕ) :
    l2 (orbit i (n+N)-(-GroundNativeIteration.nativeCandidate (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (orbit i (n+N)))) ≤
      (4*((GroundOriginalOffsetBasins.data i).s : ℝ)+4*(a : ℝ))*
        ((GroundOriginalOffsetBasins.rate i : ℝ)^n*(δ : ℝ)) := by
  let b := GroundOriginalOffsets.rounded_b i
  let u := (GroundOriginalOffsets.roundedRoot i).1
  have hc : nativeCandidate b (κ i : ℝ) (orbit i (n+N)) =
      realEmbed (selected b (κ i : ℝ) (unpack (-orbit i (n+N)))) := by
    have h := nativeCandidate_pack b (κ i : ℝ) (unpack (-orbit i (n+N)))
    rw [show pack (unpack (-orbit i (n+N))) = -orbit i (n+N) from packCLE.apply_symm_apply _,
      GroundNativeReflection.nativeCandidate_neg] at h
    exact h
  have h := l2_sub_triangle (orbit i (n+N)) (realEmbed (-u))
    (-nativeCandidate b (κ i : ℝ) (orbit i (n+N)))
  have he : realEmbed (-u)-(-nativeCandidate b (κ i : ℝ) (orbit i (n+N))) =
      realEmbed (selected b (κ i : ℝ) (unpack (-orbit i (n+N)))-u) := by
    rw [hc,GroundNativeReflection.realEmbed_neg]
    funext j;simp [realEmbed];ring
  rw [he] at h
  have ht := (l2_realEmbed_le _).trans
    (mul_le_mul_of_nonneg_left (selector_tail_bound i hentry hd ha hrows n) (by norm_num : (0 : ℝ) ≤ 4))
  exact h.trans ((add_le_add (euclidean_tail_bound i hentry hd n) ht).trans (by ring_nf; exact le_rfl))

theorem sourced_potential_bounds (i : Fin 18) {N : ℕ} {A B : ℚ}
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ))
    (hbounds : ∀ j : Fin 8, A ≤ (GroundUncertainNativeBox.sourceBox (GroundOriginalOffsetBasins.data i).c.β
      (GroundOriginalOffsetBasins.data i).c.κ (GroundOriginalOffsetBasins.data i).c.input j).lo ∧
      (GroundUncertainNativeBox.sourceBox (GroundOriginalOffsetBasins.data i).c.β
      (GroundOriginalOffsetBasins.data i).c.κ (GroundOriginalOffsetBasins.data i).c.input j).hi ≤ B)
    (n : ℕ) : ∀ j, (A : ℝ) ≤ complexSourcePotential (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (orbit i (n+N)) j ∧
      complexSourcePotential (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (orbit i (n+N)) j ≤ (B : ℝ) := by
  have hb : ∀ j, ((GroundOriginalOffsetBasins.data i).c.β j).Contains (GroundOriginalOffsets.rounded_b i j) := by
    rw [(GroundOriginalOffsetBasins.data i).inputs]
    exact GroundOriginalOffsets.rounded_inputs_sound i
  have hx := input_on_ball i (reflected_tail_in_ball i hentry n)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  have hp := source_pack (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (unpack (-orbit i (n+N)))
  rw [show pack (unpack (-orbit i (n+N))) = -orbit i (n+N) from packCLE.apply_symm_apply _,
    GroundNativeReflection.complexSourcePotential_neg] at hp
  simp only [GroundOffsetSeedReturn.κ] at hp
  intro j
  have hs := GroundUncertainNativeBox.sourceBox_sound (GroundOriginalOffsetBasins.data i).c.β
    (GroundOriginalOffsetBasins.data i).c.κ hb hx j
  rw [(GroundOriginalOffsetBasins.data i).coupling,← hp] at hs
  have hj := hbounds j
  rw [(GroundOriginalOffsetBasins.data i).coupling] at hj
  exact ⟨(Rat.cast_le.mpr hj.1).trans hs.1,hs.2.trans (Rat.cast_le.mpr hj.2)⟩
end
end SbtCosmo.Derivation.GroundOffsetSelectorBudget
