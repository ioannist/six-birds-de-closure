import SbtCosmo.Derivation.AllocationSample

/-! Actual original local-budget and source-coupled controls.
Each control changes the constraint or the original objective coupling. -/
namespace SbtCosmo.Derivation.AllocationSampleControls
noncomputable section
open AllocationPrice AllocationSensitivity AllocationScreening AllocationSample

def localPrice (i : Fin 32) : ℝ := marginal (weights i) (curvatures i) 0 (budget/32)
def sourceAllocation (s : ℝ) (i : Fin 32) : ℝ := demand (weights i) (curvatures i) s 0

theorem source_kkt (s : ℝ) :
    AllocationKKT weights curvatures (fun _ => s) (sourceAllocation s)
      (mass (sourceAllocation s)) 0 := by
  refine ⟨fun i => demand_nonnegative _ _ _ _,le_rfl,by norm_num,?_,?_,by simp⟩
  · intro i
    exact (demand_certificate (b := s) (p := (0:ℝ)) (weights_positive i) (curvatures_positive i)).1
  · intro i
    exact (demand_certificate (b := s) (p := (0:ℝ)) (weights_positive i) (curvatures_positive i)).2

/-- No constraint on the competitor's total allocation is used. -/
theorem source_unconstrained_optimal (s : ℝ) {x : Fin 32 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    utility weights curvatures (fun _ => s) x ≤
      utility weights curvatures (fun _ => s) (sourceAllocation s)-penalty curvatures (sourceAllocation s) x := by
  have hs := kkt_strong_support (fun i => (weights_positive i).le) (source_kkt s) hx
  simpa only [zero_mul,add_zero] using hs

theorem source_unconstrained_unique (s : ℝ) {x : Fin 32 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hu : utility weights curvatures (fun _ => s) (sourceAllocation s) ≤ utility weights curvatures (fun _ => s) x) :
    sourceAllocation s = x := by
  have hs := source_unconstrained_optimal s hx
  have hp := penalty_nonnegative (fun i => (curvatures_positive i).le)
    (x := sourceAllocation s) (y := x)
  exact (penalty_zero_iff curvatures_positive).mp (by linarith)

theorem local_controls : (∀ i : Fin 32, 0 < localPrice i) ∧
    (1/20:ℝ) < localPrice 1-localPrice 0 := by
  constructor
  · intro i
    simpa only [localPrice,marginal,weights,curvatures,budget,Rat.cast_div,Rat.cast_sub,
      Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,add_zero] using
      (Rat.cast_pos (K := ℝ)).mpr (AllocationSampleData.local_price_control.1 i)
  · simpa only [localPrice,marginal,weights,curvatures,budget,Rat.cast_div,Rat.cast_sub,
      Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,add_zero] using
      (Rat.cast_lt (K := ℝ)).mpr AllocationSampleData.local_price_control.2

theorem local_kkt (i : Fin 32) :
    AllocationKKT (fun _ : Fin 1 => weights i) (fun _ => curvatures i) (fun _ => 0)
      (fun _ => budget/32) (budget/32) (localPrice i) := by
  have hB : 0 < budget/32 := div_pos (by linarith [budget_bounds.1]) (by norm_num)
  have hm : mass (fun _ : Fin 1 => budget/32) = budget/32 := by simp [mass]
  refine ⟨fun _ => hB.le,by rw [hm],(local_controls.1 i).le,fun _ => le_rfl,?_,?_⟩
  · intro _
    simp only [localPrice,sub_self,zero_mul]
  · rw [hm]
    ring

theorem local_selector_return (i : Fin 32) :
    selectedAllocation (fun _ : Fin 1 => weights i) (fun _ => curvatures i) (fun _ => 0)
        (fun _ => weights_positive i) (fun _ => curvatures_positive i) (budget/32) =
      (fun _ => budget/32) ∧
    selectedPrice (fun _ : Fin 1 => weights i) (fun _ => curvatures i) (fun _ => 0)
      (fun _ => weights_positive i) (fun _ => curvatures_positive i) (budget/32) = localPrice i := by
  have hB : 0 < budget/32 := div_pos (by linarith [budget_bounds.1]) (by norm_num)
  exact kkt_unique (fun _ => (weights_positive i).le) (fun _ => curvatures_positive i)
    (selected_kkt (fun _ => weights_positive i) (fun _ => curvatures_positive i) hB.le)
    (local_kkt i) hB

theorem local_selected_prices_unequal :
    selectedPrice (fun _ : Fin 1 => weights 0) (fun _ => curvatures 0) (fun _ => 0)
        (fun _ => weights_positive 0) (fun _ => curvatures_positive 0) (budget/32) ≠
      selectedPrice (fun _ : Fin 1 => weights 1) (fun _ => curvatures 1) (fun _ => 0)
        (fun _ => weights_positive 1) (fun _ => curvatures_positive 1) (budget/32) := by
  rw [(local_selector_return 0).2,(local_selector_return 1).2]
  linarith [local_controls.2]

theorem local_budget_total : mass (fun _ : Fin 32 => budget/32) = budget := by
  simp only [mass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem local_allocation_differs : allocation 0 ≠ (fun _ : Fin 32 => budget/32) := by
  intro he
  have hh := original_heterogeneity
  rw [he] at hh
  exact (lt_irrefl _) hh

theorem source_profile_return : response 0 = sourceAllocation 0 ∧
    response 3 = sourceAllocation (-(1/5)) ∧ response 4 = sourceAllocation (1/5) := by
  refine ⟨?_,?_,?_⟩
  · funext i
    unfold response sourceAllocation
    rw [demand_offset_return]
    congr 1
    norm_num [AllocationSampleData.price]
  · funext i
    unfold response sourceAllocation
    rw [demand_offset_return]
    congr 1
    norm_num [AllocationSampleData.price,Matrix.cons_val_three]
  · funext i
    unfold response sourceAllocation
    rw [demand_offset_return]
    congr 1
    norm_num [AllocationSampleData.price,Matrix.cons_val_four]

theorem source_signed_shift_gaps :
    (1/2:ℝ) < sourceAllocation 0 8-sourceAllocation (-(1/5)) 8 ∧
      (1/2:ℝ) < sourceAllocation (1/5) 8-sourceAllocation 0 8 := by
  have h : (1/2:ℝ) < (AllocationSampleData.lower 0 8:ℝ)-(AllocationSampleData.upper 3 8:ℝ) ∧
      (1/2:ℝ) < (AllocationSampleData.lower 4 8:ℝ)-(AllocationSampleData.upper 0 8:ℝ) := by
    constructor
    · simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr AllocationSampleData.source_shift_gaps.1
    · simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr AllocationSampleData.source_shift_gaps.2
  rw [← source_profile_return.1,← source_profile_return.2.1,← source_profile_return.2.2]
  constructor
  · linarith [(response_cells 0 8).1,(response_cells 3 8).2]
  · linarith [(response_cells 4 8).1,(response_cells 0 8).2]

theorem source_offset_mono {s t : ℝ} (hst : s ≤ t) (i : Fin 32) :
    sourceAllocation s i ≤ sourceAllocation t i := by
  simpa only [sourceAllocation,demand_offset_return] using
    demand_antitone (b := (0:ℝ)) (weights_positive i) (curvatures_positive i) (neg_le_neg hst)

theorem source_movement_large {s : ℝ} (hs : s ≤ -(1/5) ∨ (1/5) ≤ s) :
    (1/2:ℝ) < |sourceAllocation s 8-sourceAllocation 0 8| := by
  rcases hs with hn | hp
  · have hm := source_offset_mono hn 8
    have ha := neg_le_abs (sourceAllocation s 8-sourceAllocation 0 8)
    linarith [source_signed_shift_gaps.1]
  · have hm := source_offset_mono hp 8
    have ha := le_abs_self (sourceAllocation s 8-sourceAllocation 0 8)
    linarith [source_signed_shift_gaps.2]

theorem original_source_controls :
    (1/2:ℝ) < |sourceAllocation (offsets 0) 8-sourceAllocation 0 8| ∧
      (1/2:ℝ) < |sourceAllocation (offsets 2) 8-sourceAllocation 0 8| := by
  have hs : offsets 0 < -(1/5:ℝ) ∧ (1/5:ℝ) < offsets 2 := by
    constructor
    · have h := (Rat.cast_lt (K := ℝ)).mpr AllocationSampleData.original_offsets.2.1
      simpa only [offsets,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using h
    · have h := (Rat.cast_lt (K := ℝ)).mpr AllocationSampleData.original_offsets.2.2
      simpa only [offsets,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using h
  exact ⟨source_movement_large (Or.inl hs.1.le),source_movement_large (Or.inr hs.2.le)⟩

end
end SbtCosmo.Derivation.AllocationSampleControls
