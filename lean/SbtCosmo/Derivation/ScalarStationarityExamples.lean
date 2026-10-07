import SbtCosmo.Derivation.ScalarSchurStationarity
import SbtCosmo.Derivation.ExtendedClosurePriceExamples
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Original infinite-cost Schur return, scalar price uniqueness, and a genuinely
nonsmooth energy with a smooth actual budget value. -/
namespace SbtCosmo.Derivation.ScalarStationarityExamples
noncomputable section
open Set Filter ExtendedClosurePrice ConvexSubgradient
open scoped Topology Matrix Matrix.Norms.Elementwise

theorem extended_relative_interior :
    (1 : ℝ) ∈ intrinsicInterior ℝ (finiteDomain univ ExtendedClosurePriceExamples.objective) := by
  apply interior_subset_intrinsicInterior
  rw [ExtendedClosurePriceExamples.objective_domain,interior_Ici]
  norm_num

/-- Same-price sensitivity and stationarity of the actual extended Schur
example. All derivative, finite-value, optimizer and qualification inputs are
proved before the generic theorem is applied. -/
theorem constructed_extended_schur_stationarity :
    ∃ q η : ℝ →L[ℝ] ℝ, Subgradient ExtendedClosurePriceExamples.objective 1 q ∧
      NormalCone univ 1 η ∧
      q+SchurDifferential.traceAdjoint
        (fderiv ℝ (fun x => SbtCosmo.Adequacy.Support.residual
          (0 : Matrix (Fin 1) (Fin 1) ℝ) (SchurClosurePriceExamples.probe x)) 1) 1+η=0 ∧
      DualCertificate univ ExtendedClosurePriceExamples.objective SchurClosurePriceExamples.energy 1 1 1 ∧
      dualValue univ ExtendedClosurePriceExamples.objective SchurClosurePriceExamples.energy 1 1=(1 : EReal) := by
  have hstar : PrimalOptimum univ ExtendedClosurePriceExamples.objective SchurClosurePriceExamples.energy 1 1 := by
    simpa using ExtendedClosurePriceExamples.sqrt_primal_optimum
      (by norm_num : (0 : ℝ)<1) (by norm_num : (1 : ℝ)<4)
  have hAr : (1 : ℝ) ∈ intrinsicInterior ℝ (univ : Set ℝ) :=
    interior_subset_intrinsicInterior (by simp)
  obtain ⟨p,q,η,hp,_,_,hc,hdual,hq,hη,hstation,_⟩ :=
    ScalarSchurStationarity.positive_price_stationarity Matrix.PosSemidef.one
      (0 : Matrix (Fin 1) (Fin 1) ℝ) SchurClosurePriceExamples.probe
      ExtendedClosurePriceExamples.objective_no_bottom ExtendedClosurePriceExamples.objective_epigraph_convex
      convex_univ extended_relative_interior hAr hstar
      (by norm_num : (1 : ℝ) ∈ Ioo 0 4)
      (fun T hT => ExtendedClosurePriceExamples.local_finiteness hT.1 hT.2)
      ExtendedClosurePriceExamples.actual_value_derivative (by norm_num : (-1 : ℝ)<0)
  norm_num at hp
  subst p
  refine ⟨q,η,hq,hη,by simpa only [one_smul] using hstation,hc,?_⟩
  exact hdual.trans ExtendedClosurePriceExamples.actual_positive_certificate.2.2

/-- Actual extended budget differentiability fixes every certificate's scalar
price, including a certificate at another optimum. -/
theorem extended_price_unique {p : ℝ} {star : ℝ}
    (hc : DualCertificate univ ExtendedClosurePriceExamples.objective SchurClosurePriceExamples.energy 1 p star) :
    p=1 := by
  have hh := ScalarPriceStationarity.certificate_price_identification
    (fun x _ => ExtendedClosurePriceExamples.objective_no_bottom x) hc
    (by norm_num : (1 : ℝ) ∈ Ioo 0 4)
    (fun T hT => ExtendedClosurePriceExamples.local_finiteness hT.1 hT.2)
    ExtendedClosurePriceExamples.actual_value_derivative
  norm_num at hh
  exact hh

def kinkEnergy (x : ℝ × ℝ) : ℝ := x.1+|x.2|
def kinkObjective (x : ℝ × ℝ) : EReal := (-x.1 : ℝ)

theorem kink_energy_convex : ConvexOn ℝ univ kinkEnergy := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb _
  have hh := abs_add_le (a*x.2) (b*y.2)
  rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] at hh
  change a*x.1+b*y.1+|a*x.2+b*y.2| ≤ a*(x.1+|x.2|)+b*(y.1+|y.2|)
  nlinarith only [hh]

theorem kink_objective_convex : Convex ℝ (epigraph univ kinkObjective) := by
  have hh : ConvexOn ℝ univ (fun x : ℝ × ℝ => -x.1) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b _ _ _
    change -(a*x.1+b*y.1) ≤ a*(-x.1)+b*(-y.1)
    linarith
  simpa only [epigraph,kinkObjective,EReal.coe_le_coe_iff] using hh.convex_epigraph

theorem kink_primal_optimum (B : ℝ) :
    PrimalOptimum univ kinkObjective kinkEnergy B (B,0) := by
  refine ⟨mem_univ _,EReal.coe_ne_top _,by simp [kinkEnergy],?_⟩
  intro x _ hx
  apply EReal.coe_le_coe_iff.mpr
  dsimp [kinkEnergy] at hx
  dsimp [kinkObjective]
  linarith [abs_nonneg x.2]

theorem kink_actual_value (B : ℝ) : value univ kinkObjective kinkEnergy B=(-B : ℝ) :=
  optimum_value (kink_primal_optimum B)

theorem kink_actual_derivative (B : ℝ) :
    HasDerivAt (fun T => (value univ kinkObjective kinkEnergy T).toReal) (-1) B := by
  have he : (fun T => (value univ kinkObjective kinkEnergy T).toReal)=(fun T => -T) := by
    funext T
    rw [kink_actual_value,EReal.toReal_coe]
  rw [he]
  simpa using (hasDerivAt_id B).neg

/-- The nonsmooth scope is essential: the actual energy has no derivative at
the optimum, despite a globally differentiable actual value. -/
theorem kink_energy_not_differentiable : ¬ DifferentiableAt ℝ kinkEnergy (0,0) := by
  intro h
  have hp : DifferentiableAt ℝ (fun t : ℝ => ((0 : ℝ),t)) 0 := by fun_prop
  have hh := h.comp 0 hp
  have he : (fun t : ℝ => kinkEnergy ((0 : ℝ),t))=abs := by funext t; simp [kinkEnergy]
  change DifferentiableAt ℝ (fun t : ℝ => kinkEnergy ((0 : ℝ),t)) 0 at hh
  rw [he] at hh
  exact not_differentiableAt_abs_zero hh

/-- No energy derivative, value derivative, dual, stationarity or qualification
is supplied to this concrete application of the nonsmooth full theorem. -/
theorem constructed_nonsmooth_energy_stationarity :
    ∃ q r η : (ℝ × ℝ) →L[ℝ] ℝ, Subgradient kinkObjective (0,0) q ∧
      RealSubgradient kinkEnergy (0,0) r ∧ NormalCone univ (0,0) η ∧ q+r+η=0 ∧
      DualCertificate univ kinkObjective kinkEnergy 0 1 (0,0) ∧
      dualValue univ kinkObjective kinkEnergy 0 1=0 := by
  have hdom : finiteDomain univ kinkObjective=univ := by ext x; simp [finiteDomain,kinkObjective]
  have hC : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (finiteDomain univ kinkObjective) := by
    rw [hdom]
    exact interior_subset_intrinsicInterior (by simp)
  have hAr : (0 : ℝ × ℝ) ∈ intrinsicInterior ℝ (univ : Set (ℝ × ℝ)) :=
    interior_subset_intrinsicInterior (by simp)
  have hbottom : ∀ x, kinkObjective x ≠ ⊥ := fun x => EReal.coe_ne_bot _
  obtain ⟨p,q,r,η,hp,_,_,hc,hdual,hq,hr,hη,hstation⟩ :=
    ScalarPriceStationarity.positive_price_stationarity
      hbottom kink_objective_convex convex_univ kink_energy_convex hC hAr
      (kink_primal_optimum 0) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)
      (fun T _ => by rw [kink_actual_value]; exact ⟨EReal.coe_ne_top _,EReal.coe_ne_bot _⟩)
      (kink_actual_derivative 0) (by norm_num : (-1 : ℝ)<0)
  norm_num at hp
  subst p
  refine ⟨q,r,η,hq,hr,hη,by simpa only [one_smul] using hstation,hc,?_⟩
  rw [hdual,kink_actual_value]
  norm_num

end
end SbtCosmo.Derivation.ScalarStationarityExamples
