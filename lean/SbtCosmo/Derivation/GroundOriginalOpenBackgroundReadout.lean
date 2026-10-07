import SbtCosmo.Derivation.GroundOriginalOpenBackground

/-! Observable returns from the open background construction. Radii are
positive existence witnesses; they do not cover gaps between sampled offsets. -/
namespace SbtCosmo.Derivation.GroundOriginalOpenBackgroundReadout
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration
open GroundOriginalOffsets GroundOriginalOpenBackground Filter Metric
open scoped Topology

def orbit (i : Fin 18) (b : Field) (n : ℕ) : ComplexField :=
  (nativeUpdate GroundNativeControls.originalTolerance b ((certificates i).κ : ℝ) (1/2))^[n]
    GroundOriginalSeed.initial

def density (i : Fin 18) (b : Field) (j : Fin 8) : ℝ :=
  Complex.normSq (realEmbed (localPoint i b).1 j)

theorem density_continuous_at (i : Fin 18) (j : Fin 8) :
    ContinuousAt (fun b : Field => density i b j) (rounded_b i) := by
  have hc : Continuous (fun p : Point => Complex.normSq (realEmbed p.1 j)) := by
    unfold realEmbed
    fun_prop
  exact hc.continuousAt.comp (localPoint_smooth_at i).continuousAt

theorem density_center (i : Fin 18) (j : Fin 8) :
    density i (rounded_b i) j = Complex.normSq (realEmbed (roundedRoot i).1 j) := by
  simp only [density,localPoint_center]

theorem open_background_density_limits (i : Fin 18) :
    ∃ δ > 0, ∀ b ∈ closedBall (rounded_b i) δ, ∀ j : Fin 8,
      Tendsto (fun n : ℕ => Complex.normSq (orbit i b n j)) atTop (nhds (density i b j)) := by
  obtain ⟨δ,hδ,hreturn⟩ := open_background_original_seed_return i
  refine ⟨δ,hδ,fun b hb j => ?_⟩
  have hc : Continuous (fun z : ComplexField => Complex.normSq (z j)) := by fun_prop
  have ht := (hc.tendsto (realEmbed (-(localPoint i b).1))).comp (hreturn b hb).2.2.2.2.2.1
  simpa only [Function.comp_def,orbit,density,realEmbed,Pi.neg_apply,Complex.normSq_ofReal,
    mul_neg,neg_mul,neg_neg] using ht

theorem open_endpoint_density_separation :
    ∃ δ > 0, ∀ b₀ ∈ closedBall (rounded_b 0) δ,
      ∀ b₁ ∈ closedBall (rounded_b 17) δ,
        ∀ᶠ n : ℕ in atTop, Complex.normSq (orbit 0 b₀ n 0) + 9/100 <
          Complex.normSq (orbit 17 b₁ n 0) := by
  have hc : ContinuousAt (fun p : Field × Field => density 17 p.2 0 - density 0 p.1 0)
      (rounded_b 0,rounded_b 17) :=
    (ContinuousAt.comp' (g := fun b : Field => density 17 b 0) (f := Prod.snd)
      (x := (rounded_b 0,rounded_b 17)) (density_continuous_at 17 0) continuousAt_snd).sub
      (ContinuousAt.comp' (g := fun b : Field => density 0 b 0) (f := Prod.fst)
        (x := (rounded_b 0,rounded_b 17)) (density_continuous_at 0 0) continuousAt_fst)
  have hbase : (9/100 : ℝ) < density 17 (rounded_b 17) 0 - density 0 (rounded_b 0) 0 := by
    rw [density_center,density_center]
    linarith [actual_rounded_densities_separated]
  have hsep : ∀ᶠ p : Field × Field in nhds (rounded_b 0,rounded_b 17),
      (9/100 : ℝ) < density 17 p.2 0 - density 0 p.1 0 := hc.eventually (lt_mem_nhds hbase)
  obtain ⟨δs,hδs,hinside⟩ := nhds_basis_closedBall.mem_iff.mp hsep
  obtain ⟨δ0,hδ0,hzero⟩ := open_background_density_limits 0
  obtain ⟨δ1,hδ1,hone⟩ := open_background_density_limits 17
  refine ⟨min δs (min δ0 δ1),lt_min hδs (lt_min hδ0 hδ1),fun b₀ hb₀ b₁ hb₁ => ?_⟩
  have h0 : b₀ ∈ closedBall (rounded_b 0) δ0 := mem_closedBall.mpr
    ((mem_closedBall.mp hb₀).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h1 : b₁ ∈ closedBall (rounded_b 17) δ1 := mem_closedBall.mpr
    ((mem_closedBall.mp hb₁).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hp : (b₀,b₁) ∈ closedBall (rounded_b 0,rounded_b 17) δs := by
    rw [mem_closedBall,Prod.dist_eq]
    exact max_le ((mem_closedBall.mp hb₀).trans (min_le_left _ _))
      ((mem_closedBall.mp hb₁).trans (min_le_left _ _))
  have ht := (hone b₁ h1 0).sub (hzero b₀ h0 0)
  filter_upwards [ht.eventually (lt_mem_nhds (hinside hp))] with n hn
  linarith
end
end SbtCosmo.Derivation.GroundOriginalOpenBackgroundReadout
