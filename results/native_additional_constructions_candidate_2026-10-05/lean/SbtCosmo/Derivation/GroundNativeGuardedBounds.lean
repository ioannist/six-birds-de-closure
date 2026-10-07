import SbtCosmo.Derivation.GroundNativeEscape
import SbtCosmo.Derivation.GroundComplexEuclidean

/-! Global bounds for the exact mathematical normalized source.
The all-orbit statement retains its legality premise. No value of the total
normalization formula at zero is attributed to an actual source execution. -/
namespace SbtCosmo.Derivation.GroundNativeGuardedBounds
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativeIteration GroundComplexEuclidean
open scoped BigOperators

theorem density_le_one {z : ComplexField} (hz : complexNormSq z = 1) (i : Fin 8) :
    Complex.normSq (z i) ≤ 1 := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 8))) => Complex.normSq_nonneg (z j))
    (Finset.mem_univ i)
  change Complex.normSq (z i) ≤ complexNormSq z at h
  simpa only [hz] using h

theorem component_norm_le_one {z : ComplexField} (hz : complexNormSq z = 1) (i : Fin 8) :
    ‖z i‖ ≤ 1 := by
  have h := density_le_one hz i
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (z i)]

theorem gradient_norm_le_one {z : ComplexField} (hz : complexNormSq z = 1) (i : Fin 8) :
    ‖complexGradient z i‖ ≤ 1 := by
  have h := norm_sub_le (z (next i)) (z (prev i))
  have hnext := component_norm_le_one hz (next i)
  have hprev := component_norm_le_one hz (prev i)
  simp only [complexGradient, norm_div, Complex.norm_ofNat]
  linarith

theorem gradient_energy_le_one {z : ComplexField} (hz : complexNormSq z = 1) (i : Fin 8) :
    Complex.normSq (complexGradient z i) ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [gradient_norm_le_one hz i, norm_nonneg (complexGradient z i)]

theorem source_potential_bound {z : ComplexField} (hz : complexNormSq z = 1)
    (b : Field) (κ : ℝ) (i : Fin 8) :
    |complexSourcePotential b κ z i| ≤ |b i| + |κ| * (1 + |b i|) := by
  have hd := density_le_one hz i
  have hg := gradient_energy_le_one hz i
  have hd0 := Complex.normSq_nonneg (z i)
  have hg0 := Complex.normSq_nonneg (complexGradient z i)
  have hb : |b i * Complex.normSq (z i)| ≤ |b i| := by
    rw [abs_mul, abs_of_nonneg hd0]
    exact mul_le_of_le_one_right (abs_nonneg _) hd
  have hinner : |Complex.normSq (complexGradient z i) + b i * Complex.normSq (z i)| ≤
      1 + |b i| := by
    calc
      _ ≤ |Complex.normSq (complexGradient z i)| + |b i * Complex.normSq (z i)| := abs_add_le _ _
      _ ≤ 1 + |b i| := by rw [abs_of_nonneg hg0]; exact add_le_add hg hb
  unfold complexSourcePotential BackgroundSelection.potential
  calc
    _ ≤ |b i| + |κ * (Complex.normSq (complexGradient z i) + b i * Complex.normSq (z i))| := abs_add_le _ _
    _ ≤ |b i| + |κ| * (1 + |b i|) := by
      rw [abs_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner (abs_nonneg κ))

theorem legal_update_potential_bound {z : ComplexField} {τ κ m : ℝ} {b : Field}
    (hτ : 0 ≤ τ) (hg : NativeLegal τ b κ m z) (i : Fin 8) :
    |complexSourcePotential b κ (nativeUpdate τ b κ m z) i| ≤
      |b i| + |κ| * (1 + |b i|) :=
  source_potential_bound (GroundNativeEscape.nativeUpdate_unit hτ hg) b κ i

/-- Uniform in time for every guarded source orbit, without any convergence,
ground-entry, coupling-window or local contraction premise. -/
theorem guarded_orbit_unit_and_potential {z : ComplexField} {τ κ m : ℝ} {b : Field}
    (hτ : 0 ≤ τ) (hz : complexNormSq z = 1)
    (hg : ∀ n : ℕ, NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z)) (n : ℕ) :
    complexNormSq ((nativeUpdate τ b κ m)^[n] z) = 1 ∧
      ∀ i : Fin 8, |complexSourcePotential b κ ((nativeUpdate τ b κ m)^[n] z) i| ≤
        |b i| + |κ| * (1 + |b i|) := by
  have hu : complexNormSq ((nativeUpdate τ b κ m)^[n] z) = 1 := by
    cases n with
    | zero => exact hz
    | succ n =>
      rw [Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit hτ (hg n)
  exact ⟨hu, fun i => source_potential_bound hu b κ i⟩
end
end SbtCosmo.Derivation.GroundNativeGuardedBounds
