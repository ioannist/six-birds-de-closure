import SbtCosmo.Derivation.NativePairCertificates
namespace NativePairDensity
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox Metric NativePairCertificates NativeTransportPowers

def siteDensity (x : State) (i : Fin 8) : ℝ := (x.1 i)^2+(x.2 i)^2
def densityBox (B : StateBox) (i : Fin 8) : Interval :=
  ((B.R i).mul (B.R i)).add ((B.I i).mul (B.I i))

theorem density_sound {B : StateBox} {x : State} (hx : B.Contains x) (i : Fin 8) :
    (densityBox B i).Contains (siteDensity x i) := by
  simpa only [siteDensity,pow_two] using
    Interval.add_sound (Interval.mul_sound (hx i).1 (hx i).1) (Interval.mul_sound (hx i).2 (hx i).2)

variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State}

theorem pair_gap (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall p.first.center (p.first.radius : ℝ)) {i : Fin 8} {g : ℚ}
    (hg : g < (densityBox p.second.jet.input i).lo-(densityBox p.first.jet.input i).hi) :
    (g : ℝ) < siteDensity (T (Data.f (T := T) (κ := κ) (τ := τ) b x)) i-siteDensity (T x) i := by
  have h₀ := density_sound (p.first.input_on_ball hx) i
  have h₁ := density_sound (p.second.input_on_ball
    (next_on_ball p.first p.second hb p.seam p.intermediate_radius hx)) i
  have hgr : (g : ℝ) < ((densityBox p.second.jet.input i).lo : ℝ)-((densityBox p.first.jet.input i).hi : ℝ) := by exact_mod_cast hg
  linarith [h₀.2,h₁.1]

theorem complex_density (x : State) (i : Fin 8) :
    Complex.normSq (pack x i) = siteDensity x i := by
  simp only [Complex.normSq_apply,pack,siteDensity,pow_two]
end
end NativePairDensity
