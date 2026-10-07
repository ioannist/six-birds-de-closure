import SbtCosmo.Derivation.GroundUncertainNativeBasin
namespace SbtCosmo.Derivation.GroundNativeTransportGeometry
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundRationalInterval GroundNativeBox Metric

def point (u v : Fin 8 → ℚ) : State := (fun i => (u i : ℝ),fun i => (v i : ℝ))
def around (u v : Fin 8 → ℚ) (ρ s : ℚ) : StateBox where
  R i := ⟨u i-ρ*s,u i+ρ*s⟩
  I i := ⟨v i-ρ*s,v i+ρ*s⟩

theorem point_enclosed (u v : Fin 8 → ℚ) {ρ s : ℚ} (hr : 0 ≤ ρ) (hs : 0 ≤ s) :
    (around u v ρ s).Contains (point u v) := by
  have h : (0 : ℝ) ≤ (ρ : ℝ)*(s : ℝ) := mul_nonneg (by exact_mod_cast hr) (by exact_mod_cast hs)
  intro i
  simp only [around,point,Interval.Contains,Rat.cast_sub,Rat.cast_add,Rat.cast_mul]
  constructor <;> constructor <;> nlinarith

theorem input_on_ball (T : State ≃L[ℝ] State) (u v : Fin 8 → ℚ) {ρ s : ℚ}
    (hs : 0 ≤ s) (hT : ‖T.toContinuousLinearMap‖ ≤ (s : ℝ)) {x : State}
    (hx : x ∈ closedBall (T.symm (point u v)) (ρ : ℝ)) :
    (around u v ρ s).Contains (T x) := by
  have hd : ‖x-T.symm (point u v)‖ ≤ (ρ : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hp : ‖T x-point u v‖ ≤ (s : ℝ)*(ρ : ℝ) := by
    rw [← T.apply_symm_apply (point u v),← map_sub]
    exact (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hT hd (norm_nonneg _) (by exact_mod_cast hs))
  have hR (i : Fin 8) : |(T x).1 i-(u i : ℝ)| ≤ (s : ℝ)*(ρ : ℝ) := by
    have hcoord : |(T x).1 i-(u i : ℝ)| ≤ ‖(T x-point u v).1‖ := by
      simpa only [point,Real.norm_eq_abs,Prod.fst_sub,Pi.sub_apply] using norm_le_pi_norm (T x-point u v).1 i
    exact hcoord.trans ((by rw [Prod.norm_def]; exact le_max_left _ _ :
      ‖(T x-point u v).1‖ ≤ ‖T x-point u v‖).trans hp)
  have hI (i : Fin 8) : |(T x).2 i-(v i : ℝ)| ≤ (s : ℝ)*(ρ : ℝ) := by
    have hcoord : |(T x).2 i-(v i : ℝ)| ≤ ‖(T x-point u v).2‖ := by
      simpa only [point,Real.norm_eq_abs,Prod.snd_sub,Pi.sub_apply] using norm_le_pi_norm (T x-point u v).2 i
    exact hcoord.trans ((by rw [Prod.norm_def]; exact le_max_right _ _ :
      ‖(T x-point u v).2‖ ≤ ‖T x-point u v‖).trans hp)
  intro i
  have hr := abs_le.mp (hR i)
  have hi := abs_le.mp (hI i)
  simp only [around,Interval.Contains,Rat.cast_sub,Rat.cast_add,Rat.cast_mul]
  constructor <;> constructor <;> nlinarith
end
end SbtCosmo.Derivation.GroundNativeTransportGeometry
