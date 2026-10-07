import SbtCosmo.Derivation.GroundNativeBackgroundContinuation

/-! Return to an independently earned nearby coupled-ground branch. The
baseline seed convergence is explicit in this generic theorem; concrete
original-background instances discharge it separately. -/
namespace SbtCosmo.Derivation.GroundNativeBackgroundSeedReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeLocal
open GroundNativeReflection GroundNativeBackgroundContinuation GroundSourceJacobian Filter Metric
open scoped Topology ContDiff

def encode (T : State ≃L[ℝ] State) (x : State) : ComplexField := pack (T (-x))
def decode (T : State ≃L[ℝ] State) (z : ComplexField) : State := -T.symm (unpack z)

theorem encode_decode (T : State ≃L[ℝ] State) (z : ComplexField) : encode T (decode T z) = z := by
  simp only [encode,decode,neg_neg,T.apply_symm_apply]
  exact packCLE.apply_symm_apply z

theorem decode_encode (T : State ≃L[ℝ] State) (x : State) : decode T (encode T x) = x := by
  have hp (y : State) : unpack (pack y) = y := rfl
  simp only [decode,encode,hp,T.symm_apply_apply,neg_neg]

theorem encode_center (T : State ≃L[ℝ] State) (u : Field) :
    encode T (T.symm (u,0)) = realEmbed (-u) := by
  rw [encode,map_neg,T.apply_symm_apply]
  funext i
  apply Complex.ext <;> simp [pack,realEmbed]

theorem encode_continuous (T : State ≃L[ℝ] State) : Continuous (encode T) :=
  packCLE.continuous.comp (T.continuous.comp continuous_neg)

theorem decode_continuous (T : State ≃L[ℝ] State) : Continuous (decode T) :=
  (T.symm.continuous.comp packCLE.symm.continuous).neg

theorem reflected_seed_return (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ)
    (z : ComplexField) (n : ℕ) :
    (reflectedMap T τ b κ m)^[n] (decode T z) =
      decode T ((nativeUpdate τ b κ m)^[n] z) := by
  have h := reflected_iterate_return T τ b κ m (decode T z) n
  change encode T ((reflectedMap T τ b κ m)^[n] (decode T z)) =
    (nativeUpdate τ b κ m)^[n] (encode T (decode T z)) at h
  rw [encode_decode] at h
  simpa only [decode_encode] using congrArg (decode T) h

theorem negative_fixed_guards {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ActivePhase τ b κ (realEmbed (-u)) ∧ NativeLegal τ b κ m (realEmbed (-u)) := by
  have h := (nativeUpdate_near_fixed (m := m) hu hf hτ0 hτ1).self_of_nhds.2
  change ActivePhase τ b κ (realEmbed u) ∧ NativeLegal τ b κ m (realEmbed u) at h
  rw [realEmbed_neg]
  exact ⟨(activePhase_neg_iff τ b κ _).mpr h.1,
    (nativeLegal_neg_iff b κ m _ hτ0 h.1).mpr h.2⟩

theorem nearby_native_seed_branch_return (T : State ≃L[ℝ] State)
    {b₀ u : Field} {κ m τ : ℝ} {z : ComplexField} {v : Field → Field}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hu : normSq u = 1) (hf : groundMap b₀ κ u = u)
    (hd : ‖coordinateDerivative T b₀ κ m u‖ < 1)
    (hv : ContinuousAt v b₀) (hv0 : v b₀ = u)
    (hvg : ∀ᶠ b in nhds b₀, normSq (v b) = 1 ∧ groundMap b κ (v b) = v b)
    (hlim : Tendsto (fun n : ℕ => (nativeUpdate τ b₀ κ m)^[n] z)
      atTop (nhds (realEmbed (-u))))
    (hg : ∀ n : ℕ, ActivePhase τ b₀ κ ((nativeUpdate τ b₀ κ m)^[n] z) ∧
      NativeLegal τ b₀ κ m ((nativeUpdate τ b₀ κ m)^[n] z))
    (hz : complexNormSq z = 1) :
    ∃ δ > 0, ∀ b ∈ closedBall b₀ δ,
      Tendsto (fun n : ℕ => (nativeUpdate τ b κ m)^[n] z)
        atTop (nhds (realEmbed (-(v b)))) ∧
      ∀ n : ℕ, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[n] z) ∧
        NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) ∧
        complexNormSq ((nativeUpdate τ b κ m)^[n] z) = 1 := by
  let f := reflectedMap T τ
  let a := decode T z
  let w : Field → State := fun b => T.symm (v b,0)
  let c : State := T.symm (u,0)
  let s := reflectedRegion T τ κ m
  have hcenter := negative_fixed_guards (m := m) hu hf hτ0 hτ1
  have hca : ActivePhase τ b₀ κ (pack (T (-c))) := by
    simpa only [c,← encode_center T u,encode] using hcenter.1
  have hcn : NativeLegal τ b₀ κ m (pack (T (-c))) := by
    simpa only [c,← encode_center T u,encode] using hcenter.2
  have hc : ContDiffAt ℝ 1 (fun p : Field × State => f p.1 κ m p.2) (b₀,c) :=
    (reflected_joint_regular_at T hτ0 hca hcn).of_le (by simp)
  have hder : ‖fderiv ℝ (f b₀ κ m) c‖ < 1 := by
    rw [(reflected_root_derivative T hu hf hτ0 hτ1).fderiv]
    exact hd
  have hreturn (n : ℕ) : encode T ((f b₀ κ m)^[n] a) = (nativeUpdate τ b₀ κ m)^[n] z := by
    simpa only [f,a,← reflected_seed_return,encode_decode] using
      encode_decode T ((nativeUpdate τ b₀ κ m)^[n] z)
  have horbit (n : ℕ) : ContinuousAt (fun p : Field × State => f p.1 κ m p.2)
      (b₀,(f b₀ κ m)^[n] a) := by
    have ha : ActivePhase τ b₀ κ (encode T ((f b₀ κ m)^[n] a)) := by rw [hreturn];exact (hg n).1
    have hn : NativeLegal τ b₀ κ m (encode T ((f b₀ κ m)^[n] a)) := by rw [hreturn];exact (hg n).2
    exact (reflected_joint_regular_at T hτ0 ha hn).continuousAt
  have hguards (n : ℕ) : s ∈ nhds (b₀,(f b₀ κ m)^[n] a) := by
    have ha : ActivePhase τ b₀ κ (encode T ((f b₀ κ m)^[n] a)) := by rw [hreturn];exact (hg n).1
    have hn : NativeLegal τ b₀ κ m (encode T ((f b₀ κ m)^[n] a)) := by rw [hreturn];exact (hg n).2
    exact reflected_joint_guards_near T hτ0 ha hn
  have hlim' : Tendsto (fun n : ℕ => (f b₀ κ m)^[n] a) atTop (nhds c) := by
    have ht := ((decode_continuous T).tendsto (realEmbed (-u))).comp hlim
    have he : decode T (realEmbed (-u)) = c := by
      rw [← encode_center T u,decode_encode]
    simpa only [Function.comp_def,he,← reflected_seed_return,f,a] using ht
  have hw : ContinuousAt w b₀ := T.symm.continuous.continuousAt.comp (hv.prodMk continuousAt_const)
  have hw0 : w b₀ = c := by simp only [w,c,hv0]
  have hwfix : ∀ᶠ b in nhds b₀, f b κ m (w b) = w b := by
    filter_upwards [hvg] with b hb
    exact reflected_root_fixed T hb.1 hb.2 hτ0 hτ1
  obtain ⟨δ,hδ,hall⟩ := GroundParametricBranchReturn.nearby_original_seed_branch_returns
    (f := fun b : Field => reflectedMap T τ b κ m) (p := b₀) (u := c) (a := a) (s := s) (g := w)
    hc (reflected_root_fixed T hu hf hτ0 hτ1) hder
    (reflected_joint_guards_near T hτ0 hca hcn) horbit hguards hlim' hw hw0 hwfix
  refine ⟨δ,hδ,fun b hb => ?_⟩
  obtain ⟨ht,hguards'⟩ := hall b hb
  have he (n : ℕ) : encode T ((f b κ m)^[n] a) = (nativeUpdate τ b κ m)^[n] z := by
    rw [show a = decode T z from rfl,show f b κ m = reflectedMap T τ b κ m from rfl,
      reflected_seed_return,encode_decode]
  have hguard (n : ℕ) : ActivePhase τ b κ ((nativeUpdate τ b κ m)^[n] z) ∧
      NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) := by
    have hh := hguards' n
    change ActivePhase τ b κ (encode T ((f b κ m)^[n] a)) ∧
      NativeLegal τ b κ m (encode T ((f b κ m)^[n] a)) at hh
    simpa only [he] using hh
  have hunit (n : ℕ) : complexNormSq ((nativeUpdate τ b κ m)^[n] z) = 1 := by
    cases n with
    | zero => exact hz
    | succ n => rw [Function.iterate_succ_apply'];exact GroundNativeEscape.nativeUpdate_unit hτ0 (hguard n).2
  refine ⟨?_,fun n => ⟨(hguard n).1,(hguard n).2,hunit n⟩⟩
  have htt := ((encode_continuous T).tendsto (w b)).comp ht
  change Tendsto (fun n : ℕ => encode T ((f b κ m)^[n] a)) atTop (nhds (encode T (w b))) at htt
  rw [show (fun n : ℕ => encode T ((f b κ m)^[n] a)) =
    (fun n : ℕ => (nativeUpdate τ b κ m)^[n] z) from funext he] at htt
  simpa only [w,encode_center] using htt
end
end SbtCosmo.Derivation.GroundNativeBackgroundSeedReturn
