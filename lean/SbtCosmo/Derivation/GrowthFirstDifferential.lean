import SbtCosmo.Derivation.GrowthJointDifferential
import SbtCosmo.Derivation.GrowthFirstContinuity
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Joint C1 and signed parameter sensitivity of the unchanged actual first-time
selector. The inverse and its applicability are earned from actual nearby roots. -/
namespace SbtCosmo.Derivation.GrowthFirstDifferential
noncomputable section
open Set Filter GrowthScaleReturn GrowthParameter GrowthFirstRecordLive GrowthFirstContinuity
  GrowthJointContinuity GrowthJointDifferential
open scoped Topology

def rootJacobian (s v : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (s • ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

def rootInverse (s v : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (v⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ + (-s/v) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem rootInverse_left {s v : ℝ} (hv : v ≠ 0) :
    Function.LeftInverse (rootInverse s v) (rootJacobian s v) := by
  intro p
  apply Prod.ext
  · rfl
  · simp [rootInverse,rootJacobian,smul_eq_mul]
    field_simp
    ring

theorem rootInverse_right {s v : ℝ} (hv : v ≠ 0) :
    Function.RightInverse (rootInverse s v) (rootJacobian s v) := by
  intro p
  apply Prod.ext
  · simp [rootInverse,rootJacobian,smul_eq_mul]
    field_simp
    ring
  · rfl

def rootEquiv (s v : ℝ) (hv : v ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (rootJacobian s v) (rootInverse s v)
    (rootInverse_left hv) (rootInverse_right hv)

def firstGradient (a0 A : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (nativeDerivative a0 p.2 (firstTime a0 A p.1 p.2))⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (-finalSensitivity a0 (logScale a0 (firstTime a0 A p.1 p.2)) p.2 /
      nativeDerivative a0 p.2 (firstTime a0 A p.1 p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The actual root selector supplies the local inverse; no inverse or derivative
is supplied as an applicability hypothesis. -/
theorem firstTime_joint_hasFDerivAt {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.2) (hT : 1 < p.1)
    (hf : p.1 < nativeGrowth a0 p.2 A) :
    HasFDerivAt (fun q => firstTime a0 A q.1 q.2) (firstGradient a0 A p) p := by
  let a := firstTime a0 A p.1 p.2
  let s := finalSensitivity a0 (logScale a0 a) p.2
  let v := nativeDerivative a0 p.2 a
  have ha : a ∈ Icc a0 A := (firstTime_spec ha0 hA hl hT hf.le).1
  have hv : v ≠ 0 := (native_positive ha0 hA hl a ha).2.ne'
  let e := rootEquiv s v hv
  let F : ℝ × ℝ → ℝ × ℝ := fun q => (nativeGrowth a0 q.1 q.2,q.1)
  let g : ℝ × ℝ → ℝ × ℝ := fun q => (q.2,firstTime a0 A q.1 q.2)
  have hg : ContinuousAt g p := ContinuousAt.prodMk continuousAt_snd
    (firstTime_joint_continuousAt (p := p) ha0 hA hl hT hf)
  have hF : HasFDerivAt F (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (g p) := by
    change HasFDerivAt F (rootJacobian s v) (p.2,a)
    exact (native_growth_joint_hasFDerivAt (p := (p.2,a)) ha0 hA hl ha).prodMk
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (p.2,a)))
  have hroot : ∀ᶠ q in 𝓝 p, F (g q) = q := by
    filter_upwards [domain_mem_nhds ha0 hA hl hT hf] with q hq
    exact Prod.ext (firstTime_spec ha0 hA hq.1 hq.2.1 hq.2.2).2 rfl
  have hi : HasFDerivAt g (rootInverse s v) p :=
    HasFDerivAt.of_local_left_inverse (f' := e) hg hF hroot
  apply hi.snd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem firstGradient_continuousAt {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.2) (hT : 1 < p.1)
    (hf : p.1 < nativeGrowth a0 p.2 A) : ContinuousAt (firstGradient a0 A) p := by
  have ha := (firstTime_spec ha0 hA hl hT hf.le).1
  have hg : ContinuousAt (fun q : ℝ × ℝ => (q.2,firstTime a0 A q.1 q.2)) p :=
    ContinuousAt.prodMk continuousAt_snd (firstTime_joint_continuousAt ha0 hA hl hT hf)
  have hvel : ContinuousAt (fun q : ℝ × ℝ => nativeDerivative a0 q.2 (firstTime a0 A q.1 q.2)) p :=
    ContinuousAt.comp (f := fun q : ℝ × ℝ => (q.2,firstTime a0 A q.1 q.2)) (x := p)
      (native_velocity_joint_continuousAt ha0 hA hl ha) hg
  have hsen : ContinuousAt (fun q : ℝ × ℝ =>
      finalSensitivity a0 (logScale a0 (firstTime a0 A q.1 q.2)) q.2) p :=
    ContinuousAt.comp (f := fun q : ℝ × ℝ => (q.2,firstTime a0 A q.1 q.2)) (x := p)
      (native_sensitivity_joint_continuousAt ha0 hA hl ha) hg
  have hn := (native_positive ha0 hA hl _ ha).2.ne'
  exact ((hvel.inv₀ hn).smul continuousAt_const).add
    ((hsen.neg.div hvel hn).smul continuousAt_const)

def InteriorDomain (a0 A : ℝ) : Set (ℝ × ℝ) :=
  {p | -(1/A^3) < p.2 ∧ 1 < p.1 ∧ p.1 < nativeGrowth a0 p.2 A}

theorem interiorDomain_mem_nhds {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.2) (hT : 1 < p.1)
    (hf : p.1 < nativeGrowth a0 p.2 A) : InteriorDomain a0 A ∈ 𝓝 p := by
  have hG : ContinuousAt (fun q : ℝ × ℝ => nativeGrowth a0 q.2 A) p :=
    (native_parameter_derivative ha0 hA hl ⟨hA,le_rfl⟩).continuousAt.comp continuousAt_snd
  have hcut : ∀ᶠ q : ℝ × ℝ in 𝓝 p, -(1/A^3) < q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hl
  have hinit : ∀ᶠ q : ℝ × ℝ in 𝓝 p, 1 < q.1 :=
    continuousAt_const.eventually_lt continuousAt_fst hT
  filter_upwards [hcut,hinit,continuousAt_fst.eventually_lt hG hf] with q hq1 hq2 hq3
  exact ⟨hq1,hq2,hq3⟩

theorem interiorDomain_isOpen {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A) :
    IsOpen (InteriorDomain a0 A) :=
  isOpen_iff_mem_nhds.mpr (fun _ hp => interiorDomain_mem_nhds ha0 hA hp.1 hp.2.1 hp.2.2)

theorem firstTime_joint_c1 {a0 A : ℝ} (ha0 : 0 < a0) (hA : a0 ≤ A) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℝ => firstTime a0 A q.1 q.2) (InteriorDomain a0 A) := by
  have hd : ContinuousOn (fderiv ℝ (fun q : ℝ × ℝ => firstTime a0 A q.1 q.2))
      (InteriorDomain a0 A) := by
    apply (show ContinuousOn (firstGradient a0 A) (InteriorDomain a0 A) from
      fun _ hp => (firstGradient_continuousAt ha0 hA hp.1 hp.2.1 hp.2.2).continuousWithinAt).congr
    intro p hp
    exact (firstTime_joint_hasFDerivAt ha0 hA hp.1 hp.2.1 hp.2.2).fderiv
  rw [show (1 : WithTop ℕ∞) = 0+1 from rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen (interiorDomain_isOpen ha0 hA)]
  exact ⟨fun _ hp => (firstTime_joint_hasFDerivAt ha0 hA hp.1 hp.2.1 hp.2.2).differentiableAt.differentiableWithinAt,
    by simp,contDiffOn_zero.mpr hd⟩

theorem firstTime_joint_contDiffAt {a0 A : ℝ} {p : ℝ × ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < p.2) (hT : 1 < p.1)
    (hf : p.1 < nativeGrowth a0 p.2 A) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => firstTime a0 A q.1 q.2) p :=
  (firstTime_joint_c1 ha0 hA).contDiffAt (interiorDomain_mem_nhds ha0 hA hl hT hf)

theorem firstTime_parameter_derivative {a0 A T lam : ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < lam) (hT : 1 < T)
    (hf : T < nativeGrowth a0 lam A) :
    HasDerivAt (firstTime a0 A T)
      (-finalSensitivity a0 (logScale a0 (firstTime a0 A T lam)) lam /
        nativeDerivative a0 lam (firstTime a0 A T lam)) lam := by
  have h := (firstTime_joint_hasFDerivAt ha0 hA hl hT hf).comp lam
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) T lam)
  simpa [firstGradient] using h.hasDerivAt

theorem firstTime_parameter_derivative_positive {a0 A T lam : ℝ}
    (ha0 : 0 < a0) (hA : a0 ≤ A) (hl : -(1/A^3) < lam) (hT : 1 < T)
    (hf : T < nativeGrowth a0 lam A) : 0 < deriv (firstTime a0 A T) lam := by
  have ha := firstTime_interior ha0 hA hl hT hf
  have hs : finalSensitivity a0 (logScale a0 (firstTime a0 A T lam)) lam < 0 := by
    have h := native_parameter_derivative_negative ha0 hA hl ⟨ha.1,ha.2.le⟩
    rwa [(native_parameter_derivative ha0 hA hl ⟨ha.1.le,ha.2.le⟩).deriv] at h
  rw [(firstTime_parameter_derivative ha0 hA hl hT hf).deriv]
  exact div_pos (neg_pos.mpr hs) (native_positive ha0 hA hl _ ⟨ha.1.le,ha.2.le⟩).2

end
end SbtCosmo.Derivation.GrowthFirstDifferential
