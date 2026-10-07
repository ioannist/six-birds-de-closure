import SbtCosmo.Derivation.GroundLocalDynamics
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
namespace NativeApproximateCenterBanach
open Metric Filter
open scoped Topology

/-- A small actual center defect and an earned local Lipschitz bound construct
an actual fixed point. The center itself is not assumed to be fixed. -/
theorem approximate_center_return {α : Type*} [MetricSpace α] [CompleteSpace α]
    (f : α → α) {c : α} {R d : ℝ} {q : NNReal}
    (hR : 0 ≤ R) (hq : q < 1)
    (hL : LipschitzOnWith q f (closedBall c R))
    (hd : dist (f c) c ≤ d) (hbudget : (q : ℝ)*R+d ≤ R) :
    ∃ a ∈ closedBall c R, f a = a ∧ dist a c ≤ d/(1-(q : ℝ)) ∧
      (∀ x ∈ closedBall c R, f x = x → x = a) ∧
      ∀ y ∈ closedBall c R,
        Tendsto (fun n : ℕ => (f^[n]) y) atTop (nhds a) ∧
        ∀ n : ℕ, dist ((f^[n]) y) a ≤ (q : ℝ)^n * dist y a := by
  have hm : Set.MapsTo f (closedBall c R) (closedBall c R) := by
    intro x hx
    rw [mem_closedBall]
    calc
      dist (f x) c ≤ dist (f x) (f c)+dist (f c) c := dist_triangle _ _ _
      _ ≤ (q : ℝ)*dist x c+d := add_le_add (hL.dist_le_mul _ hx _ (mem_closedBall_self hR)) hd
      _ ≤ (q : ℝ)*R+d := add_le_add (mul_le_mul_of_nonneg_left (mem_closedBall.mp hx) q.property) le_rfl
      _ ≤ R := hbudget
  have ht : ContractingWith q (hm.restrict f _ _) :=
    ⟨hq,hm.lipschitzOnWith_iff_restrict.mp hL⟩
  obtain ⟨a,ha,hfix,_,_⟩ := ht.exists_fixedPoint'
    isClosed_closedBall.isComplete hm (mem_closedBall_self hR) (edist_ne_top c (f c))
  have hq' : (q : ℝ) < 1 := hq
  have hinner : dist a c ≤ d/(1-(q : ℝ)) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-(q : ℝ))).mpr
    have hl := hL.dist_le_mul a ha c (mem_closedBall_self hR)
    have hdac := dist_triangle (f a) (f c) c
    rw [hfix] at hl hdac
    nlinarith
  have hu : ∀ x ∈ closedBall c R, f x = x → x = a := by
    intro x hx hf
    have hl := hL.dist_le_mul x hx a ha
    rw [hf,hfix] at hl
    have hz : dist x a = 0 := by nlinarith [dist_nonneg (x := x) (y := a)]
    exact dist_eq_zero.mp hz
  refine ⟨a,ha,hfix,hinner,hu,fun y hy => ?_⟩
  obtain ⟨z,hz,hzfix,hyconv,_⟩ := ht.exists_fixedPoint'
    isClosed_closedBall.isComplete hm hy (edist_ne_top y (f y))
  rw [hu z hz hzfix] at hyconv
  refine ⟨hyconv,fun n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',pow_succ]
    calc
      dist (f ((f^[n]) y)) a = dist (f ((f^[n]) y)) (f a) := by rw [hfix]
      _ ≤ (q : ℝ)*dist ((f^[n]) y) a := hL.dist_le_mul _ (hm.iterate n hy) _ ha
      _ ≤ (q : ℝ)*((q : ℝ)^n*dist y a) := mul_le_mul_of_nonneg_left ih q.property
      _ = (q : ℝ)^n*(q : ℝ)*dist y a := by ring
end NativeApproximateCenterBanach

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
namespace NativeCycleCommutationBridge
open Metric

theorem power_fixed_of_mem_unique {α : Type*} (f : α → α) {k j : ℕ} {a : α} {S : Set α}
    (hfix : (f^[k]) a = a) (hmem : (f^[j]) a ∈ S)
    (huniq : ∀ x ∈ S, (f^[k]) x = x → x = a) : (f^[j]) a = a := by
  apply huniq _ hmem
  rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hfix]

theorem power_mem_of_inner_radius {α : Type*} [PseudoMetricSpace α]
    (f : α → α) {j : ℕ} {a c : α} {R r d : ℝ} {M : NNReal}
    (hR : 0 ≤ R) (ha : a ∈ closedBall c R)
    (hinner : dist a c ≤ r)
    (hLip : LipschitzOnWith M (f^[j]) (closedBall c R))
    (hdefect : dist ((f^[j]) c) c ≤ d) (hbudget : (M : ℝ)*r+d ≤ R) :
    (f^[j]) a ∈ closedBall c R := by
  rw [mem_closedBall]
  calc
    dist ((f^[j]) a) c ≤ dist ((f^[j]) a) ((f^[j]) c)+dist ((f^[j]) c) c := dist_triangle _ _ _
    _ ≤ (M : ℝ)*dist a c+d := add_le_add (hLip.dist_le_mul _ ha _ (mem_closedBall_self hR)) hdefect
    _ ≤ (M : ℝ)*r+d := add_le_add (mul_le_mul_of_nonneg_left hinner M.property) le_rfl
    _ ≤ R := hbudget

theorem period_two_from_power_and_inner_radius {α : Type*} [PseudoMetricSpace α]
    (f : α → α) {k : ℕ} {a c : α} {R r d : ℝ} {M : NNReal}
    (hfix : (f^[k]) a = a) (hR : 0 ≤ R) (ha : a ∈ closedBall c R)
    (huniq : ∀ x ∈ closedBall c R, (f^[k]) x = x → x = a)
    (hinner : dist a c ≤ r)
    (hLip : LipschitzOnWith M (f^[2]) (closedBall c R))
    (hdefect : dist ((f^[2]) c) c ≤ d) (hbudget : (M : ℝ)*r+d ≤ R) :
    (f^[2]) a = a :=
  power_fixed_of_mem_unique f hfix
    (power_mem_of_inner_radius f hR ha hinner hLip hdefect hbudget) huniq
end NativeCycleCommutationBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
namespace NativeCycleSubsequences
open Filter
open scoped Topology

theorem tendsto_of_finite_residues {α : Type*} [TopologicalSpace α]
    (g : ℕ → α) {a : α} {p : ℕ} (hp : 0 < p)
    (h : ∀ j : Fin p, Tendsto (fun n : ℕ => g (n*p+j.val)) atTop (nhds a)) :
    Tendsto g atTop (nhds a) := by
  apply tendsto_def.mpr
  intro S hS
  have he : ∀ᶠ n : ℕ in atTop, ∀ j : Fin p, g (n*p+j.val) ∈ S :=
    eventually_all.mpr (fun j => (h j).eventually hS)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  apply eventually_atTop.mpr
  refine ⟨N*p,fun n hn => ?_⟩
  have hd : N ≤ n/p := (Nat.le_div_iff_mul_le hp).mpr hn
  have hr := hN (n/p) hd ⟨n%p,Nat.mod_lt _ hp⟩
  simpa only [Nat.mul_comm (n/p) p,Nat.div_add_mod] using hr

/-- A contracting even power alone does not identify the even orbit limit.
Period two and continuity of the intervening powers supply that bridge. -/
theorem even_odd_returns {α : Type*} [TopologicalSpace α]
    (f : α → α) {a y : α} {p : ℕ} (hp : 0 < p)
    (h2 : (f^[2]) a = a)
    (hpower : Tendsto (fun n : ℕ => ((f^[2*p])^[n]) y) atTop (nhds a))
    (hcont : ∀ j : Fin p, ContinuousAt (f^[2*j.val]) a)
    (hstep : ContinuousAt f a) :
    Tendsto (fun n : ℕ => (f^[2*n]) y) atTop (nhds a) ∧
    Tendsto (fun n : ℕ => (f^[2*n+1]) y) atTop (nhds (f a)) := by
  have he : Tendsto (fun n : ℕ => (f^[2*n]) y) atTop (nhds a) := by
    apply tendsto_of_finite_residues _ hp
    intro j
    have hj : (f^[2*j.val]) a = a := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed h2 j.val
    have ht := ((hcont j).tendsto).comp hpower
    rw [hj] at ht
    convert ht using 1
    funext n
    have hn : 2*(n*p+j.val) = 2*j.val+(2*p)*n := by ring
    rw [hn,Function.iterate_add_apply,Function.iterate_mul (f := f) (2*p) n]
    rfl
  refine ⟨he,?_⟩
  simpa only [Function.comp_def,Function.iterate_succ_apply'] using hstep.tendsto.comp he

theorem nonconvergence_of_distinct_limits {α : Type*} [TopologicalSpace α] [T2Space α]
    (f : α → α) {a y : α}
    (he : Tendsto (fun n : ℕ => (f^[2*n]) y) atTop (nhds a))
    (ho : Tendsto (fun n : ℕ => (f^[2*n+1]) y) atTop (nhds (f a)))
    (hne : f a ≠ a) : ¬ ∃ l, Tendsto (fun n : ℕ => (f^[n]) y) atTop (nhds l) := by
  rintro ⟨l,hl⟩
  have hse : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (by intro n;change n ≤ 2*n;omega) tendsto_id
  have hso : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (by intro n;change n ≤ 2*n+1;omega) tendsto_id
  have hal : a = l := tendsto_nhds_unique he (hl.comp hse)
  have hfal : f a = l := tendsto_nhds_unique ho (hl.comp hso)
  exact hne (hfal.trans hal.symm)
end NativeCycleSubsequences

namespace NativeActualCycleConstruction
open Metric Filter
open scoped Topology

theorem actual_period_two_from_power_certificate {α : Type*} [MetricSpace α] [CompleteSpace α]
    (f : α → α) {c : α} {p : ℕ} {R d d₂ : ℝ} {q M : NNReal}
    (hp : 0 < p) (hR : 0 ≤ R) (hq : q < 1)
    (hL : LipschitzOnWith q (f^[2*p]) (closedBall c R))
    (hd : dist ((f^[2*p]) c) c ≤ d) (hbudget : (q : ℝ)*R+d ≤ R)
    (hL₂ : LipschitzOnWith M (f^[2]) (closedBall c R))
    (hd₂ : dist ((f^[2]) c) c ≤ d₂)
    (hinner_budget : (M : ℝ)*(d/(1-(q : ℝ)))+d₂ ≤ R)
    (hsep : ∀ a ∈ closedBall c R, f a ≠ a)
    (hcont : ∀ a ∈ closedBall c R, ∀ j : Fin p, ContinuousAt (f^[2*j.val]) a)
    (hstep : ∀ a ∈ closedBall c R, ContinuousAt f a) :
    ∃ a ∈ closedBall c R, (f^[2]) a = a ∧ f a ≠ a ∧ dist a c ≤ d/(1-(q : ℝ)) ∧
      ∀ y ∈ closedBall c R,
        Tendsto (fun n : ℕ => (f^[2*n]) y) atTop (nhds a) ∧
        Tendsto (fun n : ℕ => (f^[2*n+1]) y) atTop (nhds (f a)) ∧
        (∀ n : ℕ, dist (((f^[2*p])^[n]) y) a ≤ (q : ℝ)^n*dist y a) ∧
        ¬ ∃ l, Tendsto (fun n : ℕ => (f^[n]) y) atTop (nhds l) := by
  obtain ⟨a,ha,hfix,hinner,huniq,hreturns⟩ :=
    NativeApproximateCenterBanach.approximate_center_return (f^[2*p]) hR hq hL hd hbudget
  have h2 := NativeCycleCommutationBridge.period_two_from_power_and_inner_radius f hfix hR ha
    huniq hinner hL₂ hd₂ hinner_budget
  refine ⟨a,ha,h2,hsep a ha,hinner,fun y hy => ?_⟩
  have heo := NativeCycleSubsequences.even_odd_returns f hp h2 (hreturns y hy).1
    (hcont a ha) (hstep a ha)
  exact ⟨heo.1,heo.2,(hreturns y hy).2,
    NativeCycleSubsequences.nonconvergence_of_distinct_limits f heo.1 heo.2 (hsep a ha)⟩
end NativeActualCycleConstruction
