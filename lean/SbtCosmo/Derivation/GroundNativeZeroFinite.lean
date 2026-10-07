import SbtCosmo.Derivation.GroundNativeZeroOrbit
namespace SbtCosmo.Derivation.GroundNativeZeroFinite
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundNativeZeroGeometry GroundNativeZeroOrbit

theorem half_hinge {a r : ℝ} (ha : 1/2 ≤ a) (har : a ≤ r) (hr1 : r ≤ 1) :
    0 ≤ r^3-r^2+a^2*(1+r^3)-2*r*(a^2)^2 := by
  have hr : 1/2 ≤ r := ha.trans har
  have hlo : 1/4 ≤ a^2 := by nlinarith
  have hhi : a^2 ≤ r^2 := by nlinarith
  have e0 : 0 ≤ r^3-r^2+(1/4)*(1+r^3)-2*r*(1/4)^2 := by
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 7/8) (sq_nonneg (r-1/2))
    have h3 := mul_nonneg (by linarith : 0 ≤ r-1/2) (sq_nonneg (r-1/2))
    nlinarith
  have eu : 0 ≤ r^3-r^2+r^2*(1+r^3)-2*r*(r^2)^2 := by
    have h3 : 0 ≤ r^3 := pow_nonneg (by linarith) _
    have hp := mul_nonneg h3 (by nlinarith : 0 ≤ 1-r^2)
    nlinarith
  by_cases he : r = 1/2
  · have ae : a = 1/2 := by linarith
    rw [he, ae]; norm_num
  have hrs : 1/2 < r := lt_of_le_of_ne hr (Ne.symm he)
  have hv : 0 < r^2-1/4 := by nlinarith
  have h0 := mul_nonneg (sub_nonneg.mpr hhi) e0
  have hu := mul_nonneg (sub_nonneg.mpr hlo) eu
  have ht := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 2*r) hv.le)
      (sub_nonneg.mpr hlo)) (sub_nonneg.mpr hhi)
  have hid : (r^2-1/4)*(r^3-r^2+a^2*(1+r^3)-2*r*(a^2)^2) =
      (r^2-a^2)*(r^3-r^2+(1/4)*(1+r^3)-2*r*(1/4)^2) +
      (a^2-1/4)*(r^3-r^2+r^2*(1+r^3)-2*r*(r^2)^2) +
      2*r*(r^2-1/4)*(a^2-1/4)*(r^2-a^2) := by ring
  apply nonneg_of_mul_nonneg_right _ hv
  rw [hid]; linarith

theorem half_contraction {a r d c : ℝ} (ha : 1/2 ≤ a) (har : a ≤ r) (hr1 : r ≤ 1)
    (hd : d = (1-r+2*a^2/r)/2) (hc : c = a*(r+1)/(2*r*Real.sqrt d)) :
    1-c^2 ≤ (1/2)*(1-a^2) := by
  have hap : 0 < a := by linarith
  have hr : 0 < r := hap.trans_le har
  have hdp := (GroundNativeZeroScalar.mixed_bounds hap har hr1 hd).1
  have he := GroundNativeZeroScalar.coefficient_square hr hdp hd hc
  have hg := half_hinge ha har hr1
  have hden : 0 < 2*r*(r-r^2+2*a^2) := by
    have ht : 2*r*d = r-r^2+2*a^2 := by rw [hd]; field_simp
    rw [← ht]; positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  nlinarith

theorem step_half_contraction {g : Field} {x : State} (hg : normSq g = 1)
    (hx : stateNormSq x = 1) (ha : 1/2 ≤ realPart g x) :
    1-(realPart g (step g x))^2 ≤ (1/2)*(1-(realPart g x)^2) := by
  have hap : 0 < realPart g x := by linarith
  obtain ⟨hr, har, hr1⟩ := radius_bounds hg hx hap
  have hd := mixed_norm hg hx hr.ne'
  have hc : realPart g (step g x) = realPart g x*(radius g x+1)/
      (2*radius g x*Real.sqrt (stateNormSq (mix g x))) := by
    rw [step_real, mixed_real hg, div_div]
  exact half_contraction ha har hr1 hd hc

theorem orbit_half_defect {g : Field} {x : State} (hg : normSq g = 1)
    (hx : stateNormSq x = 1) (ha : 1/2 ≤ realPart g x) (n : ℕ) :
    1-(realPart g ((step g)^[n] x))^2 ≤ (1/2 : ℝ)^n*(1-(realPart g x)^2) := by
  have hap : 0 < realPart g x := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := orbit_unit_overlap hg hx hap n
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (1/2)*(1-(realPart g ((step g)^[n] x))^2) :=
        step_half_contraction hg hi.1 (ha.trans hi.2)
      _ ≤ (1/2)*((1/2 : ℝ)^n*(1-(realPart g x)^2)) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem orbit_half_distance_sq {g : Field} {x : State} (hg : normSq g = 1)
    (hx : stateNormSq x = 1) (ha : 1/2 ≤ realPart g x) (n : ℕ) :
    stateNormSq ((step g)^[n] x-(g,0)) ≤ 2*(1/2 : ℝ)^n := by
  have hap : 0 < realPart g x := by linarith
  have hi := orbit_unit_overlap hg hx hap n
  have hb := orbit_half_defect hg hx ha n
  have ha' : 0 < realPart g ((step g)^[n] x) := hap.trans_le hi.2
  have hr := radius_bounds hg hi.1 ha'
  have hu : realPart g ((step g)^[n] x) ≤ 1 := hr.2.1.trans hr.2.2
  have hpow : 0 ≤ (1/2 : ℝ)^n := by positivity
  have hd : 1-(realPart g ((step g)^[n] x))^2 ≤ (1/2 : ℝ)^n := by
    have he := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (realPart g x)] : 1-(realPart g x)^2 ≤ 1) hpow
    nlinarith
  rw [distance_identity hg hi.1]
  have hp := mul_nonneg (by linarith : 0 ≤ realPart g ((step g)^[n] x)) (by linarith : 0 ≤ 1-realPart g ((step g)^[n] x))
  nlinarith

theorem first_overlap_half {g : Field} {x : State} (hg : normSq g = 1)
    (hx : stateNormSq x = 1) (ha : 1/5 < realPart g x) (hr : radius g x < 21/100) :
    1/2 < realPart g (step g x) := by
  have hap : 0 < realPart g x := by linarith
  obtain ⟨hrp, har, hr1⟩ := radius_bounds hg hx hap
  have hd := mixed_norm hg hx hrp.ne'
  obtain ⟨hdp, _, hs⟩ := GroundNativeZeroScalar.mixed_bounds hap har hr1 hd
  have hc : realPart g (step g x) = realPart g x*(radius g x+1)/
      (2*radius g x*Real.sqrt (stateNormSq (mix g x))) := by
    rw [step_real, mixed_real hg, div_div]
  have he : 2*radius g x*Real.sqrt (stateNormSq (mix g x))*realPart g (step g x) =
      realPart g x*(radius g x+1) := by
    rw [hc]; field_simp
  have hcpos := (step_estimate hg hx hap).2.1
  have hspos := Real.sqrt_nonneg (stateNormSq (mix g x))
  by_contra h
  have hh : realPart g (step g x) ≤ 1/2 := le_of_not_gt h
  have ht := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*radius g x*Real.sqrt (stateNormSq (mix g x)))
  have h1 := mul_le_mul_of_nonneg_left hs hrp.le
  have h2 := mul_pos (by linarith : 0 < realPart g x-1/5) (by linarith : 0 < radius g x+1)
  nlinarith

theorem radius_normalize_sq (g : Field) {x : State} (hx : 0 < stateNormSq x) :
    (radius g (normalizeState x))^2*stateNormSq x = (radius g x)^2 := by
  have hs := Real.sq_sqrt hx.le
  have hsp := Real.sqrt_pos.mpr hx
  have hr : realPart g (normalizeState x) = realPart g x/Real.sqrt (stateNormSq x) := by
    change dot g (fun i => (Real.sqrt (stateNormSq x))⁻¹*x.1 i) = _
    rw [dot_smul_right]
    simp only [GroundNativeZeroGeometry.realPart, div_eq_mul_inv]; ring
  have hi : imagPart g (normalizeState x) = imagPart g x/Real.sqrt (stateNormSq x) := by
    change dot g (fun i => (Real.sqrt (stateNormSq x))⁻¹*x.2 i) = _
    rw [dot_smul_right]
    simp only [GroundNativeZeroGeometry.imagPart, div_eq_mul_inv]; ring
  rw [radius_sq, hr, hi, radius_sq]
  calc
    _ = ((realPart g x)^2+(imagPart g x)^2)/(Real.sqrt (stateNormSq x))^2*stateNormSq x := by ring
    _ = _ := by rw [hs]; field_simp

end
end SbtCosmo.Derivation.GroundNativeZeroFinite
