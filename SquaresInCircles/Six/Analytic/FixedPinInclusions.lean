import SquaresInCircles.Six.Analytic.OwnAxisWindows
import SquaresInCircles.Six.Analytic.CoreProfiles

/-!
# Fixed pins in E and W

A square E separated from C along its own axis contains the pin `(9/10, 0)`: it
contains a point `(L, 0)` of the axis with `L ≥ 9/10`, and moving that point
towards the origin keeps it inside the square. A square W separated from C along
its own axis, at angle `t` with `|t| ≤ π/4`, contains the pin at angle `11π/12`
or the one at `5π/4`. For `t ≥ -π/12` this is the sixty-degree cover
`sixty_pin_cover`. For `t ≤ -π/12`, a square that misses the pin at `11π/12` has
its far corner beyond two affine bounds in `t`, and a completed square shows
that these contradict containment.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma polar_rotate (v q t a b : ℝ) :
    openSquare (orientedSquare (t+v) a b) (polarPin (9/10) (q+v)) ↔
      openSquare (orientedSquare t a b) (polarPin (9/10) q) := by
  rw [polar_mem_iff,polar_mem_iff]
  have h : q+v-(t+v)=q-t := by ring
  rw [h]

lemma contract_transverse {L b s : ℝ} (hL : 9/10≤L)
    (hb : |b|<1/2) (hfar : |L*s+b|<1/2) : |(9/10)*s+b|<1/2 := by
  have hbb := abs_lt.mp hb
  have hff := abs_lt.mp hfar
  apply abs_lt.mpr
  by_cases hs : 0≤ s
  · have hlo := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hs
    have hhi := mul_nonneg (sub_nonneg.mpr hL) hs
    constructor <;> nlinarith [hbb.1,hbb.2,hff.1,hff.2]
  · have hlo := mul_nonpos_of_nonneg_of_nonpos
      (show (0:ℝ)≤9/10 by norm_num) (le_of_not_ge hs)
    have hhi := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hL) (le_of_not_ge hs)
    constructor <;> nlinarith [hbb.1,hbb.2,hff.1,hff.2]

/-- A square at angle `|t| ≤ 5/12` that contains a point `(L, 0)` with
`L ≥ 9/10` contains the pin `(9/10, 0)`. -/
theorem fixed_east_of_axis_point {t a b L : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (ht : |t|≤5/12) (hL : 9/10≤L)
    (hp : openSquare (orientedSquare t a b) (L,0)) :
    openSquare (orientedSquare t a b) (polarPin (9/10) 0) := by
  have htr := moving_pin_trig ht
  have hX : |(9/10)*Real.cos t-a|<1/2 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hc.a_le_rho0,rho0_upper,htr.1.1,htr.1.2,hc.half_le]
  have hfar : |L*Real.sin t+b|<1/2 := by
    have h := hp.2
    rw [orientedSquare_localY] at h
    have hid : -L*Real.sin t+0*Real.cos t-b=-(L*Real.sin t+b) := by ring
    rw [hid,abs_neg] at h
    exact h
  have hY := contract_transverse hL hb hfar
  have hY' : |-((9/10)*Real.sin t)-b|<1/2 := by
    rw [show -((9/10)*Real.sin t)-b=-((9/10)*Real.sin t+b) by ring,abs_neg]
    exact hY
  rw [polar_mem_iff]
  simpa only [zero_sub,Real.cos_neg,Real.sin_neg,mul_neg,neg_sub,abs_neg] using And.intro hX hY'

/-- A square E separated from C along its own axis has its angle in
`(-5/12, 3/10)` and contains the pin `(9/10, 0)`. -/
theorem own_east_fixed_pin {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hx0 : 0≤cx) (hy0 : 0≤cy) (hx : cx≤c0) (hy : cy≤c0)
    (ht : |t|≤Real.pi/4) (ho : 0≤centralMargin .own t a b cx cy) :
    (-5/12<t ∧ t<3/10) ∧ openSquare (orientedSquare t a b) (polarPin (9/10) 0) := by
  have hw := own_east_window hc hx0 hy0 hy ht ho
  have ha : |t|≤5/12 := abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have hp := own_moving_pin ha hc hx0 hy0 hx hy ho
  exact ⟨hw,fixed_east_of_axis_point hc hb ha (by linarith) hp⟩

lemma western_flank_quadratic (v : ℝ) :
    Q0<(277/200+v/3)^2+(49/40-(9/10)*v)^2 := by
  have hid : (277/200+v/3)^2+(49/40-(9/10)*v)^2-Q0 =
      (829/900)*(v-2307/3316)^2+20199561/165800000 := by norm_num [Q0]; ring
  have h := sq_nonneg (v-2307/3316)
  nlinarith only [hid,h]

/-- A square at phase `-v`, with `π/12 ≤ v ≤ 2/3`, contains the pin at angle
`-π/12` if its centre obeys the radial profile whenever `b < 0`. -/
theorem western_left_pin {v a b : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hv0 : Real.pi/12≤v) (hv1 : v≤2/3)
    (hprofile : b<0 → 1/2+(77/200)*Real.cos v+(1/2)*Real.sin v≤a) :
    openSquare (orientedSquare (-v) a b) (polarPin (9/10) (-Real.pi/12)) := by
  have hδ0 : 0≤v-Real.pi/12 := by linarith
  have hδ1 : v-Real.pi/12≤5/12 := by linarith [Real.pi_gt_d2]
  have htr := moving_pin_trig (abs_le.mpr ⟨by linarith, hδ1⟩ : |v-Real.pi/12|≤5/12)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith [Real.pi_gt_d2])
  have hs1 := (Real.sin_le hδ0).trans hδ1
  have hX : |(9/10)*Real.cos (v-Real.pi/12)-a|<1/2 := by
    apply abs_lt.mpr
    constructor <;> nlinarith [hc.a_le_rho0,rho0_upper,htr.1.1,htr.1.2,hc.half_le]
  have hbb := abs_lt.mp hb
  have hY : |(9/10)*Real.sin (v-Real.pi/12)-b|<1/2 := by
    apply abs_lt.mpr
    refine ⟨by nlinarith [hbb.2],?_⟩
    by_contra! hbad
    have hbneg : b<0 := by nlinarith
    have hp := hprofile hbneg
    have hv : 0≤v := by linarith [Real.pi_pos]
    have haff := trig_affine_lower (A:=(77:ℝ)/200) (B:=(1:ℝ)/2)
      (r:=(2:ℝ)/3) (by norm_num) (by norm_num) hv hv1
    have hA : 277/200+v/3≤a+1/2 := by nlinarith
    have hB : 49/40-(9/10)*v≤|b|+1/2 := by
      have hs := Real.sin_le hδ0
      rw [abs_of_neg hbneg]
      nlinarith [Real.pi_gt_d2]
    have hA0 : 0≤277/200+v/3 := by linarith
    have hB0 : 0≤49/40-(9/10)*v := by linarith
    have hAsq := mul_nonneg (sub_nonneg.mpr hA)
      (show 0≤a+1/2+(277/200+v/3) by linarith [hc.half_le])
    have hBsq := mul_nonneg (sub_nonneg.mpr hB)
      (show 0≤|b|+1/2+(49/40-(9/10)*v) by linarith [abs_nonneg b])
    nlinarith [hc.containment,western_flank_quadratic v]
  rw [polar_mem_iff]
  have harg : -Real.pi/12-(-v)=v-Real.pi/12 := by ring
  simpa only [harg] using And.intro hX hY

lemma own_west_left_pin {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hx : cx≤c0) (hy0 : 0≤cy)
    (ht : |t|≤Real.pi/4) (htleft : t≤-Real.pi/12)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) :
    openSquare (orientedSquare (Real.pi+t) a b) (polarPin (9/10) (11*Real.pi/12)) := by
  have hw := own_west_lower_window hc hx hy0 ht ho
  have hp := own_west_negative_profile (v:=-t) hx hy0
    (by linarith [Real.pi_pos]) (by linarith [(abs_le.mp ht).1])
    (by simpa only [sub_neg_eq_add] using ho)
  have hcos : 0≤Real.cos (-t) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [(abs_le.mp ht).1,Real.pi_pos]⟩
  have hlocal := western_left_pin (v:=-t) hc hb (by linarith) (by linarith)
    (fun _ => by nlinarith)
  have hphase : Real.pi+t=t+Real.pi := by ring
  have hpin : 11*Real.pi/12=(-Real.pi/12)+Real.pi := by ring
  rw [hphase,hpin,polar_rotate]
  simpa only [neg_neg] using hlocal

/-- A square W separated from C along its own axis, at angle `|t| ≤ π/4`,
contains the pin at angle `11π/12` or the one at `5π/4`. -/
theorem own_west_fixed_pins {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hx : cx≤c0) (hy0 : 0≤cy) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) :
    openSquare (orientedSquare (Real.pi+t) a b) (polarPin (9/10) (11*Real.pi/12)) ∨
      openSquare (orientedSquare (Real.pi+t) a b) (polarPin (9/10) (5*Real.pi/4)) := by
  by_cases hleft : t≤-Real.pi/12
  · exact Or.inl (own_west_left_pin hc hb hx hy0 ht hleft ho)
  · have hcover := sixty_pin_cover (t:=Real.pi+t) (q:=11*Real.pi/12) hc hb
      ⟨by linarith,by linarith [(abs_le.mp ht).2]⟩
    have hsum : 11*Real.pi/12+Real.pi/3=5*Real.pi/4 := by ring
    simpa only [hsum] using hcover

end SquaresInCircles.Six.Analytic
