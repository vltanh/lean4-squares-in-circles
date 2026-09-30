module
public import SquaresInCircles.Six.Normalization.CentralSAT
public import SquaresInCircles.Six.Normalization.ChartBounds
public import SquaresInCircles.Seven.Analysis

@[expose] public section

/-!
# Whole-interval transverse bounds from the actual central separators

These estimates do not assume a candidate D-edge or a narrower helper domain.
A backward OWN west tilt v in [0,2/3] has |b| < 47/100-2v/3.
For a west-cardinal helper, the corresponding signed bound holds on [0,2/5].
A first-octant OWN square at angle d in [0,1/2] has
|b| < 47/100-9d/20.

Each circular obstruction is one displayed sextic identity on its full
interval. The positive terms use u and 1-u, where u is a linear rescaling of
the original angle. There is no subdivision or interval-certificate premise.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def leftProfile (v : ℝ) : ℝ :=
  277/200+v/2-(77/400)*v^2-v^3/12

private def frontProfile (d : ℝ) : ℝ :=
  277/200+(77/200)*d-(77/400)*d^2-(77/1200)*d^3

private def leftPositiveSum (u : ℝ) : ℝ :=
  4009500*(1-u)^5+24748659*u*(1-u)^4+50670036*u^2*(1-u)^3+
    43013403*u^3*(1-u)^2+13241034*u^4*(1-u)+198508*u^5

private def frontPositiveSum (u : ℝ) : ℝ :=
  8914176*(1-u)^5+40366080*u*(1-u)^4+68567424*u^2*(1-u)^3+
    52576404*u^3*(1-u)^2+16415124*u^4*(1-u)+960169*u^5

private lemma left_circle_obstruction {v : ℝ} (hv : 0≤v ∧ v≤2/3) :
    Q0<(leftProfile v)^2+(97/100-(2/3)*v)^2 := by
  let u := 3*v/2
  have hu0 : 0≤u := by dsimp [u]; linarith [hv.1]
  have hu1 : 0≤1-u := by dsimp [u]; linarith [hv.2]
  have hsum : 0≤leftPositiveSum u := by dsimp [leftPositiveSum]; positivity
  have hp := mul_nonneg hu0 hsum
  have hid : (leftProfile v)^2+(97/100-(2/3)*v)^2-Q0 =
      1589/200000+u*leftPositiveSum u/65610000 := by
    dsimp [leftProfile,leftPositiveSum,u,Q0]
    ring
  nlinarith only [hid,hp]

private lemma front_circle_obstruction {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    Q0<(frontProfile d)^2+(97/100-(9/20)*d)^2 := by
  let u := 2*d
  have hu0 : 0≤u := by dsimp [u]; linarith [hd.1]
  have hu1 : 0≤1-u := by dsimp [u]; linarith [hd.2]
  have hsum : 0≤frontPositiveSum u := by dsimp [frontPositiveSum]; positivity
  have hp := mul_nonneg hu0 hsum
  have hid : (frontProfile d)^2+(97/100-(9/20)*d)^2-Q0 =
      1589/200000+u*frontPositiveSum u/92160000 := by
    dsimp [frontProfile,frontPositiveSum,u,Q0]
    ring
  nlinarith only [hid,hp]

private lemma leftProfile_nonneg {v : ℝ} (hv : 0≤v ∧ v≤2/3) : 0≤leftProfile v := by
  have hsq := mul_nonneg (sub_nonneg.mpr hv.2) (show 0≤2/3+v by linarith [hv.1])
  have hcoef : 0≤1/2-(77/400)*v-v^2/12 := by nlinarith [hv.2]
  have hp := mul_nonneg hv.1 hcoef
  dsimp [leftProfile]
  nlinarith only [hp]

private lemma frontProfile_nonneg {d : ℝ} (hd : 0≤d ∧ d≤1/2) : 0≤frontProfile d := by
  have hsq := mul_nonneg (sub_nonneg.mpr hd.2) (show 0≤1/2+d by linarith [hd.1])
  have hcoef : 0≤1-d/2-d^2/6 := by nlinarith [hd.2]
  have hp := mul_nonneg hd.1 hcoef
  dsimp [frontProfile]
  nlinarith only [hp]

/-- A real far-corner bound plus the west-negative radial profile gives a
uniform affine transverse bound throughout the original interval. -/
theorem transverse_lt_from_left_profile {a b v : ℝ}
    (hv : 0≤v ∧ v≤2/3)
    (hprofile : 1+(77/200)*Real.cos v+(1/2)*Real.sin v≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0) : |b|<47/100-(2/3)*v := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := v)
  have hs := Real.sin_ge_sub_cube hv.1
  have ha : leftProfile v≤a+1/2 := by dsimp [leftProfile]; nlinarith only [hc,hs,hprofile]
  by_contra! hb
  have hb' : 97/100-(2/3)*v≤|b|+1/2 := by linarith
  have hleft := leftProfile_nonneg hv
  have hright : 0≤97/100-(2/3)*v := by linarith [hv.2]
  have hA := mul_nonneg (sub_nonneg.mpr ha)
    (show 0≤a+1/2+leftProfile v by linarith)
  have hB := mul_nonneg (sub_nonneg.mpr hb')
    (show 0≤|b|+1/2+(97/100-(2/3)*v) by linarith [abs_nonneg b])
  have hbad := left_circle_obstruction hv
  nlinarith only [hbox,hA,hB,hbad]

/-- The first-octant radial profile has a separate full-interval bound. -/
theorem transverse_lt_from_front_profile {a b d : ℝ}
    (hd : 0≤d ∧ d≤1/2)
    (hprofile : 1+(77/200)*(Real.cos d+Real.sin d)≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0) : |b|<47/100-(9/20)*d := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := d)
  have hs := Real.sin_ge_sub_cube hd.1
  have ha : frontProfile d≤a+1/2 := by dsimp [frontProfile]; nlinarith only [hc,hs,hprofile]
  by_contra! hb
  have hb' : 97/100-(9/20)*d≤|b|+1/2 := by linarith
  have hleft := frontProfile_nonneg hd
  have hright : 0≤97/100-(9/20)*d := by linarith [hd.2]
  have hA := mul_nonneg (sub_nonneg.mpr ha)
    (show 0≤a+1/2+frontProfile d by linarith)
  have hB := mul_nonneg (sub_nonneg.mpr hb')
    (show 0≤|b|+1/2+(97/100-(9/20)*d) by linarith [abs_nonneg b])
  have hbad := front_circle_obstruction hd
  nlinarith only [hbox,hA,hB,hbad]

/-- Negative W in the OWN case. Its opposite sign of cy is retained. -/
theorem own_west_negative_transverse {a b cx cy v : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy0 : 0≤cy)
    (hv : 0≤v ∧ v≤2/3)
    (hown : 0≤centralMargin .own (Real.pi-v) a b cx cy) :
    |b|<47/100-(2/3)*v := by
  have hc0 : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hs0 : 0≤Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hxc := mul_nonneg (show 0≤1/2-cx-77/200 by linarith [c0_lt_23_200]) hc0
  have hys := mul_nonneg hy0 hs0
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hown
  apply transverse_lt_from_left_profile hv _ hc.containment
  nlinarith only [hown,hxc,hys]

/-- The signed negative transverse bound also holds for a cardinal W. No
claim is made about the positive transverse coordinate in this case. -/
theorem cardinal_west_negative_transverse {a b cx cy v : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hv : 0≤v ∧ v≤2/5)
    (hcard : 0≤centralMargin .west (Real.pi-v) a b cx cy) :
    -b<47/100-(2/3)*v := by
  by_contra! hb
  have hc0 : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hs0 : 0≤Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hv2 := mul_nonneg (sub_nonneg.mpr hv.2) (show 0≤2/5+v by linarith [hv.1])
  have hfactor : 0≤1/10-v^2/6 := by nlinarith
  have hcube := mul_nonneg hv.1 hfactor
  have hsinLow := Real.sin_ge_sub_cube hv.1
  have hs : (9/10)*v≤Real.sin v := by nlinarith only [hcube,hsinLow]
  have hbshift : 211/300≤1/2-b := by linarith [hv.2]
  have hprod := mul_le_mul hbshift hs (show 0≤(9/10)*v by positivity)
    (show 0≤1/2-b by linarith)
  have hcprod := mul_nonneg (show 0≤a-1/2 by linarith [hc.half_le])
    (show 0≤1-Real.cos v by linarith [Real.cos_le_one v])
  simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hcard
  have hprofile : 1+(77/200)*Real.cos v+(1/2)*Real.sin v≤a+1/2 := by
    have hcu := Real.cos_le_one v
    have hsu := Real.sin_le hv.1
    nlinarith [hcard,hprod,hcprod,hcu,hsu,c0_lt_23_200,hv.1]
  have hbound := transverse_lt_from_left_profile ⟨hv.1,by linarith [hv.2]⟩ hprofile hc.containment
  have hab := neg_le_abs b
  linarith

/-- A first-octant OWN square has the front radial profile independently of
which diagonal-edge source is later selected. -/
theorem own_front_radial_profile {a b cx cy d : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (hd : 0≤d ∧ d≤1/2)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    1+(77/200)*(Real.cos d+Real.sin d)≤a+1/2 := by
  have hc0 : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_gt_d2]⟩
  have hs0 : 0≤Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (by linarith [hd.2,Real.pi_gt_d2])
  have hxc := mul_nonneg (show 0≤1/2-cx-77/200 by linarith [c0_lt_23_200]) hc0
  have hys := mul_nonneg (show 0≤1/2-cy-77/200 by linarith [c0_lt_23_200]) hs0
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
    abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hown
  nlinarith only [hown,hxc,hys]

theorem own_front_transverse {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy : cy≤c0) (hd : 0≤d ∧ d≤1/2)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    |b|<47/100-(9/20)*d :=
  transverse_lt_from_front_profile hd (own_front_radial_profile hx hy hd hown) hc.containment

end SquaresInCircles.Six.Analytic
