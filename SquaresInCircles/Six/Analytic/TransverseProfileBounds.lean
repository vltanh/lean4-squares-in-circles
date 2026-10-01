import SquaresInCircles.Six.Normalization.CentralSAT
import SquaresInCircles.Six.Normalization.ChartBounds
import SquaresInCircles.Seven.Analysis

/-!
# Transverse bounds from a radial profile

For `0 ≤ v ≤ 2/3`, a contained square with
`a + 1/2 ≥ 1 + (77/200) cos v + (1/2) sin v` has `|b| < 47/100 - (2/3) v`.
Otherwise `(a + 1/2, |b| + 1/2)` would dominate the point
`(L v, 97/100 - (2/3) v)`, where `L` is a cubic lower bound of the profile, and
with `u = 3v/2` the squared length of that point exceeds `Q0` by a positive
constant plus `u` times a polynomial with positive coefficients in `u` and
`1 - u`. For W separated from C along the west side of C at the phase `π - v`,
`0 ≤ v ≤ 2/5`, the separating inequality gives this bound on `a` as soon as
`-b ≥ 47/100 - (2/3) v`; so `-b < 47/100 - (2/3) v`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def leftProfile (v : ℝ) : ℝ :=
  277/200+v/2-(77/400)*v^2-v^3/12

private def leftPositiveSum (u : ℝ) : ℝ :=
  4009500*(1-u)^5+24748659*u*(1-u)^4+50670036*u^2*(1-u)^3+
    43013403*u^3*(1-u)^2+13241034*u^4*(1-u)+198508*u^5

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

private lemma leftProfile_nonneg {v : ℝ} (hv : 0≤v ∧ v≤2/3) : 0≤leftProfile v := by
  have hsq := mul_nonneg (sub_nonneg.mpr hv.2) (show 0≤2/3+v by linarith [hv.1])
  have hcoef : 0≤1/2-(77/400)*v-v^2/12 := by nlinarith [hv.2]
  have hp := mul_nonneg hv.1 hcoef
  dsimp [leftProfile]
  nlinarith only [hp]

/-- A contained square whose radial coordinate is above the profile has
`|b| < 47/100 - (2/3) v`, for `0 ≤ v ≤ 2/3`. -/
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

/-- A square separated from C along the west side of C, at the phase `π - v`
with `0 ≤ v ≤ 2/5`, has `-b < 47/100 - (2/3) v`. -/
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
  have hprod := mul_le_mul hbshift hs (show 0≤(9/10)*v by linarith [hv.1])
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

end SquaresInCircles.Six.Analytic
