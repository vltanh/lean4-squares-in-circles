import SquaresInCircles.Six.Analytic.TransverseProfileBounds
import SquaresInCircles.Six.Analytic.SharpFrontProfile

/-!
# The transverse coordinate of W

Let W be separated from C along its own axis, at angle `π - v` with
`0 ≤ v ≤ 1/2`. Then its transverse coordinate satisfies
`|b| < 233/500 - 73v/100`. The separator and Taylor bounds give
`a + 1/2 ≥ 1387/1000 + v/2 - 387v²/2000 - v³/12`, and a larger `|b|` would put
the far corner outside the disk: the sum of the squares exceeds `Q0` by `1/2000`
plus a polynomial in `u = 2v` with positive coefficients in the Bernstein basis
of degree six. Also, every contained state satisfies
`a + 31 (|b| + b²)/100 ≤ ρ0`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def wingFrontCubic (v : ℝ) : ℝ :=
  1387/1000+v/2-(387/2000)*v^2-v^3/12

private def wingFrontPositive (u : ℝ) : ℝ :=
  15105600*(1-u)^6+56995200*u*(1-u)^5+235606320*u^2*(1-u)^4+
  521705280*u^3*(1-u)^3+486585525*u^4*(1-u)^2+
  159040590*u^5*(1-u)+756125*u^6

lemma own_wing_profile_circle {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 1/2) :
    Q0 < (wingFrontCubic v)^2+(483/500-(73/100)*v)^2 := by
  let u := 2*v
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [hv.1]
  have hu1 : 0 ≤ 1-u := by dsimp [u]; linarith [hv.2]
  have hpos : 0 ≤ wingFrontPositive u := by dsimp [wingFrontPositive]; positivity
  have hid : (wingFrontCubic v)^2+(483/500-(73/100)*v)^2-Q0 =
      1/2000+wingFrontPositive u/2880000000 := by
    dsimp [wingFrontCubic,wingFrontPositive,u,Q0]
    ring
  linarith

private lemma own_wing_front_cubic_lower {v : ℝ} (hv : 0 ≤ v) :
    wingFrontCubic v ≤ 1+(387/1000)*Real.cos v+(1/2)*Real.sin v := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := v)
  have hs := Real.sin_ge_sub_cube hv
  dsimp [wingFrontCubic]
  nlinarith only [hc,hs]

private lemma own_wing_front_cubic_positive {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 1/2) :
    0 < wingFrontCubic v := by
  have hs := mul_nonneg (sub_nonneg.mpr hv.2)
    (show 0 ≤ (1:ℝ)/2+v by linarith [hv.1])
  have hc := mul_le_mul_of_nonneg_right (show v^2 ≤ (1:ℝ)/4 by nlinarith) hv.1
  dsimp [wingFrontCubic]
  nlinarith

/-- If W is separated from C along its own axis at angle `π - v`, with
`0 ≤ v ≤ 1/2`, then `|b| < 233/500 - 73v/100`. -/
theorem own_west_transverse_small_angle {v a b cx cy : ℝ}
    (hc : ContainedChart a |b|) (hx : cx ≤ c0) (hy0 : 0 ≤ cy)
    (hv : 0 ≤ v ∧ v ≤ 1/2)
    (hown : 0 ≤ centralMargin .own (Real.pi-v) a b cx cy) :
    |b| < 233/500-(73/100)*v := by
  have hcos : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hx' : 387/1000 ≤ 1/2-cx := by dsimp [c0] at hx; linarith [rho0_upper]
  have hX := mul_nonneg (show 0 ≤ 1/2-cx-387/1000 by linarith) hcos
  have hY := mul_nonneg hy0 hsin
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin] at hown
  have hfront : wingFrontCubic v ≤ a+1/2 := by
    have ht := own_wing_front_cubic_lower hv.1
    nlinarith only [hown,hX,hY,ht]
  by_contra! hb
  have hB : 483/500-(73/100)*v ≤ |b|+1/2 := by linarith
  have hA0 := own_wing_front_cubic_positive hv
  have hB0 : 0 ≤ 483/500-(73/100)*v := by linarith [hv.2]
  have hAsq := mul_nonneg (sub_nonneg.mpr hfront)
    (show 0 ≤ a+1/2+wingFrontCubic v by linarith [hc.half_le])
  have hBsq := mul_nonneg (sub_nonneg.mpr hB)
    (show 0 ≤ |b|+1/2+(483/500-(73/100)*v) by linarith [abs_nonneg b])
  nlinarith [hc.containment,own_wing_profile_circle hv]

/-- Every contained state satisfies `a + 31 (|b| + b²)/100 ≤ ρ0`. -/
theorem radial_transverse_quadratic {a b : ℝ} (hc : ContainedChart a |b|) :
    a+(31/100)*(|b|+b^2) ≤ rho0 := by
  have ha := hc.a_le_rho0
  have hcircle : |b|+b^2 ≤ (rho0-a)*(rho0+a+1) := by
    nlinarith [hc.containment,rho0_sq,sq_abs b]
  have hcoef : (31/100)*(rho0+a+1) ≤ 1 := by
    linarith [normalization_rho_upper_sharp]
  have hprod := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ 1-(31/100)*(rho0+a+1) by linarith)
  nlinarith only [hcircle,hprod]

end SquaresInCircles.Six.Analytic
