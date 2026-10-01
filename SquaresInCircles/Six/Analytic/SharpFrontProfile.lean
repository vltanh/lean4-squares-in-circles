import SquaresInCircles.Six.Analytic.TransverseProfileBounds

/-!
# A transverse bound for a square separated along its own axis

For a square at the phase `π + d` separated from C along its own axis, the
box of the centre of C gives `a + 1/2 ≥ 1 + (387/1000)(cos d + sin d)`. If
the square is contained and `0 ≤ d ≤ 1/2`, this forces
`|b| < 58/125 - (47/100) d`: Taylor bounds give a cubic lower bound for
`a + 1/2`, and the excess of the resulting circle condition over `Q0` is a
positive constant plus `2d` times a quintic with positive coefficients in the
Bernstein basis in `2d`. Also `rho0 < 55641/50000` and `U0 < 463/1000`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma normalization_rho_upper_sharp : rho0<55641/50000 := by
  have hs : Real.sqrt (Q0-1/4)<Real.sqrt ((80641/50000:ℝ)^2) :=
    Real.sqrt_lt_sqrt (by norm_num [Q0]) (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [rho0]
  linarith

lemma normalization_transverse_upper_sharp : U0<463/1000 := by
  have hs : Real.sqrt (Q0-(5/2-rho0)^2)<Real.sqrt ((963/1000:ℝ)^2) :=
    Real.sqrt_lt_sqrt U0_radicand_pos.le (by
      rw [U0_radicand]
      linarith [normalization_rho_upper_sharp])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [U0]
  linarith

private def sharpFront (d : ℝ) : ℝ :=
  1387/1000+(387/1000)*d-(387/2000)*d^2-(129/2000)*d^3

private def sharpFrontPositiveSum (u : ℝ) : ℝ :=
  21424384*(1-u)^5+96491520*u*(1-u)^4+161204096*u^2*(1-u)^3+
    118707316*u^3*(1-u)^2+32846196*u^4*(1-u)+292481*u^5

private lemma sharp_front_circle {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    Q0<(sharpFront d)^2+(241/250-(47/100)*d)^2 := by
  let u := 2*d
  have hu0 : 0≤u := by dsimp [u]; linarith [hd.1]
  have hu1 : 0≤1-u := by dsimp [u]; linarith [hd.2]
  have hsum : 0≤ sharpFrontPositiveSum u := by dsimp [sharpFrontPositiveSum]; positivity
  have hp := mul_nonneg hu0 hsum
  have hid : (sharpFront d)^2+(241/250-(47/100)*d)^2-Q0 =
      377/200000+u*sharpFrontPositiveSum u/256000000 := by
    dsimp [sharpFront,sharpFrontPositiveSum,u,Q0]
    ring
  nlinarith only [hp,hid]

/-- A contained square with `a + 1/2 ≥ 1 + (387/1000)(cos d + sin d)`, for
`0 ≤ d ≤ 1/2`, has `|b| < 58/125 - (47/100) d`. -/
theorem sharp_front_transverse {a b d : ℝ} (hd : 0≤d ∧ d≤1/2)
    (hprofile : 1+(387/1000)*(Real.cos d+Real.sin d)≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0) : |b|<58/125-(47/100)*d := by
  have hsin := Real.sin_ge_sub_cube hd.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := d)
  have ha : sharpFront d≤a+1/2 := by dsimp [sharpFront]; nlinarith only [hsin,hcos,hprofile]
  have hdsq := mul_nonneg (sub_nonneg.mpr hd.2) (show 0≤1/2+d by linarith [hd.1])
  have hco : 0≤1-d/2-d^2/6 := by nlinarith [hd.2]
  have hprod := mul_nonneg hd.1 hco
  have ha0 : 0≤ sharpFront d := by dsimp [sharpFront]; nlinarith only [hprod]
  by_contra! hb
  have hb' : 241/250-(47/100)*d≤|b|+1/2 := by linarith
  have hb0 : 0≤241/250-(47/100)*d := by linarith [hd.2]
  have hA := mul_nonneg (sub_nonneg.mpr ha) (show 0≤a+1/2+sharpFront d by linarith)
  have hB := mul_nonneg (sub_nonneg.mpr hb')
    (show 0≤|b|+1/2+(241/250-(47/100)*d) by linarith [abs_nonneg b])
  have hbad := sharp_front_circle hd
  nlinarith only [hA,hB,hbox,hbad]

end SquaresInCircles.Six.Analytic
