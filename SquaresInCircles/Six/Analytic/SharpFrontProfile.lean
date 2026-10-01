import SquaresInCircles.Six.Analytic.TransverseProfileBounds

/-!
# A sharper front profile for the D-secondary reduction

The actual central box gives 1/2-cx,1/2-cy > 387/1000. On the full interval
0<=d<=1/2 a single sextic identity proves |b|<58/125-47d/100.
The displayed polynomial has positive coefficients in d and 1-2d; no angle
subdivision, sampled values or certificate engine are used.
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

/-- A pure profile implication used with the genuine central OWN inequality. -/
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

lemma own_sharp_front_profile {a b cx cy d : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (hd : 0≤d ∧ d≤1/2)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    1+(387/1000)*(Real.cos d+Real.sin d)≤a+1/2 := by
  have hc0 : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_gt_d2]⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1 (by linarith [hd.2,Real.pi_gt_d2])
  have hcx : 0≤1/2-cx-387/1000 := by dsimp [c0] at hx; linarith [rho0_upper]
  have hcy : 0≤1/2-cy-387/1000 := by dsimp [c0] at hy; linarith [rho0_upper]
  have hX := mul_nonneg hcx hc0
  have hY := mul_nonneg hcy hs0
  have hcpi : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm,Real.cos_add_pi]
  have hspi : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm,Real.sin_add_pi]
  simp only [centralMargin,centralNormal,angularWidth,hcpi,hspi,
    abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hown
  nlinarith only [hown,hX,hY]

lemma own_sharp_front_transverse {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy : cy≤c0) (hd : 0≤d ∧ d≤1/2)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    |b|<58/125-(47/100)*d :=
  sharp_front_transverse hd (own_sharp_front_profile hx hy hd hown) hc.containment

end SquaresInCircles.Six.Analytic
