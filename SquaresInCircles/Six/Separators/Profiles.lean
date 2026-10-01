import SquaresInCircles.Six.Separators.DiagonalAngle
import SquaresInCircles.Six.Supports

/-!
# Radial profiles and transverse coordinates

A square separated from the central square C along its own axis, or along a
side of C, has its radial coordinate `a` bounded below by a profile in its
angle, since the centre of C lies in the box `[0, c0]²`. The containment
`(a + 1/2)² + (|b| + 1/2)² ≤ Q0` then bounds its transverse coordinate `b`, as
soon as the point of the profile at the height of the bound lies outside the
disk (`transverse_lt_of_profile`). For the turned square D, at the phase
`π + d` with `1/2 < d ≤ π/4`, this gives `a > 41/40` and
`|b| < 31/100 - 17d/100`, the excess of the circle condition being concave in
`d`. For W at the phase `π - v` it gives `|b| < 233/500 - 73v/100` on its own
axis and `-b < 47/100 - 2v/3` on the west side of C, the excess being a
polynomial with positive coefficients in the Bernstein basis.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- A contained square whose far corner lies beyond the profile `L` has
`|b| < T` when the point `(L, T + 1/2)` lies outside the disk. -/
lemma transverse_lt_of_profile {a b L T : ℝ} (hc : ContainedChart a |b|)
    (hL : 0≤L) (hT : 0≤T+1/2) (hprofile : L≤a+1/2)
    (hcircle : Q0<L^2+(T+1/2)^2) : |b|<T := by
  by_contra! hb
  have hA := mul_nonneg (sub_nonneg.mpr hprofile) (show 0≤a+1/2+L by linarith [hc.half_le])
  have hB := mul_nonneg (show 0≤|b|-T by linarith)
    (show 0≤|b|+1/2+(T+1/2) by linarith [abs_nonneg b])
  nlinarith [hc.containment]

/-! ### W on the west side of C -/

private def leftProfile (v : ℝ) : ℝ :=
  277/200+v/2-(77/400)*v^2-v^3/12

private def leftPositiveSum (u : ℝ) : ℝ :=
  4009500*(1-u)^5+24748659*u*(1-u)^4+50670036*u^2*(1-u)^3+
    43013403*u^3*(1-u)^2+13241034*u^4*(1-u)+198508*u^5

private lemma left_circle_obstruction {v : ℝ} (hv : 0≤v ∧ v≤2/3) :
    Q0<(leftProfile v)^2+(47/100-(2/3)*v+1/2)^2 := by
  let u := 3*v/2
  have hu0 : 0≤u := by dsimp [u]; linarith [hv.1]
  have hu1 : 0≤1-u := by dsimp [u]; linarith [hv.2]
  have hsum : 0≤leftPositiveSum u := by dsimp [leftPositiveSum]; positivity
  have hp := mul_nonneg hu0 hsum
  have hid : (leftProfile v)^2+(47/100-(2/3)*v+1/2)^2-Q0 =
      1589/200000+u*leftPositiveSum u/65610000 := by
    dsimp [leftProfile,leftPositiveSum,u,Q0]
    ring
  nlinarith only [hid,hp]

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
  have hcube := mul_nonneg hv.1 (show 0≤1/10-v^2/6 by nlinarith)
  have hsinLow := Real.sin_ge_sub_cube hv.1
  have hs : (9/10)*v≤Real.sin v := by nlinarith only [hcube,hsinLow]
  have hprod := mul_le_mul (show 211/300≤1/2-b by linarith [hv.2]) hs
    (show 0≤(9/10)*v by linarith [hv.1]) (show 0≤1/2-b by linarith)
  have hcprod := mul_nonneg (show 0≤a-1/2 by linarith [hc.half_le])
    (show 0≤1-Real.cos v by linarith [Real.cos_le_one v])
  simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hcard
  have hprofile : leftProfile v≤a+1/2 := by
    have hcu := Real.cos_le_one v
    have hsu := Real.sin_le hv.1
    have hcl := Real.one_sub_sq_div_two_le_cos (x := v)
    dsimp [leftProfile]
    nlinarith [hcard,hprod,hcprod,hcu,hsu,c0_bounds.2,hv.1]
  have hL : 0≤leftProfile v := by
    have hp := mul_nonneg hv.1 (show 0≤1/2-(77/400)*v-v^2/12 by nlinarith [hv.2])
    dsimp [leftProfile]
    nlinarith only [hp]
  have hbound := transverse_lt_of_profile hc hL (by linarith [hv.2]) hprofile
    (left_circle_obstruction ⟨hv.1,by linarith [hv.2]⟩)
  linarith [neg_le_abs b]

/-! ### W on its own axis -/

private def wingFrontCubic (v : ℝ) : ℝ :=
  1387/1000+v/2-(387/2000)*v^2-v^3/12

private def wingFrontPositive (u : ℝ) : ℝ :=
  15105600*(1-u)^6+56995200*u*(1-u)^5+235606320*u^2*(1-u)^4+
  521705280*u^3*(1-u)^3+486585525*u^4*(1-u)^2+
  159040590*u^5*(1-u)+756125*u^6

private lemma own_wing_profile_circle {v : ℝ} (hv : 0≤v ∧ v≤1/2) :
    Q0<(wingFrontCubic v)^2+(233/500-(73/100)*v+1/2)^2 := by
  let u := 2*v
  have hu0 : 0≤u := by dsimp [u]; linarith [hv.1]
  have hu1 : 0≤1-u := by dsimp [u]; linarith [hv.2]
  have hpos : 0≤wingFrontPositive u := by dsimp [wingFrontPositive]; positivity
  have hid : (wingFrontCubic v)^2+(233/500-(73/100)*v+1/2)^2-Q0 =
      1/2000+wingFrontPositive u/2880000000 := by
    dsimp [wingFrontCubic,wingFrontPositive,u,Q0]
    ring
  linarith

/-- If W is separated from C along its own axis at angle `π - v`, with
`0 ≤ v ≤ 1/2`, then `|b| < 233/500 - 73v/100`. -/
theorem own_west_transverse_small_angle {v a b cx cy : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy0 : 0≤cy)
    (hv : 0≤v ∧ v≤1/2)
    (hown : 0≤centralMargin .own (Real.pi-v) a b cx cy) :
    |b|<233/500-(73/100)*v := by
  have hcos : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hx' : 387/1000≤1/2-cx := by dsimp [c0] at hx; linarith [rho0_bounds.2]
  have hX := mul_nonneg (show 0≤1/2-cx-387/1000 by linarith) hcos
  have hY := mul_nonneg hy0 hsin
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin] at hown
  have hfront : wingFrontCubic v≤a+1/2 := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := v)
    have hs := Real.sin_ge_sub_cube hv.1
    dsimp [wingFrontCubic]
    nlinarith only [hown,hX,hY,hc,hs]
  have hL : 0≤wingFrontCubic v := by
    have hs := mul_nonneg (sub_nonneg.mpr hv.2) (show 0≤(1:ℝ)/2+v by linarith [hv.1])
    have hc := mul_le_mul_of_nonneg_right (show v^2≤(1:ℝ)/4 by nlinarith) hv.1
    dsimp [wingFrontCubic]
    nlinarith
  exact transverse_lt_of_profile hc hL (by linarith [hv.2]) hfront (own_wing_profile_circle hv)

/-! ### The turned square D -/

/-- A square at the phase `π + d`, `0 ≤ d ≤ π/4`, separated from C along its
own axis has `a + 1/2 ≥ 1 + (387/1000)(cos d + sin d)`. -/
lemma own_front_profile {a b cx cy d : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (hd : 0≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    1+(387/1000)*(Real.cos d+Real.sin d)≤a+1/2 := by
  have hc0 : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1 (by linarith [hd.2,Real.pi_pos])
  have hX := mul_nonneg (show 0≤1/2-cx-387/1000 by dsimp [c0] at hx; linarith [rho0_bounds.2])
    hc0
  have hY := mul_nonneg (show 0≤1/2-cy-387/1000 by dsimp [c0] at hy; linarith [rho0_bounds.2])
    hs0
  simp only [centralMargin,centralNormal,angularWidth,add_comm Real.pi d,
    Real.cos_add_pi,Real.sin_add_pi,abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hown
  nlinarith only [hown,hX,hY]

private def diagonalCircleExcess (d : ℝ) : ℝ :=
  1+(387/1000)^2-Q0+2*(387/1000)*(Real.cos d+Real.sin d)+
    (387/1000)^2*Real.sin (2*d)+(81/100-(17/100)*d)^2

private lemma diagonalCircleExcess_identity (d : ℝ) : diagonalCircleExcess d =
    (1+(387/1000)*(Real.cos d+Real.sin d))^2+(31/100-(17/100)*d+1/2)^2-Q0 := by
  dsimp [diagonalCircleExcess]
  rw [Real.sin_two_mul]
  nlinarith only [Real.sin_sq_add_cos_sq d]

private lemma diagonalCircleExcess_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) diagonalCircleExcess := by
  let f' : ℝ → ℝ := fun x => 2*(387/1000)*(Real.cos x-Real.sin x)+
    2*(387/1000)^2*Real.cos (2*x)-2*(17/100)*(81/100-(17/100)*x)
  let f'' : ℝ → ℝ := fun x => -2*(387/1000)*(Real.sin x+Real.cos x)-
    4*(387/1000)^2*Real.sin (2*x)+2*(17/100)^2
  have hf (x : ℝ) : HasDerivAt diagonalCircleExcess (f' x) x := by
    have htr := ((Real.hasDerivAt_cos x).fun_add (Real.hasDerivAt_sin x)).const_mul
      (2*(387/1000))
    have htwo := (((hasDerivAt_id x).const_mul 2).sin).const_mul ((387/1000)^2)
    have hsq := ((hasDerivAt_const x (81/100)).fun_sub
      ((hasDerivAt_id x).const_mul (17/100))).fun_pow 2
    convert ((htr.const_add (1+(387/1000)^2-Q0)).fun_add htwo).fun_add hsq using 1
    · funext y; dsimp [diagonalCircleExcess]
    · dsimp [f']; ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have htr := ((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
      (2*(387/1000))
    have htwo := (((hasDerivAt_id x).const_mul 2).cos).const_mul (2*(387/1000)^2)
    have hlin := ((hasDerivAt_const x (81/100)).fun_sub
      ((hasDerivAt_id x).const_mul (17/100))).const_mul (-2*(17/100))
    convert (htr.fun_add htwo).fun_add hlin using 1
    · funext y; dsimp [f']; ring
    · dsimp [f'']; ring
  refine concave_of_deriv2 (fun x _ => hf x) (fun x _ => hff x) (fun x h => ?_)
  have hc := Real.cos_nonneg_of_mem_Icc
    (show x∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [h.1,h.2,Real.pi_pos])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := x)
    (by linarith [h.1]) (by linarith [h.2,Real.pi_pos])
  have hs2 := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤2*x by linarith [h.1]) (show 2*x≤Real.pi by linarith [h.2,Real.pi_pos])
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_nonneg hc,abs_of_nonneg hs] at hw
  dsimp [f'']
  linarith

private lemma diagonalCircleExcess_left : 0<diagonalCircleExcess (1/2) := by
  have hc := cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hs := sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  let L : ℝ := 1+(387/1000)*
    ((1-(1/2)^2/2+(1/2)^4/24-(1/2)^6/720)+
     ((1/2)-(1/2)^3/6+(1/2)^5/120-(1/2)^7/5040))
  have hL0 : 0<L := by norm_num [L]
  have hL : L≤1+(387/1000)*(Real.cos (1/2)+Real.sin (1/2)) := by
    dsimp [L]
    nlinarith only [hc,hs]
  have hprod := mul_nonneg (sub_nonneg.mpr hL)
    (show 0≤1+(387/1000)*(Real.cos (1/2)+Real.sin (1/2))+L by linarith)
  rw [diagonalCircleExcess_identity]
  norm_num [L,Q0] at hprod ⊢
  nlinarith only [hprod]

private lemma diagonalCircleExcess_right : 0<diagonalCircleExcess (Real.pi/4) := by
  have hroot : (707:ℝ)/500≤Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hpi : Real.pi≤22/7 := by linarith [Real.pi_lt_d4]
  let L : ℝ := 1+(387/1000)*(707/500)
  let T : ℝ := 81/100-(17/100)*(11/14)
  have hL0 : 0<L := by norm_num [L]
  have hT0 : 0<T := by norm_num [T]
  have hL : L≤1+(387/1000)*Real.sqrt 2 := by dsimp [L]; linarith
  have hT : T≤81/100-(17/100)*(Real.pi/4) := by dsimp [T]; linarith
  have hLs := mul_nonneg (sub_nonneg.mpr hL)
    (show 0≤1+(387/1000)*Real.sqrt 2+L by linarith)
  have hTs := mul_nonneg (sub_nonneg.mpr hT)
    (show 0≤81/100-(17/100)*(Real.pi/4)+T by linarith)
  rw [diagonalCircleExcess_identity,Real.cos_pi_div_four,Real.sin_pi_div_four]
  norm_num [L,T,Q0] at hLs hTs ⊢
  nlinarith only [hLs,hTs]

/-- The profile of D: in a normalized packing, D has radial coordinate more
than `41/40` and transverse coordinate below `31/100 - 17d/100` in absolute
value. -/
theorem normalized_diagonal_profile {R : ℝ} (P : NormalizedPacking R) :
    41/40<P.radial 3 ∧ |P.transverse 3|<31/100-(17/100)*P.diagonalAngle := by
  have hd : 1/2≤P.diagonalAngle ∧ P.diagonalAngle≤Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hown := P.own_separator 3 P.diagonal_own
  rw [show P.phase 3=Real.pi+P.diagonalAngle by
    dsimp [NormalizedPacking.diagonalAngle]; ring] at hown
  have hprofile := own_front_profile P.box.1.2 P.box.2.2
    ⟨by linarith [hd.1],hd.2⟩ hown
  have hmono := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  have hs := sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  have hc := cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hcircle := concave_gt_of_endpoints diagonalCircleExcess_concave hd
    diagonalCircleExcess_left diagonalCircleExcess_right
  rw [diagonalCircleExcess_identity] at hcircle
  refine ⟨by nlinarith only [hprofile,hmono,hs,hc],?_⟩
  apply transverse_lt_of_profile (P.contained 3) _ (by linarith [hd.2,Real.pi_lt_d2])
    hprofile (by linarith)
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show P.diagonalAngle∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (x := P.diagonalAngle)
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  linarith

/-- In a normalized packing, `|b| < 31/100 - (17/100) d` for D. -/
theorem normalized_diagonal_transverse_affine {R : ℝ} (P : NormalizedPacking R) :
    |P.transverse 3|<31/100-(17/100)*P.diagonalAngle :=
  (normalized_diagonal_profile P).2

/-- In a normalized packing, `|b| < 9/40` for D. -/
lemma normalized_diagonal_transverse_small {R : ℝ} (P : NormalizedPacking R) :
    |P.transverse 3|<9/40 := by
  linarith [normalized_diagonal_transverse_affine P,normalized_diagonal_gt_half P]

end SquaresInCircles.Six
