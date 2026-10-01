import SquaresInCircles.Six.Stress.Support

/-!
# The support of a square in a disk

Let a centre have local coordinates `(a, b)` with
`(|a| + 1/2)^2 + (|b| + 1/2)^2 ≤ R^2`, and let a force have local components
`(x, y)`. Then `x a + y b ≤ scalarSupport R x y` (`scalar_center_support`).
With `U ≥ V` the larger and the smaller of `|x|` and `|y|`, the support is
`rhoAt R * U` when `2 R V ≤ sqrt (U^2 + V^2)`, the cap case: in `A = |a| + 1/2`,
`B = |b| + 1/2` the maximum over the disk with `B ≥ 1/2` is then at the corner
`(sqrt (R^2 - 1/4), 1/2)`. Otherwise it is the far-vertex value
`R sqrt (U^2 + V^2) - (U + V)/2`, by Cauchy–Schwarz.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

/-- `sqrt (R^2 - 1/4) - 1/2`, the largest first coordinate of the centre of a
unit square in the disk of radius `R` whose second coordinate is `0`. -/
def rhoAt (R : ℝ) : ℝ := Real.sqrt (R^2-1/4)-1/2

/-- The support for a force with components `U ≥ V ≥ 0`: the cap value or the
far-vertex value. -/
def orderedSupport (R U V : ℝ) : ℝ :=
  if 2*R*V ≤ Real.sqrt (U^2+V^2) then rhoAt R*U
  else R*Real.sqrt (U^2+V^2)-(U+V)/2

/-- The support for a force with local components `(x, y)`. -/
def scalarSupport (R x y : ℝ) : ℝ :=
  if |y| ≤ |x| then orderedSupport R |x| |y| else orderedSupport R |y| |x|

private lemma corner_support {A B a b c s q : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hc : 0 ≤ c)
    (hcircle : a^2+b^2=q) (hbox : A^2+B^2 ≤ q)
    (hslope : a*s ≤ b*c) : A*c+B*s ≤ a*c+b*s := by
  have ht : a*(A-a)+b*(B-b) ≤ 0 := by
    nlinarith [sq_nonneg (A-a),sq_nonneg (B-b)]
  have hct := mul_nonpos_of_nonneg_of_nonpos hc ht
  have hsl := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hp : a*(A*c+B*s-(a*c+b*s)) ≤ 0 := by nlinarith
  by_contra! h
  have hpos := mul_pos ha (sub_pos.mpr h)
  linarith

private lemma cap_slope {R U V : ℝ} (hR : 1/2 < R) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h : 2*R*V ≤ Real.sqrt (U^2+V^2)) :
    Real.sqrt (R^2-1/4)*V ≤ U/2 := by
  have hrad : 0 ≤ R^2-1/4 := by nlinarith [sq_nonneg (R-1/2)]
  have hs := Real.sq_sqrt hrad
  have hn := Real.sq_sqrt (show 0 ≤ U^2+V^2 by positivity)
  have hp := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ Real.sqrt (U^2+V^2)+2*R*V by
      positivity)
  have hmul := congrArg (fun z : ℝ => z*V^2) hs
  have hsquare : (2*Real.sqrt (R^2-1/4)*V)^2 ≤ U^2 := by nlinarith
  have hnn : 0 ≤ 2*Real.sqrt (R^2-1/4)*V := by positivity
  by_contra! hbad
  have ht := mul_pos
    (show 0 < 2*Real.sqrt (R^2-1/4)*V-U by linarith)
    (show 0 < 2*Real.sqrt (R^2-1/4)*V+U by linarith)
  nlinarith

lemma ordered_center_support {R a b U V : ℝ}
    (hR : 1/2 < R) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ R^2) :
    |a| *U+|b| *V ≤ orderedSupport R U V := by
  unfold orderedSupport
  split_ifs with hswitch
  · have hrad : 0 < R^2-1/4 := by nlinarith [sq_nonneg (R-1/2)]
    have ha0 := Real.sqrt_pos.mpr hrad
    have hid := Real.sq_sqrt hrad.le
    have hslope := cap_slope hR hU hV hswitch
    have hcorner := corner_support
      (A := |a|+1/2) (B := |b|+1/2)
      (a := Real.sqrt (R^2-1/4)) (b := (1:ℝ)/2) (c := U) (s := V)
      ha0 (by linarith [abs_nonneg b]) hU (by nlinarith) hbox (by linarith)
    dsimp [rhoAt]
    nlinarith
  · have hround := dot_le_radius (v := (U,V)) (p := (|a|+1/2,|b|+1/2))
      (by linarith : 0 ≤ R) hbox
    dsimp [dot,vectorLength,normSq] at hround
    nlinarith

/-- The support bound for a centre with local coordinates `(a, b)` and a force
with local components `(x, y)`. -/
theorem scalar_center_support {R a b x y : ℝ}
    (hR : 1/2 < R) (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ R^2) :
    x*a+y*b ≤ scalarSupport R x y := by
  have hx : x*a ≤ |a| *|x| := by
    simpa only [abs_mul,mul_comm] using le_abs_self (x*a)
  have hy : y*b ≤ |b| *|y| := by
    simpa only [abs_mul,mul_comm] using le_abs_self (y*b)
  unfold scalarSupport
  split_ifs
  · have hh := ordered_center_support hR (abs_nonneg x) (abs_nonneg y) hbox
    linarith
  · have hbox' : (|b|+1/2)^2+(|a|+1/2)^2 ≤ R^2 := by linarith
    have hh := ordered_center_support hR (abs_nonneg y) (abs_nonneg x) hbox'
    linarith

end SquaresInCircles.Six.Stress
