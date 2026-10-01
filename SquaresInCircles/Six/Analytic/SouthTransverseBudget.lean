import SquaresInCircles.Six.Analytic.TransverseProfileBounds
import SquaresInCircles.Six.Analytic.ConstrainedCircleSupport
import SquaresInCircles.Six.Analytic.PrimaryClassification

/-!
# S read as W

The reflection in the diagonal maps a square at angle `3π/2 + s` with
coordinates `(a, b)` to a square at angle `π - s` with coordinates `(a, -b)`,
and exchanges the two coordinates of the centre of C. The margins of the
separators of C and S, along the own axis of S and along the south side of C,
are the margins of the reflected square along its own axis and along the west
side of C.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma south_own_as_west (s a b cx cy : ℝ) :
    centralMargin .own (Real.pi-s) a (-b) cy cx =
      centralMargin .own (3*Real.pi/2+s) a b cx cy := by
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    Real.cos_add,Real.sin_add,south_cos,south_sin,zero_mul,neg_one_mul,add_zero,abs_neg]
  ring_nf

lemma south_cardinal_as_west (s a b cx cy : ℝ) :
    centralMargin .west (Real.pi-s) a (-b) cy cx =
      centralMargin .south (3*Real.pi/2+s) a b cx cy := by
  simp only [centralMargin,centerX,centerY,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    Real.cos_add,Real.sin_add,south_cos,south_sin,zero_mul,neg_one_mul,add_zero,abs_neg]
  ring_nf

end SquaresInCircles.Six.Analytic
