import SquaresInCircles.Six.Normalization.StrongCardinal

/-!
# The primary and the side margins

For a square at the phase `θ + t`, where `θ` is the direction `0`, `π/2`, `π`
or `3π/2` of a side of C, its margin from C along its primary axis minus its
margin along that side is `(1 - cos t)(a + x) + sin t (b - y)` for the east
side, with its chart `(a, b)` and the centre `(x, y)` of C, and similar for the
other three. At `t = 0` the two margins agree. So in a normalized packing a
square separated from C along its primary axis but not along the matching side
of C is turned from the direction `θ` of that side.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

lemma own_minus_east (t a b x y : ℝ) :
    centralMargin .own t a b x y-centralMargin .east t a b x y =
      (1-Real.cos t)*(a+x)+Real.sin t*(b-y) := by
  dsimp [centralMargin,centralNormal,centerX]
  ring

lemma own_minus_north (t a b x y : ℝ) :
    centralMargin .own (Real.pi/2+t) a b x y-
      centralMargin .north (Real.pi/2+t) a b x y =
      (1-Real.cos t)*(a+y)+Real.sin t*(b+x) := by
  simp only [centralMargin,centralNormal,centerY,Real.cos_add,Real.sin_add,
    Real.cos_pi_div_two,Real.sin_pi_div_two,zero_mul,one_mul,zero_sub,add_zero]
  ring

lemma own_minus_west (t a b x y : ℝ) :
    centralMargin .own (Real.pi+t) a b x y-
      centralMargin .west (Real.pi+t) a b x y =
      (1-Real.cos t)*(a-x)+Real.sin t*(b+y) := by
  have hc : Real.cos (Real.pi+t) = -Real.cos t := by rw [add_comm,Real.cos_add_pi]
  have hs : Real.sin (Real.pi+t) = -Real.sin t := by rw [add_comm,Real.sin_add_pi]
  simp only [centralMargin,centralNormal,centerX,hc,hs]
  ring

lemma own_minus_south (t a b x y : ℝ) :
    centralMargin .own (3*Real.pi/2+t) a b x y-
      centralMargin .south (3*Real.pi/2+t) a b x y =
      (1-Real.cos t)*(a-y)+Real.sin t*(b-x) := by
  simp only [centralMargin,centralNormal,centerY,Real.cos_add,Real.sin_add,
    south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,add_zero]
  ring

lemma own_cardinal_at_center (k : CentralAxis) (hk : IsCardinal k)
    (a b x y : ℝ) :
    centralMargin .own (cardinalCenter k) a b x y =
      centralMargin k (cardinalCenter k) a b x y := by
  rcases hk with rfl | rfl | rfl | rfl
  · have h := own_minus_east 0 a b x y
    simpa [cardinalCenter] using sub_eq_zero.mp (by simpa using h)
  · have h := own_minus_north 0 a b x y
    simpa [cardinalCenter] using sub_eq_zero.mp (by simpa using h)
  · have h := own_minus_west 0 a b x y
    simpa [cardinalCenter] using sub_eq_zero.mp (by simpa using h)
  · have h := own_minus_south 0 a b x y
    simpa [cardinalCenter] using sub_eq_zero.mp (by simpa using h)

namespace Normalization.NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

lemma canonical_gap_pos (i : Fin 5) (hi : P.ownBits i=true) :
    0 < centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2-
      centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 := by
  have ho := P.own_separator i hi
  have hk := (P.toPinPacking.canonicalOwn_eq_true i).mp hi
  linarith

/-- A square that is not separated from C along the matching side of C has its
phase different from the direction of that side. -/
theorem own_angle_ne_zero (i : Fin 5) (hi : P.ownBits i=true) : P.helperAngle i ≠ 0 := by
  intro hz
  have ht : P.phase i=cardinalCenter (matchingCardinal i) := sub_eq_zero.mp hz
  have h := P.canonical_gap_pos i hi
  rw [ht,own_cardinal_at_center _ (matchingCardinal_isCardinal i)] at h
  linarith

end Normalization.NormalizedPacking
end SquaresInCircles.Six
