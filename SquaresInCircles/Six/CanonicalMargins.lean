import SquaresInCircles.Six.Patterns

/-!
# P1/P2 and the equality obstruction of canonical OWN bits

The four identities are exact for every angle and signed transverse
coordinate. The zero-angle corollary is the canonical-bit contradiction used
by the forbidden patterns and noncandidate survivors. It does not assume an
unproved equality classification.
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

/-- Cardinal is preferred on ties, so an OWN helper cannot have zero deviation. -/
theorem own_angle_ne_zero (i : Fin 5) (hi : P.ownBits i=true) : P.helperAngle i ≠ 0 := by
  intro hz
  have ht : P.phase i=cardinalCenter (matchingCardinal i) := sub_eq_zero.mp hz
  have h := P.canonical_gap_pos i hi
  rw [ht,own_cardinal_at_center _ (matchingCardinal_isCardinal i)] at h
  linarith

lemma zero_angle_cardinal (i : Fin 5) (hi : P.helperAngle i=0) : P.ownBits i=false := by
  cases h : P.ownBits i with
  | false => rfl
  | true => exact False.elim (P.own_angle_ne_zero i h hi)

/-- Once the four cardinal deviations vanish, the code is exactly Pattern 8. -/
theorem pattern_eight_of_zero_helpers
    (hE : P.helperAngle 0=0) (hN : P.helperAngle 1=0)
    (hW : P.helperAngle 2=0) (hS : P.helperAngle 4=0) : P.patternCode=8 := by
  have he := P.zero_angle_cardinal 0 hE
  have hn := P.zero_angle_cardinal 1 hN
  have hw := P.zero_angle_cardinal 2 hW
  have hs := P.zero_angle_cardinal 4 hS
  simp only [patternCode,CentralPattern.code,he,hn,hw,hs,P.diagonal_own]
  norm_num

end Normalization.NormalizedPacking
end SquaresInCircles.Six
