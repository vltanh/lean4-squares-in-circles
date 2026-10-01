import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.Profile

/-!
# Own W, cardinal S: positivity of the profile

Both versions of the profile are positive on the rectangle `0 ≤ v ≤ 2/3`,
`1/2 ≤ d ≤ 11/14`. They are concave in each variable, so it suffices that they
are positive at the four corners, and there Taylor polynomials of `sin` and
`cos` bound them below by more than `1/40`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalSouth

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def lowerPolynomial (upper : Bool) (v d : ℝ) : ℝ :=
  constantTerm upper+
    westWeight*(wingCos*cosLower v+(1/2+centerY upper)*sinLower v)+
    diagonalWeight*(wingCos*cosLower d+(1/2-centerY upper)*sinLower d)+
    sinLower (d+v)-chordSin*sinUpper ((d+v)/2)-chordCos*cosUpper ((d+v)/2)-
    2*southB*cosUpper (d/2)+sinLower (d/2)

private lemma polynomial_le (upper : Bool) {v d : ℝ} (hv : 0 ≤ v) (hd : 0 ≤ d) :
    lowerPolynomial upper v d ≤ profile upper v d := by
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cd := Seven.cos_lower_six hd
  have sd := Seven.sin_lower_seven hd
  have sq := Seven.sin_lower_seven (x := d+v) (by linarith)
  have sh := Seven.sin_upper_five (x := (d+v)/2) (by linarith)
  have ch := Seven.cos_upper_four (x := (d+v)/2) (by linarith)
  have ct := Seven.cos_upper_four (x := d/2) (by linarith)
  have st := Seven.sin_lower_seven (x := d/2) (by linarith)
  cases upper <;>
    dsimp [lowerPolynomial,profile,westTerm,diagonalTerm,chord,halfLinear,
      westWeight,diagonalWeight,wingCos,centerY,southB,chordSin,chordCos,
      cosLower,cosUpper,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cd,sd,sq,sh,ch,ct,st]

private def vEndpoint (upper : Bool) : ℝ := if upper then 2/3 else 0
private def dEndpoint (upper : Bool) : ℝ := if upper then 11/14 else 1/2

private lemma endpoint_margin (face west diagonal : Bool) :
    (1:ℝ)/40 < lowerPolynomial face (vEndpoint west) (dEndpoint diagonal) := by
  cases face <;> cases west <;> cases diagonal <;>
    norm_num [lowerPolynomial,constantTerm,westWeight,diagonalWeight,wingCos,centerY,
      southB,chordSin,chordCos,cosLower,cosUpper,sinLower,sinUpper,vEndpoint,dEndpoint]

lemma endpoint_positive (face west diagonal : Bool) :
    0 < profile face (vEndpoint west) (dEndpoint diagonal) := by
  have hv : 0 ≤ vEndpoint west := by cases west <;> norm_num [vEndpoint]
  have hd : 0 ≤ dEndpoint diagonal := by cases diagonal <;> norm_num [dEndpoint]
  have hp := polynomial_le face hv hd
  have hm := endpoint_margin face west diagonal
  linarith

/-- The profile is positive on the rectangle `[0, 2/3] × [1/2, 11/14]`. -/
theorem positive (upper : Bool) {v d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 < profile upper v d := by
  have hl : 0 < profile upper v (1/2) :=
    positive_on_concave_interval (f := fun w => profile upper w (1/2)) (x := v)
      (profile_west_concave upper (d := 1/2) (by norm_num)) hv
      (endpoint_positive upper false false) (endpoint_positive upper true false)
  have hu : 0 < profile upper v (11/14) :=
    positive_on_concave_interval (f := fun w => profile upper w (11/14)) (x := v)
      (profile_west_concave upper (d := 11/14) (by norm_num)) hv
      (endpoint_positive upper false true) (endpoint_positive upper true true)
  exact positive_on_concave_interval (profile_diagonal_concave upper hv) hd hl hu

end SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
