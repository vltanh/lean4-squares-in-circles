import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Vertices

/-!
# Positivity of the west-dominant profile

Taylor polynomials of `sin` and `cos` bound the profile below by a polynomial
in the three angles, and at the four vertices of the domain, with `d = 1/2` or
`d = 11/14` and for either bound on the centre of C, this polynomial exceeds
`1/30`. With the reduction to the vertices the profile is positive on the
whole west-dominant domain.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def lowerPolynomial (upper : Bool) (v s d : ℝ) : ℝ :=
  constantTerm+
    westWeight*(wingCos*cosLower v+(1/2+centerY upper)*sinLower v)+
    southWeight*((1/2-centerY upper)*cosLower s+wingSin*sinLower s)+
    diagonalWeight*(wingCos*cosLower d+(1/2-centerY upper)*sinLower d)+
    sinLower (d+v)-chordSin*sinUpper ((d+v)/2)-chordCos*cosUpper ((d+v)/2)-
    wingSin*cosUpper (d-s)+(1/2)*sinLower (d-s)-1/24+(1/24)*cosLower (2*(d-s))

private lemma polynomial_le (upper : Bool) {v s d : ℝ}
    (hv : 0 ≤ v) (hs : 0 ≤ s) (hd : 0 ≤ d) (hr : s ≤ d) :
    lowerPolynomial upper v s d ≤ profile upper v s d := by
  -- The Taylor polynomials are kept as atoms; the comparison is then linear.
  have cv : cosLower v ≤ Real.cos v := Seven.cos_lower_six hv
  have sv : sinLower v ≤ Real.sin v := Seven.sin_lower_seven hv
  have cs : cosLower s ≤ Real.cos s := Seven.cos_lower_six hs
  have ss : sinLower s ≤ Real.sin s := Seven.sin_lower_seven hs
  have cd : cosLower d ≤ Real.cos d := Seven.cos_lower_six hd
  have sd : sinLower d ≤ Real.sin d := Seven.sin_lower_seven hd
  have sq : sinLower (d+v) ≤ Real.sin (d+v) := Seven.sin_lower_seven (by linarith)
  have sh : Real.sin ((d+v)/2) ≤ sinUpper ((d+v)/2) := Seven.sin_upper_five (by linarith)
  have ch : Real.cos ((d+v)/2) ≤ cosUpper ((d+v)/2) := Seven.cos_upper_four (by linarith)
  have cr : Real.cos (d-s) ≤ cosUpper (d-s) := Seven.cos_upper_four (by linarith)
  have sr : sinLower (d-s) ≤ Real.sin (d-s) := Seven.sin_lower_seven (by linarith)
  have crr : cosLower (2*(d-s)) ≤ Real.cos (2*(d-s)) := Seven.cos_lower_six (by linarith)
  cases upper <;>
    simp only [lowerPolynomial,profile,constantTerm,westSlice,southSlice,westTerm,southTerm,
      diagonalTerm,chord,transverse,westWeight,southWeight,diagonalWeight,
      wingCos,wingSin,centerY,chordSin,chordCos,Bool.false_eq_true,ite_false,ite_true] <;>
    linarith only [cv,sv,cs,ss,cd,sd,sq,sh,ch,cr,sr,crr]

private def vertexV (i : Fin 4) : ℝ := ![0,2/3,2/3,12/25] i
private def vertexS (i : Fin 4) : ℝ := ![0,0,22/75,12/25] i
private def diagonalEndpoint (upper : Bool) : ℝ := if upper then 11/14 else 1/2

private lemma vertex_margin (face endpoint : Bool) (i : Fin 4) :
    (1:ℝ)/30 < lowerPolynomial face (vertexV i) (vertexS i) (diagonalEndpoint endpoint) := by
  cases face <;> cases endpoint <;> fin_cases i <;>
    norm_num [lowerPolynomial,constantTerm,westWeight,southWeight,diagonalWeight,
      wingCos,wingSin,centerY,chordSin,chordCos,cosLower,cosUpper,sinLower,sinUpper,
      vertexV,vertexS,diagonalEndpoint]

lemma vertex_positive (face endpoint : Bool) (i : Fin 4) :
    0 < profile face (vertexV i) (vertexS i) (diagonalEndpoint endpoint) := by
  have hv : 0 ≤ vertexV i := by fin_cases i <;> norm_num [vertexV]
  have hs : 0 ≤ vertexS i := by fin_cases i <;> norm_num [vertexS]
  have hd : 0 ≤ diagonalEndpoint endpoint := by cases endpoint <;> norm_num [diagonalEndpoint]
  have hr : vertexS i ≤ diagonalEndpoint endpoint := by
    cases endpoint <;> fin_cases i <;> norm_num [vertexS,diagonalEndpoint]
  have hp := polynomial_le face hv hs hd hr
  have hm := vertex_margin face endpoint i
  linarith

lemma endpoint_vertices (face endpoint : Bool) : FourVertices face (diagonalEndpoint endpoint) := by
  have h0 := vertex_positive face endpoint 0
  have h1 := vertex_positive face endpoint 1
  have h2 := vertex_positive face endpoint 2
  have h3 := vertex_positive face endpoint 3
  exact ⟨h0,h1,h2,h3⟩

/-- The west-dominant profile is positive on its whole domain, for either bound
on the centre of C. -/
theorem positive (upper : Bool) {v s d : ℝ}
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : 0 < profile upper v s d := by
  exact positive_of_diagonal_endpoints upper hv hs horder hsum hd
    (endpoint_vertices upper false) (endpoint_vertices upper true)

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
