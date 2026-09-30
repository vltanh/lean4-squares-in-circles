module
public import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Vertices

@[expose] public section

/-!
# Exact endpoint margins for the west-dominant profile

The preceding concavity proof leaves four vertices of the shared-angle polygon
and two diagonal endpoints. The Boolean is the supporting central y face.
Every displayed Taylor lower polynomial is strictly greater than 1/30 at these
vertices. Their evaluation is ordinary rational arithmetic after the analytic
reduction, not a generated stress table or a searched partition.
Compilation and kernel acceptance remain unverified.
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
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cs := Seven.cos_lower_six hs
  have ss := Seven.sin_lower_seven hs
  have cd := Seven.cos_lower_six hd
  have sd := Seven.sin_lower_seven hd
  have sq := Seven.sin_lower_seven (x := d+v) (by linarith)
  have sh := Seven.sin_upper_five (x := (d+v)/2) (by linarith)
  have ch := Seven.cos_upper_four (x := (d+v)/2) (by linarith)
  have cr := Seven.cos_upper_four (x := d-s) (by linarith)
  have sr := Seven.sin_lower_seven (x := d-s) (by linarith)
  have crr := Seven.cos_lower_six (x := 2*(d-s)) (by linarith)
  cases upper <;>
    dsimp [lowerPolynomial,profile,constantTerm,westSlice,southSlice,westTerm,southTerm,
      diagonalTerm,chord,transverse,westWeight,southWeight,diagonalWeight,
      wingCos,wingSin,centerY,chordSin,chordCos,cosLower,cosUpper,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cs,ss,cd,sd,sq,sh,ch,cr,sr,crr]

/-- The four coordinates are the vertices proved sufficient in Vertices.lean. -/
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

/-- Strict positivity on the whole west-dominant domain, for both central faces. -/
theorem positive (upper : Bool) {v s d : ℝ}
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : 0 < profile upper v s d := by
  exact positive_of_diagonal_endpoints upper hv hs horder hsum hd
    (endpoint_vertices upper false) (endpoint_vertices upper true)

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
