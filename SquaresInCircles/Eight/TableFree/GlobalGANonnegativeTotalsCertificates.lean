module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsData

/-!
# The twelve literal nonnegative-total polynomial certificates

Uncompiled transcription of Sections 6--7 of
`HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md`.
The triangle and rectangle are each treated as one whole domain. The
only divisions remove an exact edge or endpoint. Every arithmetic
comparison below is a finite rational proposition checked by ordinary
kernel reduction when this draft is eventually elaborated.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev d : ℚ := 8/15

def triangleQuotient (ep : Endpoint) (i : Fin 3) : Bivar :=
  divY (numerator .triangle ep i)
def triangleBase (ep : Endpoint) (i : Fin 3) : ℚ[X] :=
  baseY (numerator .triangle ep i)
def triangleFar (ep : Endpoint) (i : Fin 3) : ℚ[X] :=
  restrict (triangleQuotient ep i) X (C d-X)
def rectangleQuotient (ep : Endpoint) (i : Fin 3) : Bivar :=
  (numerator .rectangle ep i).divX
def rectangleBase (ep : Endpoint) (i : Fin 3) : ℚ[X] :=
  baseX (numerator .rectangle ep i)

/-- Equation (59), with both endpoint values retained. -/
def chordQuotient (p : ℚ[X]) : ℚ[X] :=
  (p-C (p.eval 0)-C ((p.eval d-p.eval 0)/d)*X)/(X*(C d-X))
def chordPolynomial (p : ℚ[X]) : ℚ[X] :=
  C (p.eval 0)+C ((p.eval d-p.eval 0)/d)*X+X*(C d-X)*chordQuotient p

def triangleDerivativeReserve (ep : Endpoint) : Fin 3→ℚ :=
  match ep with
  | .atA => ![-23/100,-43/100,-1/4]
  | .atT => ![-6/25,-21/50,-13/100]
def triangleFarReserve (ep : Endpoint) : Fin 2→ℚ :=
  match ep with
  | .atA => ![13/200,143/1000]
  | .atT => ![31/500,3/20]
def triangleFarDerivative (ep : Endpoint) : ℚ :=
  match ep with | .atA => -4/5 | .atT => -8/5
def triangleFarEndpoint (ep : Endpoint) : ℚ :=
  match ep with | .atA => 213/1000 | .atT => 43/500
def triangleInitialValue (ep : Endpoint) : ℚ :=
  match ep with | .atA => 1727/1000000 | .atT => 893/500000
def triangleInitialSlope (ep : Endpoint) : ℚ :=
  match ep with | .atA => 27/500 | .atT => 57/1000
def chordEndpointReserve (ep : Endpoint) (i : Fin 3) : ℚ :=
  match ep with
  | .atA => 121/1250
  | .atT => if i=1 then 893/500000 else 133/5000
def chordQuotientReserve (ep : Endpoint) (i : Fin 3) : ℚ :=
  match ep with
  | .atA => 21/100
  | .atT => if i=1 then -657/100000 else 5/4

def rectangleQuotientReserve (ep : Endpoint) : Fin 3→ℚ :=
  match ep with
  | .atA => ![13/250,18/125,223/500]
  | .atT => ![23/500,137/1000,259/1000]
def rectangleSlopeReserve (ep : Endpoint) : Fin 3→ℚ :=
  match ep with
  | .atA => ![0,1/10,99/50]
  | .atT => ![29/100000,53/500,21/10]
def massReserve : Region→ℚ | .triangle => 71/100 | .rectangle => 77/100

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    transform r (mass r ep i j)=expansion 3 (transform r (mass r ep i j)) ∧
    massReserve r<lowerOn r 3 (mass r ep i j) := by
  cases r <;> cases ep <;> fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_derivative_certificate (ep : Endpoint) (i : Fin 3) :
    transform .triangle (derivativeY (triangleQuotient ep i))=
      expansion (degree .triangle ep i) (transform .triangle (derivativeY (triangleQuotient ep i))) ∧
    upperOn .triangle (degree .triangle ep i) (derivativeY (triangleQuotient ep i))<
      triangleDerivativeReserve ep i := by
  cases ep <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_far_certificate (ep : Endpoint) (i : Fin 2) :
    WholeIntervalPolynomial.centered 0 d (triangleFar ep i.castSucc)=
      WholeIntervalPolynomial.expansion (degree .triangle ep i.castSucc)
        (WholeIntervalPolynomial.centered 0 d (triangleFar ep i.castSucc)) ∧
    triangleFarReserve ep i<WholeIntervalPolynomial.lowerOn
      (degree .triangle ep i.castSucc) 0 d (triangleFar ep i.castSucc) := by
  cases ep <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_far_B_certificate (ep : Endpoint) :
    WholeIntervalPolynomial.centered 0 d (triangleFar ep 2).derivative=
      WholeIntervalPolynomial.expansion (degree .triangle ep 2)
        (WholeIntervalPolynomial.centered 0 d (triangleFar ep 2).derivative) ∧
    WholeIntervalPolynomial.upperOn (degree .triangle ep 2) 0 d
      (triangleFar ep 2).derivative<triangleFarDerivative ep ∧
    triangleFarEndpoint ep<(triangleFar ep 2).eval d := by
  cases ep <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_initial_certificate (ep : Endpoint) :
    triangleInitialValue ep<(triangleBase ep 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (triangleBase ep 0).divX=
      WholeIntervalPolynomial.expansion (degree .triangle ep 0)
        (WholeIntervalPolynomial.centered 0 d (triangleBase ep 0).divX) ∧
    triangleInitialSlope ep<WholeIntervalPolynomial.lowerOn
      (degree .triangle ep 0) 0 d (triangleBase ep 0).divX := by
  cases ep <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_AG_certificate :
    WholeIntervalPolynomial.centered 0 d (triangleBase .atA 1)=
      WholeIntervalPolynomial.expansion (degree .triangle .atA 1)
        (WholeIntervalPolynomial.centered 0 d (triangleBase .atA 1)) ∧
    (21/12500:ℚ)<WholeIntervalPolynomial.lowerOn
      (degree .triangle .atA 1) 0 d (triangleBase .atA 1) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_chord_certificate (ep : Endpoint) (i : Fin 3)
    (hi : i=2 ∨ (ep=.atT ∧ i=1)) :
    triangleBase ep i=chordPolynomial (triangleBase ep i) ∧
    chordEndpointReserve ep i<(triangleBase ep i).eval 0 ∧
    chordEndpointReserve ep i<(triangleBase ep i).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase ep i))=
      WholeIntervalPolynomial.expansion (degree .triangle ep i)
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase ep i))) ∧
    chordQuotientReserve ep i<WholeIntervalPolynomial.lowerOn
      (degree .triangle ep i) 0 d (chordQuotient (triangleBase ep i)) := by
  rcases hi with rfl | ⟨rfl,rfl⟩
  · cases ep <;> decide
  · decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_quotient_certificate (ep : Endpoint) (i : Fin 3) :
    transform .rectangle (rectangleQuotient ep i)=
      expansion (degree .rectangle ep i) (transform .rectangle (rectangleQuotient ep i)) ∧
    rectangleQuotientReserve ep i<lowerOn .rectangle
      (degree .rectangle ep i) (rectangleQuotient ep i) := by
  cases ep <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_AH_certificate :
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 0)=
      WholeIntervalPolynomial.expansion (degree .rectangle .atA 0)
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 0)) ∧
    (1/800:ℚ)<WholeIntervalPolynomial.lowerOn
      (degree .rectangle .atA 0) 0 d (rectangleBase .atA 0) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_initial_certificate (ep : Endpoint) (i : Fin 3)
    (hi : ¬(ep=.atA ∧ i=0)) :
    (17/10000:ℚ)<(rectangleBase ep i).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase ep i).divX=
      WholeIntervalPolynomial.expansion (degree .rectangle ep i)
        (WholeIntervalPolynomial.centered 0 d (rectangleBase ep i).divX) ∧
    rectangleSlopeReserve ep i<WholeIntervalPolynomial.lowerOn
      (degree .rectangle ep i) 0 d (rectangleBase ep i).divX := by
  cases ep <;> fin_cases i <;> norm_num at hi <;> decide

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Certificate
