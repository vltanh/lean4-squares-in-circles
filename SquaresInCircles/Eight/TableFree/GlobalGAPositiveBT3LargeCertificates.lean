module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LargeData

/-!
# Literal whole-domain certificates for the six BT3 endpoint numerators

Uncompiled rational reductions from Sections 7--8 of the hand proof.
Each transform covers its entire native triangle, rectangle, or edge.
The only polynomial divisions remove an exactly vanishing base edge
or the two endpoints of the displayed chord.
-/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (r : Region) (i : Fin 3) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  cases r <;> fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_derivative_certificate (i : Fin 3) :
    transform .triangle (derivativeY (triangleQuotient i))=
      expansion 39 (transform .triangle (derivativeY (triangleQuotient i))) ∧
    upperOn .triangle 39 (derivativeY (triangleQuotient i))<triangleDerivativeReserve i := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_far_certificate (i : Fin 2) :
    WholeIntervalPolynomial.centered 0 d (triangleFar i.castSucc)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar i.castSucc)) ∧
    triangleFarReserve i<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar i.castSucc) := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_far_B_certificate :
    WholeIntervalPolynomial.centered 0 d (triangleFar 2).derivative=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar 2).derivative) ∧
    WholeIntervalPolynomial.upperOn 39 0 d (triangleFar 2).derivative<-(583/1000:ℚ) ∧
    (113/500:ℚ)<(triangleFar 2).eval d := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_initial_certificate :
    (893/500000:ℚ)<(triangleBase 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (triangleBase 0).divX=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleBase 0).divX) ∧
    (8/125:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleBase 0).divX := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_chord_certificate :
    triangleBase 1=chordPolynomial (triangleBase 1) ∧
    (893/500000:ℚ)<(triangleBase 1).eval 0 ∧
    (893/500000:ℚ)<(triangleBase 1).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase 1))=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase 1))) ∧
    (17/200:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (chordQuotient (triangleBase 1)) := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem triangle_B_certificate :
    WholeIntervalPolynomial.centered 0 d (triangleBase 2)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleBase 2)) ∧
    (3/100:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleBase 2) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_quotient_certificate (i : Fin 3) :
    transform .rectangle (rectangleQuotient i)=expansion 35
      (transform .rectangle (rectangleQuotient i)) ∧
    rectangleQuotientReserve i<lowerOn .rectangle 35 (rectangleQuotient i) := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_H_certificate :
    WholeIntervalPolynomial.centered 0 d (rectangleBase 0)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase 0)) ∧
    (4/3125:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 d (rectangleBase 0) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_initial_certificate (i : Fin 2) :
    rectangleInitialReserve i<(rectangleBase i.succ).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase i.succ).divX=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase i.succ).divX) ∧
    rectangleSlopeReserve i<WholeIntervalPolynomial.lowerOn 35 0 d
      (rectangleBase i.succ).divX := by
  fin_cases i <;> decide

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LargeCertificate
