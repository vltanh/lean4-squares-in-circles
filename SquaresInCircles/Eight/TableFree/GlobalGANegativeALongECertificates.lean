module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEData

/-!
# The twelve longer-E numerator certificates

Uncompiled transcription of Section 7. Each arithmetic proposition is
the exact finite coefficient formula of the hand proof, to be reduced by
the standard kernel when this source is eventually elaborated. The TE
base is identified with the earlier pure-T base; the RE trapezoid uses
its three actual boundary curves and its whole-domain second derivative.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

def massReserve : Region → ℚ
  | .TE => 71/100 | .TC => 107/100 | .RE => 11/10 | .RC => 103/100
def TEbase (i : Fin 3) : ℚ[X] := TwoVariablePolynomial.baseY (numerator .TE i)
def TEquotient (i : Fin 3) : Bivar := divY (numerator .TE i)
def TEfar (i : Fin 3) : ℚ[X] := restrict (TEquotient i) X (C (8/15)-X)
def TEderivativeReserve : Fin 3 → ℚ := ![-67/100,-51/100,-11/25]
def TEfarReserve : Fin 3 → ℚ := ![47/1000,13/200,11/500]
def TEcentered : ℚ[X] := (TEfar 0).comp (X+C (4/15))
def TEcoefficient (j : ℕ) : ℚ := TEcentered.coeff j
def TEtail : ℚ := ∑j : Fin 37,|TEcoefficient (j.val+3)|*(4/15)^(j.val+1)
def TEcurvature : ℚ := TEcoefficient 2-TEtail
def TCreserve : Fin 3 → ℚ := ![3/125,43/1000,153/500]
def REcurvatureReserve : Fin 3 → ℚ := ![-7,-7,-11]
def REboundary (i j : Fin 3) : ℚ[X] :=
  match j.val with
  | 0 => restrict (numerator .RE i) 0 X
  | 1 => restrict (numerator .RE i) (C (1/6)) X
  | _ => restrict (numerator .RE i) X (C (19/50)-X)
def RElength (j : Fin 3) : ℚ := ![19/50,16/75,1/6] j
def REreserve (i j : Fin 3) : ℚ :=
  ![![13/10000,37/2500,67/2500],![13/10000,37/2500,67/2500],
    ![1587/5000,37/2500,13/500]] i j
def RCbase (i : Fin 3) : ℚ[X] := TwoVariablePolynomial.baseY (numerator .RC i)
def RCquotient (i : Fin 3) : Bivar := divY (numerator .RC i)
def RCbaseReserve : Fin 3 → ℚ := ![11/500,11/500,21/1000]
def RCquotientReserve : Fin 3 → ℚ := ![9/10,123/100,91/25]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (r : Region) (i : Fin 3) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  cases r <;> fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem TEbase_identity (i : Fin 3) :
    TEbase i=NonnegativeTotals.Certificate.triangleBase .atT i := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem TEderivative_certificate (i : Fin 3) :
    transform .TE (derivativeY (TEquotient i))=
      expansion 39 (transform .TE (derivativeY (TEquotient i))) ∧
    upperOn .TE 39 (derivativeY (TEquotient i))<TEderivativeReserve i := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem TEfar_GB_certificate (i : Fin 3) (hi : i=1∨i=2) :
    WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)=
      WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 (8/15) (TEfar i)) ∧
    TEfarReserve i<WholeIntervalPolynomial.lowerOn 39 0 (8/15) (TEfar i) := by
  rcases hi with rfl|rfl <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem TEfar_H_certificate :
    TEcentered=C (TEcoefficient 0)+C (TEcoefficient 1)*X+C (TEcoefficient 2)*X^2+
      ∑j : Fin 37,C (TEcoefficient (j.val+3))*X^(j.val+3) ∧
    (133/100:ℚ)<TEcurvature ∧
    (47/1000:ℚ)<TEcoefficient 0-(TEcoefficient 1)^2/(4*TEcurvature) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem TC_certificate (i : Fin 3) :
    transform .TC (numerator .TC i)=expansion 39 (transform .TC (numerator .TC i)) ∧
    TCreserve i<lowerOn .TC 39 (numerator .TC i) := by fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem REcurvature_certificate (i : Fin 3) :
    transform .RE (numerator .RE i).derivative.derivative=
      expansion 35 (transform .RE (numerator .RE i).derivative.derivative) ∧
    upperOn .RE 35 (numerator .RE i).derivative.derivative<REcurvatureReserve i := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem REboundary_certificate (i j : Fin 3) :
    WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 (RElength j) (REboundary i j)) ∧
    REreserve i j<WholeIntervalPolynomial.lowerOn 35 0 (RElength j) (REboundary i j) := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem RCquotient_certificate (i : Fin 3) :
    transform .RC (RCquotient i)=expansion 35 (transform .RC (RCquotient i)) ∧
    RCquotientReserve i<lowerOn .RC 35 (RCquotient i) := by fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem RCbase_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)=
      WholeIntervalPolynomial.expansion 35 (WholeIntervalPolynomial.centered 0 (1/6) (RCbase i)) ∧
    RCbaseReserve i<WholeIntervalPolynomial.lowerOn 35 0 (1/6) (RCbase i) := by
  fin_cases i <;> decide

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE.Certificate
