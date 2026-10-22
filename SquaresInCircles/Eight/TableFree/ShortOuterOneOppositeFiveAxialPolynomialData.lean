module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveData

/-!
# The literal axial polynomials for opposite edge five

Uncompiled transcription of equations (32)--(40) of
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`.
The sparse degree-thirteen numerator, its squared polynomial, the two
displayed degree-eight lower polynomials, and their division by h-X
are retained exactly. All finite arithmetic here is kernel-decided
rational polynomial arithmetic, with no variable-domain oracle.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.AxialPolynomial
open Polynomial

def h : ℚ := 733/2500
def L (r : Bool) : ℚ :=
  157079632679489/100000000000000+50283/100000+pQ r*(1414575672/1000000000)+
    (PQ r+tQ r)/2-449/500
def denominator : ℚ[X] := 1+X^2
def eNumerator (r : Bool) : ℚ[X] := C (2*PQ r)*X+C (tQ r)*(1-X^2)
def radicalNumerator : ℚ[X] := C (9789/2500)*denominator^2-(C 3-X^2)^2*C (1/4)
def f (r : Bool) : ℚ[X] :=
  C (L r-3*PQ r/2)+C (-2+3*tQ r)*X+C (2*L r+2*PQ r)*X^2+
    C (-10/3-tQ r)*X^3+C (L r-PQ r/2)*X^4-C (16/15)*X^5+
      C (16/105)*X^7-C (16/315)*X^9-C (10/63)*X^11-C (2/9)*X^13
def polynomial (r : Bool) : ℚ[X] := (f r)^2-(eNumerator r)^2*radicalNumerator
def low : Bool→ℚ[X]
  | false => C (184988/100000000)-C (12669362/100000000)*X+C (275886083/100000000)*X^2-
      C (1129910079/100000000)*X^3+C (1664986399/100000000)*X^4-
        C (2393610952/100000000)*X^5+C (2262536812/100000000)*X^6-
          C (1473514417/100000000)*X^7+C (379/50)*X^8
  | true => C (139186/100000000)-C (10601133/100000000)*X+C (265965496/100000000)*X^2-
      C (1113153209/100000000)*X^3+C (1640798861/100000000)*X^4-
        C (2367380575/100000000)*X^5+C (2245323221/100000000)*X^6-
          C (1460933832/100000000)*X^7+C (189/25)*X^8
def remainder (r : Bool) : ℚ[X] := low r-C (1/10000)-C 3*X^8
def endpoint (r : Bool) : ℚ := (remainder r).eval h
def quotient (r : Bool) : ℚ[X] :=
  -∑j : Fin 8,C ((remainder r).coeff (j.val+1))*
    ∑k : Fin (j.val+1),C (h^(j.val-k.val))*X^k.val
def cubic0 : Bool→ℚ | false => 58479/10000000 | true => 43024/10000000
def cubic1 : Bool→ℚ | false => -4121613/10000000 | true => -3468926/10000000
def cubic2 : Bool→ℚ | false => 80037503/10000000 | true => 78880026/10000000
def cubic3 : Bool→ℚ | false => -128805661/10000000 | true => -12691901/1000000
def cubic (r : Bool) : ℚ[X] :=
  C (cubic0 r)+C (cubic1 r)*X+C (cubic2 r)*X^2+C (cubic3 r)*X^3
def reference : Bool→ℚ | false => 27/1000 | true => 23/1000
def valueLower : Bool→ℚ | false => 3007/10000000 | true => 3422/10000000
def slopeUpper : Bool→ℚ | false => 41/5000 | true => 21/5000
def curvature : Bool→ℚ | false => 353/100 | true => 179/50
def tailReserve (r : Bool) : ℚ :=
  ∑j : Fin 18,|(polynomial r).coeff (j.val+9)|*h^j.val
def lowDifference (r : Bool) : ℚ[X] :=
  (∑j : Fin 9,C ((polynomial r).coeff j.val)*X^j.val)-low r-C (2*h)*X^8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem tail_coefficients (r : Bool) :
    |(polynomial r).coeff 9|<3771/2000 ∧ |(polynomial r).coeff 10|<919/5000 ∧
    |(polynomial r).coeff 11|<2771/10000 ∧ |(polynomial r).coeff 12|<309/5000 ∧
    ∀j : Fin 14,|(polynomial r).coeff (j.val+13)|<3 := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem tail_reserve (r : Bool) :
    tailReserve r≤3771/2000+(919/5000)*h+(2771/10000)*h^2+(309/5000)*h^3+3*h^4/(1-h) ∧
    3771/2000+(919/5000)*h+(2771/10000)*h^2+(309/5000)*h^3+3*h^4/(1-h)≤2 := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_expansion (r : Bool) :
    polynomial r=low r+lowDifference r+C (2*h)*X^8+PowerTailBounds.tail (polynomial r) 9 18 := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem difference_expansion (r : Bool) :
    lowDifference r=C ((lowDifference r).coeff 0)+
      ∑j : Fin 8,C ((lowDifference r).coeff (j.val+1))*X^(j.val+1) := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem difference_coefficients (r : Bool) :
    0<(lowDifference r).coeff 0 ∧ ∀j : Fin 8,0≤(lowDifference r).coeff (j.val+1) := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_identity (r : Bool) :
    low r=C (1/10000)+C 3*X^8+C (endpoint r)+(C h-X)*quotient r := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem endpoint_reserve (r : Bool) :
    (if r then 303/10000000 else 352/10000000)<endpoint r := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_expansion (r : Bool) :
    quotient r=C ((quotient r).coeff 0)+C ((quotient r).coeff 1)*X+
      C ((quotient r).coeff 2)*X^2+C ((quotient r).coeff 3)*X^3+
        C ((quotient r).coeff 4)*X^4+C ((quotient r).coeff 5)*X^5+
          C ((quotient r).coeff 6)*X^6+C ((quotient r).coeff 7)*X^7 := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_coefficients (r : Bool) :
    cubic0 r<(quotient r).coeff 0 ∧ cubic1 r≤(quotient r).coeff 1 ∧
    cubic2 r≤(quotient r).coeff 2 ∧
    cubic3 r≤(quotient r).coeff 3+(quotient r).coeff 5*h^2+(quotient r).coeff 7*h^4 ∧
    0≤(quotient r).coeff 4 ∧ (quotient r).coeff 5≤0 ∧
    0≤(quotient r).coeff 6 ∧ (quotient r).coeff 7≤0 := by
  cases r <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cubic_reference (r : Bool) :
    valueLower r<(cubic r).eval (reference r) ∧
    |(cubic r).derivative.eval (reference r)|<slopeUpper r ∧
    curvature r<cubic2 r+cubic3 r*(h+2*reference r) ∧
    0<valueLower r-(slopeUpper r)^2/(4*curvature r) := by
  cases r <;> decide

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.AxialPolynomial
