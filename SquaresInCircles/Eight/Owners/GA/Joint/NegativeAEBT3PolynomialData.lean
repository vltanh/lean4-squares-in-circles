module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2PolynomialData

/-!
# Eight squares: the endpoint polynomials of the joint-negative positive-BT3 family

The variable tilt keeps its own radical. Multiplication by the positive tilt factor `f` clears
`m = c/f` before the positive masses majorize the radicals. The D transition is at `z = 1/4`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev F := JointNegativeAETD2.F
abbrev dNorm := JointNegativeAETD2.dNorm
def tilt (eta z : ℝ) : ℝ := Real.cos z+eta*Real.sin z
def sigma (eta : ℝ) : ℝ := fullSupport 1 eta
def baseline (k c eta z : ℝ) : ℝ :=
  2*k+6+(c/tilt eta z)*(1+2*Real.cos z+(1/2+(3/2)*eta-sigma eta)*Real.sin z)-
    R*(2*Real.sqrt (1+k^2)+Real.sqrt (1+(c/tilt eta z)^2)+dNorm c)

namespace Certificate
open Polynomial

inductive Row where | low | middle | high
  deriving DecidableEq

instance : Fintype Row where
  elems := {.low, .middle, .high}
  complete x := by cases x <;> decide
abbrev Endpoint := JointNegativeAETD2.Certificate.Endpoint
def left : Row→ℚ | .low=>0 | .middle=>3/20 | .high=>1/4
def right : Row→ℚ | .low=>3/20 | .middle=>1/4 | .high=>7/10
def diagonalD : Row→Bool | .low=>true | .middle=>true | .high=>false
def k : Row→ℚ[X]
  | .low=>JointNegativeAETD2.Certificate.k .low
  | _=>JointNegativeAETD2.Certificate.k .full
def eta : Row→ℚ[X]
  | .low=>C (6373/20000)
  | _=>C (4973/20000)+C (7/25)*X
def c : Row→ℚ[X]
  | .low=>C (69/50)-C (13/5)*X+C (14/5)*X^2
  | .middle=>1-C (61/50)*(X-C (1/4))+C (43/25)*(X-C (1/4))^2
  | .high=>1-C (67/100)*(X-C (1/4))+C (12/25)*(X-C (1/4))^2

abbrev Rplus : ℚ := 494696877/250000000
abbrev dPlus : ℚ := 707106781187/1000000000000
abbrev S : ℚ[X] := PositiveScalarPolynomials.sine
abbrev Cstar : ℚ[X] := PositiveScalarPolynomials.cosine
def f (r : Row) : ℚ[X] := Cstar+eta r*S
def Tstar (r : Row) : ℚ[X] := 1+C 2*Cstar+(1+C 2*eta r)*S
def v (r : Row) (e : Endpoint) : Fin 5→ℚ[X] :=
  ![1+(k r)^2,(f r)^2+(c r)^2,
    if e=.V then 1+(k r)^2-C 2*k r*S else 1+(k r)^2*Cstar^2,
    1+(eta r)^2,if diagonalD r then 0 else 1+(c r)^2]
def alpha (r : Row) (e : Endpoint) : Fin 5→ℚ[X] :=
  ![C (1/109)*(C 91+C 60*k r),C (1/29)*(C 20*f r+C 21*c r),
    if e=.V then C (1/85)*(C 36*(k r-S)+C 77*Cstar)
    else C (1/109)*(C 91+C 60*k r*Cstar),
    C (1/42)*(C 40+C 13*eta r),
    if diagonalD r then 1 else C (1/29)*(C 21+C 20*c r)]
def weight (r : Row) (e : Endpoint) : Fin 5→ℚ[X] :=
  ![if e=.V then f r else f r*Cstar,if e=.V then 1 else Cstar,f r,
    if e=.V then c r*S else c r*S*Cstar,
    if diagonalD r then 0 else if e=.V then f r else f r*Cstar]
def A (r : Row) (e : Endpoint) : ℚ[X] :=
  (if e=.V then f r*(C 2*k r+5+Cstar)+c r*Tstar r
   else (f r*(C 2*k r+5)+c r*Tstar r)*Cstar+f r*(1+C (13/12)*S))-
    if diagonalD r then C (Rplus*dPlus)*(1+c r)*f r*(if e=.V then 1 else Cstar) else 0
def numerator (r : Row) (e : Endpoint) : ℚ[X] :=
  C 2*A r e*(∏i,alpha r e i)-C Rplus*
    ∑i,weight r e i*(v r e i+(alpha r e i)^2)*∏j∈Finset.univ.erase i,alpha r e j
def degree : Row→Endpoint→ℕ
  | .low,.V=>64 | .low,.F=>66
  | .middle,.V=>71 | .middle,.F=>83
  | .high,.V=>73 | .high,.F=>85
def middleShift (e : Endpoint) : ℚ[X] := DirectedPowerBounds.shift (47/200) (numerator .middle e)
def highShift (e : Endpoint) : ℚ[X] := DirectedPowerBounds.shift (1/4) (numerator .high e)
def highQuotient (e : Endpoint) : ℚ[X] :=
  ∑i : Fin (degree .high e),C ((highShift e).coeff (i.val+1))*X^i.val

def lowValue : Endpoint→ℚ | .V=>37/12500 | .F=>241/50000
def lowSlope : Endpoint→ℚ | .V=>-67/200 | .F=>-317/1000
def middleValue : Endpoint→ℚ | .V=>1829/2500000 | .F=>1991/2500000
def middleLinear : Endpoint→ℚ | .V=>10111/1000000 | .F=>10731/1000000
def middleQuadratic : Endpoint→ℚ | .V=>798/625 | .F=>3561/2500
def middleReserve : Endpoint→ℚ | .V=>711/1000000 | .F=>97/125000
def highValue : Endpoint→ℚ | .V=>6209/5000000 | .F=>13591/10000000
def highSlope : Endpoint→ℚ | .V=>207/10000 | .F=>79/5000

end Certificate

namespace Explicit
open Polynomial
open Certificate (Row)
def k (r : Row) (z : ℝ) : ℝ := aeval z (Certificate.k r)
def c (r : Row) (z : ℝ) : ℝ := aeval z (Certificate.c r)
def eta (r : Row) (z : ℝ) : ℝ := aeval z (Certificate.eta r)
def f (r : Row) (z : ℝ) : ℝ := tilt (eta r z) z
def m (r : Row) (z : ℝ) : ℝ := c r z/f r z

theorem frame_domain (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) : z∈Icc 0 frameCap := by
  cases r <;> norm_num [Certificate.left,Certificate.right,frameCap] at hz ⊢ <;>
    constructor <;> linarith [hz.1,hz.2]

end Explicit
end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3
