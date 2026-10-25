module

public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials
public import SquaresInCircles.Eight.Owners.SecantNormCurvature

/-!
# Eight squares: exact scalar data for two negative flat-core primaries and TD2

The three rows are the two prescribed weight families split at the
intrinsic sorted-D transition. Every displayed decimal is rational.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def F (k x : ℝ) : ℝ := SecantNormCurvature.normalized R k x
abbrev eta : ℝ := 303/1000
def tilted (c z : ℝ) : ℝ := c*(Real.cos z+eta*Real.sin z)
def sigma : ℝ := fullSupport 1 eta
def dNorm (c : ℝ) : ℝ :=
  if 1≤c then (1+c)/Real.sqrt 2 else Real.sqrt (1+c^2)
def baseline (k c z : ℝ) : ℝ :=
  2*k+6+c*(1+2*Real.cos z+(1/2+(3/2)*eta-sigma)*Real.sin z)-
    R*(2*Real.sqrt (1+k^2)+Real.sqrt (1+(tilted c z)^2)+dNorm c)

namespace Certificate
open Polynomial

inductive Row where | low | transition | full
  deriving DecidableEq

instance : Fintype Row where
  elems := {.low, .transition, .full}
  complete x := by cases x <;> decide
inductive Endpoint where | V | F
  deriving DecidableEq

instance : Fintype Endpoint where
  elems := {.V, .F}
  complete x := by cases x <;> decide

def left : Row→ℚ | .low=>0 | .transition=>3/20 | .full=>19/100
def right : Row→ℚ | .low=>3/20 | .transition=>19/100 | .full=>7/10
def diagonalD : Row→Bool | .low=>true | .transition=>true | .full=>false
def k : Row→ℚ[X]
  | .low=>C (13/20)
  | _=> C (65433234/100000000)-C (6770392/100000000)*X+
    C (39062724/100000000)*X^2-C (29937498/100000000)*X^3+
    C (35999242/100000000)*X^4-C (29068717/100000000)*X^5+
    C (14649232/100000000)*X^6
def c : Row→ℚ[X]
  | .low=>C (69/50)-C (13/5)*X+C (14/5)*X^2
  | _=>C (230229/200000)-C (9/10)*X+C (11/20)*X^2

abbrev eta : ℚ := 303/1000
abbrev Rplus : ℚ := 494696877/250000000
abbrev sigmaPlus : ℚ := 1416128429/1000000000
abbrev dPlus : ℚ := 707106781187/1000000000000
abbrev S : ℚ[X] := PositiveScalarPolynomials.sine
abbrev Cstar : ℚ[X] := PositiveScalarPolynomials.cosine

def M (r : Row) : ℚ[X] := c r*(Cstar+C eta*S)
def J : ℚ[X] := 1+C 2*Cstar+C (1/2+(3/2)*eta-sigmaPlus)*S
def v (r : Row) (e : Endpoint) : Fin 4→ℚ[X] :=
  ![1+(k r)^2,1+(M r)^2,
    if e=.V then 1+(k r)^2-C 2*k r*S else 1+(k r)^2*Cstar^2,
    if diagonalD r then 0 else 1+(c r)^2]
def alpha (r : Row) (e : Endpoint) : Fin 4→ℚ[X] :=
  ![C (1/109)*(C 91+C 60*k r),C (1/29)*(C 20+C 21*M r),
    if e=.V then C (1/85)*(C 36*(k r-S)+C 77*Cstar)
    else C (1/109)*(C 91+C 60*k r*Cstar),
    if diagonalD r then 1 else C (1/29)*(C 21+C 20*c r)]
def weight (r : Row) (e : Endpoint) : Fin 4→ℚ[X] :=
  ![if e=.V then 1 else Cstar,if e=.V then 1 else Cstar,1,
    if diagonalD r then 0 else if e=.V then 1 else Cstar]
def H (r : Row) (e : Endpoint) : ℚ[X] :=
  (if e=.V then C 2*k r+5+Cstar+c r*J
   else (C 2*k r+5+c r*J)*Cstar+1+C (13/12)*S)-
    if diagonalD r then C (Rplus*dPlus)*(1+c r)*(if e=.V then 1 else Cstar) else 0
def numerator (r : Row) (e : Endpoint) : ℚ[X] :=
  C 2*H r e*(∏i,alpha r e i)-C Rplus*
    ∑i,weight r e i*(v r e i+(alpha r e i)^2)*∏j∈Finset.univ.erase i,alpha r e j

def degree : Row→Endpoint→ℕ
  | .low,.V=>52 | .low,.F=>68
  | .transition,.V=>58 | .transition,.F=>80
  | .full,.V=>60 | .full,.F=>82
def center : Row→ℚ | .low=>3/20 | .transition=>37/200 | .full=>19/100
def centered (r : Row) (e : Endpoint) : ℚ[X] :=
  DirectedPowerBounds.shift (center r) (numerator r e)

def lowConstant : Endpoint→ℚ | .V=>329/200000 | .F=>3289/1000000
def lowLinear : Endpoint→ℚ | .V=>-63/500 | .F=>-1/10
def lowQuadratic : Endpoint→ℚ | .V=>73/125 | .F=>617/500
def middleConstant : Endpoint→ℚ | .V=>4709/100000000 | .F=>1267/25000000
def middleLinear : Endpoint→ℚ | .V=>799/1000000 | .F=>421/500000
def middleQuadratic : Endpoint→ℚ | .V=>3001/5000 | .F=>13/20
def middleReserve : Endpoint→ℚ | .V=>117/2500000 | .F=>63/1250000

end Certificate

namespace Explicit
open Polynomial
open Certificate (Row)
def k (r : Row) (z : ℝ) : ℝ := aeval z (Certificate.k r)
def c (r : Row) (z : ℝ) : ℝ := aeval z (Certificate.c r)
def m (r : Row) (z : ℝ) : ℝ := tilted (c r z) z
def cap (r : Row) (z : ℝ) : ℝ := if r=.low then m r z else 539/500

theorem frame_domain (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) : z∈Icc 0 frameCap := by
  cases r <;> norm_num [Certificate.left,Certificate.right,frameCap] at hz ⊢ <;>
    constructor <;> linarith [hz.1,hz.2]

end Explicit
end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2
