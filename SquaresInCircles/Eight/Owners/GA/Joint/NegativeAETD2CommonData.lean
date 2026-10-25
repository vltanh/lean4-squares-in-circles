module

public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Radicals
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials

/-!
# Eight squares: the derivative and polynomial data of the common secant gain

Inverse half-powers are written as odd powers of the positive square root `D k x`. The two
coefficient certificates are the rational polynomials `P`, of degree 13, and `J`, of degree 150,
with their shifts `centeredP` and `centeredJ`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

abbrev K : ℝ := 13/12
def shapeA (k y : ℝ) : ℝ := 1+k^2-k^2*y^2
def shapeB (k y : ℝ) : ℝ := (1+k^2)*(1+y^2)-2*k^2*y^4
def shapeC (k y : ℝ) : ℝ :=
  (1+k^2)*(5+8*k^2)+(1+k^2)*(1-12*k^2)*y^2-2*k^2*y^4+4*k^4*y^6
def D (k x : ℝ) : ℝ := Real.sqrt (1+k^2*Real.cos x^2)
def F1 (k x : ℝ) : ℝ :=
  (K+Real.sin x-R*Real.sin x/D k x)/Real.cos x^2
def F2 (k x : ℝ) : ℝ :=
  (2*K*Real.sin x+1+Real.sin x^2-R*shapeB k (Real.sin x)/(D k x)^3)/Real.cos x^3
def F3 (k x : ℝ) : ℝ :=
  (2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3-
    R*Real.sin x*shapeC k (Real.sin x)/(D k x)^5)/Real.cos x^4
def F2k (k x : ℝ) : ℝ :=
  R*k*Real.cos x*(1+k^2*(1+2*Real.sin x^2))/(D k x)^5
def signPolynomial (p u : ℝ) : ℝ :=
  (1+p)*(8*p-1)-2*p*(5+2*p)*u-4*p^2*u^2
def F3k (k x : ℝ) : ℝ :=
  R*k*Real.sin x*signPolynomial (k^2) (Real.sin x^2)/(D k x)^7
def E2 (x : ℝ) : ℝ :=
  -1/250+(33/25)*(x-7/20)-(1/10)*(x-7/20)^2+(19/10)*(x-7/20)^3
def L (v : ℝ) : ℝ := 1+(5/2)*v+(35/8)*v^2+8*v^3
def L2 (v : ℝ) : ℝ := 1+(3/2)*v+(15/8)*v^2+(35/16)*v^3

namespace Certificate
open Polynomial
abbrev pLow : ℚ := 169/400
abbrev pHigh : ℚ := (751/1000)^2
def b (p : ℚ) : ℚ[X] := C (1+p)*(1+X^2)-C (2*p)*X^4
def c (p : ℚ) : ℚ[X] :=
  C ((1+p)*(5+8*p))+C ((1+p)*(1-12*p))*X^2-C (2*p)*X^4+C (4*p^2)*X^6
def l : ℚ[X] := 1+C (5/2)*X+C (35/8)*X^2+C 8*X^3
def l2 : ℚ[X] := 1+C (3/2)*X+C (15/8)*X^2+C (35/16)*X^3
def e2 : ℚ[X] := -C (1/250)+C (33/25)*(X-C (7/20))-
  C (1/10)*(X-C (7/20))^2+C (19/10)*(X-C (7/20))^3
def P : ℚ[X] :=
  C (13/6-11/10)+C 5*X+C (13/3+11/5)*X^2+X^3-C (11/10)*X^4-
    C (163983/200000)*X*c pLow*(l.comp (C (pLow/(1+pLow))*X^2))
def J : ℚ[X] :=
  e2*PositiveScalarPolynomials.cosine^3-C (13/6)*PositiveScalarPolynomials.sine-
    1-PositiveScalarPolynomials.sine^2+C (6323/6250)*
      ((b pHigh).comp PositiveScalarPolynomials.sine)*
      (l2.comp (C (pHigh/(1+pHigh))*PositiveScalarPolynomials.sine^2))
def centeredP : ℚ[X] := DirectedPowerBounds.shift (2/5) P
def centeredJ : ℚ[X] := DirectedPowerBounds.shift (7/20) J
def jTailNorm : ℚ :=
  ∑i:Fin 145,|centeredJ.coeff (i.val+6)| *(7/20)^(i.val+4)

end Certificate
end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
