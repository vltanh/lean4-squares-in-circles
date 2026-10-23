module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Data

/-!
# The six positive-BT3 large-total endpoint polynomials

Uncompiled transcription of Section 7 of
`HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md`.
The native triangle and rectangle, the weights, and the E-charge
polynomial are the already established nonnegative-total families.
Here the rotating coefficient occurs at D; B retains the fixed m.
-/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals

abbrev theta := NonnegativeTotals.Certificate.theta
abbrev e := NonnegativeTotals.Certificate.e
abbrev delta := NonnegativeTotals.Certificate.delta
abbrev k := NonnegativeTotals.Certificate.k
abbrev l := NonnegativeTotals.Certificate.l
abbrev m := NonnegativeTotals.Certificate.c
abbrev jE := NonnegativeTotals.Certificate.jE
abbrev Rbar := NonnegativeTotals.Certificate.Rbar
abbrev transform := NonnegativeTotals.Certificate.transform
abbrev lowerOn := NonnegativeTotals.Certificate.lowerOn
abbrev upperOn := NonnegativeTotals.Certificate.upperOn
abbrev d : ℚ := 8/15

/-- The positive rotating coefficient is bounded above by this polynomial. -/
def rotation (r : Region) : Bivar :=
  m r*(lift (theta r) PositiveTD.Certificate.C12+
    scalar (293/1000)*lift (theta r) PositiveTD.Certificate.S9)

def qB : Region → Bivar
  | .triangle => NonnegativeTotals.Certificate.qStar .triangle
  | .rectangle => m .rectangle

def A (r : Region) (i : Fin 3) : Bivar :=
  NonnegativeTotals.Certificate.ABase r .atT+
    (![1,l r,qB r] i)*(lift (delta r) PositiveTD.Certificate.C10-1)

def baseNorm (r : Region) : Fin 4 → Bivar :=
  ![1+(k r)^2,(k r)^2+(l r)^2,(l r)^2+(m r)^2,1+(rotation r)^2]

def P (r : Region) (i : Fin 3) (j : Fin 4) : Bivar :=
  baseNorm r j-
    if j.val=i.val then scalar 2*(![k r,k r*l r,l r*m r,0] j)*
      lift (delta r) PositiveTD.Certificate.S11 else 0

def rho (i : Fin 3) (j : Fin 4) : ℚ :=
  if j.val=i.val then if j=2 then 81386069/62500000 else 27678887/25000000
  else if j=2 then 142578599/100000000
  else if j=3 then 1451171531/1000000000
  else 150407189/125000000

/-- The opposite cubic corrections in the triangle G certificate are
part of the literal hand certificate. Positivity is proved separately. -/
def mass (r : Region) (i : Fin 3) (j : Fin 4) : Bivar :=
  cubicMass (rho i j) (P r i j)+
    if r=.triangle ∧ i=1 then
      if j=1 then -scalar (1/4)*X^3
      else if j=3 then scalar (1/4)*X^3 else 0
    else 0

def numerator (r : Region) (i : Fin 3) : Bivar :=
  let w := mass r i
  scalar 2*A r i*w 0*w 1*w 2*w 3-scalar Rbar*
    ((P r i 0+(w 0)^2)*w 1*w 2*w 3+
      (P r i 1+(w 1)^2)*w 0*w 2*w 3+
      (P r i 2+(w 2)^2)*w 0*w 1*w 3+
      (P r i 3+(w 3)^2)*w 0*w 1*w 2)

def degree : Region → ℕ | .triangle => 39 | .rectangle => 35

def triangleQuotient (i : Fin 3) : Bivar := divY (numerator .triangle i)
def triangleBase (i : Fin 3) : ℚ[X] := baseY (numerator .triangle i)
def triangleFar (i : Fin 3) : ℚ[X] := restrict (triangleQuotient i) X (C d-X)
def rectangleQuotient (i : Fin 3) : Bivar := (numerator .rectangle i).divX
def rectangleBase (i : Fin 3) : ℚ[X] := baseX (numerator .rectangle i)

abbrev chordQuotient := NonnegativeTotals.Certificate.chordQuotient
abbrev chordPolynomial := NonnegativeTotals.Certificate.chordPolynomial

def triangleDerivativeReserve : Fin 3 → ℚ := ![-231/1000,-21/50,-119/500]
def triangleFarReserve : Fin 2 → ℚ := ![41/1000,29/250]
def rectangleQuotientReserve : Fin 3 → ℚ := ![23/500,17/125,411/1000]
def rectangleInitialReserve : Fin 2 → ℚ := ![893/500000,149/500]
def rectangleSlopeReserve : Fin 2 → ℚ := ![7/100,199/100]
def massReserve : Region → ℚ | .triangle => 7/10 | .rectangle => 77/100

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LargeCertificate
