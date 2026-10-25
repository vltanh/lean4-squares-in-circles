module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDPolynomialData
public import SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds

/-!
# The fourteen negative-flat-A / positive-TD2 endpoint polynomials

Uncompiled transcription of Sections 2--9 of the complete scalar
companion. The two coefficient families and every radical tangent are
the displayed hand formulas. The last four endpoints retain the actual
GA and AB angle cuts; no extension of their analytic interval is made.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial
open PositiveTD.Certificate (etaQ Rbar cbar sigmabar h S5 S9 S11 C4 C10 C12
  num3 num4 mMinus mPlus ch Ch sh)

abbrev split : ℚ := 1/5

inductive Family where | low | high
  deriving DecidableEq

instance : Fintype Family where
  elems := {.low, .high}
  complete x := by cases x <;> decide

def left : Family→ℚ | .low => 0 | .high => split
def right : Family→ℚ | .low => split | .high => h
def t : Family→ℚ[X] | .low => C split-X | .high => X-C split

def k : Family→ℚ[X]
  | .low => C (169/250)-C (1/5)*t .low+C (19/5)*(t .low)^2-C 5*(t .low)^3
  | .high => C (169/250)+C (1/5)*t .high+C (9/10)*(t .high)^2-C (13/10)*(t .high)^3
def l : Family→ℚ[X]
  | .low => C (41/40)-C (1/4)*t .low+C (29/2)*(t .low)^2+
      C (55/4)*(t .low)^3-C 200*(t .low)^4
  | .high => C (41/40)+C (11/50)*t .high-C (3/10)*(t .high)^2
def c : Family→ℚ[X]
  | .low => 1+C (11/10)*t .low+C 17*(t .low)^2
  | .high => 1-C (7/10)*t .high+C (22/25)*(t .high)^2

def C2 : ℚ[X] := 1-C (1/2)*X^2
def S3 : ℚ[X] := X-C (1/6)*X^3
def mLo (f : Family) : ℚ[X] := mMinus (c f)
def mHi (f : Family) : ℚ[X] := mPlus (c f)
def mCoarse (f : Family) : ℚ[X] := c f*(C2+C etaQ*S3)
def mu (f : Family) : ℚ[X] := c f*(C4+C etaQ*S5)
def widthLo : ℚ[X] := C (1/2)*(1+C10+S11)

def elementary (f : Family) : ℚ[X] :=
  C 2*k f+C 3*l f+C (3/2)*mLo f+c f*widthLo+C (5/2)-c f*C sigmabar*S9+
    if f=.low then -(1+c f)*C cbar else C (1/2)*(1+c f)

def PH (f : Family) : ℚ[X] := 1+(k f)^2
def PG (f : Family) : ℚ[X] := (k f)^2+(l f)^2
def PB (f : Family) : ℚ[X] := (mHi f)^2+(l f)^2
def PD (f : Family) : ℚ[X] := 1+(c f)^2
def PHminus (f : Family) : ℚ[X] := PH f-C 2*k f*S11
def PGminus (f : Family) : ℚ[X] := PG f-C 2*k f*l f*S11
def PBminus (f : Family) : ℚ[X] := PB f-C 2*l f*mLo f*S11
def RH (f : Family) : ℚ[X] := C (83/100)+C (279/500)*k f
def RG (f : Family) : ℚ[X] := C (11/20)*k f+C (167/200)*l f
def RB (f : Family) : ℚ[X] := C (29/40)*mu f+C (689/1000)*l f
def RD (f : Family) : ℚ[X] := C (7071/10000)*(1+c f)
def RHminus (f : Family) : ℚ[X] := C (179/200)*C4+C (223/500)*(k f-S5)
def RGminus (f : Family) : ℚ[X] := C (9/10)*l f*C4+C (109/250)*(k f-l f*S5)
def RBminus (f : Family) : ℚ[X] := C (94/125)*l f*C4+C (33/50)*(mu f-l f*S5)
def qStar (f : Family) : ℚ[X] := l f+C (3/100)*(C h-X)

def NH (f : Family) : ℚ[X] :=
  if f=.low then num3 (elementary f+C10-1)
    (PG f) (PB f) (PHminus f) (RG f) (RB f) (RHminus f)
  else num4 (elementary f+C10-1)
    (PG f) (PB f) (PHminus f) (PD f) (RG f) (RB f) (RHminus f) (RD f)

def NG : ℚ[X] := num4 (elementary .high+l .high*(C10-1))
  (PH .high) (PB .high) (PGminus .high) (PD .high)
  (RH .high) (RB .high) (RGminus .high) (RD .high)
def NB : ℚ[X] := num4 (elementary .high+qStar .high*(C10-1))
  (PH .high) (PG .high) (PBminus .high) (PD .high)
  (RH .high) (RG .high) (RBminus .high) (RD .high)

def AZ (f : Family) : ℚ[X] := C10*(elementary f-l f)+l f+C (13/12)*l f*S11
def equalGAP (f : Family) : Fin 4→ℚ[X] :=
  ![C12^2*PH f,(l f)^2+(k f)^2*C12^2,C12^2*PB f,C12^2*PD f]
def equalGAR (f : Family) : Fin 4→ℚ[X] :=
  ![C4*RH f,C (21/25)*l f+C (543/1000)*k f*C4,C4*RB f,C4*RD f]
def NZ (f : Family) : ℚ[X] :=
  if f=.low then num3 (AZ f) (equalGAP f 0) (equalGAP f 1) (equalGAP f 2)
    (equalGAR f 0) (equalGAR f 1) (equalGAR f 2)
  else num4 (AZ f) (equalGAP f 0) (equalGAP f 1) (equalGAP f 2) (equalGAP f 3)
    (equalGAR f 0) (equalGAR f 1) (equalGAR f 2) (equalGAR f 3)

def equalABP : Fin 4→ℚ[X] :=
  ![C12^2*PH .high,C12^2*PG .high,(l .high)^2+(mHi .high)^2*C12^2,C12^2*PD .high]
def equalABR : Fin 4→ℚ[X] :=
  ![C4*RH .high,C4*RG .high,C (4/5)*l .high+C (3/5)*mu .high*C4,C4*RD .high]
def NZA : ℚ[X] := num4 (AZ .high)
  (equalABP 0) (equalABP 1) (equalABP 2) (equalABP 3)
  (equalABR 0) (equalABR 1) (equalABR 2) (equalABR 3)

def phiLo : ℚ[X] := C (ch+sh)*C10-C (Ch-sh)*S9
def NM : ℚ[X] := num3 (elementary .low+k .low*(phiLo-1)+l .low*C (ch-1))
  (PH .low) (PB .low) (PGminus .low) (RH .low) (RB .low) (RGminus .low)
def lowStar : ℚ[X] := elementary .low-C (109/200)*(mHi .low+C (2/5)*X)*(C h-X)
def PHcap : ℚ[X] := PH .low-C (2*sh)*k .low
def PGcap : ℚ[X] := PG .low-C (2*sh)*k .low*l .low
def NSH : ℚ[X] := num3 (lowStar+C (ch-1))
  (PG .low) (PB .low) PHcap (RG .low) (RB .low) (C (77/100))
def NSG : ℚ[X] := num3 (lowStar+l .low*C (ch-1))
  (PH .low) (PB .low) PGcap (RH .low) (RB .low) (C (77/100)*l .low)

inductive Cut where | gaH | gaB | abG | abH
  deriving DecidableEq

instance : Fintype Cut where
  elems := {.gaH, .gaB, .abG, .abH}
  complete x := by cases x <;> decide
def cutAtG : Cut→Bool | .gaH => true | .gaB => true | .abG => false | .abH => false
def cutAngle (e : Cut) : ℚ := if cutAtG e then 1/4 else 19/50
def cutRole : Cut→Fin 4 | .gaH => 0 | .gaB => 2 | .abG => 1 | .abH => 0
def gammaLo (e : Cut) : ℚ := C10.eval (cutAngle e)
def gammaHi (e : Cut) : ℚ := C12.eval (cutAngle e)
def tauLo (e : Cut) : ℚ := S11.eval (cutAngle e)
def tauHi (e : Cut) : ℚ := S9.eval (cutAngle e)
def gammaApprox (e : Cut) : ℚ := C4.eval (cutAngle e)
def tauApprox (e : Cut) : ℚ := S5.eval (cutAngle e)
def theta (e : Cut) : ℚ[X] := X-C (cutAngle e)
def thetaCosLo (e : Cut) : ℚ[X] := C (gammaLo e)*C10+C (tauLo e)*S11
def thetaSinLo (e : Cut) : ℚ[X] := C (gammaLo e)*S11-C (tauHi e)*C12
def thetaCosApprox (e : Cut) : ℚ[X] := C (gammaApprox e)*C4+C (tauApprox e)*S5
def thetaSinApprox (e : Cut) : ℚ[X] := C (gammaApprox e)*S5-C (tauApprox e)*C4

def cutA (e : Cut) : ℚ[X] :=
  C (gammaLo e)*(elementary .high-l .high)+l .high+C (13/12*tauLo e)*l .high+
    C (gammaHi e)*(if cutRole e=0 then 1 else l .high)*(thetaCosLo e-1)

def cutP0 (e : Cut) : Fin 4→ℚ[X] :=
  if cutAtG e then
    ![C (gammaHi e)^2*PH .high,(l .high)^2+C (gammaHi e)^2*(k .high)^2,
      C (gammaHi e)^2*PB .high,C (gammaHi e)^2*PD .high]
  else
    ![C (gammaHi e)^2*PH .high,C (gammaHi e)^2*PG .high,
      (l .high)^2+C (gammaHi e)^2*(mHi .high)^2,C (gammaHi e)^2*PD .high]
def cutR0 (e : Cut) : Fin 4→ℚ[X] :=
  if cutAtG e then
    ![C (gammaApprox e)*RH .high,C (21/25)*l .high+C (543/1000*gammaApprox e)*k .high,
      C (gammaApprox e)*RB .high,C (gammaApprox e)*RD .high]
  else
    ![C (gammaApprox e)*RH .high,C (gammaApprox e)*RG .high,
      C (4/5)*l .high+C (3/5*gammaApprox e)*mu .high,C (gammaApprox e)*RD .high]

def cutP (e : Cut) : Fin 4→ℚ[X] := Function.update (cutP0 e) (cutRole e)
  (if cutRole e=0 then C (gammaHi e)^2*PH .high-
      C (2*gammaLo e^2)*k .high*thetaSinLo e
   else if cutRole e=1 then C (gammaHi e)^2*PG .high-
      C (2*gammaLo e^2)*k .high*l .high*thetaSinLo e
   else C (gammaHi e)^2*PB .high-C (2*gammaLo e^2)*l .high*mLo .high*thetaSinLo e)
def cutR (e : Cut) : Fin 4→ℚ[X] := Function.update (cutR0 e) (cutRole e)
  (if cutRole e=0 then C (gammaApprox e)*
      (C (87/100)*thetaCosApprox e+C (493/1000)*(k .high-thetaSinApprox e))
   else if cutRole e=1 then C (gammaApprox e)*
      (C (9/10)*l .high*thetaCosApprox e+C (109/250)*(k .high-l .high*thetaSinApprox e))
   else C (gammaApprox e)*
      ((C (357/500)+C (11/20)*theta e)*l .high*thetaCosApprox e+
        (C (7/10)-C (41/50)*theta e)*(mu .high-l .high*thetaSinApprox e)))
def cutN (e : Cut) : ℚ[X] := num4 (cutA e)
  (cutP e 0) (cutP e 1) (cutP e 2) (cutP e 3)
  (cutR e 0) (cutR e 1) (cutR e 2) (cutR e 3)

def lowHFlip : ℚ[X] := (NH .low).comp (C split-X)
def lowZFlip : ℚ[X] := (NZ .low).comp (C split-X)
def lowHTail : ℚ[X] := lowHFlip.divX.divX.divX
def lowZTail : ℚ[X] := lowZFlip.divX.divX
def highHQuotient : ℚ[X] := (NH .high-C ((NH .high).eval split)).divByMonic (X-C split)
def highGQuotient : ℚ[X] := (NG-C (NG.eval split)).divByMonic (X-C split)
def cutHQuotient : ℚ[X] :=
  (cutN .gaH-C ((cutN .gaH).eval (1/4))).divByMonic (X-C (1/4))

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
