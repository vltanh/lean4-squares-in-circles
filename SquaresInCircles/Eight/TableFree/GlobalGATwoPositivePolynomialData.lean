module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDPolynomialData
public import SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds

/-!
# Exact polynomial numerators for the positive A/T split

These are the displayed rational formulas for the two intrinsic scalar
endpoints, with all rotation at A or all rotation at T.  The low T
endpoint uses the already established TD2 polynomials.  No endpoint is
asserted to be a geometrically feasible replacement cycle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

open Polynomial PositiveTD.Certificate

abbrev abar : ℚ := 1414575672/1000000000

def lowJ : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9
def lowA : ℚ[X] := C 2*lowK+C 3*lowL+C (5/2)*lowC+C (5/2)-
  (1+lowC)*C cbar+lowL*lowJ
def lowPH : ℚ[X] := 1+lowK^2-C 2*lowK*S11
def lowPG : ℚ[X] := lowK^2+lowL^2
def lowPB : ℚ[X] := lowC^2+lowL^2
def lowRH : ℚ[X] := C (89/100)*(1-C (1/2)*X^2)+
  C (57/125)*(lowK-X+C (1/6)*X^3)
def lowRG : ℚ[X] := C (11/20)*lowK+C (167/200)*lowL
def lowRB : ℚ[X] := C (729/1000)*lowC+C (1369/2000)*lowL
def lowDen : ℚ[X] := C 2*lowRH*lowRG*lowRB
def lowP : ℚ[X] := num3 (lowA+C10-1) lowPH lowPG lowPB lowRH lowRG lowRB
def lowMixedCharge : ℚ[X] :=
  lowK*(C (ch+sh)*C10-C (Ch-sh)*S9-1)+lowL*(C ch-C12)
def lowPM : ℚ[X] := lowP+lowDen*lowMixedCharge
def lowAstar : ℚ[X] := lowA-C (109/200)*lowC*(C h-X)
def lowPHh : ℚ[X] := 1+lowK^2-C (2*sh)*lowK
def lowPH0 : ℚ[X] := 1+lowK^2
def lowPGh : ℚ[X] := lowK^2+lowL^2-C (2*sh)*lowK*lowL
def lowPSH : ℚ[X] := num3 (lowAstar+C (ch-1)) lowPHh lowPG lowPB
  (C (77/100)) lowRG lowRB
def lowPSG : ℚ[X] := num3 (lowAstar+lowL*C (ch-1)) lowPH0 lowPGh lowPB
  (C (41/50)+C (143/250)*lowK) (C (153/200)*lowL) lowRB
def lowQuotient : ℚ[X] := -((lowP-C (lowP.eval L)).divByMonic (X-C L))

def t : ℚ[X] := X-C L
def highK : ℚ[X] := C (1673/2500)+C (2609/5000)*t-
  C (1489/2500)*t^2+C (527/1250)*t^3
def highL : ℚ[X] := 1+C (7/400)*t-C (2733/2500)*t^2+C (639/500)*t^3
def highC : ℚ[X] := C (10163/10000)-C (209/10000)*t-
  C (5743/5000)*t^2+C (14069/10000)*t^3
def highJ : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9-C (43/500)*t^4

inductive Endpoint where
  | atT
  | atA
  deriving DecidableEq, Fintype

def highMMinus : Endpoint→ℚ[X]
  | .atT => mMinus highC
  | .atA => highC
def highMPlus : Endpoint→ℚ[X]
  | .atT => mPlus highC
  | .atA => highC
def highMu : Endpoint→ℚ[X]
  | .atT => highC*(C4+C etaQ*S5)
  | .atA => highC
def highA : Endpoint→ℚ[X]
  | .atT => C 2*highK+C 3*highL+C (3/2)*highMMinus .atT+C (1/2)*highC+C 3+
      C (1/2)*highC*(1+C10+S11)-highC*C sigmabar*S9
  | .atA => C 2*highK+C 3*highL+C 3*highC+C 3+highL*highJ

def highPH : ℚ[X] := 1+highK^2
def highPG : ℚ[X] := highK^2+highL^2
def highPD : ℚ[X] := 1+highC^2
def highPB (e : Endpoint) : ℚ[X] := (highMPlus e)^2+highL^2
def highPHminus : ℚ[X] := highPH-C 2*highK*S11
def highPGminus : ℚ[X] := highPG-C 2*highK*highL*S11
def highPBminus (e : Endpoint) : ℚ[X] := highPB e-C 2*highL*highMMinus e*S11
def highRH : ℚ[X] := C (4/5)+C (3/5)*highK
def highRG : ℚ[X] := C (31/50)*highK+C (3923/5000)*highL
def highRD : ℚ[X] := C (18/25)+C (347/500)*highC
def highRB (e : Endpoint) : ℚ[X] := C (7071/10000)*(highL+highMu e)
def highRHminus : ℚ[X] := C (89/100)*C4+C (57/125)*(highK-S5)
def highRGminus : ℚ[X] := C (89/100)*highL*C4+C (57/125)*(highK-highL*S5)
def highRBminus (e : Endpoint) : ℚ[X] :=
  C (83/100)*highL*C4+C (14/25)*(highMu e-highL*S5)
def highQ : ℚ[X] := highL+C (3/20)*(C h-X)
def highQGap : ℚ[X] := highQ-highC*(C4+C etaQ*S5)

def highNH (e : Endpoint) : ℚ[X] := num4 (highA e+C10-1)
  highPG (highPB e) highPHminus highPD highRG (highRB e) highRHminus highRD
def highNG (e : Endpoint) : ℚ[X] := num4 (highA e+highL*(C10-1))
  highPH (highPB e) highPGminus highPD highRH (highRB e) highRGminus highRD
def highNB (e : Endpoint) : ℚ[X] := num4 (highA e+highQ*(C10-1))
  highPH highPG (highPBminus e) highPD highRH highRG (highRBminus e) highRD

def highQH (e : Endpoint) : ℚ[X] :=
  (highNH e-C ((highNH e).eval L)).divByMonic (X-C L)
def highQG (e : Endpoint) : ℚ[X] :=
  (highNG e-C ((highNG e).eval L)).divByMonic (X-C L)
def highChord (e : Endpoint) : ℚ[X] :=
  C (1/(h-L))*(C h-X)*C ((highNB e).eval L)+
    C (1/(h-L))*(X-C L)*C ((highNB e).eval h)
def highQB (e : Endpoint) : ℚ[X] :=
  -(((highNB e-highChord e).divByMonic (X-C L)).divByMonic (X-C h))

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
