module

public import SquaresInCircles.Eight.Owners.GA.Positive.TDWeights
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor

/-!
# Eight squares: exact scalar polynomials for the positive TD2 weight families

Every polynomial is defined by the analytic formula
in the scalar companion.  The auxiliary tangent masses are arbitrary
positive polynomials; no root-approximation assertion is an input.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
open Polynomial Explicit

abbrev etaQ : ℚ := 293/1000
abbrev Rbar : ℚ := 1978787508/1000000000
abbrev cbar : ℚ := 899214066/1000000000
abbrev sigmabar : ℚ := 1415477291/1000000000
abbrev L : ℚ := 1/6
abbrev h : ℚ := 7/10

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def S9 : ℚ[X] := S5-C (1/5040)*X^7+C (1/362880)*X^9
def S11 : ℚ[X] := S9-C (1/39916800)*X^11
def C4 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4
def C10 : ℚ[X] := C4-C (1/720)*X^6+C (1/40320)*X^8-C (1/3628800)*X^10
def C12 : ℚ[X] := C10+C (1/479001600)*X^12

def num3 (A P0 P1 P2 r0 r1 r2 : ℚ[X]) : ℚ[X] :=
  C 2*A*r0*r1*r2-C Rbar*
    ((P0+r0^2)*r1*r2+(P1+r1^2)*r0*r2+(P2+r2^2)*r0*r1)

def num4 (A P0 P1 P2 P3 r0 r1 r2 r3 : ℚ[X]) : ℚ[X] :=
  C 2*A*r0*r1*r2*r3-C Rbar*
    ((P0+r0^2)*r1*r2*r3+(P1+r1^2)*r0*r2*r3+
      (P2+r2^2)*r0*r1*r3+(P3+r3^2)*r0*r1*r2)

def lowK : ℚ[X] := C (84/125)-C (1/5)*(X-C (83/500))+C (5/2)*(X-C (83/500))^2
def lowL : ℚ[X] := C (101/100)-C (5/2)*(X-C (83/500))+
  C 6*(X-C (83/500))^2+C 48*(X-C (83/500))^3
def lowC : ℚ[X] := C (1043/1000)-C (21/5)*(X-C (83/500))+C 8*(X-C (83/500))^2

def mMinus (c : ℚ[X]) : ℚ[X] := c*(C10+C etaQ*S11)
def mPlus (c : ℚ[X]) : ℚ[X] := c*(C12+C etaQ*S9)

def lowA : ℚ[X] := C 2*lowK+C 3*lowL+C (3/2)*mMinus lowC+C (3/2)+C10+
  lowC*C (1/2)*(1+C10+S11)-(1+lowC)*C cbar-lowC*C sigmabar*S9
def lowPH : ℚ[X] := 1+lowK^2-C 2*lowK*S11
def lowPG : ℚ[X] := lowK^2+lowL^2
def lowPB : ℚ[X] := (mPlus lowC)^2+lowL^2
def lowRH : ℚ[X] := C (89/100)*(1-C (1/2)*X^2)+
  C (57/125)*(lowK-X+C (1/6)*X^3)
def lowRG : ℚ[X] := C (11/20)*lowK+C (167/200)*lowL
def lowRB : ℚ[X] := C (729/1000)*lowC*(1+C etaQ*X-C (1/2)*X^2)+C (1369/2000)*lowL
def lowDen : ℚ[X] := C 2*lowRH*lowRG*lowRB
def lowP : ℚ[X] := num3 lowA lowPH lowPG lowPB lowRH lowRG lowRB

def ch : ℚ := C10.eval h
def Ch : ℚ := C12.eval h
def sh : ℚ := S11.eval h
def lowJ : ℚ[X] :=
  lowK*(C (ch+sh)*C10-C (Ch-sh)*S9-1)+lowL*(C ch-C12)
def lowPM : ℚ[X] := lowP+lowDen*lowJ

def lowAstar : ℚ[X] := C 2*lowK+C 3*lowL+C (3/2)*mMinus lowC+C (5/2)+
  lowC*C (1/2)*(1+C10+S11)-(1+lowC)*C cbar-lowC*C sigmabar*S9-
    C (109/200)*mPlus lowC*(C h-X)
def lowPHh : ℚ[X] := 1+lowK^2-C (2*sh)*lowK
def lowPSH : ℚ[X] := num3 (lowAstar+C (ch-1)) lowPHh lowPG lowPB
  (C (77/100)) lowRG lowRB
def lowPH0 : ℚ[X] := 1+lowK^2
def lowPGh : ℚ[X] := lowK^2+lowL^2-C (2*sh)*lowK*lowL
def lowRHzero : ℚ[X] := C (41/50)+C (143/250)*lowK
def lowRGcap : ℚ[X] := C (153/200)*lowL
def lowPSG : ℚ[X] := num3 (lowAstar+lowL*C (ch-1)) lowPH0 lowPGh lowPB
  lowRHzero lowRGcap lowRB
def lowChord : ℚ[X] := (1-C (1/L)*X)*C (lowPSG.eval 0)+C (1/L)*X*C (lowPSG.eval L)
def lowChordQuotient : ℚ[X] := -(((lowPSG-lowChord).divX).divByMonic (X-C L))

def upperK : Upper→ℚ[X]
  | .varying => C (117/200)+C (1/2)*X
  | .clamped => C (653/800)
def upperC : Upper→ℚ[X]
  | .varying => C (57/50)-C (7/10)*X
  | .clamped => C (653/800)

@[simp] theorem S9_eval (z : ℝ) : aeval z S9=Arithmetic.sin9 z := by
  simp [S9,S5,Arithmetic.sin9,Arithmetic.sin7]
  ring
@[simp] theorem S11_eval (z : ℝ) : aeval z S11=HighOrderTaylor.S11 z := by
  simp [S11,HighOrderTaylor.S11]
  ring
@[simp] theorem C10_eval (z : ℝ) : aeval z C10=Arithmetic.cos10 z := by
  simp [C10,C4,Arithmetic.cos10,Arithmetic.cos8]
  ring
@[simp] theorem C12_eval (z : ℝ) : aeval z C12=HighOrderTaylor.C12 z := by
  simp [C12,HighOrderTaylor.C12]
  ring
@[simp] theorem lowK_eval (z : ℝ) : aeval z lowK=Explicit.lowK z := by
  simp [lowK,Explicit.lowK]
  ring
@[simp] theorem lowL_eval (z : ℝ) : aeval z lowL=Explicit.lowL z := by
  simp [lowL,Explicit.lowL]
@[simp] theorem lowC_eval (z : ℝ) : aeval z lowC=Explicit.lowC z := by
  simp [lowC,Explicit.lowC]
@[simp] theorem upperK_eval (a : Upper) (z : ℝ) :
    aeval z (upperK a)=Explicit.upperK a z := by
  cases a <;> simp [upperK,Explicit.upperK,Explicit.cap]
  ring
@[simp] theorem upperC_eval (a : Upper) (z : ℝ) :
    aeval z (upperC a)=Explicit.upperC a z := by
  cases a <;> simp [upperC,Explicit.upperC,Explicit.cap]

end SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
