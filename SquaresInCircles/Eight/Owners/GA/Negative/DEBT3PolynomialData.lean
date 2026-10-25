module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3PolynomialData

/-!
# Eight squares: the literal negative-DE / positive-BT3 endpoint polynomials

The low native variable is
θ; the high native variable is x=θ-1/6. Cubic masses use the exact
rational square-root prescription already defined for the EH companion.
Only their separately stated positivity is needed in norm transfer.
The high tilt is total-dependent and is not the older constant TD tilt.
-/

@[expose] public section
noncomputable section
open Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Certificate
open PositiveTD.Certificate (S9 S11 C10 C12 num3 num4)

abbrev Rbar : ℚ := 1978787508/1000000000
abbrev Rlo : ℚ := 1978787/1000000
abbrev abar : ℚ := 1414575672/1000000000
abbrev cbar : ℚ := 449607033/500000000
abbrev sigmabar : ℚ := 1415477291/1000000000
abbrev eta0 : ℚ := 293/1000
abbrev K : ℚ := 13/12
abbrev L : ℚ := 1/6
abbrev h : ℚ := 7/10
abbrev span : ℚ := h-L
abbrev root12 := NegativeEHBT3.Certificate.root12
abbrev truncate3 := NegativeEHBT3.Certificate.truncate3

def mass (P : ℚ[X]) : ℚ[X] :=
  let w := C (1/P.eval 0)*(truncate3 P-C (P.eval 0))
  C (root12 (P.eval 0))*truncate3 (1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3)

def lowK : ℚ[X] := C (2933/5000)+C (1239/2500)*X
def lowM : ℚ[X] := C (5821/5000)-C (4437/5000)*X
def J : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9
def lowBase : Split→ℚ[X]
  | .atA => C 2*lowK+C (11/2-cbar)+C (5/2-cbar)*lowM+J
  | .atT => C 2*lowK+C (11/2-cbar)+lowM*
      (1+C (3/2-cbar)*C10+C (1/2+eta0*(1-cbar)-sigmabar)*S9)
def lowA (ep : Split) : ℚ[X] :=
  C10*lowBase ep+C K*S11+C (cbar-1/2)*(C10-1)
def lowP : Fin 3→ℚ[X] :=
  ![C12^2*(1+lowK^2),C12^2*(1+lowK^2),C12^2*(1+lowM^2)]
def lowMass (i : Fin 3) : ℚ[X] := mass (lowP i)
def lowNumerator (ep : Split) : ℚ[X] :=
  num3 (lowA ep) (lowP 0) (lowP 1) (lowP 2) (lowMass 0) (lowMass 1) (lowMass 2)

def theta : ℚ[X] := X+C L
def parameter : ℚ[X] := C (15/8)*X
def highK : ℚ[X] := C (670158/1000000)+C (113718/1000000)*parameter+
  C (6506/1000000)*parameter^2+C (9026/1000000)*parameter^3+C (1/1000)*parameter^4
def highL : ℚ[X] := C (1005069/1000000)-C (146411/1000000)*parameter-
  C (157739/1000000)*parameter^2+C (162815/1000000)*parameter^3
def highM : ℚ[X] := C (1021248/1000000)-C (168873/1000000)*parameter-
  C (165381/1000000)*parameter^2+C (175944/1000000)*parameter^3
def highEta : ℚ[X] := C eta0+C (1351/10000)*X
def etaIncrement : ℚ[X] := C (1/(1+eta0^2))*(highEta^2-C (eta0^2))
def sigmaUpper : ℚ[X] :=
  C (sigmabar+(1+eta0)/2)*
    (1+C (1/2)*etaIncrement-C (1/8)*etaIncrement^2+C (1/16)*etaIncrement^3)-
      C (1/2)*(1+highEta)
def highC : ℚ[X] := highM*(C12.comp theta+highEta*S9.comp theta)
def highSineCoefficient : ℚ[X] := C (1/2)+C (3/2)*highEta-sigmaUpper
def highBase : ℚ[X] := C 2*highK+C 3*highL+C 3+
  highM*(1+C 2*C10.comp theta+highSineCoefficient*S9.comp theta)
def highQStar : ℚ[X] := highL+C (3/20)*(C h-theta)
def highNormZero : Fin 4→ℚ[X] :=
  ![1+highK^2,highK^2+highL^2,highL^2+highM^2,1+highC^2]
def highProduct : Fin 3→ℚ[X] := ![highK,highK*highL,highL*highM]
def highCosineCoefficient : Fin 3→ℚ[X] := ![1,highL,highQStar]

inductive HighCase where | H | G | B | equal
  deriving DecidableEq

instance : Fintype HighCase where
  elems := {.H, .G, .B, .equal}
  complete x := by cases x <;> decide

def highIndex : HighCase→Fin 3 | .H=>0 | .G=>1 | .B=>2 | .equal=>0

def highA (r : HighCase) : ℚ[X] :=
  if r=.equal then C10.comp theta*(highBase-1)+1+C K*S11.comp theta
  else highBase+highCosineCoefficient (highIndex r)*(C10.comp theta-1)
def highP (r : HighCase) (i : Fin 4) : ℚ[X] :=
  if r=.equal then
    if i=3 then 1+highC^2*(C12.comp theta)^2
    else (C12.comp theta)^2*highNormZero i
  else highNormZero i-
    if i=(highIndex r).castSucc then C 2*highProduct (highIndex r)*S11.comp theta else 0
def highMass (r : HighCase) (i : Fin 4) : ℚ[X] := mass (highP r i)
def highNumerator (r : HighCase) : ℚ[X] :=
  num4 (highA r) (highP r 0) (highP r 1) (highP r 2) (highP r 3)
    (highMass r 0) (highMass r 1) (highMass r 2) (highMass r 3)
def highDegree : HighCase→ℕ | .equal=>63 | _=>39
def highReserve : HighCase→ℚ | .H=>79/100000 | .G=>7/5000 | .B=>69/1000 | .equal=>3/1250

def highHQuotient : ℚ[X] :=
  ∑i : Fin 39,C ((highNumerator .H).coeff (i.val+1))*X^i.val

def derivativeP (atH : Bool) : ℚ[X] := if atH then 1+highK^2 else highK^2+highL^2
def derivativeProduct (atH : Bool) : ℚ[X] := if atH then highK else highK*highL
def derivativeD : ℚ[X] := 1+highC^2*(C12.comp theta)^2
def derivativeMass (atH : Bool) : ℚ[X] := mass (derivativeP atH)
def derivativeDMass : ℚ[X] := mass derivativeD

def derivativeNumerator (atH : Bool) : ℚ[X] :=
  let AP := derivativeP atH+(derivativeMass atH)^2
  let AD := derivativeD+derivativeDMass^2
  C (2*Rlo)*derivativeProduct atH*(C10.comp theta)^2*AD*derivativeMass atH+
    C (2*Rlo)*S11.comp theta*AP*derivativeDMass-
      (C K+S9.comp theta)*AP*AD
def derivativeDegree : Bool→ℕ | true=>81 | false=>84
def derivativeReserve : Bool→ℚ | true=>259/500 | false=>1/25

def lateLine : ℚ[X] := C (2153/2000)-C (61/200)*theta
def lateDifference : ℚ[X] := lateLine-highC
abbrev lateLeft : ℚ := 11/20-L

@[simp] theorem lowK_eval (x : ℝ) : aeval x lowK=Explicit.k .low x := by
  simp [lowK,Explicit.k,PositiveBT3.lowK]
@[simp] theorem lowM_eval (x : ℝ) : aeval x lowM=Explicit.m .low x := by
  simp [lowM,Explicit.m,PositiveBT3.lowM,PositiveBT3.Cmax]
@[simp] theorem theta_eval (x : ℝ) : aeval x theta=x+(L:ℝ) := by simp [theta]
@[simp] theorem highK_eval (x : ℝ) : aeval x highK=Explicit.k .high (x+(L:ℝ)) := by
  simp [highK,parameter,Explicit.k,NegativeDEPositiveTD.Explicit.k,NegativeDEPositiveTD.Explicit.t,
    NegativeDEPositiveTD.Explicit.L,L]
@[simp] theorem highL_eval (x : ℝ) : aeval x highL=Explicit.l .high (x+(L:ℝ)) := by
  simp [highL,parameter,Explicit.l,NegativeDEPositiveTD.Explicit.l,NegativeDEPositiveTD.Explicit.t,
    NegativeDEPositiveTD.Explicit.L,L]
@[simp] theorem highM_eval (x : ℝ) : aeval x highM=Explicit.m .high (x+(L:ℝ)) := by
  simp [highM,parameter,Explicit.m,NegativeDEPositiveTD.Explicit.c,NegativeDEPositiveTD.Explicit.t,
    NegativeDEPositiveTD.Explicit.L,L]
@[simp] theorem highEta_eval (x : ℝ) : aeval x highEta=Explicit.eta .high (x+(L:ℝ)) := by
  simp [highEta,Explicit.eta,Explicit.L,L,eta0]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Certificate
