module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Data
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowPolynomial

/-!
# Eight squares: literal polynomials for the fourteen negative-A BT3 reference curves

Every high curve uses its stated native
variable z minus its left endpoint. Each auxiliary mass is the cubic
truncation prescribed by (33); its positivity is a separate certificate.
The cosine-scaled curves retain the lower cosine on positive terms
and the upper cosine on negative angular cost terms.
-/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.Certificate
open PositiveTD.Certificate (etaQ Rbar cbar sigmabar h S9 S11 C10 C12 num3 num4)

inductive Curve where
  | lowH | lowM | lowSH | lowSG | lowGA
  | highH | highG | highB | highGA | highAB
  | gaH | gaB | abG | abH
  deriving DecidableEq

instance : Fintype Curve where
  elems := {.lowH, .lowM, .lowSH, .lowSG, .lowGA, .highH, .highG, .highB, .highGA, .highAB, .gaH, .gaB, .abG, .abH}
  complete x := by cases x <;> decide

def family : Curve→Family
  | .lowH | .lowM | .lowSH | .lowSG | .lowGA => .low
  | _ => .high
def start : Curve→ℚ
  | .lowH | .lowM | .lowSH | .lowSG | .lowGA => 0
  | .abG | .abH => 19/50
  | _ => 1/4
def length (e : Curve) : ℚ := right (family e)-start e
def z (e : Curve) : ℚ[X] := X+C (start e)
def kAt (e : Curve) : ℚ[X] := (k (family e)).comp (z e)
def lAt (e : Curve) : ℚ[X] := (l (family e)).comp (z e)
def mAt (e : Curve) : ℚ[X] := (m (family e)).comp (z e)
def rotation (e : Curve) : ℚ[X] := mAt e*(C12.comp (z e)+C etaQ*S9.comp (z e))
def scaled : Curve→Bool
  | .lowGA | .highGA | .highAB | .gaH | .gaB | .abG | .abH => true
  | _ => false
def atG : Curve→Bool | .highAB | .abG | .abH => false | _ => true
def angle (e : Curve) : ℚ[X] :=
  match e with
  | .lowGA | .highGA | .highAB => z e
  | .gaH | .gaB => C (1/4)
  | .abG | .abH => C (19/50)
  | _ => 0
def selected : Curve→Option (Fin 4)
  | .lowH | .lowSH | .highH | .gaH | .abH => some 0
  | .lowM | .lowSG | .highG | .abG => some 1
  | .highB | .gaB => some 2
  | _ => none
def negativeAngle (e : Curve) : ℚ[X] :=
  match e with
  | .lowSH | .lowSG => C h
  | .gaH | .gaB | .abG | .abH => z e-angle e
  | _ => z e
def separated : Curve→Bool | .lowSH | .lowSG => true | _ => false
def cost (e : Curve) : ℚ[X] :=
  match selected e with
  | some j => if j=0 then 1 else lAt e
  | none => 0

def elementary (f : Family) : ℚ[X] :=
  if f=.low then C 2*k f+C 3*l f+C (5/2-cbar)+m f*
    (1+C (3/2-cbar)*C10+C (1/2+etaQ*(1-cbar)-sigmabar)*S9)
  else C 2*k f+C 3*l f+C 3+m f*
    (1+C 2*C10+C (1/2+3*etaQ/2-sigmabar)*S9)
def baseA (e : Curve) : ℚ[X] := (elementary (family e)).comp (z e)
def extraA (e : Curve) : ℚ[X] :=
  if e=.lowM then
    kAt e*((C10+S11).comp (C h-z e)-1)+lAt e*C (C10.eval h-1)
  else cost e*(C10.comp (negativeAngle e)-1)-
    if separated e then C (109/160)*(C h-z e) else 0
def A (e : Curve) : ℚ[X] :=
  if scaled e then C10.comp (angle e)*(baseA e-lAt e)+lAt e+
    C (13/12)*lAt e*S11.comp (angle e)+C12.comp (angle e)*extraA e
  else baseA e+extraA e
def baseP (e : Curve) : Fin 4→ℚ[X] :=
  ![1+(kAt e)^2,(kAt e)^2+(lAt e)^2,(lAt e)^2+(mAt e)^2,1+(rotation e)^2]
def pairProduct (e : Curve) : Fin 4→ℚ[X] := ![kAt e,kAt e*lAt e,lAt e*mAt e,rotation e]
def scaledP (e : Curve) (j : Fin 4) : ℚ[X] :=
  if atG e=true ∧ j=1 then (lAt e)^2+(kAt e)^2*(C12.comp (angle e))^2
  else if atG e=false ∧ j=2 then (lAt e)^2+(mAt e)^2*(C12.comp (angle e))^2
  else (C12.comp (angle e))^2*baseP e j
def P (e : Curve) (j : Fin 4) : ℚ[X] :=
  (if scaled e then scaledP e j else baseP e j)-
    if selected e=some j then
      C 2*(if scaled e then (C10.comp (angle e))^2 else 1)*pairProduct e j*
        S11.comp (negativeAngle e)
    else 0

def lowRho : Fin 4→ℚ :=
  ![1201850425155/1000000000000,1257298868386/1000000000000,
    1590206275928/1000000000000,1]
def highRho : Fin 4→ℚ :=
  ![1213863422159/1000000000000,1243063542284/1000000000000,
    1411857840755/1000000000000,1414033763977/1000000000000]
def gaRho : Fin 4→ℚ :=
  ![1176127347990/1000000000000,1231351623317/1000000000000,
    1367966599597/1000000000000,1370074878635/1000000000000]
def abRho : Fin 4→ℚ :=
  ![1176127347990/1000000000000,1204419707095/1000000000000,
    1391737262208/1000000000000,1370074878635/1000000000000]
def cutABRho : Fin 4→ℚ :=
  ![1151745317104/1000000000000,1193219895370/1000000000000,
    1339697088381/1000000000000,1263457367714/1000000000000]
def rho (e : Curve) (j : Fin 4) : ℚ :=
  match e with
  | .lowSH => if j=0 then 765171567774/1000000000000 else lowRho j
  | .lowSG => if j=1 then 815568741219/1000000000000 else lowRho j
  | .lowH | .lowM | .lowGA => lowRho j
  | .highH => if j=0 then 1064421563117/1000000000000 else highRho j
  | .highG => if j=1 then 1092123719510/1000000000000 else highRho j
  | .highB => if j=2 then 1225390819604/1000000000000 else highRho j
  | .highGA | .gaH | .gaB => gaRho j
  | .highAB => abRho j
  | .abG | .abH => cutABRho j
abbrev truncate3 := PositiveBT3.LowCertificate.truncate3
def mass (e : Curve) (j : Fin 4) : ℚ[X] :=
  if family e=.low ∧ j=3 then 1 else
  let p := P e j
  let w := C (1/p.eval 0)*(truncate3 p-C (p.eval 0))
  C (rho e j)*truncate3 (1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3)
def numerator (e : Curve) : ℚ[X] :=
  if family e=.low then num3 (A e) (P e 0) (P e 1) (P e 2) (mass e 0) (mass e 1) (mass e 2)
  else num4 (A e) (P e 0) (P e 1) (P e 2) (P e 3)
    (mass e 0) (mass e 1) (mass e 2) (mass e 3)
def degree : Curve→ℕ
  | .lowH | .lowM | .lowSH | .lowSG => 21
  | .lowGA => 34
  | .highGA | .highAB => 61
  | _ => 37

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.Certificate
