module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Weights
public import SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Exact endpoint polynomials for a negative DE3 and positive TD2

Uncompiled transcription of Sections 6--10 of the complete scalar
companion.  These are the eighteen displayed numerator formulas, with
the original A/T split and the original low/high interval retained.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
open Polynomial
open PositiveTD.Certificate (etaQ Rbar cbar sigmabar L h S5 S9 S11 C4 C10 C12
  num3 num4 ch Ch sh)

abbrev Rlo : ℚ := 1978787507/1000000000
abbrev abar : ℚ := 1414575672/1000000000
abbrev K : ℚ := 13/12
abbrev dbar : ℚ := cbar-1/2

def left : Family → ℚ | .low => 0 | .high => L
def right : Family → ℚ | .low => L | .high => h
def t : ℚ[X] := C (15/8)*(X-C L)
def k : Family → ℚ[X]
  | .low => C (6708/10000)+C (3/20)*(X-C L)+C 4*(X-C L)^2
  | .high => C (670158/1000000)+C (113718/1000000)*t+
      C (6506/1000000)*t^2+C (9026/1000000)*t^3+C (1/1000)*t^4
def l : Family → ℚ[X]
  | .low => C (10073/10000)-C (17/10)*(X-C L)+C (11/5)*(X-C L)^2
  | .high => C (1005069/1000000)-C (146411/1000000)*t-
      C (157739/1000000)*t^2+C (162815/1000000)*t^3
def c : Family → ℚ[X]
  | .low => C (10389/10000)-C (69/20)*(X-C L)+C 9*(X-C L)^2
  | .high => C (1021248/1000000)-C (168873/1000000)*t-
      C (165381/1000000)*t^2+C (175944/1000000)*t^3

def C2 : ℚ[X] := 1-C (1/2)*X^2
def S3 : ℚ[X] := X-C (1/6)*X^3
def J0 : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9
def J1 : ℚ[X] := J0-C (151/500)*(X-C L)^6
def mLo (f : Family) : Split → ℚ[X]
  | .atT => c f*(C10+C etaQ*S11) | .atA => c f
def mHi (f : Family) : Split → ℚ[X]
  | .atT => c f*(C12+C etaQ*S9) | .atA => c f
def mu (f : Family) : Split → ℚ[X]
  | .atT => c f*(if f=.low then C2+C etaQ*X else C4+C etaQ*S5)
  | .atA => c f

def lowE : Split → ℚ[X]
  | .atT => C 2*k .low+C 3*l .low+C (3/2)*mLo .low .atT+C (5/2)+
      C (1/2)*c .low*(1+C10+S11)-c .low*C sigmabar*S9
  | .atA => C 2*k .low+C 3*l .low+C (5/2)*c .low+C (5/2)+l .low*J0
def lowB (e : Split) : ℚ[X] := lowE e-C cbar*(1+c .low)
def highB : Split → ℚ[X]
  | .atT => C 2*k .high+C 3*l .high+C (3/2)*mLo .high .atT+
      C (1/2)*c .high+C 3+C (1/2)*c .high*(1+C10+S11)-
        c .high*C sigmabar*S9
  | .atA => C 2*k .high+C 3*l .high+C 3*c .high+C 3+l .high*J1

def PH (f : Family) : ℚ[X] := 1+(k f)^2
def PG (f : Family) : ℚ[X] := (k f)^2+(l f)^2
def PB (f : Family) (e : Split) : ℚ[X] := (mHi f e)^2+(l f)^2
def PD (f : Family) : ℚ[X] := 1+(c f)^2
def PHminus (f : Family) : ℚ[X] := PH f-C 2*k f*S11
def PGminus (f : Family) : ℚ[X] := PG f-C 2*k f*l f*S11
def PBminus (f : Family) (e : Split) : ℚ[X] := PB f e-C 2*l f*mLo f e*S11
def PHcap : ℚ[X] := PH .low-C (2*sh)*k .low
def PGcap : ℚ[X] := PG .low-C (2*sh)*k .low*l .low

def RH : Family → ℚ[X]
  | .low => C (41/50)+C (143/250)*k .low
  | .high => C (4/5)+C (3/5)*k .high
def RG : Family → ℚ[X]
  | .low => C (11/20)*k .low+C (167/200)*l .low
  | .high => C (31/50)*k .high+C (3923/5000)*l .high
def RB (f : Family) (e : Split) : ℚ[X] :=
  if f=.low then C (729/1000)*mu f e+C (1369/2000)*l f
  else C (7071/10000)*(l f+mu f e)
def RD : ℚ[X] := C (18/25)+C (347/500)*c .high
def RHminus : Family → ℚ[X]
  | .low => C (89/100)*C2+C (57/125)*(k .low-S3)
  | .high => C (93/100)*C4+C (919/2500)*(k .high-S5)
def RGminus : ℚ[X] := C (93/100)*l .high*C4+
  C (919/2500)*(k .high-l .high*S5)
def RBminus (e : Split) : ℚ[X] := C (83/100)*l .high*C4+
  C (14/25)*(mu .high e-l .high*S5)
def RHcap : ℚ[X] := C (77/100)
def RGcap : ℚ[X] := C (153/200)*l .low
def qStar : ℚ[X] := l .high+C (3/20)*(C h-X)

def NH (f : Family) (e : Split) : ℚ[X] :=
  if f=.low then num3 (lowB e+C10-1)
    (PHminus f) (PG f) (PB f e) (RHminus f) (RG f) (RB f e)
  else num4 (highB e+C10-1)
    (PG f) (PB f e) (PHminus f) (PD f) (RG f) (RB f e) (RHminus f) RD
def lowDen (e : Split) : ℚ[X] := C 2*RHminus .low*RG .low*RB .low e
def ZG : ℚ[X] := k .low*(C (ch+sh)*C10-C (Ch-sh)*S9-1)+
  l .low*(C ch-C12)
def NM (e : Split) : ℚ[X] := NH .low e+lowDen e*ZG
def NSH (e : Split) : ℚ[X] :=
  num3 (lowB e-C (109/200)*mHi .low e*(C h-X)+C (ch-1))
    PHcap (PG .low) (PB .low e) RHcap (RG .low) (RB .low e)
def NSG (e : Split) : ℚ[X] :=
  num3 (lowB e-C (109/200)*mHi .low e*(C h-X)+l .low*C (ch-1))
    (PH .low) PGcap (PB .low e) (RH .low) RGcap (RB .low e)
def NG (e : Split) : ℚ[X] :=
  num4 (highB e+l .high*(C10-1))
    (PH .high) (PB .high e) (PGminus .high) (PD .high)
    (RH .high) (RB .high e) RGminus RD
def NB (e : Split) : ℚ[X] :=
  num4 (highB e+qStar*(C10-1))
    (PH .high) (PG .high) (PBminus .high e) (PD .high)
    (RH .high) (RG .high) (RBminus e) RD
def secantR : ℚ[X] := C (379/500)+C (163/250)*c .high*C4
def NZ (f : Family) (e : Split) : ℚ[X] :=
  if f=.low then
    num3 (C10*(lowB e+C dbar)+C K*S11-C dbar)
      (C12^2*PH f) (C12^2*PG f) (C12^2*PB f e)
      (C4*RH f) (C4*RG f) (C4*RB f e)
  else
    num4 (C10*(highB e-1)+1+C K*S11)
      (C12^2*PH f) (C12^2*PG f) (C12^2*PB f e) (1+(c f)^2*C12^2)
      (C4*RH f) (C4*RG f) (C4*RB f e) secantR

def derivativeNumerator (atH : Bool) : ℚ[X] :=
  let P := if atH then PH .high else PG .high
  let r := if atH then RH .high else RG .high
  let f := if atH then k .high else k .high*l .high
  let A := P+r^2
  let D := 1+(c .high)^2*C12^2+secantR^2
  C (2*Rlo)*r*f*C10^2*D+C (2*Rlo)*secantR*S11*A-
    (C K+S9)*A*D

@[simp] theorem k_eval (f : Family) (θ : ℝ) : aeval θ (k f)=Explicit.k f θ := by
  cases f <;> simp [k,t,Explicit.k,Explicit.t,Explicit.L,L] <;> ring
@[simp] theorem l_eval (f : Family) (θ : ℝ) : aeval θ (l f)=Explicit.l f θ := by
  cases f <;> simp [l,t,Explicit.l,Explicit.t,Explicit.L,L] <;> ring
@[simp] theorem c_eval (f : Family) (θ : ℝ) : aeval θ (c f)=Explicit.c f θ := by
  cases f <;> simp [c,t,Explicit.c,Explicit.t,Explicit.L,L] <;> ring

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
