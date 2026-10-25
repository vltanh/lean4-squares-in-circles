module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Data

/-!
# Eight squares: the thirty-two new negative-EH / positive-TD2 endpoint numerators

The ten small-E endpoints
reuse the exact negative-DE family and its three/four norm baselines.
The twenty-two far-E endpoints keep the prescribed fixed EH multiplier,
full D support, and the two linear coefficient families.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
open Polynomial
open PositiveTD.Certificate (etaQ Rbar sigmabar L h S5 S9 S11 C4 C10 C12 num3 num4)

abbrev v : ℚ := 1/10
abbrev u : ℚ := 1/4
abbrev beta : ℚ := 82/125
abbrev K : ℚ := 13/12
abbrev p : ℚ := 201/200
abbrev epsilon : ℚ := 1/200
abbrev C2 := NegativeDEPositiveTD.Certificate.C2
abbrev S3 := NegativeDEPositiveTD.Certificate.S3
abbrev J0 := NegativeDEPositiveTD.Certificate.J0
abbrev J1 := NegativeDEPositiveTD.Certificate.J1

def gStar (s : ℚ) : ℚ := K*S11.eval s+beta*(C10.eval s-1)
def GStar (s : ℚ) : ℚ := p*gStar s-11/50000
def gPoly : ℚ[X] := C K*S11+C beta*(C10-1)
def GPoly : ℚ[X] := C p*gPoly-C (11/50000)
def smallDelta : ℚ[X] := X-C v

inductive SmallCase where | lowZero | lowH | highH | highG | highB
  deriving DecidableEq

instance : Fintype SmallCase where
  elems := {.lowZero, .lowH, .highH, .highG, .highB}
  complete x := by cases x <;> decide
def smallFamily : SmallCase→Family | .lowZero=>.low | .lowH=>.low | _=>.high
def smallLeft : SmallCase→ℚ | .lowZero=>0 | .lowH=>v | _=>L
def smallRight : SmallCase→ℚ | .lowZero=>v | .lowH=>L | _=>h
def smallP (r : SmallCase) (e : Split) : Fin 4→ℚ[X] :=
  let f := smallFamily r
  let k := NegativeDEPositiveTD.Certificate.k f
  let l := NegativeDEPositiveTD.Certificate.l f
  ![NegativeDEPositiveTD.Certificate.PH f-
      (if r=.lowH ∨ r=.highH then C 2*k*S11.comp smallDelta else 0),
    NegativeDEPositiveTD.Certificate.PG f-
      (if r=.highG then C 2*k*l*S11.comp smallDelta else 0),
    NegativeDEPositiveTD.Certificate.PB f e-
      (if r=.highB then C 2*l*NegativeDEPositiveTD.Certificate.mLo f e*S11.comp smallDelta else 0),
    if f=.low then 0 else NegativeDEPositiveTD.Certificate.PD f]
def smallMass (r : SmallCase) (e : Split) : Fin 4→ℚ[X] :=
  let f := smallFamily r
  let k := NegativeDEPositiveTD.Certificate.k f
  let l := NegativeDEPositiveTD.Certificate.l f
  ![if r=.lowH then C (89/100)*C2.comp smallDelta+C (57/125)*(k-S3.comp smallDelta)
      else if r=.highH then C (93/100)*C4.comp smallDelta+C (919/2500)*(k-S5.comp smallDelta)
      else NegativeDEPositiveTD.Certificate.RH f,
    if r=.highG then C (93/100)*l*C4.comp smallDelta+C (919/2500)*(k-l*S5.comp smallDelta)
      else NegativeDEPositiveTD.Certificate.RG f,
    if r=.highB then C (83/100)*l*C4.comp smallDelta+
      C (14/25)*(NegativeDEPositiveTD.Certificate.mu f e-l*S5.comp smallDelta)
      else NegativeDEPositiveTD.Certificate.RB f e,
    if f=.low then 1 else NegativeDEPositiveTD.Certificate.RD]
def smallNonradical (r : SmallCase) (e : Split) : ℚ[X] :=
  let B := if smallFamily r=.low then NegativeDEPositiveTD.Certificate.lowB e
    else NegativeDEPositiveTD.Certificate.highB e
  match r with
  | .lowZero => B+gPoly
  | .lowH | .highH => B+C (gStar v)+C10.comp smallDelta-1
  | .highG => B+C (gStar v)+NegativeDEPositiveTD.Certificate.l .high*(C10.comp smallDelta-1)
  | .highB => B+C (gStar v)+NegativeDEPositiveTD.Certificate.qStar*(C10.comp smallDelta-1)
def smallNumerator (r : SmallCase) (e : Split) : ℚ[X] :=
  let P := smallP r e
  let a := smallMass r e
  if smallFamily r=.low then num3 (smallNonradical r e) (P 0) (P 1) (P 2) (a 0) (a 1) (a 2)
  else num4 (smallNonradical r e) (P 0) (P 1) (P 2) (P 3) (a 0) (a 1) (a 2) (a 3)
def smallDegree : SmallCase→Split→ℕ
  | .lowZero,.atA=>18 | .lowZero,.atT=>32
  | .lowH,.atA=>19 | .lowH,.atT=>33
  | .highH,.atA=>28 | .highH,.atT=>42
  | .highG,.atA=>31 | .highG,.atT=>45
  | .highB,.atA=>32 | .highB,.atT=>41
def smallReserve : SmallCase→Split→ℚ
  | .lowZero,.atA=>8991/100000 | .lowZero,.atT=>183947/10000000
  | .lowH,.atA=>94417/10000000 | .lowH,.atT=>27740/10000000
  | .highH,.atA=>7429/10000000 | .highH,.atT=>8161/10000000
  | .highG,.atA=>45860/10000000 | .highG,.atT=>49256/10000000
  | .highB,.atA=>923872/10000000 | .highB,.atT=>344132/10000000
def smallQuadratic (r : SmallCase) (e : Split) : Bool :=
  (r=.lowZero ∨ r=.lowH) ∧ e=.atT

def farK : Family→ℚ[X]
  | .low=>C (121/200) | .high=>C (101/200)+C (2/5)*X
def farL : Family→ℚ[X]
  | .low=>1-C (9/25)*X | .high=>C (381/400)-C (17/100)*X
def farC : Family→ℚ[X]
  | .low=>C (111/100)-C (77/100)*X | .high=>C (1929/2000)-C (47/250)*X
def farMLo (f : Family) : Split→ℚ[X]
  | .atT=>farC f*(C10+C etaQ*S11) | .atA=>farC f
def farMHi (f : Family) : Split→ℚ[X]
  | .atT=>farC f*(C12+C etaQ*S9) | .atA=>farC f
def farMu (f : Family) : Split→ℚ[X]
  | .atT=>farC f*(C4+C etaQ*S5) | .atA=>farC f
def farB (f : Family) : Split→ℚ[X]
  | .atT=>C 2*farK f+C 3*farL f+C (3/2)*farMLo f .atT+C (1/2)*farC f+C 3+
      C (1/2)*farC f*(1+C10+S11)-farC f*C sigmabar*S9
  | .atA=>C 2*farK f+C 3*farL f+C 3*farC f+C 3+farL f*(if f=.low then J0 else J1)
def farPH (f : Family) : ℚ[X] := 1+(farK f)^2
def farPG (f : Family) : ℚ[X] := (farK f)^2+(farL f)^2
def farPB (f : Family) (e : Split) : ℚ[X] := (farMHi f e)^2+(farL f)^2
def farPD (f : Family) : ℚ[X] := 1+(farC f)^2
def farRH (f : Family) : ℚ[X] := C (4/5)+C (3/5)*farK f
def farRG (f : Family) : ℚ[X] := C (31/50)*farK f+C (3923/5000)*farL f
def farRB (f : Family) (e : Split) : ℚ[X] := C (7071/10000)*(farL f+farMu f e)
def farRD (f : Family) : ℚ[X] := C (18/25)+C (347/500)*farC f
def farQStar : ℚ[X] := farL .high+C (3/20)*(C h-X)

inductive FarCase where
  | lowUH | lowUB | lowVH | lowVG | lowZero | highHv | highGv | highBv | highHu | highGu | highBu
  deriving DecidableEq

instance : Fintype FarCase where
  elems := {.lowUH, .lowUB, .lowVH, .lowVG, .lowZero, .highHv, .highGv, .highBv, .highHu, .highGu, .highBu}
  complete x := by cases x <;> decide
def farFamily : FarCase→Family
  | .lowUH | .lowUB | .lowVH | .lowVG | .lowZero=>.low | _=>.high
def farLeft : FarCase→ℚ | .lowUH | .lowUB=>0 | .lowVH | .lowVG | .lowZero=>v | _=>u
def farRight : FarCase→ℚ | .lowUH | .lowUB=>v | .lowVH | .lowVG | .lowZero=>u | _=>h
def farS : FarCase→ℚ | .highHu | .highGu | .highBu=>u | _=>v
def farDelta (r : FarCase) : ℚ[X] :=
  if r=.lowUH ∨ r=.lowUB then C v-X else X-C (farS r)
def farNegativeH (r : FarCase) : Bool := r=.lowVH ∨ r=.highHv ∨ r=.highHu
def farNegativeG (r : FarCase) : Bool := r=.lowVG ∨ r=.highGv ∨ r=.highGu
def farNegativeB (r : FarCase) : Bool := r=.highBv ∨ r=.highBu
def farP (r : FarCase) (e : Split) : Fin 4→ℚ[X] :=
  let f := farFamily r
  let d := farDelta r
  ![if r=.lowUH then farPH f+C 2*farK f*S9.comp d
      else farPH f-(if farNegativeH r then C 2*farK f*S11.comp d else 0),
    farPG f-(if farNegativeG r then C 2*farK f*farL f*S11.comp d else 0),
    if r=.lowUB then farPB f e+C 2*farL f*farMHi f e*S9.comp d
      else farPB f e-(if farNegativeB r then C 2*farL f*farMLo f e*S11.comp d else 0),
    farPD f]
def farMass (r : FarCase) (e : Split) : Fin 4→ℚ[X] :=
  let f := farFamily r
  let d := farDelta r
  ![if r=.lowUH then C (209/250)*C2.comp d+C (137/250)*(farK f+S3.comp d)
      else if r=.lowVH then C (89/100)*C2.comp d+C (57/125)*(farK f-S3.comp d)
      else if farNegativeH r then C (47/50)*C4.comp d+C (853/2500)*(farK f-S5.comp d)
      else farRH f,
    if r=.lowVG then C (89/100)*farL f*C2.comp d+C (57/125)*(farK f-farL f*S3.comp d)
      else if farNegativeG r then C (179/200)*farL f*C4.comp d+
        C (223/500)*(farK f-farL f*S5.comp d) else farRG f,
    if r=.lowUB then C (16/25)*farL f*C2.comp d+C (96/125)*(farMu f e+farL f*S3.comp d)
      else if farNegativeB r then C (41/50)*farL f*C4.comp d+
        C (143/250)*(farMu f e-farL f*S5.comp d) else farRB f e,
    farRD f]
def farNonradical (r : FarCase) (e : Split) : ℚ[X] :=
  let f := farFamily r
  let d := farDelta r
  let B := farB f e
  if r=.lowZero then B+GPoly
  else B+C (GStar (farS r))+
    (if r=.lowUH then farK f*(C10.comp d+S11.comp d-1)-C epsilon*d
     else if r=.lowUB then farL f*(C10.comp d+S11.comp d-1)-C epsilon*d
     else (if farNegativeG r then farL f else if farNegativeB r then farQStar else 1)*
       (C10.comp d-1))
def farNumerator (r : FarCase) (e : Split) : ℚ[X] :=
  let P := farP r e
  let a := farMass r e
  num4 (farNonradical r e) (P 0) (P 1) (P 2) (P 3) (a 0) (a 1) (a 2) (a 3)
def farDegree : FarCase→Split→ℕ
  | .lowUH,.atA=>17 | .lowUH,.atT=>31
  | .lowUB,.atA=>18 | .lowUB,.atT=>28
  | .lowVH,.atA=>17 | .lowVH,.atT=>31
  | .lowVG,.atA=>17 | .lowVG,.atT=>31
  | .lowZero,.atA=>14 | .lowZero,.atT=>28
  | .highHv,.atA | .highHu,.atA=>19
  | .highGv,.atA | .highGu,.atA | .highBv,.atA | .highBu,.atA=>20
  | .highHv,.atT | .highHu,.atT=>33
  | .highGv,.atT | .highGu,.atT=>34
  | .highBv,.atT | .highBu,.atT=>29
def farReserve : FarCase→Split→ℚ
  | .lowUH,.atA=>441112/10000000 | .lowUH,.atT=>98274/10000000
  | .lowUB,.atA=>508864/10000000 | .lowUB,.atT=>145059/10000000
  | .lowVH,.atA=>293761/10000000 | .lowVH,.atT=>246572/10000000
  | .lowVG,.atA=>165940/10000000 | .lowVG,.atT=>220630/10000000
  | .lowZero,.atA=>145527/10000000 | .lowZero,.atT=>201415/10000000
  | .highHv,.atA=>255999/10000000 | .highHv,.atT=>302465/10000000
  | .highGv,.atA=>155563/10000000 | .highGv,.atT=>223385/10000000
  | .highBv,.atA=>1028199/10000000 | .highBv,.atT=>474660/10000000
  | .highHu,.atA=>104322/10000000 | .highHu,.atT=>147124/10000000
  | .highGu,.atA=>132153/10000000 | .highGu,.atT=>198910/10000000
  | .highBu,.atA=>132561/10000000 | .highBu,.atT=>166633/10000000

@[simp] theorem farK_eval (f : Family) (θ : ℝ) : aeval θ (farK f)=Explicit.k .far f θ := by
  cases f <;> simp [farK,Explicit.k]
@[simp] theorem farL_eval (f : Family) (θ : ℝ) : aeval θ (farL f)=Explicit.l .far f θ := by
  cases f <;> simp [farL,Explicit.l]
@[simp] theorem farC_eval (f : Family) (θ : ℝ) : aeval θ (farC f)=Explicit.c .far f θ := by
  cases f <;> simp [farC,Explicit.c]

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
