module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Data

/-!
# The thirty-four intrinsic EH1/BT3 endpoint polynomials

Uncompiled Section 8. Every formula uses its native variable
x=theta-b on the full stated interval. Cubic masses use the exact
integer square-root prescription at precision 10^-12. Their only
subsequent analytic requirement is their independently proved positivity.
-/

@[expose] public section
noncomputable section
open Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Certificate
open PositiveTD.Certificate (S9 S11 C10 C12)

abbrev Rbar : ℚ := 1978787508/1000000000
abbrev abar : ℚ := 1414575672/1000000000
abbrev sigmabar : ℚ := 1415477291/1000000000
abbrev cbar : ℚ := 449607033/500000000
abbrev eta : ℚ := 293/1000
abbrev h : ℚ := 7/10

def theta (r : Row) : ℚ[X] := X+C (left r)
def kBase : Family→ℚ[X]
  | .smallLow => C (2933/5000)+C (1239/2500)*X
  | .smallHigh => C (1673/2500)+C (2609/5000)*(X-C (1/6))-
      C (1489/2500)*(X-C (1/6))^2+C (527/1250)*(X-C (1/6))^3
  | .farLow => C (121/200)
  | .farHigh => C (101/200)+C (2/5)*X
def lBase : Family→ℚ[X]
  | .smallLow => 1
  | .smallHigh => 1+C (7/400)*(X-C (1/6))-C (2733/2500)*(X-C (1/6))^2+
      C (639/500)*(X-C (1/6))^3
  | .farLow => 1-C (9/25)*X
  | .farHigh => C (381/400)-C (17/100)*X
def mBase : Family→ℚ[X]
  | .smallLow => C (5821/5000)-C (4437/5000)*X
  | .smallHigh => C (10163/10000)-C (209/10000)*(X-C (1/6))-
      C (5743/5000)*(X-C (1/6))^2+C (14069/10000)*(X-C (1/6))^3
  | .farLow => C (111/100)-C (77/100)*X
  | .farHigh => C (1929/2000)-C (47/250)*X
def k (r : Row) : ℚ[X] := (kBase (family r)).comp (theta r)
def l (r : Row) : ℚ[X] := (lBase (family r)).comp (theta r)
def m (r : Row) : ℚ[X] := (mBase (family r)).comp (theta r)
def s (r : Row) : ℚ[X] :=
  if equal r then theta r else match r with | .farHigh _ true=>C (1/4) | _=>C (1/10)
def d (r : Row) : ℚ[X] := if positive r then s r-theta r else theta r-s r
def J0 : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9
def JBase : Family→ℚ[X]
  | .smallHigh => J0-C (43/500)*(X-C (1/6))^4
  | .farHigh => J0-C (151/500)*(X-C (1/6))^6
  | _=>J0
def J (r : Row) : ℚ[X] := (JBase (family r)).comp (theta r)
def qStar (r : Row) : ℚ[X] := l r+C (3/20)*(C h-theta r)
def cUpper (r : Row) : Split→ℚ[X]
  | .atA => m r
  | .atT => m r*(C12.comp (theta r)+C eta*S9.comp (theta r))

def base (r : Row) (ep : Split) : ℚ[X] :=
  if family r=.smallLow then
    match ep with
    | .atA => C 2*k r+C 3*l r+C (5/2-cbar)+C (5/2-cbar)*m r+l r*J r
    | .atT => C 2*k r+C 3*l r+C (5/2-cbar)+m r*
        (1+C (3/2-cbar)*C10.comp (theta r)+
          C (1/2+eta*(1-cbar)-sigmabar)*S9.comp (theta r))
  else
    match ep with
    | .atA => C 2*k r+C 3*l r+C 3+C 3*m r+l r*J r
    | .atT => C 2*k r+C 3*l r+C 3+m r*
        (1+C 2*C10.comp (theta r)+C (1/2+(3/2)*eta-sigmabar)*S9.comp (theta r))

def g (r : Row) : ℚ[X] := C (13/12)*S11.comp (s r)+C (82/125)*(C10.comp (s r)-1)
def gainLower (r : Row) : ℚ[X] :=
  if far (family r) then C (201/200)*g r-C (11/50000) else g r
def smaller (r : Row) : Fin 4→ℚ[X] := ![k r,k r,l r,1]
def larger (r : Row) : Fin 4→ℚ[X] := ![1,l r,qStar r,1]
def positiveExtra (r : Row) : ℚ[X] :=
  smaller r (index r)*(C10.comp (d r)+S11.comp (d r)-1)-C (1/200)*d r
def negativeExtra (r : Row) : ℚ[X] := larger r (index r)*(C10.comp (d r)-1)
def A (r : Row) (ep : Split) : ℚ[X] :=
  base r ep+gainLower r+if equal r then 0 else if positive r then positiveExtra r else negativeExtra r

def normZero (r : Row) (ep : Split) : Fin 4→ℚ[X] :=
  ![1+(k r)^2,(k r)^2+(l r)^2,(l r)^2+(m r)^2,1+(cUpper r ep)^2]
def product (r : Row) (ep : Split) : Fin 4→ℚ[X] :=
  ![k r,k r*l r,l r*m r,cUpper r ep]
def P (r : Row) (ep : Split) (i : Fin 4) : ℚ[X] :=
  if active r i then normZero r ep i+
    if equal r∨i≠index r then 0
    else if positive r then C 2*product r ep i*S9.comp (d r)
    else -C 2*product r ep i*S11.comp (d r)
  else 0

def root12 (q : ℚ) : ℚ :=
  let n := Nat.sqrt ((q.num.natAbs*1000000000000000000000000)/q.den)
  let j := if q*1000000000000000000000000<((n:ℚ)+1/2)^2 then n else n+1
  (j:ℚ)/1000000000000
def truncate3 (p : ℚ[X]) : ℚ[X] := ∑i : Fin 4,C (p.coeff i.val)*X^i.val
def rho (r : Row) (ep : Split) (i : Fin 4) : ℚ := root12 ((P r ep i).eval 0)
def mass (r : Row) (ep : Split) (i : Fin 4) : ℚ[X] :=
  if active r i then
    let p := P r ep i
    let w := C (1/p.eval 0)*(truncate3 p-C (p.eval 0))
    C (rho r ep i)*truncate3 (1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3)
  else 1
def numerator (r : Row) (ep : Split) : ℚ[X] :=
  C 2*A r ep*(∏i,mass r ep i)-C Rbar*
    ∑i,if active r i then (P r ep i+(mass r ep i)^2)*∏j∈Finset.univ.erase i,mass r ep j else 0
def quotient (r : Row) (ep : Split) : ℚ[X] :=
  ∑i : Fin 39,C ((numerator r ep).coeff (i.val+1))*X^i.val
def affineCertificate : Row→Bool | .smallHigh i=>decide (i≠2) | _=>false
def massReserve (r : Row) : ℚ := match family r with
  | .smallLow=>23/20 | .smallHigh=>83/100 | .farLow=>101/100 | .farHigh=>3/4
def reserve (r : Row) : ℚ := match family r with
  | .smallLow=>49/10000 | .smallHigh=>27/500 | .farLow=>61/5000 | .farHigh=>29/2500

@[simp] theorem k_eval (r : Row) (x : ℝ) : aeval x (k r)=Explicit.k (family r) (x+(left r:ℝ)) := by
  cases r <;> simp [k,kBase,theta,Explicit.k,family,left,L]
@[simp] theorem l_eval (r : Row) (x : ℝ) : aeval x (l r)=Explicit.l (family r) (x+(left r:ℝ)) := by
  cases r <;> simp [l,lBase,theta,Explicit.l,family,left,L]
@[simp] theorem m_eval (r : Row) (x : ℝ) : aeval x (m r)=Explicit.m (family r) (x+(left r:ℝ)) := by
  cases r <;> simp [m,mBase,theta,Explicit.m,family,left,L]
@[simp] theorem s_eval (r : Row) (x : ℝ) :
    aeval x (s r)=gainArgument r (x+(left r:ℝ)) := by
  cases r with
  | farHigh i b => cases b <;> simp [s,gainArgument,equal,u,v]
  | _ => simp [s,gainArgument,equal,theta,v]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Certificate
