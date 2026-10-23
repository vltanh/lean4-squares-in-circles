module

public import SquaresInCircles.Eight.TableFree.PositiveScalarPolynomials
public import Mathlib.Data.Nat.Sqrt

/-!
# Whole-strip radical polynomials for the sharp supporting chain

Uncompiled source of the construction in Section 7 of the critical-strip
hand proof. There are three intrinsic chains: the lower comparison,
the upper comparison, and the enclosure between them. A sextic root
polynomial is formed algebraically, then proved to enclose the square
root by its squared residual on the entire interval. The displayed
kernel arithmetic proofs have not been executed or replayed.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CriticalEPolynomials
open Polynomial WholeIntervalPolynomial

inductive Chain where
  | lower | upper | mixed
  deriving DecidableEq, Fintype

def length : ℚ := 3/50
def parameter : ℚ[X] := C (1/10)+X
def uMinus : ℚ[X] := C (499/500)-C (127/200)*parameter
def uPlus : ℚ[X] := C (501/500)-C (16/25)*parameter
def a : Chain → ℚ[X] | .lower | .mixed => uMinus | .upper => uPlus
def b : Chain → ℚ[X] | .upper | .mixed => uPlus | .lower => uMinus
def qLower : ℚ := 19577/5000
def qUpper : ℚ := 1957767069/500000000
def epsilon : ℚ := 1/10000000

def sextic (P : ℚ[X]) : ℚ[X] := ∑n : Fin 7,monomial n.val (P.coeff n.val)
def binomial : Fin 7 → ℚ := ![1,1/2,-1/8,1/16,-5/128,7/256,-21/1024]

/-- Nearest multiple of 10^-12, chosen by a rational square comparison.
Its role is only to construct the polynomial; the root bound below is
proved independently by the full squared residual. -/
def rootSeed (A : ℚ[X]) : ℚ :=
  let v : ℚ := A.coeff 0*(10:ℚ)^24
  let n : ℕ := Nat.sqrt (Int.toNat ⌊v⌋)
  (if v≤((n:ℚ)+1/2)^2 then (n:ℚ) else (n:ℚ)+1)/(10:ℚ)^12

def rootPolynomial (A : ℚ[X]) : ℚ[X] :=
  let d := C (1/A.coeff 0)*(sextic A-C (A.coeff 0))
  sextic (C (rootSeed A)*∑j : Fin 7,C (binomial j)*d^j.val)
def rootLower (A : ℚ[X]) : ℚ[X] := rootPolynomial A-C epsilon
def rootUpper (A : ℚ[X]) : ℚ[X] := rootPolynomial A+C epsilon

def rArgLo (s : Chain) : ℚ[X] := C qLower-(b s)^2
def rArgHi (s : Chain) : ℚ[X] := C qUpper-(a s)^2
def rLo (s : Chain) : ℚ[X] := rootLower (rArgLo s)
def rHi (s : Chain) : ℚ[X] := rootUpper (rArgHi s)
def UArgLo (s : Chain) : ℚ[X] := C qLower-(2-a s)^2
def UArgHi (s : Chain) : ℚ[X] := C qUpper-(2-b s)^2
def ULo (s : Chain) : ℚ[X] := rootLower (UArgLo s)
def UHi (s : Chain) : ℚ[X] := rootUpper (UArgHi s)
def VLo (s : Chain) : ℚ[X] := 3-UHi s
def VHi (s : Chain) : ℚ[X] := 3-ULo s
def YArgLo (s : Chain) : ℚ[X] := C qLower-(VHi s)^2
def YArgHi (s : Chain) : ℚ[X] := C qUpper-(VLo s)^2
def YLo (s : Chain) : ℚ[X] := rootLower (YArgLo s)
def YHi (s : Chain) : ℚ[X] := rootUpper (YArgHi s)
def vLo (s : Chain) : ℚ[X] := 2-YHi s
def vHi (s : Chain) : ℚ[X] := 2-YLo s
def wArgLo (s : Chain) : ℚ[X] := C qLower-(vHi s)^2
def wArgHi (s : Chain) : ℚ[X] := C qUpper-(vLo s)^2
def wLo (s : Chain) : ℚ[X] := rootLower (wArgLo s)
def wHi (s : Chain) : ℚ[X] := rootUpper (wArgHi s)

def rootArgument (s : Chain) : Fin 8 → ℚ[X] :=
  ![rArgLo s,rArgHi s,UArgLo s,UArgHi s,YArgLo s,YArgHi s,wArgLo s,wArgHi s]
def coordinateLower (s : Chain) : Fin 6 → ℚ[X] := ![rLo s,ULo s,VLo s,YLo s,vLo s,wLo s]
def coordinateUpper (s : Chain) : Fin 6 → ℚ[X] := ![rHi s,UHi s,VHi s,YHi s,vHi s,wHi s]

def sineLo : ℚ[X] := PositiveScalarPolynomials.sine.comp parameter
def sineHi : ℚ[X] :=
  (PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15).comp parameter
def cosineLo : ℚ[X] :=
  (PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16).comp parameter
def cosineHi : ℚ[X] := PositiveScalarPolynomials.cosine.comp parameter

def firstLo (s : Chain) : ℚ[X] := 2-cosineHi*(rHi s-1)+sineLo*a s
def firstHi (s : Chain) : ℚ[X] := 2-cosineLo*(rLo s-1)+sineHi*b s
def secondLo (s : Chain) : ℚ[X] := 1+cosineLo*vLo s-sineHi*(wHi s-1)
def secondHi (s : Chain) : ℚ[X] := 1+cosineHi*vHi s-sineLo*(wLo s-1)

def positionUpperAt (s : Chain) : ℚ[X] :=
  firstHi s*(cosineHi*b s+sineHi*rHi s)*UHi s*YHi s*wHi s-
    secondLo s*(2-b s)*VLo s*(cosineLo*wLo s+sineLo*vLo s)*rLo s

def positionLowerAt (s : Chain) : ℚ[X] :=
  firstLo s*(cosineLo*a s+sineLo*rLo s)*ULo s*YLo s*wLo s-
    secondHi s*(2-a s)*VHi s*(cosineHi*wHi s+sineHi*vHi s)*rHi s

def positionUpper : ℚ[X] := positionUpperAt .lower
def positionLower : ℚ[X] := positionLowerAt .upper

inductive Coefficient where
  | etaLower | etaUpper | kLower | kUpper | ellUpper | ellK
  | cLower | cUpper | ellCLower | ellCUpper | cK
  deriving DecidableEq, Fintype

def cleared : Coefficient → ℚ[X]
  | .etaLower => vLo .mixed-C (27/100)*wHi .mixed
  | .etaUpper => C (31/100)*wLo .mixed-vHi .mixed
  | .kLower => (cosineLo*wLo .mixed+sineLo*vLo .mixed)*VLo .mixed-
      C (37/40)*wHi .mixed*YHi .mixed
  | .kUpper => C (197/200)*wLo .mixed*YLo .mixed-
      (cosineHi*wHi .mixed+sineHi*vHi .mixed)*VHi .mixed
  | .ellUpper => C (67/100)*wLo .mixed*YLo .mixed*ULo .mixed-
      (cosineHi*wHi .mixed+sineHi*vHi .mixed)*VHi .mixed*(2-a .mixed)
  | .ellK => C (27/40)*ULo .mixed-(2-a .mixed)
  | .cLower => firstLo .mixed-C (37/40)*secondHi .mixed
  | .cUpper => secondLo .mixed-firstHi .mixed
  | .ellCLower => sineLo*rLo .mixed+cosineLo*a .mixed-C (63/100)*rHi .mixed
  | .ellCUpper => C (17/25)*rLo .mixed-sineHi*rHi .mixed-cosineHi*b .mixed
  | .cK => C (51/50)*ULo .lower*(sineLo*rLo .lower+cosineLo*a .lower)-
      (2-a .lower)*rHi .lower

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem root_identities (s : Chain) (i : Fin 8) :
    centered 0 length (rootLower (rootArgument s i))=
      expansion 6 (centered 0 length (rootLower (rootArgument s i))) ∧
    centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)=
      expansion 12 (centered 0 length (rootArgument s i-rootLower (rootArgument s i)^2)) ∧
    centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)=
      expansion 12 (centered 0 length (rootUpper (rootArgument s i)^2-rootArgument s i)) := by
  cases s <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem root_reserves (s : Chain) (i : Fin 8) :
    (2879/2000:ℚ)<lowerOn 6 0 length (rootLower (rootArgument s i)) ∧
    (23/80000000:ℚ)<lowerOn 12 0 length (rootArgument s i-rootLower (rootArgument s i)^2) ∧
    (9/31250000:ℚ)<lowerOn 12 0 length (rootUpper (rootArgument s i)^2-rootArgument s i) := by
  cases s <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coordinate_identities (s : Chain) (i : Fin 6) :
    centered 0 length (coordinateLower s i)=expansion 6 (centered 0 length (coordinateLower s i)) ∧
    centered 0 length (coordinateUpper s i)=expansion 6 (centered 0 length (coordinateUpper s i)) := by
  cases s <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coordinate_reserves (s : Chain) (i : Fin 6) :
    (1/2:ℚ)<lowerOn 6 0 length (coordinateLower s i) ∧
    upperOn 6 0 length (coordinateUpper s i)<2 := by
  cases s <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem auxiliary_reserves (s : Chain) :
    (1:ℚ)<lowerOn 6 0 length (rLo s) ∧
    (1:ℚ)<lowerOn 6 0 length (wLo s) ∧
    (1:ℚ)<lowerOn 22 0 length (firstLo s) ∧
    (1:ℚ)<lowerOn 22 0 length (secondLo s) := by
  cases s <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem auxiliary_identities (s : Chain) :
    centered 0 length (firstLo s)=expansion 22 (centered 0 length (firstLo s)) ∧
    centered 0 length (secondLo s)=expansion 22 (centered 0 length (secondLo s)) := by
  cases s <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem position_identities :
    centered 0 length positionUpper=expansion 64 (centered 0 length positionUpper) ∧
    centered 0 length positionLower=expansion 64 (centered 0 length positionLower) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem position_reserves :
    upperOn 64 0 length positionUpper<-(1/50:ℚ) ∧
    (1/25:ℚ)<lowerOn 64 0 length positionLower := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_identity (i : Coefficient) :
    centered 0 length (cleared i)=expansion 32 (centered 0 length (cleared i)) := by
  cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserve (i : Coefficient) : (0:ℚ)<lowerOn 32 0 length (cleared i) := by
  cases i <;> decide

theorem coefficient_positive (i : Coefficient) {z : ℝ} (hz : z∈Set.Icc 0 (length:ℝ)) :
    0<aeval z (cleared i) :=
  positive_on_interval (by norm_num [length]) (coefficient_identity i) (coefficient_reserve i) hz

end SquaresInCircles.Eight.TableFree.CriticalEPolynomials
