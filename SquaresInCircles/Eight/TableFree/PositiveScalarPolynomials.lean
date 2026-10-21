module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The seven explicit rational scalar polynomials

Uncompiled source draft of Sections 3--4 of
HAND_G5_POSITIVE_GA_CORE_E_SCALAR_CERTIFICATES.md. The polynomial builders
are the formulas in the note. The exact identities and rational reserves
below use kernel reduction (`decide`), never `native_decide`, external
arithmetic, or a sampled acceptance predicate. They have not been run.

These theorems establish polynomial positivity. Applying them to the
original trigonometric scalars additionally requires the Taylor and radical
transfer; polynomial positivity by itself is not that geometric exclusion.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.PositiveScalarPolynomials
open Polynomial WholeIntervalPolynomial

inductive ScalarCase where
  | PV | PL | PE | NV | NL | NE | NET
  deriving DecidableEq, Fintype

def k : ℚ := 863/1000
def h : ℚ := 7/10
def radiusUpper : ℚ := 494696877/250000000
def epsilon : ℚ := 1/1000000000000

def sine : ℚ[X] :=
  X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+
    C (1/362880)*X^9-C (1/39916800)*X^11+
    C (1/6227020800)*X^13-C (1/1307674368000)*X^15

def cosine : ℚ[X] :=
  1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+
    C (1/40320)*X^8-C (1/3628800)*X^10+
    C (1/479001600)*X^12-C (1/87178291200)*X^14+
    C (1/20922789888000)*X^16

def isP : ScalarCase → Bool
  | .PV | .PL | .PE => true
  | _ => false

def isV : ScalarCase → Bool
  | .PV | .NV => true
  | _ => false

def l (c : ScalarCase) : ℚ[X] :=
  if isP c then C (1263/2500)+C (49/100)*X-C (27/250)*X^2
  else C (2527/5000)+C (11/20)*X-C (1/5)*X^2

def cWeight (c : ScalarCase) : ℚ[X] :=
  if isP c then C k else C k+C (7/20)*X-C (3/20)*X^2

def eta (c : ScalarCase) : ℚ[X] :=
  if isP c then C (1/4)+C (329/2000)*X else C (19/50)

def lambda (c : ScalarCase) : ℚ[X] :=
  if isP c then C (103/100) else C (1111/1250)+C (1/5)*X

def n (c : ScalarCase) : ℚ[X] := C k*(cosine+eta c*sine)

structure RadicalRow where
  v : ℚ[X]
  a : ℚ[X]
  w : ℚ[X]
  deriving DecidableEq

def dummy : RadicalRow := ⟨0,1,0⟩

def constantRow : RadicalRow :=
  ⟨C (1+k^2),C ((21+20*k)/29),2⟩

def klRow (c : ScalarCase) : RadicalRow :=
  ⟨C (k^2)+(l c)^2,C (1/5)*(C (4*k)+3*l c),1⟩

def tiltedRow (c : ScalarCase) : RadicalRow :=
  ⟨(l c)^2+(n c)^2,C (1/5)*(3*l c+4*n c),1⟩

def primaryRow (c : ScalarCase) : RadicalRow :=
  ⟨1+(eta c)^2,C (1/25)*(24+7*eta c),C k*sine⟩

def HRow (c : ScalarCase) : RadicalRow :=
  ⟨1+(n c)^2,C (1/29)*(21+20*n c),1⟩

def BRow (c : ScalarCase) : RadicalRow :=
  ⟨(l c)^2+(cWeight c)^2,C (1/5)*(3*l c+4*cWeight c),1⟩

def DRow (c : ScalarCase) : RadicalRow :=
  ⟨1+(cWeight c)^2,C (1/29)*(21+20*cWeight c),1⟩

def VRow (c : ScalarCase) : RadicalRow :=
  ⟨C (k^2)+(l c)^2-C (2*k)*l c*sine,
    1-C (1/5)*X-C (33/100)*X^2,1⟩

/-- The fifth P row has zero weight and unit mass; it keeps the product
formula uniform without altering any scalar or degree. -/
def rows (c : ScalarCase) : Fin 5 → RadicalRow :=
  if isP c then
    if isV c then ![constantRow,tiltedRow c,primaryRow c,VRow c,dummy]
    else ![constantRow,klRow c,tiltedRow c,primaryRow c,dummy]
  else if isV c then ![HRow c,BRow c,DRow c,primaryRow c,VRow c]
    else ![HRow c,klRow c,BRow c,DRow c,primaryRow c]

def jCharge : ℚ[X] :=
  -C (1/12)*sine.comp (C h-X)-C (13/12)*(1-cosine.comp (C h-X))

def demand (c : ScalarCase) : ℚ[X] :=
  3+2*l c+3*cWeight c+C k*(1+2*cosine+(1+2*eta c)*sine)+
    match c with
    | .PV | .NV => C k*(cosine-1)
    | .PL | .NL => lambda c*X
    | .PE | .NE => jCharge+l c-C (87/1250)
    | .NET => jCharge+C h*lambda c

def mass (c : ScalarCase) : ℚ[X] := ∏ i : Fin 5,(rows c i).a

def massExcept (c : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏ j : Fin 5,if j=i then 1 else (rows c j).a

def certificate (c : ScalarCase) : ℚ[X] :=
  2*(demand c-C epsilon)*mass c-
    C radiusUpper*∑ i : Fin 5,(rows c i).w*((rows c i).v+(rows c i).a^2)*massExcept c i

def degree (c : ScalarCase) : ℕ := if isP c then 35 else 38

def reserve : ScalarCase → ℚ
  | .PV => 87/10000
  | .PL => 167/50000
  | .PE => 579/25000
  | .NV => 1173/100000
  | .NL => 469/50000
  | .NE => 1961/12500
  | .NET => 14079/100000

/- These finite reductions are deliberately not native evaluation. Their
resource requirements remain unmeasured because this draft is uncompiled. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_identity (c : ScalarCase) :
    centered 0 h (certificate c)=expansion (degree c) (centered 0 h (certificate c)) := by
  cases c <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_reserve (c : ScalarCase) :
    reserve c<lowerOn (degree c) 0 h (certificate c) := by
  cases c <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_identity (c : ScalarCase) (i : Fin 5) :
    centered 0 h (rows c i).a=expansion 16 (centered 0 h (rows c i).a) := by
  cases c <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_reserves (c : ScalarCase) (i : Fin 5) :
    69/100<lowerOn 16 0 h (rows c i).a ∧
      upperOn 16 0 h (rows c i).a<3/2 := by
  cases c <;> fin_cases i <;> decide

theorem reserve_pos (c : ScalarCase) : (0:ℚ)<reserve c := by cases c <;> norm_num [reserve]

theorem certificate_positive (c : ScalarCase) {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) : 0<aeval d (certificate c) := by
  have hd' : d∈Set.Icc ((0:ℚ):ℝ) (h:ℝ) := by simpa [h,frameCap] using hd
  have h := positive_on_interval (by norm_num [h]) (certificate_identity c)
    (certificate_reserve c) hd'
  have hr : (0:ℝ)<(reserve c:ℝ) := by exact_mod_cast reserve_pos c
  exact hr.trans h

theorem mass_positive (c : ScalarCase) (i : Fin 5) {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) :
    69/100<aeval d (rows c i).a ∧ aeval d (rows c i).a<3/2 := by
  have hd' : d∈Set.Icc ((0:ℚ):ℝ) (h:ℝ) := by simpa [h,frameCap] using hd
  have hb := interval_bounds (by norm_num [h]) (mass_identity c i) hd'
  have hlo : (69/100 : ℝ)<(lowerOn 16 0 h (rows c i).a:ℝ) := by
    exact_mod_cast (mass_reserves c i).1
  have hhi : (upperOn 16 0 h (rows c i).a:ℝ)<(3/2 : ℝ) := by
    exact_mod_cast (mass_reserves c i).2
  exact ⟨hlo.trans_le hb.1,hb.2.trans_lt hhi⟩

theorem radiusUpper_sq_gt : qCap<(radiusUpper:ℝ)^2 := by norm_num [qCap,radiusUpper]

theorem sine_eval (x : ℝ) : aeval x sine=HighOrderTaylor.S15 x := by
  simp [sine,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7]
  ring

theorem cosine_eval (x : ℝ) : aeval x cosine=HighOrderTaylor.C16 x := by
  simp [cosine,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.cos10,Arithmetic.cos8]
  ring

end SquaresInCircles.Eight.TableFree.PositiveScalarPolynomials
