module

public import SquaresInCircles.Eight.TableFree.SoleECoefficients
public import SquaresInCircles.Eight.TableFree.PositiveScalarPolynomials
public import SquaresInCircles.Eight.TableFree.WholeIntervalBernstein

/-!
# Explicit whole-interval polynomials for the sole-E endpoints

Uncompiled source. These are the eighteen sole-EH scalars and the six
additional sole-DE scalars in the two hand proofs. The masses are built
by three rational Newton steps at the left endpoint, followed by cubic
truncation. Every identity and reserve is a kernel arithmetic proof
which has not been run. No numerical samples or external replay occur.

The polynomial bounds are kept separate from their trigonometric and
radical transfer. Their presence alone is not a geometric exclusion.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleScalarPolynomials
open Polynomial WholeIntervalPolynomial SoleECoefficients

inductive ScalarCase where
  | lowE | lowG
  | middleE (i : Fin 4) | middleG (i : Fin 4)
  | highE (i : Fin 4) | highG (i : Fin 4)
  | lowDE | middleDE (i : Fin 4) | highDEH
  deriving DecidableEq, Fintype

def band : ScalarCase → Band
  | .lowE | .lowG | .lowDE => .low
  | .middleE _ | .middleG _ | .middleDE _ => .middle
  | _ => .high

def origin : Band → ℚ
  | .low => 0 | .middle => 1/5 | .high => 7/20

def length : Band → ℚ
  | .low => 1/5 | .middle => 3/20 | .high => 7/20

def negativeIndex : ScalarCase → Fin 4
  | .lowE | .lowG | .lowDE => 2
  | .middleE i | .middleG i | .highE i | .highG i | .middleDE i => i
  | .highDEH => 0

def atG : ScalarCase → Bool
  | .lowG | .middleG _ | .highG _ | .highDEH => true
  | _ => false

def isDE : ScalarCase → Bool
  | .lowDE | .middleDE _ => true
  | _ => false

def radiusUpper : ℚ := 989385433/500000000
def axisUpper : ℚ := 1414558471/1000000000
def margin : ℚ := 1/100000000

def parameter (b : Band) : ℚ[X] := C (origin b)+X
def sine (b : Band) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter b)
def cosine (b : Band) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter b)
def halfSine (b : Band) : ℚ[X] :=
  PositiveScalarPolynomials.sine.comp (C (1/2)*parameter b)

def k : Band → ℚ[X]
  | .low => C (17253/20000)+C (11/20)*X+C (3/10)*X^2
  | .middle => C (983/1000)+C (1/10)*X-C (3/10)*X^2
  | .high => C (1017/1000)-C (1/50)*parameter .high

def c : Band → ℚ[X]
  | .low => k .low+C (3/10)*X
  | .middle => C (209/200)+C (13/20)*X-C (3/2)*X^2
  | .high => C (113/100)

def ell : Band → ℚ[X]
  | .low => C (50521/100000)+C (823/1000)*X+C (7/10)*X^2
  | .middle => C (349/500)+C (9/10)*X-X^2
  | .high => C (7/10)+C (9/25)*parameter .high

def g : Band → ℚ[X]
  | .low => C (8/25)
  | .middle => C (31/100)
  | .high => C (27/100)+C (2/25)*parameter .high

def eta : Band → ℚ[X]
  | .low => C (131/500)+C (267/1000)*X+C (1/10)*X^2
  | .middle => C (319/1000)+C (1/5)*X
  | .high => C (7/20)

def n (b : Band) : ℚ[X] := k b*(cosine b+g b*sine b)
def p (b : Band) : ℚ[X] := if b=.high then 1 else cosine b+eta b*sine b
def r (b : Band) : ℚ[X] := cosine b+C (7/10)*sine b

def first (s : ScalarCase) : Fin 4 → ℚ[X] :=
  let b := band s
  if atG s then ![1,k b,ell b,1]
  else if isDE s then ![r b,k b,ell b,1]
  else ![1,k b,ell b,p b]

def second (s : ScalarCase) : Fin 4 → ℚ[X] :=
  let b := band s
  ![if atG s then n b else k b,ell b,c b,c b]

def nu (s : ScalarCase) : ℚ[X] :=
  let b := band s
  if s=.highDEH then C (53/50)
  else ![if atG s then n b else if isDE s then r b else k b,ell b,c b,c b]
    (negativeIndex s)

def outside (s : ScalarCase) : ℚ[X] :=
  let b := band s
  (if atG s then
      3+2*ell b+3*c b+k b*(1+2*cosine b+(1+2*g b)*sine b)
    else if isDE s then
      3*k b+2*ell b+3*c b+1+C (1/2)*cosine b+
        C (1/2-axisUpper)*sine b+C (3/2)*r b
    else if b=.high then
      3+sine b-C (2*radiusUpper)*halfSine b+3*k b+2*ell b+3*c b
    else
      3*k b+2*ell b+3*c b+1+2*cosine b+(1+2*eta b)*sine b)+
    nu s*(cosine b-1)

def squaredNorm (s : ScalarCase) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if i=negativeIndex s then 2*first s i*second s i*sine (band s) else 0)

def rowSquare (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩
  else if atG s then 1+(g (band s))^2
  else if isDE s=true ∨ band s=.high then 1 else 1+(eta (band s))^2

def rowWeight (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if i.val<4 then 1 else if atG s then k (band s)*sine (band s)
  else if isDE s=true ∨ band s=.high then 0 else sine (band s)

def truncateThree (v : ℚ[X]) : ℚ[X] :=
  C (v.coeff 0)+C (v.coeff 1)*X+C (v.coeff 2)*X^2+C (v.coeff 3)*X^3

def newton (v : ℚ) : ℕ → ℚ
  | 0 => 1
  | j+1 => (newton v j+v/newton v j)/2

def newtonMass (v : ℚ[X]) : ℚ[X] :=
  let v0 := v.coeff 0
  let w := C (1/v0)*(truncateThree v-C v0)
  truncateThree (C (newton v0 3)*(1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3))

def massAt (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if i.val=4 ∧ (isDE s=true ∨ band s=.high) ∧ atG s=false then 1
  else newtonMass (rowSquare s i)

def mass (s : ScalarCase) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏j : Fin 5,if j=i then 1 else massAt s j

def certificate (s : ScalarCase) : ℚ[X] :=
  2*(outside s-C margin)*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i

def degree : ScalarCase → ℕ
  | .lowDE => 41
  | _ => 46

theorem length_pos (b : Band) : 0<length b := by cases b <;> norm_num [length]

theorem local_parameter {b : Band} {t : ℝ} (ht : t∈domain b) :
    t-(origin b:ℝ)∈Set.Icc 0 (length b:ℝ) := by
  cases b <;> norm_num [domain,origin,length,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

/- These exact reductions are deliberately unrun. Their inputs are the
displayed rational formulas, not a stored angle or state enumeration. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_identity (s : ScalarCase) :
    centered 0 (length (band s)) (certificate s)=
      expansion (degree s) (centered 0 (length (band s)) (certificate s)) := by
  cases s <;> first | decide | (rename_i i; fin_cases i <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_reserve (s : ScalarCase) (hs : s≠.lowDE) :
    (1/100000 : ℚ)<lowerOn (degree s) 0 (length (band s)) (certificate s) := by
  cases s <;> first | contradiction | decide | (rename_i i; fin_cases i <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lowDE_identity : certificate .lowDE=
    WholeIntervalBernstein.expansion 41 (1/5) (certificate .lowDE) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lowDE_partition :
    (∑i : Fin 42,WholeIntervalBernstein.basis 41 (1/5) i)=1 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lowDE_reserve (i : Fin 42) :
    (1/500 : ℚ)≤WholeIntervalBernstein.coefficient 41 (1/5) (certificate .lowDE) i := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length (band s)) (massAt s i)=
      expansion 3 (centered 0 (length (band s)) (massAt s i)) := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_reserves (s : ScalarCase) (i : Fin 5) :
    (4/5 : ℚ)<lowerOn 3 0 (length (band s)) (massAt s i) ∧
      upperOn 3 0 (length (band s)) (massAt s i)<3 := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem square_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length (band s)) (rowSquare s i)=
      expansion 38 (centered 0 (length (band s)) (rowSquare s i)) := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem square_reserves (s : ScalarCase) (i : Fin 5) :
    (1/4 : ℚ)<lowerOn 38 0 (length (band s)) (rowSquare s i) ∧
      upperOn 38 0 (length (band s)) (rowSquare s i)<6 := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

theorem certificate_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) : 0<aeval z (certificate s) := by
  by_cases hs : s=.lowDE
  · subst s
    have hh := WholeIntervalBernstein.lower_on_interval (by norm_num : (0:ℚ)<1/5)
      lowDE_identity lowDE_partition lowDE_reserve hz
    norm_num at hh
    linarith
  · have hh := positive_on_interval (length_pos (band s)) (certificate_identity s)
      (certificate_reserve s hs) hz
    norm_num at hh
    linarith

theorem mass_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    4/5<aeval z (massAt s i) ∧ aeval z (massAt s i)<3 := by
  have hh := interval_bounds (length_pos (band s)) (mass_identity s i) hz
  have hl : (4/5 : ℝ)<(lowerOn 3 0 (length (band s)) (massAt s i):ℝ) := by
    exact_mod_cast (mass_reserves s i).1
  have hu : (upperOn 3 0 (length (band s)) (massAt s i):ℝ)<(3:ℝ) := by
    exact_mod_cast (mass_reserves s i).2
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem square_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    1/4<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<6 := by
  have hh := interval_bounds (length_pos (band s)) (square_identity s i) hz
  have hl : (1/4 : ℝ)<(lowerOn 38 0 (length (band s)) (rowSquare s i):ℝ) := by
    exact_mod_cast (square_reserves s i).1
  have hu : (upperOn 38 0 (length (band s)) (rowSquare s i):ℝ)<(6:ℝ) := by
    exact_mod_cast (square_reserves s i).2
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem radius_upper : Real.sqrt qTrial<(radiusUpper:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hn := Real.sqrt_nonneg qTrial
  norm_num [qTrial,radiusUpper] at *
  nlinarith

theorem axis_upper : axisCoordinate qTrial<(axisUpper:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤qTrial-1/4 by norm_num [qTrial])
  have hn := Real.sqrt_nonneg (qTrial-1/4)
  norm_num [axisCoordinate,qTrial,axisUpper] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.SoleScalarPolynomials
