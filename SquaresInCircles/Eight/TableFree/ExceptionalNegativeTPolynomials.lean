module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarModel

/-!
# Whole-interval certificates for the forty-four negative-T endpoints

Uncompiled source. This is the exact cubic-Newton-mass construction in
the outside-strip hand proof. Each rational assertion concerns a whole
intrinsic interval. The middle TD diagonal uses its constant term and
positive first quotient. The arithmetic proof terms have not been run.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTPolynomials
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients
open ExceptionalNegativeTScalarModel (Row Case band isTD diagonal index origin length domain cap)

def radiusUpper : ℚ := 989385433/500000000
def parameter (s : Case) : ℚ[X] := C (origin s.row)+X
def removed (s : Case) : ℚ[X] := if diagonal s.row then parameter s else C (cap s.row)
def angle (s : Case) : ℚ[X] := parameter s-removed s
def sine (s : Case) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter s)
def cosine (s : Case) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter s)
def shortSine (s : Case) : ℚ[X] := PositiveScalarPolynomials.sine.comp (angle s)
def shortCosine (s : Case) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (angle s)

def k (s : Case) : ℚ[X] :=
  if band s.row=.low then C (17253/20000)+C (67/100)*parameter s+C (27/100)*(parameter s)^2 else 1
def ell (s : Case) : ℚ[X] :=
  match band s.row with
  | .low => C (50521/100000)+C (21/25)*parameter s+C (1/2)*(parameter s)^2
  | .middle => C (551/1000)+C (67/100)*parameter s+C (21/100)*(parameter s)^2
  | .high => C (7/10)+C (8/25)*parameter s
def c (s : Case) : ℚ[X] :=
  match band s.row with
  | .low => C (17253/20000)+C (18/25)*parameter s+C (3/10)*(parameter s)^2
  | .middle => C (891/1000)+C (16/25)*parameter s+C (1/50)*(parameter s)^2
  | .high => C (113/100)
def eta (s : Case) : ℚ[X] :=
  match band s.row with
  | .low => C (131/500)+C (19/100)*parameter s+C (2/25)*(parameter s)^2
  | .middle => C (61/200)-C (1/50)*parameter s+C (7/200)*(parameter s)^2
  | .high => C (27/100)+C (2/25)*parameter s
def slope (s : Case) : ℚ[X] :=
  if isTD s.row then C (13/12)-C (1/5)*removed s+C (8/25)*(removed s)^2 else C (21/20)
def correction (s : Case) : ℚ[X] :=
  if isTD s.row && decide (band s.row≠.low) then C (8/25)*(c s-1)^2 else 0
def p (s : Case) : ℚ[X] := cosine s+eta s*sine s
def first (s : Case) : Fin 4 → ℚ[X] := ![if s.atG then 1 else p s,k s,ell s,1]
def second (s : Case) : Fin 4 → ℚ[X] := ![if s.atG then k s*p s else k s,ell s,c s,c s]
def nu (s : Case) : ℚ[X] := ![C (53/50),ell s,c s] (index s.row)

def outside (s : Case) : ℚ[X] :=
  (if s.atG then 3+2*ell s+3*c s+k s*(1+2*cosine s+(1+2*eta s)*sine s)
    else 3*k s+2*ell s+3*c s+1+2*cosine s+(1+2*eta s)*sine s)+
    correction s+c s*slope s*removed s+
    (if diagonal s.row then 0 else nu s*(shortCosine s-1))
def squaredNorm (s : Case) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if !diagonal s.row && decide (i.val=(index s.row).val)
      then 2*first s i*second s i*shortSine s else 0)
def rowSquare (s : Case) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩ else 1+(eta s)^2
def rowWeight (s : Case) (i : Fin 5) : ℚ[X] :=
  if i.val<4 then 1 else if s.atG then k s*sine s else sine s
def massAt (s : Case) (i : Fin 5) : ℚ[X] := SoleScalarPolynomials.newtonMass (rowSquare s i)
def mass (s : Case) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : Case) (i : Fin 5) : ℚ[X] := ∏j : Fin 5,if j=i then 1 else massAt s j
def certificate (s : Case) : ℚ[X] :=
  2*outside s*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i
def middleQuotient (face : Bool) : ℚ[X] :=
  (certificate ⟨.tdMiddleDiagonal,face⟩-C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0)).divX

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_identity (s : Case) :
    centered 0 (length s.row) (certificate s)=
      expansion 50 (centered 0 (length s.row) (certificate s)) := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> first | decide | (rename_i i; fin_cases i <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem ordinary_reserve (s : Case) (hm : s.row≠.tdMiddleDiagonal) :
    (1/250:ℚ)<lowerOn 50 0 (length s.row) (certificate s) := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> first | contradiction | decide | (rename_i i; fin_cases i <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middle_identity (face : Bool) :
    certificate ⟨.tdMiddleDiagonal,face⟩=
      C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0)+X*middleQuotient face := by
  cases face <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middle_quotient_identity (face : Bool) :
    centered 0 (3/25) (middleQuotient face)=
      expansion 49 (centered 0 (3/25) (middleQuotient face)) := by cases face <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middle_reserves (face : Bool) :
    (119/50000:ℚ)<(certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0 ∧
      (9/1250:ℚ)<lowerOn 49 0 (3/25) (middleQuotient face) := by cases face <;> decide

theorem certificate_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    (119/50000:ℝ)<aeval z (certificate s) := by
  by_cases hm : s.row=.tdMiddleDiagonal
  · rcases s with ⟨r,face⟩
    dsimp at hm
    subst r
    have hquot := positive_on_interval (by norm_num : (0:ℚ)<3/25)
      (middle_quotient_identity face) (middle_reserves face).2 hz
    have hzero : (119/50000:ℝ)<((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0:ℝ) := by
      exact_mod_cast (middle_reserves face).1
    have hprod := mul_nonneg hz.1 (show 0≤aeval z (middleQuotient face) by linarith)
    rw [middle_identity]
    simp only [map_add,map_mul,aeval_C,aeval_X]
    linarith
  · have hb := (interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row)
      (certificate_identity s) hz).1
    have hr : (1/250:ℝ)<(lowerOn 50 0 (length s.row) (certificate s):ℝ) := by
      exact_mod_cast ordinary_reserve s hm
    linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_identity (s : Case) (i : Fin 5) :
    centered 0 (length s.row) (massAt s i)=
      expansion 3 (centered 0 (length s.row) (massAt s i)) := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_reserves (s : Case) (i : Fin 5) :
    (89/100:ℚ)<lowerOn 3 0 (length s.row) (massAt s i) ∧
      upperOn 3 0 (length s.row) (massAt s i)<151/100 := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem square_identity (s : Case) (i : Fin 5) :
    centered 0 (length s.row) (rowSquare s i)=
      expansion 38 (centered 0 (length s.row) (rowSquare s i)) := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem square_reserves (s : Case) (i : Fin 5) :
    (79/100:ℚ)<lowerOn 38 0 (length s.row) (rowSquare s i) ∧
      upperOn 38 0 (length s.row) (rowSquare s i)<3 := by
  rcases s with ⟨r,face⟩
  cases r <;> cases face <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

theorem mass_bounds (s : Case) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    89/100<aeval z (massAt s i) ∧ aeval z (massAt s i)<151/100 := by
  have hb := interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row) (mass_identity s i) hz
  have hl : (89/100:ℝ)<(lowerOn 3 0 (length s.row) (massAt s i):ℝ) := by
    exact_mod_cast (mass_reserves s i).1
  have hu : (upperOn 3 0 (length s.row) (massAt s i):ℝ)<(151/100:ℝ) := by
    exact_mod_cast (mass_reserves s i).2
  exact ⟨hl.trans_le hb.1,hb.2.trans_lt hu⟩

theorem square_bounds (s : Case) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    79/100<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<3 := by
  have hb := interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row) (square_identity s i) hz
  have hl : (79/100:ℝ)<(lowerOn 38 0 (length s.row) (rowSquare s i):ℝ) := by
    exact_mod_cast (square_reserves s i).1
  have hu : (upperOn 38 0 (length s.row) (rowSquare s i):ℝ)<(3:ℝ) := by
    exact_mod_cast (square_reserves s i).2
  exact ⟨hl.trans_le hb.1,hb.2.trans_lt hu⟩

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTPolynomials
