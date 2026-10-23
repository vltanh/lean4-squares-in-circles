module

public import SquaresInCircles.Eight.TableFree.ExceptionalECoefficients
public import SquaresInCircles.Eight.TableFree.SoleScalarPolynomials

/-!
# Ten whole-interval exceptional endpoint polynomials

Uncompiled source. The four domains are the two low intervals and the
complete middle and high intervals in the hand argument. Each of the
five radical masses comes from three rational Newton steps and a cubic
truncation. The displayed arithmetic proofs have not been run. These
polynomial facts are transferred to the actual trigonometric stress in
subsequent files; they are not assumed geometric conclusions.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalEPolynomials
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients

inductive ScalarCase where
  | lowZero | lowReturn | middle (i : Fin 4) | high (i : Fin 4)
  deriving DecidableEq, Fintype

def band : ScalarCase → Band
  | .lowZero | .lowReturn => .low
  | .middle _ => .middle
  | .high _ => .high

def origin : ScalarCase → ℚ
  | .lowZero => 0 | .lowReturn => 4/25 | .middle _ => 9/50 | .high _ => 7/20

def length : ScalarCase → ℚ
  | .lowZero => 1/10 | .lowReturn => 1/50 | .middle _ => 17/100 | .high _ => 7/20

def domain (s : ScalarCase) : Set ℝ := Set.Icc (origin s:ℝ) ((origin s+length s):ℝ)

def negativeIndex : ScalarCase → Fin 4
  | .lowZero | .lowReturn => 2
  | .middle i | .high i => i

def radiusUpper : ℚ := 989385433/500000000
def margin : ℚ := 1/100000000
def parameter (s : ScalarCase) : ℚ[X] := C (origin s)+X
def sine (s : ScalarCase) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter s)
def cosine (s : ScalarCase) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter s)

def k (s : ScalarCase) : ℚ[X] :=
  if band s=.low then C (17253/20000)+C (67/100)*parameter s+C (27/100)*(parameter s)^2 else 1

def ell (s : ScalarCase) : ℚ[X] :=
  match band s with
  | .low => C (50521/100000)+C (21/25)*parameter s+C (1/2)*(parameter s)^2
  | .middle => C (551/1000)+C (67/100)*parameter s+C (21/100)*(parameter s)^2
  | .high => C (7/10)+C (8/25)*parameter s

def c (s : ScalarCase) : ℚ[X] :=
  match band s with
  | .low => C (17253/20000)+C (18/25)*parameter s+C (3/10)*(parameter s)^2
  | .middle => C (891/1000)+C (16/25)*parameter s+C (1/50)*(parameter s)^2
  | .high => C (113/100)

def eta (s : ScalarCase) : ℚ[X] :=
  match band s with
  | .low => C (131/500)+C (19/100)*parameter s+C (2/25)*(parameter s)^2
  | .middle => C (61/200)-C (1/50)*parameter s+C (7/200)*(parameter s)^2
  | .high => C (27/100)+C (2/25)*parameter s

def p (s : ScalarCase) : ℚ[X] := cosine s+eta s*sine s
def first (s : ScalarCase) : Fin 4 → ℚ[X] := ![p s,k s,ell s,1]
def second (s : ScalarCase) : Fin 4 → ℚ[X] := ![k s,ell s,c s,c s]
def nu (s : ScalarCase) : ℚ[X] := ![C (53/50),ell s,c s,c s] (negativeIndex s)

def outside (s : ScalarCase) : ℚ[X] :=
  3*k s+2*ell s+3*c s+1+2*cosine s+(1+2*eta s)*sine s+nu s*(cosine s-1)

def squaredNorm (s : ScalarCase) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if i=negativeIndex s then 2*first s i*second s i*sine s else 0)

def rowSquare (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩ else 1+(eta s)^2

def rowWeight (s : ScalarCase) (i : Fin 5) : ℚ[X] := if i.val<4 then 1 else sine s
def massAt (s : ScalarCase) (i : Fin 5) : ℚ[X] := SoleScalarPolynomials.newtonMass (rowSquare s i)
def mass (s : ScalarCase) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏j : Fin 5,if j=i then 1 else massAt s j

def certificate (s : ScalarCase) : ℚ[X] :=
  2*(outside s-C margin)*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i

def middleBQuotient : ℚ[X] := (certificate (.middle 2)-C ((certificate (.middle 2)).coeff 0)).divX

theorem length_pos (s : ScalarCase) : 0<length s := by cases s <;> norm_num [length]

theorem family_domain {s : ScalarCase} {t : ℝ} (ht : t∈domain s) :
    t∈ExceptionalECoefficients.domain (band s) := by
  cases s <;> norm_num [domain,ExceptionalECoefficients.domain,origin,length,band,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem local_parameter {s : ScalarCase} {t : ℝ} (ht : t∈domain s) :
    t-(origin s:ℝ)∈Set.Icc 0 (length s:ℝ) := by
  dsimp [domain] at ht
  push_cast at ht
  constructor <;> linarith [ht.1,ht.2]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_identity (s : ScalarCase) :
    centered 0 (length s) (certificate s)=expansion 46 (centered 0 (length s) (certificate s)) := by
  cases s <;> first | decide | (rename_i i; fin_cases i <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem ordinary_reserve (s : ScalarCase) (h0 : s≠.lowZero) (hB : s≠.middle 2) :
    (1/1000:ℚ)<lowerOn 46 0 (length s) (certificate s) := by
  cases s <;> first | contradiction | decide | (rename_i i; fin_cases i <;> first | contradiction | decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_derivative_identity :
    centered 0 (1/10) (certificate .lowZero).derivative=
      expansion 45 (centered 0 (1/10) (certificate .lowZero).derivative) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_derivative_reserve :
    upperOn 45 0 (1/10) (certificate .lowZero).derivative<-(49/1000:ℚ) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_right_reserve : (1/2000:ℚ)<(certificate .lowZero).eval (1/10) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middleB_identity :
    certificate (.middle 2)=C ((certificate (.middle 2)).coeff 0)+X*middleBQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middleB_quotient_identity :
    centered 0 (17/100) middleBQuotient=expansion 45 (centered 0 (17/100) middleBQuotient) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middleB_reserves : (1/250:ℚ)<(certificate (.middle 2)).coeff 0 ∧
    (1/5:ℚ)<lowerOn 45 0 (17/100) middleBQuotient := by decide

theorem polynomial_hasDerivAt (P : ℚ[X]) (z : ℝ) :
    HasDerivAt (fun x : ℝ => aeval x P) (aeval z P.derivative) z := by
  simpa [Polynomial.aeval_def,Polynomial.derivative_map] using
    (P.map (algebraMap ℚ ℝ)).hasDerivAt z

theorem certificate_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 0<aeval z (certificate s) := by
  by_cases h0 : s=.lowZero
  · subst s
    have hmono : MonotoneOn (fun x : ℝ => -aeval x (certificate .lowZero)) (Set.Icc 0 (1/10)) := by
      apply monoOn_of_hasDeriv_nonneg
      · fun_prop
      · intro x _; exact (polynomial_hasDerivAt _ x).neg
      · intro x hx
        have hb := (interval_bounds (by norm_num : (0:ℚ)<1/10)
          low_derivative_identity (Set.Ioo_subset_Icc_self hx)).2
        have hr : (upperOn 45 0 (1/10) (certificate .lowZero).derivative:ℝ)<-49/1000 := by
          exact_mod_cast low_derivative_reserve
        linarith
    have hright : (1/2000:ℝ)<aeval (1/10:ℝ) (certificate .lowZero) := by
      exact_mod_cast low_right_reserve
    have hm := hmono hz (by norm_num) hz.2
    linarith
  · by_cases hB : s=.middle 2
    · subst s
      have hquot := positive_on_interval (by norm_num : (0:ℚ)<17/100)
        middleB_quotient_identity middleB_reserves.2 hz
      have hc0 : (1/250:ℝ)<((certificate (.middle 2)).coeff 0:ℝ) := by
        exact_mod_cast middleB_reserves.1
      have hm := mul_nonneg hz.1 (show 0≤aeval z middleBQuotient by linarith)
      rw [middleB_identity]
      simp only [map_add,map_mul,aeval_C,aeval_X]
      linarith
    · have hh := positive_on_interval (length_pos s) (certificate_identity s)
        (ordinary_reserve s h0 hB) hz
      norm_num at hh
      linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length s) (massAt s i)=expansion 3 (centered 0 (length s) (massAt s i)) := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_reserves (s : ScalarCase) (i : Fin 5) :
    (4/5:ℚ)<lowerOn 3 0 (length s) (massAt s i) ∧ upperOn 3 0 (length s) (massAt s i)<3 := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem square_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length s) (rowSquare s i)=expansion 38 (centered 0 (length s) (rowSquare s i)) := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem square_reserves (s : ScalarCase) (i : Fin 5) :
    (1/4:ℚ)<lowerOn 38 0 (length s) (rowSquare s i) ∧ upperOn 38 0 (length s) (rowSquare s i)<6 := by
  cases s <;> fin_cases i <;> first | decide | (rename_i j; fin_cases j <;> decide)

theorem mass_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 4/5<aeval z (massAt s i) ∧ aeval z (massAt s i)<3 := by
  have hh := interval_bounds (length_pos s) (mass_identity s i) hz
  have hl : (4/5:ℝ)<(lowerOn 3 0 (length s) (massAt s i):ℝ) := by exact_mod_cast (mass_reserves s i).1
  have hu : (upperOn 3 0 (length s) (massAt s i):ℝ)<(3:ℝ) := by exact_mod_cast (mass_reserves s i).2
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem square_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 1/4<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<6 := by
  have hh := interval_bounds (length_pos s) (square_identity s i) hz
  have hl : (1/4:ℝ)<(lowerOn 38 0 (length s) (rowSquare s i):ℝ) := by exact_mod_cast (square_reserves s i).1
  have hu : (upperOn 38 0 (length s) (rowSquare s i):ℝ)<(6:ℝ) := by exact_mod_cast (square_reserves s i).2
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

end SquaresInCircles.Eight.TableFree.ExceptionalEPolynomials
