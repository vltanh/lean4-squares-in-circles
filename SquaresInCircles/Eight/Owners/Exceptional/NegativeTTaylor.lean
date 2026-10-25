module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PackedPolynomials
public import SquaresInCircles.Eight.Owners.Exceptional.EBalanced
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTScalarModel
public import SquaresInCircles.Eight.Owners.Sole.LowGapPolynomials

/-!
# Eight squares: actual trigonometric negative-T endpoint inequalities

The S15/C16 errors are carried through all four
trigonometric inputs on each complete intrinsic interval. The rational
numerator reserve pays their total loss. The support radius is then
decreased to the unchanged original common q.
-/

section
/-!
## Whole-interval certificates for the forty-four negative-T endpoints

This is the exact cubic-Newton-mass construction in
the outside-strip hand proof. Each rational assertion concerns a whole
intrinsic interval. The middle TD diagonal uses its constant term and
positive first quotient. The arithmetic proof terms have not been run.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTPolynomials
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients PackedPolynomials
open ExceptionalNegativeTScalarModel (Row Case band isTD diagonal index origin length domain cap)
open WholeIntervalPolynomial.Certificate (Scaled toPoly chebList twoX lowerZ upperZ)

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

/-! ## The scalars, packed

`fK k r cn` packs `(f s).comp (aff r cn)` at the base `2 ^ k`, for a scalar `s` of the interval
row `r`: the polynomial itself when `cn = false`, its centered polynomial on `[0, length r]`
when `cn = true`. The packings that depend on the face also take `g = s.atG`; those of the
rows `1 ≤ i` do not, so that both faces of a row share them in the kernel. -/

private def aff (r : Row) (cn : Bool) : ℚ[X] := if cn then affine 0 (length r) else X

/-- `C a + X`, composed. -/
private def affK (k : ℕ) (r : Row) (cn : Bool) (a : ℚ) : Packed :=
  if cn then
    (Packed.const (a + length r / 2)).add ((Packed.const (length r / 2)).mul (Packed.var (2 ^ k)))
  else (Packed.const a).add (Packed.var (2 ^ k))

private theorem affK_rep (k : ℕ) (r : Row) (cn : Bool) (a : ℚ) :
    (affK k r cn a).Rep (2 ^ k) ((C a + X).comp (aff r cn)) := by
  unfold affK aff
  split_ifs
  · have e : (C a + X).comp (affine 0 (length r)) = C (a + length r / 2) + C (length r / 2) * X := by
      simp only [add_comp, C_comp, X_comp, affine, zero_add, sub_zero, C_add]; ring
    rw [e]
    exact (Packed.rep_const _).add ((Packed.rep_const _).mul (Packed.rep_var _))
  · rw [comp_X]
    exact (Packed.rep_const _).add (Packed.rep_var _)

private def parK (k : ℕ) (r : Row) (cn : Bool) : Packed := affK k r cn (origin r)

private theorem parK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (parK k s.row cn).Rep (2 ^ k) ((parameter s).comp (aff s.row cn)) := affK_rep k s.row cn _

private def sinK (k : ℕ) (r : Row) (cn : Bool) : Packed := sineK (parK k r cn)
private def cosK (k : ℕ) (r : Row) (cn : Bool) : Packed := cosineK (parK k r cn)

private theorem sinK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (sinK k s.row cn).Rep (2 ^ k) ((sine s).comp (aff s.row cn)) := by
  rw [sine, comp_assoc]; exact sineK_rep (parK_rep k s cn)

private theorem cosK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (cosK k s.row cn).Rep (2 ^ k) ((cosine s).comp (aff s.row cn)) := by
  rw [cosine, comp_assoc]; exact cosineK_rep (parK_rep k s cn)

private def shortSinK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  if diagonal r then Packed.zero else sineK (affK k r cn (origin r - cap r))
private def shortCosK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  if diagonal r then Packed.ofNat 1 else cosineK (affK k r cn (origin r - cap r))

private theorem angle_eq (s : Case) (h : diagonal s.row = false) :
    angle s = C (origin s.row - cap s.row) + X := by
  simp only [angle, removed, h, Bool.false_eq_true, ite_false, parameter, C_sub]; ring

private theorem shortSinK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (shortSinK k s.row cn).Rep (2 ^ k) ((shortSine s).comp (aff s.row cn)) := by
  unfold shortSinK
  split_ifs with h
  · have e : (shortSine s).comp (aff s.row cn) = 0 := by
      simp only [shortSine, angle, removed, h, ite_true, sub_self, comp_assoc, zero_comp]
      simp [PositiveScalarPolynomials.sine]
    rw [e]; exact Packed.rep_zero
  · rw [shortSine, comp_assoc, angle_eq s (by simpa using h)]
    exact sineK_rep (affK_rep k s.row cn _)

private theorem shortCosK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (shortCosK k s.row cn).Rep (2 ^ k) ((shortCosine s).comp (aff s.row cn)) := by
  unfold shortCosK
  split_ifs with h
  · have e : (shortCosine s).comp (aff s.row cn) = ((1 : ℕ) : ℚ[X]) := by
      simp only [shortCosine, angle, removed, h, ite_true, sub_self, comp_assoc, zero_comp]
      simp [PositiveScalarPolynomials.cosine]
    rw [e]; exact Packed.rep_ofNat 1
  · rw [shortCosine, comp_assoc, angle_eq s (by simpa using h)]
    exact cosineK_rep (affK_rep k s.row cn _)

private def removedK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  if diagonal r then parK k r cn else Packed.const (cap r)

private theorem removedK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (removedK k s.row cn).Rep (2 ^ k) ((removed s).comp (aff s.row cn)) := by
  unfold removedK removed
  split_ifs
  · exact parK_rep k s cn
  · rw [C_comp]; exact Packed.rep_const _

private def quadK (k : ℕ) (r : Row) (cn : Bool) (a b c : ℚ) : Packed :=
  ((Packed.const a).add ((Packed.const b).mul (parK k r cn))).add
    ((Packed.const c).mul ((parK k r cn).pow 2))

private theorem quadK_rep (k : ℕ) (s : Case) (cn : Bool) (a b c : ℚ) :
    (quadK k s.row cn a b c).Rep (2 ^ k)
      ((C a + C b * parameter s + C c * (parameter s) ^ 2).comp (aff s.row cn)) := by
  simp only [add_comp, mul_comp, C_comp, pow_comp]
  exact ((Packed.rep_const a).add ((Packed.rep_const b).mul (parK_rep k s cn))).add
    ((Packed.rep_const c).mul ((parK_rep k s cn).pow 2))

private theorem lin_rep (k : ℕ) (s : Case) (cn : Bool) (a b : ℚ) :
    ((Packed.const a).add ((Packed.const b).mul (parK k s.row cn))).Rep (2 ^ k)
      ((C a + C b * parameter s).comp (aff s.row cn)) := by
  simp only [add_comp, mul_comp, C_comp]
  exact (Packed.rep_const a).add ((Packed.rep_const b).mul (parK_rep k s cn))

private def kK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  if band r = .low then quadK k r cn (17253/20000) (67/100) (27/100) else Packed.ofNat 1

private theorem kK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (kK k s.row cn).Rep (2 ^ k) ((ExceptionalNegativeTPolynomials.k s).comp (aff s.row cn)) := by
  unfold kK ExceptionalNegativeTPolynomials.k
  split_ifs
  · exact quadK_rep k s cn _ _ _
  · rw [one_comp]; exact Packed.rep_one'

private def ellK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  match band r with
  | .low => quadK k r cn (50521/100000) (21/25) (1/2)
  | .middle => quadK k r cn (551/1000) (67/100) (21/100)
  | .high => (Packed.const (7/10)).add ((Packed.const (8/25)).mul (parK k r cn))

private theorem ellK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (ellK k s.row cn).Rep (2 ^ k) ((ell s).comp (aff s.row cn)) := by
  unfold ellK ell
  generalize band s.row = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · exact quadK_rep k s cn _ _ _
  · exact lin_rep k s cn _ _

private def cK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  match band r with
  | .low => quadK k r cn (17253/20000) (18/25) (3/10)
  | .middle => quadK k r cn (891/1000) (16/25) (1/50)
  | .high => Packed.const (113/100)

private theorem cK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (cK k s.row cn).Rep (2 ^ k) ((c s).comp (aff s.row cn)) := by
  unfold cK c
  generalize band s.row = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · exact quadK_rep k s cn _ _ _
  · rw [C_comp]; exact Packed.rep_const _

private def etaK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  match band r with
  | .low => quadK k r cn (131/500) (19/100) (2/25)
  | .middle => ((Packed.const (61/200)).sub ((Packed.const (1/50)).mul (parK k r cn))).add
      ((Packed.const (7/200)).mul ((parK k r cn).pow 2))
  | .high => (Packed.const (27/100)).add ((Packed.const (2/25)).mul (parK k r cn))

private theorem etaK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (etaK k s.row cn).Rep (2 ^ k) ((eta s).comp (aff s.row cn)) := by
  unfold etaK eta
  generalize band s.row = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · simp only [add_comp, sub_comp, mul_comp, C_comp, pow_comp]
    exact ((Packed.rep_const _).sub ((Packed.rep_const _).mul (parK_rep k s cn))).add
      ((Packed.rep_const _).mul ((parK_rep k s cn).pow 2))
  · exact lin_rep k s cn _ _

private def slopeK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  if isTD r then ((Packed.const (13/12)).sub ((Packed.const (1/5)).mul (removedK k r cn))).add
    ((Packed.const (8/25)).mul ((removedK k r cn).pow 2)) else Packed.const (21/20)

private theorem slopeK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (slopeK k s.row cn).Rep (2 ^ k) ((slope s).comp (aff s.row cn)) := by
  unfold slopeK slope
  split_ifs
  · simp only [add_comp, sub_comp, mul_comp, C_comp, pow_comp]
    exact ((Packed.rep_const _).sub ((Packed.rep_const _).mul (removedK_rep k s cn))).add
      ((Packed.rep_const _).mul ((removedK_rep k s cn).pow 2))
  · rw [C_comp]; exact Packed.rep_const _

private def correctionK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  if isTD r && decide (band r ≠ .low) then
    (Packed.const (8/25)).mul (((cK k r cn).sub (Packed.ofNat 1)).pow 2) else Packed.zero

private theorem correctionK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (correctionK k s.row cn).Rep (2 ^ k) ((correction s).comp (aff s.row cn)) := by
  unfold correctionK correction
  split_ifs
  · simp only [mul_comp, C_comp, pow_comp, sub_comp, one_comp]
    exact (Packed.rep_const _).mul (((cK_rep k s cn).sub Packed.rep_one').pow 2)
  · rw [zero_comp]; exact Packed.rep_zero

private def pK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  (cosK k r cn).add ((etaK k r cn).mul (sinK k r cn))

private theorem pK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (pK k s.row cn).Rep (2 ^ k) ((p s).comp (aff s.row cn)) := by
  rw [p, add_comp, mul_comp]
  exact (cosK_rep k s cn).add ((etaK_rep k s cn).mul (sinK_rep k s cn))

private def firstK (k : ℕ) (r : Row) (g cn : Bool) : Fin 4 → Packed :=
  ![if g then Packed.ofNat 1 else pK k r cn, kK k r cn, ellK k r cn, Packed.ofNat 1]

private def secondK (k : ℕ) (r : Row) (g cn : Bool) : Fin 4 → Packed :=
  ![if g then (kK k r cn).mul (pK k r cn) else kK k r cn, ellK k r cn, cK k r cn, cK k r cn]

private theorem one_rep (k : ℕ) (r : Row) (cn : Bool) :
    (Packed.ofNat 1).Rep (2 ^ k) ((1 : ℚ[X]).comp (aff r cn)) := by
  rw [one_comp]; exact Packed.rep_one'

private theorem firstK_rep (k : ℕ) (s : Case) (cn : Bool) (i : Fin 4) :
    (firstK k s.row s.atG cn i).Rep (2 ^ k) ((first s i).comp (aff s.row cn)) := by
  fin_cases i
  · show (if s.atG then Packed.ofNat 1 else pK k s.row cn).Rep (2 ^ k)
      ((if s.atG then 1 else p s).comp (aff s.row cn))
    split_ifs
    · exact one_rep k s.row cn
    · exact pK_rep k s cn
  · exact kK_rep k s cn
  · exact ellK_rep k s cn
  · exact one_rep k s.row cn

private theorem secondK_rep (k : ℕ) (s : Case) (cn : Bool) (i : Fin 4) :
    (secondK k s.row s.atG cn i).Rep (2 ^ k) ((second s i).comp (aff s.row cn)) := by
  fin_cases i
  · show (if s.atG then (kK k s.row cn).mul (pK k s.row cn) else kK k s.row cn).Rep (2 ^ k)
      ((if s.atG then ExceptionalNegativeTPolynomials.k s * p s
        else ExceptionalNegativeTPolynomials.k s).comp (aff s.row cn))
    split_ifs
    · rw [mul_comp]; exact (kK_rep k s cn).mul (pK_rep k s cn)
    · exact kK_rep k s cn
  · exact ellK_rep k s cn
  · exact cK_rep k s cn
  · exact cK_rep k s cn

private def nuK (k : ℕ) (r : Row) (cn : Bool) : Packed :=
  ![Packed.const (53/50), ellK k r cn, cK k r cn] (index r)

private theorem nuK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (nuK k s.row cn).Rep (2 ^ k) ((nu s).comp (aff s.row cn)) := by
  unfold nuK nu
  generalize index s.row = i
  fin_cases i
  · show (Packed.const (53/50)).Rep (2 ^ k) ((C (53/50)).comp (aff s.row cn))
    rw [C_comp]; exact Packed.rep_const _
  · exact ellK_rep k s cn
  · exact cK_rep k s cn

private def outsideIK (k : ℕ) (r : Row) (g cn : Bool) : Packed :=
  if g then
    (((Packed.ofNat 3).add ((Packed.ofNat 2).mul (ellK k r cn))).add
      ((Packed.ofNat 3).mul (cK k r cn))).add
      ((kK k r cn).mul (((Packed.ofNat 1).add ((Packed.ofNat 2).mul (cosK k r cn))).add
        (((Packed.ofNat 1).add ((Packed.ofNat 2).mul (etaK k r cn))).mul (sinK k r cn))))
  else
    ((((((Packed.ofNat 3).mul (kK k r cn)).add ((Packed.ofNat 2).mul (ellK k r cn))).add
      ((Packed.ofNat 3).mul (cK k r cn))).add (Packed.ofNat 1)).add
      ((Packed.ofNat 2).mul (cosK k r cn))).add
      (((Packed.ofNat 1).add ((Packed.ofNat 2).mul (etaK k r cn))).mul (sinK k r cn))

private def outsideK (k : ℕ) (r : Row) (g cn : Bool) : Packed :=
  (((outsideIK k r g cn).add (correctionK k r cn)).add
    (((cK k r cn).mul (slopeK k r cn)).mul (removedK k r cn))).add
    (if diagonal r then Packed.zero else (nuK k r cn).mul ((shortCosK k r cn).sub (Packed.ofNat 1)))

private theorem outsideK_rep (k : ℕ) (s : Case) (cn : Bool) :
    (outsideK k s.row s.atG cn).Rep (2 ^ k) ((outside s).comp (aff s.row cn)) := by
  have h1 : (Packed.ofNat 1).Rep (2 ^ k) (1 : ℚ[X]) := Packed.rep_one'
  have h2 : (Packed.ofNat 2).Rep (2 ^ k) ((2 : ℕ) : ℚ[X]) := Packed.rep_ofNat 2
  have h3 : (Packed.ofNat 3).Rep (2 ^ k) ((3 : ℕ) : ℚ[X]) := Packed.rep_ofNat 3
  unfold outsideK outsideIK outside
  rw [add_comp, add_comp, add_comp]
  refine (((?_ : Packed.Rep _ _ _).add (correctionK_rep k s cn)).add ?_).add ?_
  · split_ifs
    · simp only [add_comp, mul_comp, one_comp, ofNat_comp]
      exact ((h3.add (h2.mul (ellK_rep k s cn))).add (h3.mul (cK_rep k s cn))).add
        ((kK_rep k s cn).mul ((h1.add (h2.mul (cosK_rep k s cn))).add
          ((h1.add (h2.mul (etaK_rep k s cn))).mul (sinK_rep k s cn))))
    · simp only [add_comp, mul_comp, one_comp, ofNat_comp]
      exact (((((h3.mul (kK_rep k s cn)).add (h2.mul (ellK_rep k s cn))).add
        (h3.mul (cK_rep k s cn))).add h1).add (h2.mul (cosK_rep k s cn))).add
        ((h1.add (h2.mul (etaK_rep k s cn))).mul (sinK_rep k s cn))
  · rw [mul_comp, mul_comp]
    exact ((cK_rep k s cn).mul (slopeK_rep k s cn)).mul (removedK_rep k s cn)
  · split_ifs
    · rw [zero_comp]; exact Packed.rep_zero
    · rw [mul_comp, sub_comp, one_comp]
      exact (nuK_rep k s cn).mul ((shortCosK_rep k s cn).sub h1)

private def squaredNormK (k : ℕ) (r : Row) (g cn : Bool) (i : Fin 4) : Packed :=
  if !diagonal r && decide (i.val = (index r).val) then
    (((firstK k r g cn i).pow 2).add ((secondK k r g cn i).pow 2)).sub
      ((((Packed.ofNat 2).mul (firstK k r g cn i)).mul (secondK k r g cn i)).mul (shortSinK k r cn))
  else ((firstK k r g cn i).pow 2).add ((secondK k r g cn i).pow 2)

private theorem squaredNormK_rep (k : ℕ) (s : Case) (cn : Bool) (i : Fin 4) :
    (squaredNormK k s.row s.atG cn i).Rep (2 ^ k) ((squaredNorm s i).comp (aff s.row cn)) := by
  unfold squaredNormK squaredNorm
  split_ifs
  · simp only [add_comp, sub_comp, mul_comp, pow_comp, ofNat_comp]
    exact (((firstK_rep k s cn i).pow 2).add ((secondK_rep k s cn i).pow 2)).sub
      ((((Packed.rep_ofNat 2).mul (firstK_rep k s cn i)).mul (secondK_rep k s cn i)).mul
        (shortSinK_rep k s cn))
  · simp only [add_comp, pow_comp, sub_zero]
    exact ((firstK_rep k s cn i).pow 2).add ((secondK_rep k s cn i).pow 2)

private def rowSquareAt (k : ℕ) (r : Row) (g cn : Bool) (i : Fin 5) : Packed :=
  if hi : i.val < 4 then squaredNormK k r g cn ⟨i.val, hi⟩
  else (Packed.ofNat 1).add ((etaK k r cn).pow 2)

private theorem rowSquareAt_rep (k : ℕ) (s : Case) (cn : Bool) (i : Fin 5) :
    (rowSquareAt k s.row s.atG cn i).Rep (2 ^ k) ((rowSquare s i).comp (aff s.row cn)) := by
  unfold rowSquareAt rowSquare
  split_ifs
  · exact squaredNormK_rep k s cn _
  · rw [add_comp, pow_comp]
    exact (one_rep k s.row cn).add ((etaK_rep k s cn).pow 2)

private theorem rowSquare_face (s : Case) {i : Fin 5} (h : i.val ≠ 0) :
    rowSquare ⟨s.row, false⟩ i = rowSquare s i := by
  fin_cases i
  · exact absurd rfl h
  all_goals rfl

private theorem massAt_face (s : Case) {i : Fin 5} (h : i.val ≠ 0) :
    massAt ⟨s.row, false⟩ i = massAt s i := by
  unfold massAt; rw [rowSquare_face s h]

/-- The rows `1 ≤ i` are taken at the face `false`, the same packing for both faces. -/
private def rowSquareK (k : ℕ) (r : Row) (g cn : Bool) (i : Fin 5) : Packed :=
  if i.val = 0 then rowSquareAt k r g cn i else rowSquareAt k r false cn i

private theorem rowSquareK_rep (k : ℕ) (s : Case) (cn : Bool) (i : Fin 5) :
    (rowSquareK k s.row s.atG cn i).Rep (2 ^ k) ((rowSquare s i).comp (aff s.row cn)) := by
  unfold rowSquareK
  split_ifs with h
  · exact rowSquareAt_rep k s cn i
  · have h' := rowSquareAt_rep k ⟨s.row, false⟩ cn i
    rw [rowSquare_face s h] at h'
    exact h'

private def rowWeightK (k : ℕ) (r : Row) (g cn : Bool) (i : Fin 5) : Packed :=
  if i.val < 4 then Packed.ofNat 1 else if g then (kK k r cn).mul (sinK k r cn) else sinK k r cn

private theorem rowWeightK_rep (k : ℕ) (s : Case) (cn : Bool) (i : Fin 5) :
    (rowWeightK k s.row s.atG cn i).Rep (2 ^ k) ((rowWeight s i).comp (aff s.row cn)) := by
  unfold rowWeightK rowWeight
  split_ifs
  · exact one_rep k s.row cn
  · rw [mul_comp]; exact (kK_rep k s cn).mul (sinK_rep k s cn)
  · exact sinK_rep k s cn

/-! ### The Newton masses -/

/-- The checks behind the Newton mass of row `i` at the face `g`, on its uncentered row square. -/
private def massGoodAt (k : ℕ) (r : Row) (g : Bool) (i : Fin 5) : Bool :=
  newtonOK k (rowSquareAt k r g false i)

/-- The coefficients of `massAt`. -/
private def massListAt (k : ℕ) (r : Row) (g : Bool) (i : Fin 5) : Scaled :=
  newtonList k (rowSquareAt k r g false i)

private theorem massListAt_rep {k : ℕ} {s : Case} {i : Fin 5}
    (h : massGoodAt k s.row s.atG i = true) : (massListAt k s.row s.atG i).Rep (massAt s i) := by
  have hr := rowSquareAt_rep k s false i
  rw [aff, ite_eq_right Bool.false_ne_true, comp_X] at hr
  exact newtonList_rep hr h

private def massGood (k : ℕ) (r : Row) (g : Bool) (i : Fin 5) : Bool :=
  if i.val = 0 then massGoodAt k r g i else massGoodAt k r false i

private def massList (k : ℕ) (r : Row) (g : Bool) (i : Fin 5) : Scaled :=
  if i.val = 0 then massListAt k r g i else massListAt k r false i

private theorem massList_rep {k : ℕ} {s : Case} {i : Fin 5} (h : massGood k s.row s.atG i = true) :
    (massList k s.row s.atG i).Rep (massAt s i) := by
  unfold massList
  unfold massGood at h
  split_ifs at h ⊢ with hi
  · exact massListAt_rep h
  · have h' := massListAt_rep (s := ⟨s.row, false⟩) h
    rw [massAt_face s hi] at h'
    exact h'

/-- Centering on `[0, length r]`. -/
private def cen (r : Row) (c : Scaled) : Scaled :=
  c.center (length r).num.toNat (2 * (length r).den) 1 1

private theorem half_eq (L : ℚ) (hL : 0 < L) :
    L / 2 = ((L.num.toNat : ℕ) : ℚ) * ((1:ℤ) : ℚ) / ((2 * L.den : ℕ) : ℚ) := by
  have hn : ((L.num.toNat : ℕ) : ℚ) = L.num := by
    have : 0 ≤ L.num := Rat.num_nonneg.mpr hL.le
    exact_mod_cast Int.toNat_of_nonneg this
  have hd : (L.den : ℚ) ≠ 0 := by exact_mod_cast L.den_ne_zero
  rw [hn]
  conv_lhs => rw [← Rat.num_div_den L]
  push_cast
  field_simp

private theorem cen_rep (r : Row) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (cen r c).Rep (centered 0 (length r) p) := by
  have hL := ExceptionalNegativeTScalarModel.length_pos r
  unfold cen
  exact hc.centered _ _ 1 1 (by simp) (by rw [zero_add, half_eq _ hL])
    (by rw [sub_zero, half_eq _ hL])

/-- The mass of row `i` as a list, centered on `[0, length r]` when `cn`. -/
private def massLC (k : ℕ) (r : Row) (g cn : Bool) (i : Fin 5) : Scaled :=
  if cn then cen r (massList k r g i) else massList k r g i

private theorem massLC_rep {k : ℕ} {s : Case} (cn : Bool) {i : Fin 5}
    (h : massGood k s.row s.atG i = true) :
    (massLC k s.row s.atG cn i).Rep ((massAt s i).comp (aff s.row cn)) := by
  unfold massLC aff
  split_ifs
  · exact cen_rep s.row (massList_rep h)
  · rw [comp_X]; exact massList_rep h

/-! ### The certificate -/

private def certK (k : ℕ) (r : Row) (g cn : Bool) : Packed :=
  certificateK (outsideK k r g cn) (Packed.const radiusUpper) (rowWeightK k r g cn)
    (rowSquareK k r g cn) (fun i => Packed.ofList k (massLC k r g cn i).l)
    (fun i => (massLC k r g cn i).s)

private def massesGood (k : ℕ) (r : Row) (g : Bool) : Bool :=
  massGood k r g 0 && massGood k r g 1 && massGood k r g 2 && massGood k r g 3 && massGood k r g 4

private theorem massesGood_spec {k : ℕ} {r : Row} {g : Bool} (h : massesGood k r g = true)
    (i : Fin 5) : massGood k r g i = true := by
  simp only [massesGood, Bool.and_eq_true] at h
  fin_cases i
  exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]

private theorem certK_rep {k : ℕ} {s : Case} (cn : Bool) (h : massesGood k s.row s.atG = true) :
    (certK k s.row s.atG cn).Rep (2 ^ k) ((certificate s).comp (aff s.row cn)) := by
  refine (certificateK_rep (outsideK_rep k s cn) (Packed.rep_const radiusUpper)
    (rowWeightK_rep k s cn) (rowSquareK_rep k s cn)
    (fun i => Packed.rep_ofList_of_rep k (massLC_rep cn (massesGood_spec h i)))).of_eq ?_
  rw [certificate, mass]
  unfold massExcept
  rw [fiveMasses_comp, C_comp]

/-! ### The checks, one declaration per interval row -/

/-- The bits of the base `2 ^ k` of each interval row: a few more than its checks need. -/
private def bits : Row → ℕ
  | .tdLowZero => 2000
  | .tdLowReturn => 5730
  | .tdMiddleDiagonal => 5900
  | .btLowDiagonal => 2170
  | .tdMiddle _ => 4140
  | .tdHigh 0 => 4280
  | .tdHigh 1 => 5440
  | .tdHigh 2 => 5500
  | .btLowZero _ => 6890
  | .btLowReturn 0 => 6210
  | .btLowReturn 1 => 7380
  | .btLowReturn 2 => 7400
  | .btMiddle 0 => 5970
  | .btMiddle 1 => 7300
  | .btMiddle 2 => 7500
  | .btHigh 0 => 4670
  | .btHigh 1 => 5610
  | .btHigh 2 => 5680

/-- The centered certificate, as an explicit list. -/
private def certList (k : ℕ) (r : Row) (g : Bool) : Scaled :=
  (certK k r g true).digits k (max (certK k r g true).n 2)

/-- The certificate itself, as an explicit list. -/
private def certListU (k : ℕ) (r : Row) (g : Bool) : Scaled :=
  (certK k r g false).digits k (certK k r g false).n

private def middleOK (k : ℕ) (r : Row) (g : Bool) : Bool :=
  decide (2 * (certK k r g false).b < 2 ^ k) && decide (0 < (certK k r g false).s) &&
    decide ((119 : ℤ) * (certK k r g false).s < 50000 * (certListU k r g).l.getD 0 0) &&
    lowOK k 49 (cen r (certListU k r g).divX) (9/1250)

/-- The certificate checks of one scalar. -/
private def certOK (k : ℕ) (r : Row) (g : Bool) : Bool :=
  decide (1 ≤ k) && massesGood k r g && decide (2 * (certK k r g true).b < 2 ^ k) &&
    decide (0 < (certK k r g true).s) && decide ((certK k r g true).n ≤ 50 + 1) &&
    (if r = .tdMiddleDiagonal then middleOK k r g else lowOK k 50 (certList k r g) (1/250))

/-- The centered row square, as an explicit list. -/
private def squareList (k : ℕ) (r : Row) (g : Bool) (i : Fin 5) : Scaled :=
  (rowSquareK k r g true i).digits k (max (rowSquareK k r g true i).n 2)

/-- The four whole-interval bounds of a row and its Newton mass. -/
private def rowCheck (k : ℕ) (r : Row) (g : Bool) (i : Fin 5) : Bool :=
  decide (1 ≤ k) && decide (2 * (rowSquareK k r g true i).b < 2 ^ k) &&
    lowOK k 38 (squareList k r g i) (79/100) && upOK k 38 (squareList k r g i) 3 &&
    massGood k r g i && lowOK k 3 (cen r (massList k r g i)) (89/100) &&
    upOK k 3 (cen r (massList k r g i)) (151/100)

/-- All checks of the two scalars of one interval row; the rows `1 ≤ i` are the same for both
faces. -/
private def rowOK (r : Row) : Bool :=
  certOK (bits r) r false && certOK (bits r) r true && rowCheck (bits r) r false 0 &&
    rowCheck (bits r) r true 0 && rowCheck (bits r) r false 1 && rowCheck (bits r) r false 2 &&
    rowCheck (bits r) r false 3 && rowCheck (bits r) r false 4

set_option Elab.async false in
private theorem rowOK_tdLowZero : rowOK .tdLowZero = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdLowReturn : rowOK .tdLowReturn = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdMiddleDiagonal : rowOK .tdMiddleDiagonal = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowDiagonal : rowOK .btLowDiagonal = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdMiddle0 : rowOK (.tdMiddle 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdMiddle1 : rowOK (.tdMiddle 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdMiddle2 : rowOK (.tdMiddle 2) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdHigh0 : rowOK (.tdHigh 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdHigh1 : rowOK (.tdHigh 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_tdHigh2 : rowOK (.tdHigh 2) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowZero0 : rowOK (.btLowZero 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowZero1 : rowOK (.btLowZero 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowZero2 : rowOK (.btLowZero 2) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowReturn0 : rowOK (.btLowReturn 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowReturn1 : rowOK (.btLowReturn 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btLowReturn2 : rowOK (.btLowReturn 2) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btMiddle0 : rowOK (.btMiddle 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btMiddle1 : rowOK (.btMiddle 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btMiddle2 : rowOK (.btMiddle 2) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btHigh0 : rowOK (.btHigh 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btHigh1 : rowOK (.btHigh 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowOK_btHigh2 : rowOK (.btHigh 2) = true := by decide +kernel

private theorem rowOK_all (r : Row) : rowOK r = true := by
  cases r with
  | tdLowZero => exact rowOK_tdLowZero
  | tdLowReturn => exact rowOK_tdLowReturn
  | tdMiddleDiagonal => exact rowOK_tdMiddleDiagonal
  | btLowDiagonal => exact rowOK_btLowDiagonal
  | tdMiddle i =>
      fin_cases i
      exacts [rowOK_tdMiddle0, rowOK_tdMiddle1, rowOK_tdMiddle2]
  | tdHigh i =>
      fin_cases i
      exacts [rowOK_tdHigh0, rowOK_tdHigh1, rowOK_tdHigh2]
  | btLowZero i =>
      fin_cases i
      exacts [rowOK_btLowZero0, rowOK_btLowZero1, rowOK_btLowZero2]
  | btLowReturn i =>
      fin_cases i
      exacts [rowOK_btLowReturn0, rowOK_btLowReturn1, rowOK_btLowReturn2]
  | btMiddle i =>
      fin_cases i
      exacts [rowOK_btMiddle0, rowOK_btMiddle1, rowOK_btMiddle2]
  | btHigh i =>
      fin_cases i
      exacts [rowOK_btHigh0, rowOK_btHigh1, rowOK_btHigh2]

private theorem certOK_all (s : Case) : certOK (bits s.row) s.row s.atG = true := by
  have h := rowOK_all s.row
  simp only [rowOK, Bool.and_eq_true] at h
  rcases s with ⟨r, _ | _⟩
  · exact h.1.1.1.1.1.1.1
  · exact h.1.1.1.1.1.1.2

/-- The scalar whose row `i` is checked: the face `false` for `1 ≤ i`. -/
private def fc (s : Case) (i : Fin 5) : Case := ⟨s.row, if i.val = 0 then s.atG else false⟩

private theorem fc_eq (s : Case) (i : Fin 5) :
    rowSquare (fc s i) i = rowSquare s i ∧ massAt (fc s i) i = massAt s i := by
  unfold fc
  split_ifs with h
  · exact ⟨rfl, rfl⟩
  · exact ⟨rowSquare_face s h, massAt_face s h⟩

private theorem rowCheck_all (s : Case) (i : Fin 5) :
    rowCheck (bits s.row) s.row (fc s i).atG i = true := by
  have h := rowOK_all s.row
  simp only [rowOK, Bool.and_eq_true] at h
  fin_cases i
  · rcases s with ⟨r, _ | _⟩
    · exact h.1.1.1.1.1.2
    · exact h.1.1.1.1.2
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

private theorem certOK_parts (s : Case) :
    1 ≤ bits s.row ∧ massesGood (bits s.row) s.row s.atG = true ∧
      2 * (certK (bits s.row) s.row s.atG true).b < 2 ^ bits s.row ∧
      0 < (certK (bits s.row) s.row s.atG true).s ∧ (certK (bits s.row) s.row s.atG true).n ≤ 50 + 1 ∧
      (if s.row = .tdMiddleDiagonal then middleOK (bits s.row) s.row s.atG
        else lowOK (bits s.row) 50 (certList (bits s.row) s.row s.atG) (1/250)) = true := by
  have h := certOK_all s
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem certList_rep (s : Case) :
    (certList (bits s.row) s.row s.atG).Rep (centered 0 (length s.row) (certificate s)) := by
  obtain ⟨hk, hm, hb, -, -, -⟩ := certOK_parts s
  exact (certK_rep true hm).digits hk hb (le_max_left _ 2)

theorem certificate_identity (s : Case) :
    centered 0 (length s.row) (certificate s)=
      expansion 50 (centered 0 (length s.row) (certificate s)) := by
  obtain ⟨-, -, -, hs, hn, -⟩ := certOK_parts s
  refine (certList_rep s).eq_expansion (by simp only [certList, Packed.digits]; omega) ?_
  simp only [certList, Packed.digits, length_digs]
  omega

theorem ordinary_reserve (s : Case) (hm : s.row≠.tdMiddleDiagonal) :
    (1/250:ℚ)<lowerOn 50 0 (length s.row) (certificate s) := by
  obtain ⟨-, -, -, -, -, h⟩ := certOK_parts s
  rw [ite_eq_right hm] at h
  exact (lowOK_spec (certList_rep s) h).1

theorem middle_identity (face : Bool) :
    certificate ⟨.tdMiddleDiagonal,face⟩=
      C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0)+X*middleQuotient face := by
  have h := X_mul_divX_add (certificate ⟨.tdMiddleDiagonal,face⟩-
    C ((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0))
  simp only [coeff_sub, coeff_C_zero, sub_self, map_zero, add_zero] at h
  rw [middleQuotient, h]
  ring

private theorem middleQuotient_eq (face : Bool) :
    middleQuotient face = (certificate ⟨.tdMiddleDiagonal,face⟩).divX := by
  ext n
  simp [middleQuotient, coeff_divX, coeff_sub]

private theorem middle_parts (face : Bool) :
    (certListU (bits .tdMiddleDiagonal) .tdMiddleDiagonal face).Rep
        (certificate ⟨.tdMiddleDiagonal, face⟩) ∧
      0 < (certK (bits .tdMiddleDiagonal) .tdMiddleDiagonal face false).s ∧
      (119 : ℤ) * (certK (bits .tdMiddleDiagonal) .tdMiddleDiagonal face false).s <
        50000 * (certListU (bits .tdMiddleDiagonal) .tdMiddleDiagonal face).l.getD 0 0 ∧
      lowOK (bits .tdMiddleDiagonal) 49
        (cen .tdMiddleDiagonal (certListU (bits .tdMiddleDiagonal) .tdMiddleDiagonal face).divX)
        (9/1250) = true := by
  obtain ⟨hk, hm, -, -, -, h⟩ := certOK_parts ⟨.tdMiddleDiagonal, face⟩
  rw [ite_eq_left rfl] at h
  simp only [middleOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hs⟩, hc⟩, hl⟩ := h
  have hr := certK_rep (s := ⟨.tdMiddleDiagonal, face⟩) false hm
  rw [aff, ite_eq_right Bool.false_ne_true, comp_X] at hr
  exact ⟨hr.digits hk hb le_rfl, hs, hc, hl⟩

private theorem middle_check (face : Bool) :
    (9/1250:ℚ)<lowerOn 49 0 (3/25) (middleQuotient face) ∧
      centered 0 (3/25) (middleQuotient face)=expansion 49 (centered 0 (3/25) (middleQuotient face)) := by
  obtain ⟨hr, -, -, hl⟩ := middle_parts face
  have hq := cen_rep .tdMiddleDiagonal (hr.divX)
  rw [← middleQuotient_eq] at hq
  exact lowOK_spec hq hl

theorem middle_quotient_identity (face : Bool) :
    centered 0 (3/25) (middleQuotient face)=
      expansion 49 (centered 0 (3/25) (middleQuotient face)) :=
  (middle_check face).2

theorem middle_reserves (face : Bool) :
    (119/50000:ℚ)<(certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0 ∧
      (9/1250:ℚ)<lowerOn 49 0 (3/25) (middleQuotient face) := by
  refine ⟨?_, (middle_check face).1⟩
  obtain ⟨hr, hs, hc, -⟩ := middle_parts face
  have hs' : (certListU (bits .tdMiddleDiagonal) .tdMiddleDiagonal face).s ≠ 0 := by
    simp only [certListU, Packed.digits]; omega
  rw [hr.coeff hs' 0, lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hs')]
  have hc' := (Int.cast_lt (R := ℚ)).2 hc
  simp only [certListU, Packed.digits] at hc' ⊢
  push_cast at hc' ⊢
  linarith

theorem certificate_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    (119/50000:ℝ)<aeval z (certificate s) := by
  by_cases hm : s.row=.tdMiddleDiagonal
  · rcases s with ⟨r,face⟩
    dsimp at hm
    subst r
    have hz' : z∈Set.Icc ((0:ℚ):ℝ) ((3/25:ℚ):ℝ) := by
      simpa [ExceptionalNegativeTScalarModel.length] using hz
    have hquot := positive_on_interval (by norm_num : (0:ℚ)<3/25)
      (middle_quotient_identity face) (middle_reserves face).2 hz'
    have hzero : (119/50000:ℝ)<((certificate ⟨.tdMiddleDiagonal,face⟩).coeff 0:ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr (middle_reserves face).1; push_cast at this; exact this
    have hz0 : 0 ≤ z := by simpa using hz'.1
    have hprod := mul_nonneg hz0 (show 0≤aeval z (middleQuotient face) by push_cast at hquot; linarith)
    rw [middle_identity]
    simp only [map_add,map_mul,aeval_C,aeval_X]
    simp only [eq_ratCast] at *
    linarith
  · have hb := (interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row)
      (certificate_identity s) (by simpa using hz)).1
    have hr : (1/250:ℝ)<(lowerOn 50 0 (length s.row) (certificate s):ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr (ordinary_reserve s hm); push_cast at this; exact this
    linarith

private theorem rowCheck_parts (s : Case) (i : Fin 5) :
    lowOK (bits s.row) 38 (squareList (bits s.row) s.row (fc s i).atG i) (79/100) = true ∧
      upOK (bits s.row) 38 (squareList (bits s.row) s.row (fc s i).atG i) 3 = true ∧
      (cen s.row (massList (bits s.row) s.row (fc s i).atG i)).Rep
        (centered 0 (length s.row) (massAt s i)) ∧
      lowOK (bits s.row) 3 (cen s.row (massList (bits s.row) s.row (fc s i).atG i)) (89/100) = true ∧
      upOK (bits s.row) 3 (cen s.row (massList (bits s.row) s.row (fc s i).atG i)) (151/100) = true ∧
      (squareList (bits s.row) s.row (fc s i).atG i).Rep
        (centered 0 (length s.row) (rowSquare s i)) := by
  have h := rowCheck_all s i
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hb⟩, hl⟩, hu⟩, hm⟩, hml⟩, hmu⟩ := h
  obtain ⟨e1, e2⟩ := fc_eq s i
  have hmr := massList_rep (s := fc s i) hm
  rw [e2] at hmr
  have hsr := (rowSquareK_rep (bits s.row) (fc s i) true i).digits hk hb (le_max_left _ 2)
  rw [e1] at hsr
  exact ⟨hl, hu, cen_rep s.row hmr, hml, hmu, hsr⟩

theorem mass_identity (s : Case) (i : Fin 5) :
    centered 0 (length s.row) (massAt s i)=
      expansion 3 (centered 0 (length s.row) (massAt s i)) :=
  (lowOK_spec (rowCheck_parts s i).2.2.1 (rowCheck_parts s i).2.2.2.1).2

theorem mass_reserves (s : Case) (i : Fin 5) :
    (89/100:ℚ)<lowerOn 3 0 (length s.row) (massAt s i) ∧
      upperOn 3 0 (length s.row) (massAt s i)<151/100 :=
  ⟨(lowOK_spec (rowCheck_parts s i).2.2.1 (rowCheck_parts s i).2.2.2.1).1,
    (upOK_spec (rowCheck_parts s i).2.2.1 (rowCheck_parts s i).2.2.2.2.1).1⟩

theorem square_identity (s : Case) (i : Fin 5) :
    centered 0 (length s.row) (rowSquare s i)=
      expansion 38 (centered 0 (length s.row) (rowSquare s i)) :=
  (lowOK_spec (rowCheck_parts s i).2.2.2.2.2 (rowCheck_parts s i).1).2

theorem square_reserves (s : Case) (i : Fin 5) :
    (79/100:ℚ)<lowerOn 38 0 (length s.row) (rowSquare s i) ∧
      upperOn 38 0 (length s.row) (rowSquare s i)<3 :=
  ⟨(lowOK_spec (rowCheck_parts s i).2.2.2.2.2 (rowCheck_parts s i).1).1,
    (upOK_spec (rowCheck_parts s i).2.2.2.2.2 (rowCheck_parts s i).2.1).1⟩

theorem mass_bounds (s : Case) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    89/100<aeval z (massAt s i) ∧ aeval z (massAt s i)<151/100 := by
  have hb := interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row) (mass_identity s i)
    (by simpa using hz)
  have hl : (89/100:ℝ)<(lowerOn 3 0 (length s.row) (massAt s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 3 0 (length s.row) (massAt s i):ℝ)<(151/100:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hb.1,hb.2.trans_lt hu⟩

theorem square_bounds (s : Case) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    79/100<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<3 := by
  have hb := interval_bounds (ExceptionalNegativeTScalarModel.length_pos s.row) (square_identity s i)
    (by simpa using hz)
  have hl : (79/100:ℝ)<(lowerOn 38 0 (length s.row) (rowSquare s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 38 0 (length s.row) (rowSquare s i):ℝ)<(3:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hb.1,hb.2.trans_lt hu⟩

end SquaresInCircles.Eight.ExceptionalNegativeTPolynomials
end
end
end

section
/-!
## Real inputs for the exceptional negative-T certificates

Both the total primary angle and its remaining
ordinary angle have independent sine/cosine inputs. The coefficient
families and the removed secant angle remain exact throughout the
Taylor substitution.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTScalarData
open Polynomial HighOrderTaylor ExceptionalNegativeTScalarModel

def taylorOutside (s : Case) (t : ℝ) : ℝ :=
  outside s t (S15 t) (C16 t) (S15 (angle s.row t)) (C16 (angle s.row t))
def taylorSum (s : Case) (t : ℝ) : ℝ :=
  rowSum s t (S15 t) (C16 t) (S15 (angle s.row t))

theorem coordinates_bounds (s : Case) {t sn cs : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row))
    (hs : sn∈Set.Icc 0 1) (hc : cs∈Set.Icc 0 (1001/1000)) (i : Fin 4) :
    0≤first s t sn cs i ∧ first s t sn cs i≤2 ∧
      0≤ second s t sn cs i ∧ second s t sn cs i≤2 := by
  rcases ExceptionalEScalarData.coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc0,hc1,he,he1⟩
  have hp0 := add_nonneg hc.1 (mul_nonneg he hs.1)
  have hp1 := mul_le_mul_of_nonneg_left hs.2 he
  have hkp0 := mul_nonneg hk.le hp0
  have hkp1 := mul_le_mul_of_nonneg_right hk1 hp0
  fin_cases i <;> cases h : s.atG <;> simp only [first,second,h] <;> refine ⟨?_,?_,?_,?_⟩ <;>
    simp <;> nlinarith [hc.2]

theorem nu_bounds {r : Row} {t : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band r)) (i : Fin 3) :
    nu r t i∈Set.Icc 0 2 := by
  rcases ExceptionalEScalarData.coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  fin_cases i <;> simp [nu] <;> constructor <;> linarith

theorem weight_bounds (s : Case) {t sn : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row)) (hs : sn∈Set.Icc 0 1) (i : Fin 5) :
    weight s t sn i∈Set.Icc 0 2 := by
  have hk := (ExceptionalECoefficients.ranges ht).1
  have hp0 := mul_nonneg (show 0≤ExceptionalECoefficients.k (band s.row) t by linarith [hk.1]) hs.1
  have hp1 := mul_le_mul hk.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤1)
  dsimp [weight]
  split_ifs <;> constructor <;> linarith [hs.1,hs.2]

theorem square_nonneg (s : Case) {t sn cs sd : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row))
    (hs : sn∈Set.Icc 0 1) (hc : cs∈Set.Icc 0 (1001/1000))
    (hd : sd∈Set.Icc 0 1) (i : Fin 5) : 0≤ square s t sn cs sd i := by
  dsimp [square]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds s ht hs hc j
    have hp := mul_nonneg (mul_nonneg hb.1 hb.2.2.1) (sub_nonneg.mpr hd.2)
    dsimp [squared]
    split_ifs
    · nlinarith [sq_nonneg (first s t sn cs j-second s t sn cs j)]
    · rw [sub_zero]; positivity
  · positivity

theorem polynomial_parameters (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.k s)=ExceptionalECoefficients.k (band s.row) t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.ell s)=ExceptionalECoefficients.ell (band s.row) t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.c s)=ExceptionalECoefficients.c (band s.row) t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.eta s)=ExceptionalECoefficients.eta (band s.row) t := by
  rcases s with ⟨r,face⟩
  cases r <;> simp [ExceptionalNegativeTPolynomials.k,ExceptionalNegativeTPolynomials.ell,
    ExceptionalNegativeTPolynomials.c,ExceptionalNegativeTPolynomials.eta,
    ExceptionalNegativeTPolynomials.parameter,origin,band,
    ExceptionalECoefficients.k,ExceptionalECoefficients.ell,ExceptionalECoefficients.c,
    ExceptionalECoefficients.eta] <;> (repeat' constructor) <;> ring

theorem polynomial_removed (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.removed s)=removed s.row t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.angle s)=angle s.row t := by
  unfold ExceptionalNegativeTPolynomials.angle ExceptionalNegativeTPolynomials.removed angle removed
  split_ifs <;> simp [ExceptionalNegativeTPolynomials.parameter]

theorem polynomial_trig (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.sine s)=S15 t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.cosine s)=C16 t ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.shortSine s)=S15 (angle s.row t) ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.shortCosine s)=C16 (angle s.row t) := by
  have hp : aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.parameter s)=t := by
    simp [ExceptionalNegativeTPolynomials.parameter]
  simp [ExceptionalNegativeTPolynomials.sine,ExceptionalNegativeTPolynomials.cosine,
    ExceptionalNegativeTPolynomials.shortSine,ExceptionalNegativeTPolynomials.shortCosine,
    Polynomial.aeval_comp,hp,(polynomial_removed s t).2,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval]

theorem polynomial_coordinates (s : Case) (t : ℝ) (i : Fin 4) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.first s i)=first s t (S15 t) (C16 t) i ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.second s i)=second s t (S15 t) (C16 t) i := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco,hd,hcd⟩
  fin_cases i <;> cases h : s.atG <;> simp [ExceptionalNegativeTPolynomials.first,
    ExceptionalNegativeTPolynomials.second,ExceptionalNegativeTPolynomials.p,first,second,h,
    hk,hl,hc,he,hs,hco]

theorem polynomial_nu (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.nu s)=nu s.row t (index s.row) := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  generalize hj : index s.row=j
  fin_cases j <;> simp [ExceptionalNegativeTPolynomials.nu,nu,hj,hl,hc]

theorem polynomial_rows (s : Case) (t : ℝ) (i : Fin 5) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.rowSquare s i)=
      square s t (S15 t) (C16 t) (S15 (angle s.row t)) i ∧
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.rowWeight s i)=weight s t (S15 t) i := by
  have hv := polynomial_coordinates s t
  rcases polynomial_trig s t with ⟨hs,hco,hd,hcd⟩
  have hk := (polynomial_parameters s t).1
  have he := (polynomial_parameters s t).2.2.2
  have e2 : aeval (t-(origin s.row:ℝ)) (2:ℚ[X]) = 2 := map_ofNat _ 2
  constructor
  · unfold ExceptionalNegativeTPolynomials.rowSquare square
    split_ifs with hi
    · unfold ExceptionalNegativeTPolynomials.squaredNorm squared
      obtain ⟨h1, h2⟩ := hv ⟨i.val, hi⟩
      split_ifs <;> simp [h1, h2, hd, e2]
    · simp [he]
  · unfold ExceptionalNegativeTPolynomials.rowWeight weight
    split_ifs <;> simp [hs, hk]

theorem polynomial_outside (s : Case) (t : ℝ) :
    aeval (t-(origin s.row:ℝ)) (ExceptionalNegativeTPolynomials.outside s)=taylorOutside s t := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco,hd,hcd⟩
  have hn := polynomial_nu s t
  have hr := (polynomial_removed s t).1
  set z := t-(origin s.row:ℝ)
  have e2 : aeval z (2:ℚ[X]) = 2 := map_ofNat _ 2
  have e3 : aeval z (3:ℚ[X]) = 3 := map_ofNat _ 3
  have hA : aeval z (if s.atG then 3+2*ExceptionalNegativeTPolynomials.ell s+
        3*ExceptionalNegativeTPolynomials.c s+ExceptionalNegativeTPolynomials.k s*
        (1+2*ExceptionalNegativeTPolynomials.cosine s+(1+2*ExceptionalNegativeTPolynomials.eta s)*
          ExceptionalNegativeTPolynomials.sine s)
      else 3*ExceptionalNegativeTPolynomials.k s+2*ExceptionalNegativeTPolynomials.ell s+
        3*ExceptionalNegativeTPolynomials.c s+1+2*ExceptionalNegativeTPolynomials.cosine s+
        (1+2*ExceptionalNegativeTPolynomials.eta s)*ExceptionalNegativeTPolynomials.sine s)=
      (if s.atG then 3+2*ExceptionalECoefficients.ell (band s.row) t+
        3*ExceptionalECoefficients.c (band s.row) t+ExceptionalECoefficients.k (band s.row) t*
        (1+2*C16 t+(1+2*ExceptionalECoefficients.eta (band s.row) t)*S15 t)
      else 3*ExceptionalECoefficients.k (band s.row) t+2*ExceptionalECoefficients.ell (band s.row) t+
        3*ExceptionalECoefficients.c (band s.row) t+1+2*C16 t+
        (1+2*ExceptionalECoefficients.eta (band s.row) t)*S15 t) := by
    split_ifs <;> simp only [map_add, map_mul, map_one, e2, e3, hk, hl, hc, he, hs, hco]
  have hcorr : aeval z (ExceptionalNegativeTPolynomials.correction s)=correction s.row t := by
    unfold ExceptionalNegativeTPolynomials.correction correction
    split_ifs
    · simp only [map_mul, map_pow, map_sub, map_one, aeval_C, hc, eq_ratCast]; push_cast; ring
    · simp
  have hslope : aeval z (ExceptionalNegativeTPolynomials.slope s)=
      ExceptionalNegativeTScalarModel.slope s.row t := by
    unfold ExceptionalNegativeTPolynomials.slope ExceptionalNegativeTScalarModel.slope g
    split_ifs
    · simp only [map_add, map_mul, map_pow, map_sub, aeval_C, hr, eq_ratCast]; push_cast; ring
    · simp only [aeval_C, eq_ratCast]; push_cast; ring
  have hlast : aeval z (if diagonal s.row then 0 else ExceptionalNegativeTPolynomials.nu s*
      (ExceptionalNegativeTPolynomials.shortCosine s-1))=
      (if diagonal s.row then 0 else nu s.row t (index s.row)*(C16 (angle s.row t)-1)) := by
    split_ifs
    · simp
    · simp only [map_mul, map_sub, map_one, hn, hcd]
  unfold ExceptionalNegativeTPolynomials.outside taylorOutside outside
  rw [map_add, map_add, map_add, hA, hcorr, map_mul, map_mul, hc, hslope, hr, hlast]

end SquaresInCircles.Eight.ExceptionalNegativeTScalarData
end
end
end

section
/-!
## Positive-mass transfer at the exceptional negative-T endpoints

The five-mass factorization (`certificate_factorization`) keeps the numerator reserve `0.00238`
and the denominator bound `16` (`denominator_bounds`, `rational_reserve`). The weighted radicals
are compared with the rational sum through a positive square at every point of the interval
(`radical_le_rational`, `radical_reserve`, `taylor_reserve`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTRadicals
open Polynomial ExceptionalNegativeTPolynomials ExceptionalNegativeTScalarData HighOrderTaylor
open ExceptionalNegativeTScalarModel (Case origin length domain local_parameter family_domain)

def radicalSum (s : Case) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*Real.sqrt (aeval z (rowSquare s i))
def rationalSum (s : Case) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*
    (aeval z (rowSquare s i)+(aeval z (massAt s i))^2)/(2*aeval z (massAt s i))

private theorem five_mass_identity (a v w : Fin 5 → ℝ) (ha : ∀i,a i≠0) :
    (∑i : Fin 5,w i*(v i+(a i)^2)*∏j : Fin 5,if j=i then 1 else a j)=
      2*(∏i : Fin 5,a i)*(∑i : Fin 5,w i*(v i+(a i)^2)/(2*a i)) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

theorem certificate_factorization (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    aeval z (certificate s)=2*(∏i : Fin 5,aeval z (massAt s i))*
      (aeval z (outside s)-(radiusUpper:ℝ)*rationalSum s z) := by
  have ha : ∀i : Fin 5,aeval z (massAt s i)≠0 := by
    intro i
    linarith [(mass_bounds s i hz).1]
  have hid := five_mass_identity (fun i => aeval z (massAt s i))
    (fun i => aeval z (rowSquare s i)) (fun i => aeval z (rowWeight s i)) ha
  simp only [certificate,mass,massExcept,map_sub,map_mul,map_add,map_ofNat,map_sum,
    map_pow,map_prod,aeval_C,map_one,apply_ite,eq_ratCast] at *
  rw [hid]
  unfold rationalSum
  ring

theorem denominator_bounds (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    0<2*(∏i : Fin 5,aeval z (massAt s i)) ∧
      2*(∏i : Fin 5,aeval z (massAt s i))<16 := by
  have h := fun i => mass_bounds s i hz
  rw [Fin.prod_univ_five]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have q0 : (0:ℝ) < aeval z (massAt s 0) := by linarith [h0.1]
  have q1 : (0:ℝ) < aeval z (massAt s 1) := by linarith [h1.1]
  have q2 : (0:ℝ) < aeval z (massAt s 2) := by linarith [h2.1]
  have q3 : (0:ℝ) < aeval z (massAt s 3) := by linarith [h3.1]
  have q4 : (0:ℝ) < aeval z (massAt s 4) := by linarith [h4.1]
  have p01 := mul_lt_mul'' h0.2 h1.2 q0.le q1.le
  have p012 := mul_lt_mul'' p01 h2.2 (mul_pos q0 q1).le q2.le
  have p0123 := mul_lt_mul'' p012 h3.2 (mul_pos (mul_pos q0 q1) q2).le q3.le
  have p01234 := mul_lt_mul'' p0123 h4.2 (mul_pos (mul_pos (mul_pos q0 q1) q2) q3).le q4.le
  constructor
  · exact mul_pos two_pos (mul_pos (mul_pos (mul_pos (mul_pos q0 q1) q2) q3) q4)
  · norm_num at p01234
    linarith

theorem rational_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    (119/800000:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*rationalSum s z := by
  have hp := certificate_reserve s hz
  rw [certificate_factorization s hz] at hp
  have hb := denominator_bounds s hz
  by_contra! h
  have hm := mul_le_mul_of_nonneg_left h hb.1.le
  nlinarith

theorem radical_le_rational (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) : radicalSum s z≤rationalSum s z := by
  apply Finset.sum_le_sum
  intro i _
  have hm : 0<aeval z (massAt s i) := by linarith [(mass_bounds s i hz).1]
  have hv : 0≤aeval z (rowSquare s i) := by linarith [(square_bounds s i hz).1]
  have hh := mul_le_mul_of_nonneg_left (ScalarRadicalTransfer.sqrt_le_mass_majorant hv hm) (hw i)
  simpa only [mul_div_assoc] using hh

theorem radical_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) :
    (119/800000:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*radicalSum s z := by
  have hp := rational_reserve s hz
  have hm := mul_le_mul_of_nonneg_left (radical_le_rational s hz hw)
    (show (0:ℝ)≤(radiusUpper:ℝ) by norm_num [radiusUpper])
  linarith

theorem taylor_weights (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    ∀i : Fin 5,0≤aeval (t-(origin s.row:ℝ)) (rowWeight s i) := by
  have hd := ExceptionalECoefficients.angle (family_domain ht)
  have hs : S15 t∈Set.Icc 0 1 := ⟨S15_nonneg hd,(S15_le_sin hd.1).trans (Real.sin_le_one t)⟩
  intro i
  rw [(polynomial_rows s t i).2]
  exact (weight_bounds s (family_domain ht) hs i).1

theorem polynomial_radicalSum (s : Case) (t : ℝ) :
    radicalSum s (t-(origin s.row:ℝ))=taylorSum s t := by
  unfold radicalSum taylorSum ExceptionalNegativeTScalarModel.rowSum
  apply Finset.sum_congr rfl
  intro i _
  rw [(polynomial_rows s t i).1,(polynomial_rows s t i).2]

theorem taylor_reserve (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    (119/800000:ℝ)<taylorOutside s t-(radiusUpper:ℝ)*taylorSum s t := by
  have hp := radical_reserve s (local_parameter ht) (taylor_weights s ht)
  simpa only [polynomial_outside,polynomial_radicalSum] using hp

end SquaresInCircles.Eight.ExceptionalNegativeTRadicals
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalNegativeTTaylor
open ExceptionalNegativeTScalarModel ExceptionalNegativeTScalarData
open HighOrderTaylor BoundedRadicalPerturbation
open ExceptionalNegativeTPolynomials (radiusUpper)

theorem coordinate_errors (s : Case) {t : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row)) (i : Fin 4) :
    |first s t (Real.sin t) (Real.cos t) i-first s t (S15 t) (C16 t) i|≤3*remainder ∧
    |second s t (Real.sin t) (Real.cos t) i-second s t (S15 t) (C16 t) i|≤3*remainder := by
  rcases ExceptionalEScalarData.coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have hp := SoleScalarTaylor.tilted_error (ExceptionalECoefficients.angle ht)
    (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10)) ⟨he,by linarith⟩
  have hn := SoleScalarTaylor.tilted_error (ExceptionalECoefficients.angle ht)
    (show ExceptionalECoefficients.k (band s.row) t∈Set.Icc 0 (11/10) from
      ⟨hk.le,by linarith⟩) ⟨he,by linarith⟩
  simp only [one_mul] at hp
  have h0 : 0≤remainder := by norm_num [remainder]
  fin_cases i <;> cases h : s.atG <;> refine ⟨?_,?_⟩ <;> simp [first,second,h] <;> linarith

theorem weight_error (s : Case) {t : ℝ}
    (ht : t∈ExceptionalECoefficients.domain (band s.row)) (i : Fin 5) :
    |weight s t (Real.sin t) i-weight s t (S15 t) i|≤3*remainder := by
  have hs := (SoleScalarTaylor.input_errors (ExceptionalECoefficients.angle ht)).1
  have hk := (ExceptionalECoefficients.ranges ht).1
  have hkabs : |ExceptionalECoefficients.k (band s.row) t|≤1 := by
    rw [abs_of_nonneg (by linarith [hk.1])]
    exact hk.2
  have hm := constant_product_difference hkabs hs
  have h0 : 0≤remainder := by norm_num [remainder]
  dsimp [weight]
  split_ifs
  · simp only [sub_self,abs_zero]; linarith
  · linarith
  · linarith

theorem square_error (s : Case) {t : ℝ} (ht : t∈domain s.row) (i : Fin 5) :
    |square s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) i-
      square s t (S15 t) (C16 t) (S15 (angle s.row t)) i|≤100*remainder := by
  have hf := family_domain ht
  rcases SoleScalarTaylor.input_bounds (angles ht).1 with ⟨hs,hc,hs',hc'⟩
  rcases SoleScalarTaylor.input_bounds (angles ht).2.2.1 with ⟨hd,hcd,hd',hcd'⟩
  have he := SoleScalarTaylor.input_errors (angles ht).2.2.1
  have he0 : 0≤remainder := by norm_num [remainder]
  dsimp [square]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds s hf hs hc j
    have hb' := coordinates_bounds s hf hs' hc' j
    have herror := coordinate_errors s hf j
    have ha : |first s t (Real.sin t) (Real.cos t) j|≤2 := by rw [abs_of_nonneg hb.1]; exact hb.2.1
    have ha' : |first s t (S15 t) (C16 t) j|≤2 := by rw [abs_of_nonneg hb'.1]; exact hb'.2.1
    have hbb : |second s t (Real.sin t) (Real.cos t) j|≤2 := by
      rw [abs_of_nonneg hb.2.2.1]; exact hb.2.2.2
    have hbb' : |second s t (S15 t) (C16 t) j|≤2 := by rw [abs_of_nonneg hb'.2.2.1]; exact hb'.2.2.2
    unfold squared
    split_ifs
    · exact negative_pair_difference he0 ha ha' hbb hbb'
        (by rw [abs_of_nonneg hd'.1]; exact hd'.2) herror.1 herror.2 he.1
    · simpa only [sub_zero] using positive_pair_difference he0 ha ha' hbb hbb' herror.1 herror.2
  · simp only [sub_self, abs_zero]; linarith

theorem row_error (s : Case) {t : ℝ} (ht : t∈domain s.row) (i : Fin 5) :
    |weight s t (Real.sin t) i*Real.sqrt (square s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) i)-
      weight s t (S15 t) i*Real.sqrt (square s t (S15 t) (C16 t) (S15 (angle s.row t)) i)|≤500*remainder := by
  have hf := family_domain ht
  rcases SoleScalarTaylor.input_bounds (angles ht).1 with ⟨hs,hc,hs',hc'⟩
  have hd := (SoleScalarTaylor.input_bounds (angles ht).2.2.1).1
  have hp := ExceptionalNegativeTPolynomials.square_bounds s i (local_parameter ht)
  rw [(polynomial_rows s t i).1] at hp
  exact weighted_root_difference (square_nonneg s hf hs hc hd i)
    (by linarith [hp.1]) (by linarith [hp.2])
    (by norm_num [remainder]) (by norm_num [remainder])
    (weight_bounds s hf hs i) (weight_bounds s hf hs' i) (square_error s ht i) (weight_error s hf i)

theorem rowSum_error (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    rowSum s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t))≤taylorSum s t+2500*remainder := by
  have hh (i : Fin 5) :
      weight s t (Real.sin t) i*Real.sqrt (square s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) i)≤
        weight s t (S15 t) i*Real.sqrt (square s t (S15 t) (C16 t) (S15 (angle s.row t)) i)+500*remainder := by
    have hi := (le_abs_self _).trans (row_error s ht i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold taylorSum rowSum
  push_cast at hsum
  linarith

theorem outside_error (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    taylorOutside s t-100*remainder≤
      outside s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) (Real.cos (angle s.row t)) := by
  have hf := family_domain ht
  have hn := nu_bounds hf (index s.row)
  rcases ExceptionalEScalarData.coefficient_bounds hf with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have herr := SoleScalarTaylor.input_errors (angles ht).1
  have hshort := SoleScalarTaylor.input_errors (angles ht).2.2.1
  have hlinear := linear_difference (by norm_num : |(2:ℝ)|≤2)
    (show |1+2*ExceptionalECoefficients.eta (band s.row) t|≤2 by
      rw [abs_of_nonneg (by linarith)]; linarith) herr.2.1 herr.1
  have hkabs : |ExceptionalECoefficients.k (band s.row) t|≤1 := by
    rw [abs_of_nonneg hk.le]
    exact hk1
  have hscaled := constant_product_difference hkabs hlinear
  have hnabs : |nu s.row t (index s.row)|≤2 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hcharge := constant_product_difference hnabs hshort.2.1
  have hmain0 := (abs_le.mp hlinear).1
  have hmain1 := (abs_le.mp hscaled).1
  have hcharge0 := (abs_le.mp hcharge).1
  dsimp [taylorOutside,outside]
  have h0 : 0≤remainder := by norm_num [remainder]
  split_ifs <;> linarith

theorem conservative_reserve (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    (7/50000:ℝ)<value s (radiusUpper:ℝ) t := by
  have hp := ExceptionalNegativeTRadicals.taylor_reserve s ht
  have hd := outside_error s ht
  have hs := rowSum_error s ht
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hR2 : (radiusUpper:ℝ)≤(2:ℝ) := by norm_num [radiusUpper]
  have hm := mul_le_mul_of_nonneg_left hs hR
  have he := mul_le_mul_of_nonneg_right hR2 (show 0≤2500*remainder by norm_num [remainder])
  have hmargin : (5100:ℝ)*remainder<119/800000-7/50000 := by norm_num [remainder]
  unfold value
  nlinarith

theorem rowSum_nonneg (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    0≤rowSum s t (Real.sin t) (Real.cos t) (Real.sin (angle s.row t)) := by
  have hs := (SoleScalarTaylor.input_bounds (angles ht).1).1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_bounds s (family_domain ht) hs i).1 (Real.sqrt_nonneg _)

theorem actual_radius_reserve (s : Case) {R t : ℝ}
    (ht : t∈domain s.row) (_hR : 0≤R) (hQU : R^2≤qTrial) :
    (7/50000:ℝ)<value s R t := by
  have hroot := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hroot0 := Real.sqrt_nonneg qTrial
  have hupper := SoleScalarPolynomials.radius_upper
  have hh : R≤Real.sqrt qTrial := by nlinarith
  have hRupper : R≤(radiusUpper:ℝ) :=
    hh.trans (by simpa [radiusUpper,SoleScalarPolynomials.radiusUpper] using hupper.le)
  have hm := mul_le_mul_of_nonneg_right hRupper (rowSum_nonneg s ht)
  have hp := conservative_reserve s ht
  dsimp [value] at *
  linarith

theorem endpoint_positive (s : Case) {R t : ℝ}
    (ht : t∈domain s.row) (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<baseline s R t+correction s.row t+ExceptionalECoefficients.c (band s.row) t*
      slope s.row t*removed s.row t+charge s R t (angle s.row t) (index s.row) := by
  have hh := actual_radius_reserve s ht hR hQU
  rw [value_identity] at hh
  linarith

end SquaresInCircles.Eight.ExceptionalNegativeTTaylor
end
end
end
