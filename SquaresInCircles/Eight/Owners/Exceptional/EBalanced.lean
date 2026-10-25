module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.Interval
public import SquaresInCircles.Eight.Arithmetic.PackedPolynomials
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTSupport
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTScalarModel
public import SquaresInCircles.Eight.Owners.Positive.GAOuterSoleReduction
public import SquaresInCircles.Eight.Owners.Positive.TDSpanScalars
public import SquaresInCircles.Eight.Owners.Sole.LowGapPolynomials
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope

/-!
# Eight squares: the middle and high ordinary envelope at the exceptional contact

The H block keeps its two angles. The lower bound `0.95` for the larger coefficients pays every
positive ordinary allocation, since `0.545 * 1.131 < (2/3) * 0.95` (`conditions`). So the same four
pure charges bound both endpoints of the split (`charge_le_pure`), for either owner of AB and
without aligning EH, and the endpoint scalars are positive on the middle and high bands
(`scalar_endpoints`).
-/

section
/-!
## Ten whole-interval exceptional endpoint polynomials

The four domains are the two low intervals and the
complete middle and high intervals in the hand argument. Each of the
five radical masses comes from three rational Newton steps and a cubic
truncation. The displayed arithmetic proofs have not been run. These
polynomial facts are transferred to the actual trigonometric stress in
subsequent files; they are not assumed geometric conclusions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalEPolynomials
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients PackedPolynomials
open WholeIntervalPolynomial.Certificate (Scaled toPoly chebList twoX lowerZ upperZ)

inductive ScalarCase where
  | lowZero | lowReturn | middle (i : Fin 4) | high (i : Fin 4)
  deriving DecidableEq

instance : Fintype ScalarCase where
  elems := {.lowZero, .lowReturn} ∪
    Finset.univ.image ScalarCase.middle ∪
    Finset.univ.image ScalarCase.high
  complete x := by cases x <;> simp

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
  constructor <;> linarith [ht.1,ht.2]

/-! ## The scalars, packed

`fK k s cn` packs `(f s).comp (aff s cn)` at the base `2 ^ k`: the polynomial itself when
`cn = false`, its centered polynomial on `[0, length s]` when `cn = true`. -/

private def aff (s : ScalarCase) (cn : Bool) : ℚ[X] := if cn then affine 0 (length s) else X

/-- `C a + X`, composed. -/
private def affK (k : ℕ) (s : ScalarCase) (cn : Bool) (a : ℚ) : Packed :=
  if cn then
    (Packed.const (a + length s / 2)).add ((Packed.const (length s / 2)).mul (Packed.var (2 ^ k)))
  else (Packed.const a).add (Packed.var (2 ^ k))

private theorem affK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (a : ℚ) :
    (affK k s cn a).Rep (2 ^ k) ((C a + X).comp (aff s cn)) := by
  unfold affK aff
  split_ifs
  · have e : (C a + X).comp (affine 0 (length s)) = C (a + length s / 2) + C (length s / 2) * X := by
      simp only [add_comp, C_comp, X_comp, affine, zero_add, sub_zero, C_add]; ring
    rw [e]
    exact (Packed.rep_const _).add ((Packed.rep_const _).mul (Packed.rep_var _))
  · rw [comp_X]
    exact (Packed.rep_const _).add (Packed.rep_var _)

private def parK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed := affK k s cn (origin s)

private theorem parK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (parK k s cn).Rep (2 ^ k) ((parameter s).comp (aff s cn)) := affK_rep k s cn _

private def sinK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed := sineK (parK k s cn)
private def cosK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed := cosineK (parK k s cn)

private theorem sinK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (sinK k s cn).Rep (2 ^ k) ((sine s).comp (aff s cn)) := by
  rw [sine, comp_assoc]; exact sineK_rep (parK_rep k s cn)

private theorem cosK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (cosK k s cn).Rep (2 ^ k) ((cosine s).comp (aff s cn)) := by
  rw [cosine, comp_assoc]; exact cosineK_rep (parK_rep k s cn)

private def quadK (k : ℕ) (s : ScalarCase) (cn : Bool) (a b c : ℚ) : Packed :=
  ((Packed.const a).add ((Packed.const b).mul (parK k s cn))).add
    ((Packed.const c).mul ((parK k s cn).pow 2))

private theorem quadK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (a b c : ℚ) :
    (quadK k s cn a b c).Rep (2 ^ k)
      ((C a + C b * parameter s + C c * (parameter s) ^ 2).comp (aff s cn)) := by
  simp only [add_comp, mul_comp, C_comp, pow_comp]
  exact ((Packed.rep_const a).add ((Packed.rep_const b).mul (parK_rep k s cn))).add
    ((Packed.rep_const c).mul ((parK_rep k s cn).pow 2))

private theorem lin_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (a b : ℚ) :
    ((Packed.const a).add ((Packed.const b).mul (parK k s cn))).Rep (2 ^ k)
      ((C a + C b * parameter s).comp (aff s cn)) := by
  simp only [add_comp, mul_comp, C_comp]
  exact (Packed.rep_const a).add ((Packed.rep_const b).mul (parK_rep k s cn))

private def kK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  if band s = .low then quadK k s cn (17253/20000) (67/100) (27/100) else Packed.ofNat 1

private theorem kK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (kK k s cn).Rep (2 ^ k) ((ExceptionalEPolynomials.k s).comp (aff s cn)) := by
  unfold kK ExceptionalEPolynomials.k
  split_ifs
  · exact quadK_rep k s cn _ _ _
  · rw [one_comp]; exact Packed.rep_one'

private def ellK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  match band s with
  | .low => quadK k s cn (50521/100000) (21/25) (1/2)
  | .middle => quadK k s cn (551/1000) (67/100) (21/100)
  | .high => (Packed.const (7/10)).add ((Packed.const (8/25)).mul (parK k s cn))

private theorem ellK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (ellK k s cn).Rep (2 ^ k) ((ell s).comp (aff s cn)) := by
  unfold ellK ell
  generalize band s = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · exact quadK_rep k s cn _ _ _
  · exact lin_rep k s cn _ _

private def cK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  match band s with
  | .low => quadK k s cn (17253/20000) (18/25) (3/10)
  | .middle => quadK k s cn (891/1000) (16/25) (1/50)
  | .high => Packed.const (113/100)

private theorem cK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (cK k s cn).Rep (2 ^ k) ((c s).comp (aff s cn)) := by
  unfold cK c
  generalize band s = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · exact quadK_rep k s cn _ _ _
  · rw [C_comp]; exact Packed.rep_const _

private def etaK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  match band s with
  | .low => quadK k s cn (131/500) (19/100) (2/25)
  | .middle => ((Packed.const (61/200)).sub ((Packed.const (1/50)).mul (parK k s cn))).add
      ((Packed.const (7/200)).mul ((parK k s cn).pow 2))
  | .high => (Packed.const (27/100)).add ((Packed.const (2/25)).mul (parK k s cn))

private theorem etaK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (etaK k s cn).Rep (2 ^ k) ((eta s).comp (aff s cn)) := by
  unfold etaK eta
  generalize band s = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · simp only [add_comp, sub_comp, mul_comp, C_comp, pow_comp]
    exact ((Packed.rep_const _).sub ((Packed.rep_const _).mul (parK_rep k s cn))).add
      ((Packed.rep_const _).mul ((parK_rep k s cn).pow 2))
  · exact lin_rep k s cn _ _

private def pK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  (cosK k s cn).add ((etaK k s cn).mul (sinK k s cn))

private theorem pK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (pK k s cn).Rep (2 ^ k) ((p s).comp (aff s cn)) := by
  rw [p, add_comp, mul_comp]
  exact (cosK_rep k s cn).add ((etaK_rep k s cn).mul (sinK_rep k s cn))

private def firstK (k : ℕ) (s : ScalarCase) (cn : Bool) : Fin 4 → Packed :=
  ![pK k s cn, kK k s cn, ellK k s cn, Packed.ofNat 1]

private def secondK (k : ℕ) (s : ScalarCase) (cn : Bool) : Fin 4 → Packed :=
  ![kK k s cn, ellK k s cn, cK k s cn, cK k s cn]

private theorem one_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (Packed.ofNat 1).Rep (2 ^ k) ((1 : ℚ[X]).comp (aff s cn)) := by
  rw [one_comp]; exact Packed.rep_one'

private theorem firstK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 4) :
    (firstK k s cn i).Rep (2 ^ k) ((first s i).comp (aff s cn)) := by
  fin_cases i
  · exact pK_rep k s cn
  · exact kK_rep k s cn
  · exact ellK_rep k s cn
  · exact one_rep k s cn

private theorem secondK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 4) :
    (secondK k s cn i).Rep (2 ^ k) ((second s i).comp (aff s cn)) := by
  fin_cases i
  · exact kK_rep k s cn
  · exact ellK_rep k s cn
  · exact cK_rep k s cn
  · exact cK_rep k s cn

private def nuK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  ![Packed.const (53/50), ellK k s cn, cK k s cn, cK k s cn] (negativeIndex s)

private theorem nuK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (nuK k s cn).Rep (2 ^ k) ((nu s).comp (aff s cn)) := by
  unfold nuK nu
  generalize negativeIndex s = i
  fin_cases i
  · show (Packed.const (53/50)).Rep (2 ^ k) ((C (53/50)).comp (aff s cn))
    rw [C_comp]; exact Packed.rep_const _
  · exact ellK_rep k s cn
  · exact cK_rep k s cn
  · exact cK_rep k s cn

private def outsideK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  (((((((Packed.ofNat 3).mul (kK k s cn)).add ((Packed.ofNat 2).mul (ellK k s cn))).add
    ((Packed.ofNat 3).mul (cK k s cn))).add (Packed.ofNat 1)).add
    ((Packed.ofNat 2).mul (cosK k s cn))).add
    (((Packed.ofNat 1).add ((Packed.ofNat 2).mul (etaK k s cn))).mul (sinK k s cn))).add
    ((nuK k s cn).mul ((cosK k s cn).sub (Packed.ofNat 1)))

private theorem outsideK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (outsideK k s cn).Rep (2 ^ k) ((outside s).comp (aff s cn)) := by
  have h1 : (Packed.ofNat 1).Rep (2 ^ k) (1 : ℚ[X]) := Packed.rep_one'
  have h2 : (Packed.ofNat 2).Rep (2 ^ k) ((2 : ℕ) : ℚ[X]) := Packed.rep_ofNat 2
  have h3 : (Packed.ofNat 3).Rep (2 ^ k) ((3 : ℕ) : ℚ[X]) := Packed.rep_ofNat 3
  unfold outsideK outside
  simp only [add_comp, mul_comp, sub_comp, one_comp, ofNat_comp]
  exact ((((((h3.mul (kK_rep k s cn)).add (h2.mul (ellK_rep k s cn))).add
    (h3.mul (cK_rep k s cn))).add h1).add (h2.mul (cosK_rep k s cn))).add
    ((h1.add (h2.mul (etaK_rep k s cn))).mul (sinK_rep k s cn))).add
    ((nuK_rep k s cn).mul ((cosK_rep k s cn).sub h1))

private def squaredNormK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 4) : Packed :=
  if i = negativeIndex s then
    (((firstK k s cn i).pow 2).add ((secondK k s cn i).pow 2)).sub
      ((((Packed.ofNat 2).mul (firstK k s cn i)).mul (secondK k s cn i)).mul (sinK k s cn))
  else ((firstK k s cn i).pow 2).add ((secondK k s cn i).pow 2)

private theorem squaredNormK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 4) :
    (squaredNormK k s cn i).Rep (2 ^ k) ((squaredNorm s i).comp (aff s cn)) := by
  unfold squaredNormK squaredNorm
  split_ifs
  · simp only [add_comp, sub_comp, mul_comp, pow_comp, ofNat_comp]
    exact (((firstK_rep k s cn i).pow 2).add ((secondK_rep k s cn i).pow 2)).sub
      ((((Packed.rep_ofNat 2).mul (firstK_rep k s cn i)).mul (secondK_rep k s cn i)).mul
        (sinK_rep k s cn))
  · simp only [add_comp, pow_comp, sub_zero]
    exact ((firstK_rep k s cn i).pow 2).add ((secondK_rep k s cn i).pow 2)

private def rowSquareK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : Packed :=
  if hi : i.val < 4 then squaredNormK k s cn ⟨i.val, hi⟩
  else (Packed.ofNat 1).add ((etaK k s cn).pow 2)

private theorem rowSquareK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) :
    (rowSquareK k s cn i).Rep (2 ^ k) ((rowSquare s i).comp (aff s cn)) := by
  unfold rowSquareK rowSquare
  split_ifs
  · exact squaredNormK_rep k s cn _
  · rw [add_comp, pow_comp]
    exact (one_rep k s cn).add ((etaK_rep k s cn).pow 2)

private def rowWeightK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : Packed :=
  if i.val < 4 then Packed.ofNat 1 else sinK k s cn

private theorem rowWeightK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) :
    (rowWeightK k s cn i).Rep (2 ^ k) ((rowWeight s i).comp (aff s cn)) := by
  unfold rowWeightK rowWeight
  split_ifs
  · exact one_rep k s cn
  · exact sinK_rep k s cn

/-! ### The Newton masses -/

/-- The checks behind the Newton mass of row `i`, on its uncentered row square. -/
private def massGood (k : ℕ) (s : ScalarCase) (i : Fin 5) : Bool :=
  newtonOK k (rowSquareK k s false i)

/-- The coefficients of `massAt`. -/
private def massList (k : ℕ) (s : ScalarCase) (i : Fin 5) : Scaled :=
  newtonList k (rowSquareK k s false i)

private theorem massList_rep {k : ℕ} {s : ScalarCase} {i : Fin 5} (h : massGood k s i = true) :
    (massList k s i).Rep (massAt s i) := by
  have hr := rowSquareK_rep k s false i
  rw [aff, ite_eq_right Bool.false_ne_true, comp_X] at hr
  exact newtonList_rep hr h

private def lnum : ScalarCase → ℕ
  | .lowZero | .lowReturn => 1 | .middle _ => 17 | .high _ => 7

private def lden : ScalarCase → ℕ
  | .lowZero => 20 | .lowReturn => 100 | .middle _ => 200 | .high _ => 40

/-- Centering on `[0, length s]`. -/
private def cen (s : ScalarCase) (c : Scaled) : Scaled := c.center (lnum s) (lden s) 1 1

private theorem cen_rep (s : ScalarCase) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (cen s c).Rep (centered 0 (length s) p) := by
  unfold cen
  exact hc.centered _ _ 1 1 (by cases s <;> simp [lden]) (by cases s <;> norm_num [length, lnum, lden])
    (by cases s <;> norm_num [length, lnum, lden])

/-- The mass of row `i` as a list, centered on `[0, length s]` when `cn`. -/
private def massLC (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : Scaled :=
  if cn then cen s (massList k s i) else massList k s i

private theorem massLC_rep {k : ℕ} {s : ScalarCase} (cn : Bool) {i : Fin 5}
    (h : massGood k s i = true) : (massLC k s cn i).Rep ((massAt s i).comp (aff s cn)) := by
  unfold massLC aff
  split_ifs
  · exact cen_rep s (massList_rep h)
  · rw [comp_X]; exact massList_rep h

/-! ### The certificate -/

private def certK (k : ℕ) (s : ScalarCase) (cn : Bool) : Packed :=
  certificateK ((outsideK k s cn).sub (Packed.const margin)) (Packed.const radiusUpper)
    (rowWeightK k s cn) (rowSquareK k s cn) (fun i => Packed.ofList k (massLC k s cn i).l)
    (fun i => (massLC k s cn i).s)

private def massesGood (k : ℕ) (s : ScalarCase) : Bool :=
  massGood k s 0 && massGood k s 1 && massGood k s 2 && massGood k s 3 && massGood k s 4

private theorem massesGood_spec {k : ℕ} {s : ScalarCase} (h : massesGood k s = true) (i : Fin 5) :
    massGood k s i = true := by
  simp only [massesGood, Bool.and_eq_true] at h
  fin_cases i
  exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]

private theorem certK_rep {k : ℕ} {s : ScalarCase} (cn : Bool) (h : massesGood k s = true) :
    (certK k s cn).Rep (2 ^ k) ((certificate s).comp (aff s cn)) := by
  refine (certificateK_rep ((outsideK_rep k s cn).sub (Packed.rep_const margin))
    (Packed.rep_const radiusUpper) (rowWeightK_rep k s cn) (rowSquareK_rep k s cn)
    (fun i => Packed.rep_ofList_of_rep k (massLC_rep cn (massesGood_spec h i)))).of_eq ?_
  rw [certificate, mass]
  unfold massExcept
  rw [fiveMasses_comp, sub_comp, C_comp, C_comp]

/-- The derivative of a coefficient list. -/
private def derivAux : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, a :: t => ((k:ℤ) * a) :: derivAux (k+1) t

private def derivS (c : Certificate.Scaled) : Certificate.Scaled := ⟨derivAux 1 c.l.tail, c.s⟩

/-- The value of a coefficient list at a rational point. -/
private def evalL (x : ℚ) : List ℤ → ℚ
  | [] => 0
  | a :: t => (a : ℚ) + x * evalL x t

/-- `10 ^ (n - 1)` times the value at `1/10` of a list with `n` entries. -/
private def ev10 : List ℤ → ℤ
  | [] => 0
  | a :: t => a * 10 ^ t.length + ev10 t

private theorem derivAux_getD : ∀ (l : List ℤ) (k n : ℕ),
    (derivAux k l).getD n 0 = ((k + n : ℕ) : ℤ) * l.getD n 0
  | [], _, _ => by simp [derivAux]
  | a :: t, k, 0 => by simp [derivAux]
  | a :: t, k, n + 1 => by
    simp only [derivAux, List.getD_cons_succ, derivAux_getD t (k + 1) n]
    congr 2; omega

private theorem derivS_rep {c : Certificate.Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (derivS c).Rep (derivative p) := by
  unfold Certificate.Scaled.Rep at *
  have h : Certificate.toPoly (derivAux 1 c.l.tail) = derivative (Certificate.toPoly c.l) := by
    ext n
    rw [coeff_derivative, Certificate.coeff_toPoly, Certificate.coeff_toPoly, derivAux_getD]
    rcases c.l with _ | ⟨a, t⟩
    · simp
    · simp only [List.tail_cons, List.getD_cons_succ]; push_cast; ring
  show toPoly (derivAux 1 c.l.tail) = C (c.s : ℚ) * derivative p
  rw [h, hc, derivative_C_mul]

private theorem evalL_eq (x : ℚ) : ∀ l : List ℤ, evalL x l = (Certificate.toPoly l).eval x
  | [] => by simp [evalL, Certificate.toPoly]
  | a :: t => by simp [evalL, Certificate.toPoly, evalL_eq x t]

private theorem eval_of_rep {c : Certificate.Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s ≠ 0)
    (x : ℚ) : p.eval x = evalL x c.l / c.s := by
  unfold Certificate.Scaled.Rep at hc
  have hs' : (c.s:ℚ) ≠ 0 := by exact_mod_cast hs
  rw [evalL_eq, hc, eval_mul, eval_C]
  field_simp

private theorem ev10_eq : ∀ l : List ℤ, (ev10 l : ℚ) * 10 = 10 ^ l.length * evalL (1/10) l
  | [] => by simp [ev10, evalL]
  | a :: t => by
    have ih := ev10_eq t
    simp only [ev10, evalL, List.length_cons]
    push_cast
    linear_combination ih

/-! ### The checks, one declaration per scalar case -/

/-- The bits of the base `2 ^ k`: a few more than the checks of each case need. -/
private def bits : ScalarCase → ℕ
  | .lowZero => 1920 | .lowReturn => 6540
  | .middle 0 => 5870 | .middle 1 => 7080 | .middle 2 => 7420 | .middle 3 => 7120
  | .high 0 => 4210 | .high 1 => 5380 | .high 2 => 5450 | .high 3 => 5500

/-- The centered certificate, as an explicit list. -/
private def certList (k : ℕ) (s : ScalarCase) : Scaled :=
  (certK k s true).digits k (max (certK k s true).n 2)

/-- The certificate itself, as an explicit list. -/
private def certListU (k : ℕ) (s : ScalarCase) : Scaled :=
  (certK k s false).digits k (certK k s false).n

/-- The checks of the case `s = .lowZero`. The case is an argument, here and in `middleBOK`: a
literal `.middle 2` in a definition carries another proof of `NeZero 4` than the same literal in a
statement, and matching the two makes Lean evaluate the certificate. -/
private def lowZeroOK (k : ℕ) (s : ScalarCase) : Bool :=
  decide (2 * (certK k s false).b < 2 ^ k) && decide (0 < (certK k s false).s) &&
    upOK k 45 (cen s (derivS (certListU k s))) (-49/1000) &&
    decide ((10 : ℤ) ^ (certListU k s).l.length * (certK k s false).s <
      20000 * ev10 (certListU k s).l)

/-- The checks of the case `s = .middle 2`. -/
private def middleBOK (k : ℕ) (s : ScalarCase) : Bool :=
  decide (2 * (certK k s false).b < 2 ^ k) && decide (0 < (certK k s false).s) &&
    decide (((certK k s false).s : ℤ) < 250 * (certListU k s).l.getD 0 0) &&
    lowOK k 45 (cen s (certListU k s).divX) (1/5)

/-- The certificate checks of one scalar case. -/
private def certOK (k : ℕ) (s : ScalarCase) : Bool :=
  decide (1 ≤ k) && massesGood k s && decide (2 * (certK k s true).b < 2 ^ k) &&
    decide (0 < (certK k s true).s) && decide ((certK k s true).n ≤ 46 + 1) &&
    (if s = .lowZero then lowZeroOK k s else if s = .middle 2 then middleBOK k s
      else lowOK k 46 (certList k s) (1/1000))

/-- The centered row square, as an explicit list. -/
private def squareList (k : ℕ) (s : ScalarCase) (i : Fin 5) : Scaled :=
  (rowSquareK k s true i).digits k (max (rowSquareK k s true i).n 2)

private def rowCheck (k : ℕ) (s : ScalarCase) (i : Fin 5) : Bool :=
  decide (1 ≤ k) && decide (2 * (rowSquareK k s true i).b < 2 ^ k) &&
    lowOK k 38 (squareList k s i) (1/4) && upOK k 38 (squareList k s i) 6 &&
    massGood k s i && lowOK k 3 (cen s (massList k s i)) (4/5) && upOK k 3 (cen s (massList k s i)) 3

private def rowsCheck (k : ℕ) (s : ScalarCase) : Bool :=
  rowCheck k s 0 && rowCheck k s 1 && rowCheck k s 2 && rowCheck k s 3 && rowCheck k s 4

set_option Elab.async false in
private theorem certOK_lowZero : certOK (bits .lowZero) .lowZero = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_lowReturn : certOK (bits .lowReturn) .lowReturn = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_middle0 : certOK (bits (.middle 0)) (.middle 0) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_middle1 : certOK (bits (.middle 1)) (.middle 1) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_middle2 : certOK (bits (.middle 2)) (.middle 2) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_middle3 : certOK (bits (.middle 3)) (.middle 3) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_high0 : certOK (bits (.high 0)) (.high 0) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_high1 : certOK (bits (.high 1)) (.high 1) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_high2 : certOK (bits (.high 2)) (.high 2) = true := by decide +kernel

set_option Elab.async false in
private theorem certOK_high3 : certOK (bits (.high 3)) (.high 3) = true := by decide +kernel

set_option Elab.async false in
private theorem rowsCheck_lowZero : rowsCheck (bits .lowZero) .lowZero = true := by decide +kernel

set_option Elab.async false in
private theorem rowsCheck_lowReturn : rowsCheck (bits .lowReturn) .lowReturn = true := by
  decide +kernel

set_option Elab.async false in
private theorem rowsCheck_middle0 : rowsCheck (bits (.middle 0)) (.middle 0) = true := by
  decide +kernel

set_option Elab.async false in
private theorem rowsCheck_middle1 : rowsCheck (bits (.middle 1)) (.middle 1) = true := by
  decide +kernel

set_option Elab.async false in
private theorem rowsCheck_middle2 : rowsCheck (bits (.middle 2)) (.middle 2) = true := by
  decide +kernel

set_option Elab.async false in
private theorem rowsCheck_middle3 : rowsCheck (bits (.middle 3)) (.middle 3) = true := by
  decide +kernel

set_option Elab.async false in
private theorem rowsCheck_high0 : rowsCheck (bits (.high 0)) (.high 0) = true := by decide +kernel

set_option Elab.async false in
private theorem rowsCheck_high1 : rowsCheck (bits (.high 1)) (.high 1) = true := by decide +kernel

set_option Elab.async false in
private theorem rowsCheck_high2 : rowsCheck (bits (.high 2)) (.high 2) = true := by decide +kernel

set_option Elab.async false in
private theorem rowsCheck_high3 : rowsCheck (bits (.high 3)) (.high 3) = true := by decide +kernel

private theorem certOK_all (s : ScalarCase) : certOK (bits s) s = true := by
  cases s with
  | lowZero => exact certOK_lowZero
  | lowReturn => exact certOK_lowReturn
  | middle i =>
      fin_cases i
      exacts [certOK_middle0, certOK_middle1, certOK_middle2, certOK_middle3]
  | high i =>
      fin_cases i
      exacts [certOK_high0, certOK_high1, certOK_high2, certOK_high3]

private theorem rowsCheck_all (s : ScalarCase) : rowsCheck (bits s) s = true := by
  cases s with
  | lowZero => exact rowsCheck_lowZero
  | lowReturn => exact rowsCheck_lowReturn
  | middle i =>
      fin_cases i
      exacts [rowsCheck_middle0, rowsCheck_middle1, rowsCheck_middle2, rowsCheck_middle3]
  | high i =>
      fin_cases i
      exacts [rowsCheck_high0, rowsCheck_high1, rowsCheck_high2, rowsCheck_high3]

private theorem certOK_parts (s : ScalarCase) :
    1 ≤ bits s ∧ massesGood (bits s) s = true ∧ 2 * (certK (bits s) s true).b < 2 ^ bits s ∧
      0 < (certK (bits s) s true).s ∧ (certK (bits s) s true).n ≤ 46 + 1 ∧
      (if s = .lowZero then lowZeroOK (bits s) s else if s = .middle 2 then middleBOK (bits s) s
        else lowOK (bits s) 46 (certList (bits s) s) (1/1000)) = true := by
  have h := certOK_all s
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem certList_rep (s : ScalarCase) :
    (certList (bits s) s).Rep (centered 0 (length s) (certificate s)) := by
  obtain ⟨hk, hm, hb, -, -, -⟩ := certOK_parts s
  exact (certK_rep true hm).digits hk hb (le_max_left _ 2)

private theorem certListU_rep (s : ScalarCase) (hb : 2 * (certK (bits s) s false).b < 2 ^ bits s) :
    (certListU (bits s) s).Rep (certificate s) := by
  obtain ⟨hk, hm, -, -, -, -⟩ := certOK_parts s
  have hr := certK_rep (s := s) false hm
  rw [aff, ite_eq_right Bool.false_ne_true, comp_X] at hr
  exact hr.digits hk hb le_rfl

theorem certificate_identity (s : ScalarCase) :
    centered 0 (length s) (certificate s)=expansion 46 (centered 0 (length s) (certificate s)) := by
  obtain ⟨-, -, -, hs, hn, -⟩ := certOK_parts s
  refine (certList_rep s).eq_expansion (by simp only [certList, Packed.digits]; omega) ?_
  simp only [certList, Packed.digits, length_digs]
  omega

theorem ordinary_reserve (s : ScalarCase) (h0 : s≠.lowZero) (hB : s≠.middle 2) :
    (1/1000:ℚ)<lowerOn 46 0 (length s) (certificate s) := by
  obtain ⟨-, -, -, -, -, h⟩ := certOK_parts s
  rw [ite_eq_right h0, ite_eq_right hB] at h
  exact (lowOK_spec (certList_rep s) h).1

private theorem lowZero_parts :
    (certListU (bits .lowZero) .lowZero).Rep (certificate .lowZero) ∧
      0 < (certK (bits .lowZero) .lowZero false).s ∧
      upOK (bits .lowZero) 45 (cen .lowZero (derivS (certListU (bits .lowZero) .lowZero)))
        (-49/1000) = true ∧
      (10 : ℤ) ^ (certListU (bits .lowZero) .lowZero).l.length * (certK (bits .lowZero) .lowZero false).s <
        20000 * ev10 (certListU (bits .lowZero) .lowZero).l := by
  obtain ⟨-, -, -, -, -, h⟩ := certOK_parts .lowZero
  rw [ite_eq_left rfl] at h
  simp only [lowZeroOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hs⟩, hu⟩, he⟩ := h
  exact ⟨certListU_rep .lowZero hb, hs, hu, he⟩

private theorem low_derivative_check :
    upperOn 45 0 (1/10) (certificate .lowZero).derivative < -(49/1000:ℚ) ∧
      centered 0 (1/10) (certificate .lowZero).derivative =
        expansion 45 (centered 0 (1/10) (certificate .lowZero).derivative) := by
  obtain ⟨hr, -, hu, -⟩ := lowZero_parts
  have h := upOK_spec (cen_rep .lowZero (derivS_rep hr)) hu
  exact ⟨h.1.trans_le (by norm_num), h.2⟩

theorem low_derivative_identity :
    centered 0 (1/10) (certificate .lowZero).derivative=
      expansion 45 (centered 0 (1/10) (certificate .lowZero).derivative) :=
  low_derivative_check.2

theorem low_derivative_reserve :
    upperOn 45 0 (1/10) (certificate .lowZero).derivative< -(49/1000:ℚ) :=
  low_derivative_check.1

theorem low_right_reserve : (1/2000:ℚ)<(certificate .lowZero).eval (1/10) := by
  obtain ⟨hr, hs, -, he⟩ := lowZero_parts
  have hs' : (certListU (bits .lowZero) .lowZero).s ≠ 0 := by
    simp only [certListU, Packed.digits]; omega
  have hsq : (0 : ℚ) < (certListU (bits .lowZero) .lowZero).s := by
    exact_mod_cast Nat.pos_of_ne_zero hs'
  rw [eval_of_rep hr hs', lt_div_iff₀ hsq]
  have he' := (Int.cast_lt (R := ℚ)).2 he
  have h10 := ev10_eq (certListU (bits .lowZero) .lowZero).l
  have hp : (0 : ℚ) < 10 ^ (certListU (bits .lowZero) .lowZero).l.length := by positivity
  simp only [certListU, Packed.digits] at he' h10 hp ⊢
  push_cast at he' h10 hp ⊢
  clear hr hs hs' hsq he
  generalize digs (bits .lowZero) (certK (bits .lowZero) .lowZero false).n
    (certK (bits .lowZero) .lowZero false).v = L at he' h10 hp ⊢
  generalize (certK (bits .lowZero) .lowZero false).s = S at he' ⊢
  nlinarith

theorem middleB_identity :
    certificate (.middle 2)=C ((certificate (.middle 2)).coeff 0)+X*middleBQuotient := by
  have h := X_mul_divX_add (certificate (.middle 2)-C ((certificate (.middle 2)).coeff 0))
  simp only [coeff_sub, coeff_C_zero, sub_self, map_zero, add_zero] at h
  rw [middleBQuotient, h]
  ring

private theorem middleBQuotient_eq : middleBQuotient = (certificate (.middle 2)).divX := by
  ext n
  simp [middleBQuotient, coeff_divX, coeff_sub]

private theorem middleB_parts :
    (certListU (bits (.middle 2)) (.middle 2)).Rep (certificate (.middle 2)) ∧
      0 < (certK (bits (.middle 2)) (.middle 2) false).s ∧
      ((certK (bits (.middle 2)) (.middle 2) false).s : ℤ) <
        250 * (certListU (bits (.middle 2)) (.middle 2)).l.getD 0 0 ∧
      lowOK (bits (.middle 2)) 45 (cen (.middle 2) (certListU (bits (.middle 2)) (.middle 2)).divX)
        (1/5) = true := by
  obtain ⟨-, -, -, -, -, h⟩ := certOK_parts (.middle 2)
  rw [ite_eq_right (by decide), ite_eq_left rfl] at h
  simp only [middleBOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hs⟩, hc⟩, hl⟩ := h
  exact ⟨certListU_rep (.middle 2) hb, hs, hc, hl⟩

private theorem middleB_check :
    (1/5:ℚ)<lowerOn 45 0 (17/100) middleBQuotient ∧
      centered 0 (17/100) middleBQuotient=expansion 45 (centered 0 (17/100) middleBQuotient) := by
  obtain ⟨hr, -, -, hl⟩ := middleB_parts
  have hq := cen_rep (.middle 2) hr.divX
  rw [← middleBQuotient_eq] at hq
  exact lowOK_spec hq hl

theorem middleB_quotient_identity :
    centered 0 (17/100) middleBQuotient=expansion 45 (centered 0 (17/100) middleBQuotient) :=
  middleB_check.2

theorem middleB_reserves : (1/250:ℚ)<(certificate (.middle 2)).coeff 0 ∧
    (1/5:ℚ)<lowerOn 45 0 (17/100) middleBQuotient := by
  refine ⟨?_, middleB_check.1⟩
  obtain ⟨hr, hs, hc, -⟩ := middleB_parts
  have hs' : (certListU (bits (.middle 2)) (.middle 2)).s ≠ 0 := by
    simp only [certListU, Packed.digits]; omega
  rw [hr.coeff hs' 0, lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hs')]
  have hc' := (Int.cast_lt (R := ℚ)).2 hc
  simp only [certListU, Packed.digits] at hc' ⊢
  push_cast at hc' ⊢
  linarith

theorem polynomial_hasDerivAt (P : ℚ[X]) (z : ℝ) :
    HasDerivAt (fun x : ℝ => aeval x P) (aeval z P.derivative) z := by
  simpa [Polynomial.aeval_def,Polynomial.derivative_map] using
    (P.map (algebraMap ℚ ℝ)).hasDerivAt z

theorem certificate_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 0<aeval z (certificate s) := by
  by_cases h0 : s=.lowZero
  · subst s
    have hz' : z∈Set.Icc (0:ℝ) (1/10) := by simpa [length] using hz
    have hmono : MonotoneOn (fun x : ℝ => -aeval x (certificate .lowZero)) (Set.Icc 0 (1/10)) := by
      apply monoOn_of_hasDeriv_nonneg (d := fun x => -aeval x (certificate .lowZero).derivative)
      · exact fun x _ => ((polynomial_hasDerivAt _ x).neg).continuousAt.continuousWithinAt
      · intro x _; exact (polynomial_hasDerivAt _ x).neg
      · intro x hx
        have hb := (interval_bounds (by norm_num : (0:ℚ)<1/10)
          low_derivative_identity (x := x) (by
            have := Set.Ioo_subset_Icc_self hx; push_cast; exact this)).2
        have hr : (upperOn 45 0 (1/10) (certificate .lowZero).derivative:ℝ) < -49/1000 := by
          have := (Rat.cast_lt (K := ℝ)).mpr low_derivative_reserve; push_cast at this; linarith
        show 0 ≤ -aeval x (certificate .lowZero).derivative
        linarith
    have hright : (1/2000:ℝ)<aeval (1/10:ℝ) (certificate .lowZero) := by
      have h := low_right_reserve
      have e : aeval (1/10:ℝ) (certificate .lowZero) = (((certificate .lowZero).eval (1/10) : ℚ) : ℝ) := by
        rw [show (1/10:ℝ) = algebraMap ℚ ℝ (1/10) by norm_num, aeval_algebraMap_apply_eq_algebraMap_eval]
        rfl
      rw [e]
      have := (Rat.cast_lt (K := ℝ)).mpr h; push_cast at this; exact this
    have hm := hmono hz' (by norm_num) hz'.2
    simp only at hm
    linarith
  · by_cases hB : s=.middle 2
    · subst s
      have hz' : z∈Set.Icc ((0:ℚ):ℝ) ((17/100:ℚ):ℝ) := by
        simpa [length] using hz
      have hquot := positive_on_interval (by norm_num : (0:ℚ)<17/100)
        middleB_quotient_identity middleB_reserves.2 hz'
      have hc0 : (1/250:ℝ)<((certificate (.middle 2)).coeff 0:ℝ) := by
        have := (Rat.cast_lt (K := ℝ)).mpr middleB_reserves.1; push_cast at this; exact this
      have hz0 : 0 ≤ z := by simpa using hz'.1
      have hm := mul_nonneg hz0 (show 0≤aeval z middleBQuotient by push_cast at hquot; linarith)
      rw [middleB_identity]
      simp only [map_add,map_mul,aeval_C,aeval_X]
      simp only [eq_ratCast] at *
      linarith
    · have hh := positive_on_interval (length_pos s) (certificate_identity s)
        (ordinary_reserve s h0 hB) (by simpa using hz)
      norm_num at hh
      linarith

private theorem rowCheck_parts (s : ScalarCase) (i : Fin 5) :
    lowOK (bits s) 38 (squareList (bits s) s i) (1/4) = true ∧
      upOK (bits s) 38 (squareList (bits s) s i) 6 = true ∧
      (cen s (massList (bits s) s i)).Rep (centered 0 (length s) (massAt s i)) ∧
      lowOK (bits s) 3 (cen s (massList (bits s) s i)) (4/5) = true ∧
      upOK (bits s) 3 (cen s (massList (bits s) s i)) 3 = true ∧
      (squareList (bits s) s i).Rep (centered 0 (length s) (rowSquare s i)) := by
  have h := rowsCheck_all s
  simp only [rowsCheck, Bool.and_eq_true] at h
  have h' : rowCheck (bits s) s i = true := by
    fin_cases i
    exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨hk, hb⟩, hl⟩, hu⟩, hm⟩, hml⟩, hmu⟩ := h'
  exact ⟨hl, hu, cen_rep s (massList_rep hm), hml, hmu,
    (rowSquareK_rep _ s true i).digits hk hb (le_max_left _ 2)⟩

theorem mass_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length s) (massAt s i)=expansion 3 (centered 0 (length s) (massAt s i)) :=
  (lowOK_spec (rowCheck_parts s i).2.2.1 (rowCheck_parts s i).2.2.2.1).2

theorem mass_reserves (s : ScalarCase) (i : Fin 5) :
    (4/5:ℚ)<lowerOn 3 0 (length s) (massAt s i) ∧ upperOn 3 0 (length s) (massAt s i)<3 :=
  ⟨(lowOK_spec (rowCheck_parts s i).2.2.1 (rowCheck_parts s i).2.2.2.1).1,
    (upOK_spec (rowCheck_parts s i).2.2.1 (rowCheck_parts s i).2.2.2.2.1).1⟩

theorem square_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length s) (rowSquare s i)=expansion 38 (centered 0 (length s) (rowSquare s i)) :=
  (lowOK_spec (rowCheck_parts s i).2.2.2.2.2 (rowCheck_parts s i).1).2

theorem square_reserves (s : ScalarCase) (i : Fin 5) :
    (1/4:ℚ)<lowerOn 38 0 (length s) (rowSquare s i) ∧ upperOn 38 0 (length s) (rowSquare s i)<6 :=
  ⟨(lowOK_spec (rowCheck_parts s i).2.2.2.2.2 (rowCheck_parts s i).1).1,
    (upOK_spec (rowCheck_parts s i).2.2.2.2.2 (rowCheck_parts s i).2.1).1⟩

theorem mass_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 4/5<aeval z (massAt s i) ∧ aeval z (massAt s i)<3 := by
  have hh := interval_bounds (length_pos s) (mass_identity s i) (by simpa using hz)
  have hl : (4/5:ℝ)<(lowerOn 3 0 (length s) (massAt s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 3 0 (length s) (massAt s i):ℝ)<(3:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem square_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) : 1/4<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<6 := by
  have hh := interval_bounds (length_pos s) (square_identity s i) (by simpa using hz)
  have hl : (1/4:ℝ)<(lowerOn 38 0 (length s) (rowSquare s i):ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).1; push_cast at this; exact this
  have hu : (upperOn 38 0 (length s) (rowSquare s i):ℝ)<(6:ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).2; push_cast at this; exact this
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩


end SquaresInCircles.Eight.ExceptionalEPolynomials
end
end
end

section
/-!
## Real scalar model of the exceptional endpoint polynomials

The common negative H coefficient is 1.06; the
other three coefficients are the actual l,c,c. Only the B alternative
is needed in either low interval. The radius appears solely in the
support term, so the final transfer retains the original common radius.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalEScalarData
open Polynomial ExceptionalECoefficients HighOrderTaylor
open ExceptionalEPolynomials (ScalarCase band negativeIndex)

def firstData (b : Band) (t sn cs : ℝ) : Fin 4 → ℝ := ![cs+eta b t*sn,k b t,ell b t,1]
def secondData (b : Band) (t : ℝ) : Fin 4 → ℝ := ![k b t,ell b t,c b t,c b t]
def nuData (b : Band) (t : ℝ) : Fin 4 → ℝ := ![53/50,ell b t,c b t,c b t]

def outsideData (s : ScalarCase) (t sn cs : ℝ) : ℝ :=
  3*k (band s) t+2*ell (band s) t+3*c (band s) t+1+2*cs+
    (1+2*eta (band s) t)*sn+nuData (band s) t (negativeIndex s)*(cs-1)

def squaredData (s : ScalarCase) (t sn cs : ℝ) (i : Fin 4) : ℝ :=
  (firstData (band s) t sn cs i)^2+(secondData (band s) t i)^2-
    (if i=negativeIndex s then 2*firstData (band s) t sn cs i*secondData (band s) t i*sn else 0)

def squareData (s : ScalarCase) (t sn cs : ℝ) (i : Fin 5) : ℝ :=
  if hi : i.val<4 then squaredData s t sn cs ⟨i.val,hi⟩ else 1+(eta (band s) t)^2

def weightData (sn : ℝ) (i : Fin 5) : ℝ := if i.val<4 then 1 else sn
def rowSum (s : ScalarCase) (t sn cs : ℝ) : ℝ :=
  ∑i : Fin 5,weightData sn i*Real.sqrt (squareData s t sn cs i)
def valueAt (s : ScalarCase) (R t : ℝ) : ℝ :=
  outsideData s t (Real.sin t) (Real.cos t)-R*rowSum s t (Real.sin t) (Real.cos t)
def taylorOutside (s : ScalarCase) (t : ℝ) : ℝ := outsideData s t (S15 t) (C16 t)
def taylorSum (s : ScalarCase) (t : ℝ) : ℝ := rowSum s t (S15 t) (C16 t)

def charge (R : ℝ) (b : Band) (t : ℝ) (i : Fin 4) : ℝ :=
  SingleAngleConcavity.Vnu R (firstData b t (Real.sin t) (Real.cos t) i)
    (secondData b t i) (nuData b t i) t

theorem coefficient_bounds {b : Band} {t : ℝ} (ht : t∈domain b) :
    0<k b t ∧ k b t≤1 ∧ 0<ell b t ∧ ell b t<1 ∧
      0<c b t ∧ c b t<6/5 ∧ 0≤eta b t ∧ eta b t≤7/20 := by
  rcases ranges ht with ⟨hk,hl,hl1,hc,hc1,he⟩
  exact ⟨by linarith [hk.1],hk.2,hl,hl1,hc,by linarith,by linarith [he.1],by linarith [he.2]⟩

theorem nu_bounds {b : Band} {t : ℝ} (ht : t∈domain b) (i : Fin 4) :
    nuData b t i∈Set.Icc 0 2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  fin_cases i <;> simp [nuData] <;> constructor <;> linarith

theorem coordinates_bounds {b : Band} {t sn cs : ℝ}
    (ht : t∈domain b) (hs : sn∈Set.Icc 0 1) (hco : cs∈Set.Icc 0 (1001/1000)) (i : Fin 4) :
    0≤firstData b t sn cs i ∧ firstData b t sn cs i≤2 ∧
      0≤ secondData b t i ∧ secondData b t i≤2 := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have hp0 := add_nonneg hco.1 (mul_nonneg he hs.1)
  have hp1 := mul_le_mul_of_nonneg_left hs.2 he
  fin_cases i <;> simp only [firstData,secondData] <;> refine ⟨?_,?_,?_,?_⟩ <;>
    simp <;> nlinarith [hco.2]

theorem weight_bounds {sn : ℝ} (hs : sn∈Set.Icc 0 1) (i : Fin 5) :
    0≤weightData sn i ∧ weightData sn i≤2 := by
  dsimp [weightData]
  split_ifs <;> constructor <;> linarith [hs.1,hs.2]

theorem square_nonneg (s : ScalarCase) {t sn cs : ℝ}
    (ht : t∈domain (band s)) (hs : sn∈Set.Icc 0 1)
    (hco : cs∈Set.Icc 0 (1001/1000)) (i : Fin 5) : 0≤ squareData s t sn cs i := by
  dsimp [squareData]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds ht hs hco j
    have hp := mul_nonneg (mul_nonneg hb.1 hb.2.2.1) (sub_nonneg.mpr hs.2)
    dsimp [squaredData]
    split_ifs
    · nlinarith [sq_nonneg (firstData (band s) t sn cs j-secondData (band s) t j)]
    · rw [sub_zero]; positivity
  · positivity

theorem polynomial_parameters (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.k s)=k (band s) t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.ell s)=ell (band s) t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.c s)=c (band s) t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.eta s)=eta (band s) t := by
  cases s <;> refine ⟨?_,?_,?_,?_⟩
  all_goals (try simp [ExceptionalEPolynomials.k,ExceptionalEPolynomials.ell,
    ExceptionalEPolynomials.c,ExceptionalEPolynomials.eta,ExceptionalEPolynomials.parameter,
    ExceptionalEPolynomials.origin,band,ExceptionalECoefficients.k,ExceptionalECoefficients.ell,
    ExceptionalECoefficients.c,ExceptionalECoefficients.eta])
  all_goals ring

theorem polynomial_trig (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.sine s)=S15 t ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.cosine s)=C16 t := by
  have hp : aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.parameter s)=t := by
    simp [ExceptionalEPolynomials.parameter]
  simp [ExceptionalEPolynomials.sine,ExceptionalEPolynomials.cosine,Polynomial.aeval_comp,hp,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval]

theorem polynomial_coordinates (s : ScalarCase) (t : ℝ) (i : Fin 4) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.first s i)=
      firstData (band s) t (S15 t) (C16 t) i ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.second s i)=
      secondData (band s) t i := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco⟩
  fin_cases i <;> simp [ExceptionalEPolynomials.first,ExceptionalEPolynomials.second,
    ExceptionalEPolynomials.p,firstData,secondData,hk,hl,hc,he,hs,hco]

theorem polynomial_nu (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.nu s)=
      nuData (band s) t (negativeIndex s) := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  generalize hj : negativeIndex s=j
  fin_cases j <;> simp [ExceptionalEPolynomials.nu,nuData,hj,hl,hc]

theorem polynomial_rows (s : ScalarCase) (t : ℝ) (i : Fin 5) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.rowSquare s i)=
      squareData s t (S15 t) (C16 t) i ∧
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.rowWeight s i)=
      weightData (S15 t) i := by
  have hv := polynomial_coordinates s t
  have hs := (polynomial_trig s t).1
  have he := (polynomial_parameters s t).2.2.2
  constructor
  · unfold ExceptionalEPolynomials.rowSquare squareData
    split_ifs with hi
    · unfold ExceptionalEPolynomials.squaredNorm squaredData
      obtain ⟨h1, h2⟩ := hv ⟨i.val, hi⟩
      have e2 : aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (2:ℚ[X]) = 2 := map_ofNat _ 2
      split_ifs <;> simp [h1, h2, hs, e2]
    · simp [he]
  · unfold ExceptionalEPolynomials.rowWeight weightData
    split_ifs <;> simp [hs]

theorem polynomial_outside (s : ScalarCase) (t : ℝ) :
    aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (ExceptionalEPolynomials.outside s)=
      taylorOutside s t := by
  rcases polynomial_parameters s t with ⟨hk,hl,hc,he⟩
  rcases polynomial_trig s t with ⟨hs,hco⟩
  have hn := polynomial_nu s t
  have e2 : aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (2:ℚ[X]) = 2 := map_ofNat _ 2
  have e3 : aeval (t-(ExceptionalEPolynomials.origin s:ℝ)) (3:ℚ[X]) = 3 := map_ofNat _ 3
  simp [ExceptionalEPolynomials.outside,taylorOutside,outsideData,hk,hl,hc,he,hs,hco,hn,e2,e3]

theorem value_eq_endpoint_charge (s : ScalarCase) (R t : ℝ) :
    valueAt s R t=ExceptionalContactSupport.atE R (k (band s) t) (ell (band s) t)
      (c (band s) t) (eta (band s) t) t+charge R (band s) t (negativeIndex s) := by
  unfold valueAt outsideData rowSum squareData squaredData weightData charge
  simp only [Fin.sum_univ_five]
  generalize band s = b
  generalize negativeIndex s = j
  fin_cases j <;>
    simp [firstData,secondData,nuData,SingleAngleConcavity.Vnu,ExceptionalContactSupport.atE,
      ExceptionalContactSupport.contactScalar,ExceptionalContactStress.tilt,
      PositiveAngularEnvelope.pairNorm,Real.sin_neg,Fin.ext_iff] <;> ring_nf

end SquaresInCircles.Eight.ExceptionalEScalarData
end
end
end

section
/-!
## Positive-mass transfer for the exceptional contact endpoints

Positive masses and exact factorization turn each
whole-interval polynomial into a strict Taylor-model inequality. The
five weighted square roots are bounded by the elementary positive-square
identity, with every denominator proved positive on the whole interval.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalERadicals
open Polynomial ExceptionalEPolynomials HighOrderTaylor

def radicalSum (s : ScalarCase) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*Real.sqrt (aeval z (rowSquare s i))
def rationalSum (s : ScalarCase) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*
    (aeval z (rowSquare s i)+(aeval z (massAt s i))^2)/(2*aeval z (massAt s i))

private theorem five_mass_identity (a v w : Fin 5 → ℝ) (ha : ∀i,a i≠0) :
    (∑i : Fin 5,w i*(v i+(a i)^2)*∏j : Fin 5,if j=i then 1 else a j)=
      2*(∏i : Fin 5,a i)*(∑i : Fin 5,w i*(v i+(a i)^2)/(2*a i)) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

theorem certificate_factorization (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) :
    aeval z (certificate s)=2*(∏i : Fin 5,aeval z (massAt s i))*
      (aeval z (outside s)-(margin:ℝ)-(radiusUpper:ℝ)*rationalSum s z) := by
  have ha : ∀i : Fin 5,aeval z (massAt s i)≠0 := by
    intro i
    have hi := (mass_bounds s i hz).1
    linarith
  have hid := five_mass_identity (fun i => aeval z (massAt s i))
    (fun i => aeval z (rowSquare s i)) (fun i => aeval z (rowWeight s i)) ha
  simp only [certificate,mass,massExcept,map_sub,map_mul,map_add,map_ofNat,map_sum,
    map_pow,map_prod,aeval_C,map_one,apply_ite,eq_ratCast] at *
  rw [hid]
  unfold rationalSum
  ring

theorem rational_positive (s : ScalarCase) {z : ℝ} (hz : z∈Set.Icc 0 (length s:ℝ)) :
    0<aeval z (outside s)-(margin:ℝ)-(radiusUpper:ℝ)*rationalSum s z := by
  have hp := certificate_positive s hz
  rw [certificate_factorization s hz] at hp
  have hM : 0<∏i : Fin 5,aeval z (massAt s i) := by
    apply Finset.prod_pos
    intro i _
    have hi := (mass_bounds s i hz).1
    linarith
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) hM)).mp hp

theorem radical_le_rational (s : ScalarCase) {z : ℝ} (hz : z∈Set.Icc 0 (length s:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) : radicalSum s z≤rationalSum s z := by
  apply Finset.sum_le_sum
  intro i _
  have hm : 0<aeval z (massAt s i) := by linarith [(mass_bounds s i hz).1]
  have hv : 0≤aeval z (rowSquare s i) := by linarith [(square_bounds s i hz).1]
  have hh := mul_le_mul_of_nonneg_left (ScalarRadicalTransfer.sqrt_le_mass_majorant hv hm) (hw i)
  simpa only [mul_div_assoc] using hh

theorem radical_reserve (s : ScalarCase) {z : ℝ} (hz : z∈Set.Icc 0 (length s:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) :
    (margin:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*radicalSum s z := by
  have hp := rational_positive s hz
  have hm := mul_le_mul_of_nonneg_left (radical_le_rational s hz hw)
    (show (0:ℝ)≤(radiusUpper:ℝ) by norm_num [radiusUpper])
  linarith

theorem taylor_weights (s : ScalarCase) {t : ℝ} (ht : t∈domain s) :
    ∀i : Fin 5,0≤aeval (t-(origin s:ℝ)) (rowWeight s i) := by
  have hd := ExceptionalECoefficients.angle (family_domain ht)
  have hs : S15 t∈Set.Icc 0 1 := ⟨S15_nonneg hd,(S15_le_sin hd.1).trans (Real.sin_le_one t)⟩
  intro i
  rw [(ExceptionalEScalarData.polynomial_rows s t i).2]
  exact (ExceptionalEScalarData.weight_bounds hs i).1

theorem polynomial_radicalSum (s : ScalarCase) (t : ℝ) :
    radicalSum s (t-(origin s:ℝ))=ExceptionalEScalarData.taylorSum s t := by
  unfold radicalSum ExceptionalEScalarData.taylorSum ExceptionalEScalarData.rowSum
  apply Finset.sum_congr rfl
  intro i _
  rw [(ExceptionalEScalarData.polynomial_rows s t i).1,(ExceptionalEScalarData.polynomial_rows s t i).2]

theorem taylor_reserve (s : ScalarCase) {t : ℝ} (ht : t∈domain s) :
    (margin:ℝ)<ExceptionalEScalarData.taylorOutside s t-
      (radiusUpper:ℝ)*ExceptionalEScalarData.taylorSum s t := by
  have hp := radical_reserve s (local_parameter ht) (taylor_weights s ht)
  simpa only [ExceptionalEScalarData.polynomial_outside,polynomial_radicalSum] using hp

end SquaresInCircles.Eight.ExceptionalERadicals
end
end
end

section
/-!
## The trigonometric endpoint inequalities of the exceptional contact

The remainder of the Taylor polynomials `S15` and `C16` controls the outside term and the five
weighted radicals on each interval (`row_error`, `rowSum_error`, `outside_error`), and the
allowance `10⁻⁸` of the polynomials pays that error. The endpoint expressions are then positive at
every common radius up to `qTrial` (`actual_radius_positive`, `endpoint_positive`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalETaylor
open ExceptionalECoefficients ExceptionalEScalarData HighOrderTaylor BoundedRadicalPerturbation
open ExceptionalEPolynomials (ScalarCase band negativeIndex radiusUpper margin)

theorem coordinate_errors (s : ScalarCase) {t : ℝ}
    (ht : t∈domain (band s)) (i : Fin 4) :
    |firstData (band s) t (Real.sin t) (Real.cos t) i-firstData (band s) t (S15 t) (C16 t) i|≤
      3*remainder := by
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have hp := SoleScalarTaylor.tilted_error (angle ht)
    (by norm_num : (1:ℝ)∈Set.Icc 0 (11/10)) ⟨he,by linarith⟩
  simp only [one_mul] at hp
  fin_cases i <;> simp [firstData] <;> linarith [show 0≤remainder by norm_num [remainder]]

theorem weight_error {t : ℝ} (ht : t∈Set.Icc 0 frameCap) (i : Fin 5) :
    |weightData (Real.sin t) i-weightData (S15 t) i|≤3*remainder := by
  have hs := (SoleScalarTaylor.input_errors ht).1
  have h0 : 0≤remainder := by norm_num [remainder]
  dsimp [weightData]
  split_ifs
  · simp only [sub_self,abs_zero]; linarith
  · linarith

theorem square_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) (i : Fin 5) :
    |squareData s t (Real.sin t) (Real.cos t) i-squareData s t (S15 t) (C16 t) i|≤
      100*remainder := by
  rcases SoleScalarTaylor.input_bounds (angle ht) with ⟨hs,hc,hs',hc'⟩
  have he := SoleScalarTaylor.input_errors (angle ht)
  have he0 : 0≤remainder := by norm_num [remainder]
  dsimp [squareData]
  split_ifs with hi
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hb := coordinates_bounds ht hs hc j
    have hb' := coordinates_bounds ht hs' hc' j
    have hd := coordinate_errors s ht j
    have ha : |firstData (band s) t (Real.sin t) (Real.cos t) j|≤2 := by
      rw [abs_of_nonneg hb.1]; exact hb.2.1
    have ha' : |firstData (band s) t (S15 t) (C16 t) j|≤2 := by
      rw [abs_of_nonneg hb'.1]; exact hb'.2.1
    have hbb : |secondData (band s) t j|≤2 := by rw [abs_of_nonneg hb.2.2.1]; exact hb.2.2.2
    have hd0 : |secondData (band s) t j-secondData (band s) t j|≤3*remainder := by
      rw [sub_self, abs_zero]; linarith
    change |squaredData s t (Real.sin t) (Real.cos t) j-
      squaredData s t (S15 t) (C16 t) j|≤100*remainder
    unfold squaredData
    split_ifs
    · exact negative_pair_difference he0 ha ha' hbb hbb
        (by rw [abs_of_nonneg hs'.1]; exact hs'.2) hd hd0 he.1
    · simpa only [sub_zero] using positive_pair_difference he0 ha ha' hbb hbb hd hd0
  · simp only [sub_self, abs_zero]; linarith

theorem row_error (s : ScalarCase) {t : ℝ} (ht : t∈ExceptionalEPolynomials.domain s) (i : Fin 5) :
    |weightData (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)-
      weightData (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)|≤500*remainder := by
  have hf := ExceptionalEPolynomials.family_domain ht
  rcases SoleScalarTaylor.input_bounds (angle hf) with ⟨hs,hc,hs',hc'⟩
  have hp := ExceptionalEPolynomials.square_bounds s i (ExceptionalEPolynomials.local_parameter ht)
  rw [(polynomial_rows s t i).1] at hp
  exact weighted_root_difference (square_nonneg s hf hs hc i) hp.1.le hp.2.le
    (by norm_num [remainder]) (by norm_num [remainder])
    (weight_bounds hs i) (weight_bounds hs' i) (square_error s hf i) (weight_error (angle hf) i)

theorem rowSum_error (s : ScalarCase) {t : ℝ} (ht : t∈ExceptionalEPolynomials.domain s) :
    rowSum s t (Real.sin t) (Real.cos t)≤taylorSum s t+2500*remainder := by
  have hh (i : Fin 5) :
      weightData (Real.sin t) i*Real.sqrt (squareData s t (Real.sin t) (Real.cos t) i)≤
        weightData (S15 t) i*Real.sqrt (squareData s t (S15 t) (C16 t) i)+500*remainder := by
    have hi := (le_abs_self _).trans (row_error s ht i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold taylorSum rowSum
  push_cast at hsum
  linarith

theorem outside_error (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    taylorOutside s t-100*remainder≤outsideData s t (Real.sin t) (Real.cos t) := by
  have hn := nu_bounds ht (negativeIndex s)
  rcases coefficient_bounds ht with ⟨hk,hk1,hl,hl1,hc,hc1,he,he1⟩
  have herr := SoleScalarTaylor.input_errors (angle ht)
  have hh := linear_difference
    (show |2+nuData (band s) t (negativeIndex s)|≤4 by
      rw [abs_of_nonneg (by linarith [hn.1])]; linarith [hn.2])
    (show |1+2*eta (band s) t|≤2 by rw [abs_of_nonneg (by linarith)]; linarith)
    herr.2.1 herr.1
  have hlower := (abs_le.mp hh).1
  dsimp [taylorOutside,outsideData]
  nlinarith [show 0≤remainder by norm_num [remainder]]

theorem conservative_positive (s : ScalarCase) {t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) : 0<valueAt s (radiusUpper:ℝ) t := by
  have hp := ExceptionalERadicals.taylor_reserve s ht
  have hd := outside_error s (ExceptionalEPolynomials.family_domain ht)
  have hs := rowSum_error s ht
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hR2 : (radiusUpper:ℝ)≤(2:ℝ) := by norm_num [radiusUpper]
  have hm := mul_le_mul_of_nonneg_left hs hR
  have he := mul_le_mul_of_nonneg_right hR2 (show 0≤2500*remainder by norm_num [remainder])
  have hmargin : (5100:ℝ)*remainder<(margin:ℝ) := by norm_num [remainder,margin]
  unfold valueAt
  nlinarith

theorem rowSum_nonneg (s : ScalarCase) {t : ℝ} (ht : t∈domain (band s)) :
    0≤rowSum s t (Real.sin t) (Real.cos t) := by
  have hs := (SoleScalarTaylor.input_bounds (angle ht)).1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_bounds hs i).1 (Real.sqrt_nonneg _)

theorem valueAt_positive (s : ScalarCase) {R t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) (hR : R≤(radiusUpper:ℝ)) : 0<valueAt s R t := by
  have hp := conservative_positive s ht
  have hm := mul_le_mul_of_nonneg_right hR (rowSum_nonneg s (ExceptionalEPolynomials.family_domain ht))
  dsimp [valueAt] at *
  linarith

/-- The scalar is positive at every radius `R` with `R² ≤ qTrial`; `qTrial` only bounds the support
coefficient. -/
theorem actual_radius_positive (s : ScalarCase) {R t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) (_hR : 0≤R) (hQU : R^2≤qTrial) :
    0<valueAt s R t := by
  apply valueAt_positive s ht
  have hroot := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hroot0 := Real.sqrt_nonneg qTrial
  have hupper := SoleScalarPolynomials.radius_upper
  have hh : R≤Real.sqrt qTrial := by nlinarith
  exact hh.trans (by simpa [radiusUpper,SoleScalarPolynomials.radiusUpper] using hupper.le)

theorem endpoint_positive (s : ScalarCase) {R t : ℝ}
    (ht : t∈ExceptionalEPolynomials.domain s) (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<ExceptionalContactSupport.atE R (k (band s) t) (ell (band s) t)
      (c (band s) t) (eta (band s) t) t+charge R (band s) t (negativeIndex s) := by
  rw [← value_eq_endpoint_charge]
  exact actual_radius_positive s ht hR hQU

end SquaresInCircles.Eight.ExceptionalETaylor
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalEBalanced
open Candidate ExceptionalECoefficients ExceptionalContactBlocks ExceptionalContactStress
open SingleAngleConcavity PositiveAngularEnvelope OrdinaryAngleConcavity
open ExceptionalEScalarData (charge firstData secondData nuData)

def endpointX (atG : Bool) (t : ℝ) : ℝ := if atG then t else 0
def endpointE (atG : Bool) (t : ℝ) : ℝ := if atG then 0 else t

theorem endpoints_mem (atG : Bool) {t : ℝ} (ht : 0≤t) :
    endpointX atG t∈Icc 0 t ∧ endpointE atG t∈Icc 0 t := by
  cases atG <;> simp [endpointX,endpointE,ht]

theorem conditions {b : Band} {t x e : ℝ} (hb : b≠.low) (ht : t∈domain b)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,(2/3)*large (k b t) (ell b t) (c b t) (eta b t) x e i≤
      small (k b t) (ell b t) (c b t) (eta b t) x e i) ∧
    (∀ i,(19/20:ℝ)≤large (k b t) (ell b t) (c b t) (eta b t) x e i ∧
      large (k b t) (ell b t) (c b t) (eta b t) x e i≤1131/1000) := by
  rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
  obtain ⟨hx0,hx1⟩ := balanced_tilt hb ht hx
  obtain ⟨he0',he1'⟩ := balanced_tilt hb ht he
  have hH := SoleBalancedCoefficients.ratio_from_interval
    (show tilt (eta b t) e∈Icc (19/20:ℝ) (53/50) from ⟨he0'.le,he1'.le⟩)
    (show tilt (eta b t) x∈Icc (19/20:ℝ) (53/50) from ⟨hx0.le,hx1.le⟩) (by norm_num)
  have hlc : ell b t≤c b t := by linarith
  constructor
  · intro i
    fin_cases i
    · show (2/3)*max (ExceptionalContactStress.tilt (eta b t) e)
          (k b t*ExceptionalContactStress.tilt (eta b t) x)≤
        min (ExceptionalContactStress.tilt (eta b t) e)
          (k b t*ExceptionalContactStress.tilt (eta b t) x)
      rw [hk,one_mul]; exact hH
    · show (2/3)*max (ell b t) (k b t)≤ min (ell b t) (k b t)
      rw [hk,max_eq_right hl1.le,min_eq_left hl1.le]; linarith
    · show (2/3)*max (ell b t) (c b t)≤ min (ell b t) (c b t)
      rw [max_eq_right hlc,min_eq_left hlc]; exact hcl
    · show (2/3)*max 1 (c b t)≤ min 1 (c b t)
      rw [max_eq_right hc0.le,min_eq_left hc0.le]; linarith
  · intro i
    fin_cases i
    · show (19/20:ℝ)≤ max (ExceptionalContactStress.tilt (eta b t) e)
          (k b t*ExceptionalContactStress.tilt (eta b t) x) ∧
        max (ExceptionalContactStress.tilt (eta b t) e)
          (k b t*ExceptionalContactStress.tilt (eta b t) x)≤1131/1000
      rw [hk,one_mul]
      exact ⟨he0'.le.trans (le_max_left _ _),max_le (by linarith) (by linarith)⟩
    · show (19/20:ℝ)≤ max (ell b t) (k b t) ∧ max (ell b t) (k b t)≤1131/1000
      rw [hk,max_eq_right hl1.le]; norm_num
    · show (19/20:ℝ)≤ max (ell b t) (c b t) ∧ max (ell b t) (c b t)≤1131/1000
      rw [max_eq_right hlc]; constructor <;> linarith
    · show (19/20:ℝ)≤ max 1 (c b t) ∧ max 1 (c b t)≤1131/1000
      rw [max_eq_right hc0.le]; constructor <;> linarith

theorem original_lower {C : SignedCycle} {ab : Fin 4} {b : Band} {R t x e L : ℝ}
    (hb : b≠.low) (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t)
    (hpure : ∀ i,L≤pure (single i) R
      (small (k b t) (ell b t) (c b t) (eta b t) x e i)
      (large (k b t) (ell b t) (c b t) (eta b t) x e i)
      (nu (k b t) (ell b t) (c b t) (eta b t) x e i) t) :
    L≤ExceptionalContactSupport.increment C ab R (k b t) (ell b t) (c b t) (eta b t) x e := by
  rcases ranges ht with ⟨hk,hl,hl1,hc,hc1,heta⟩
  have hp := small_pos (k := k b t) (by linarith [hk.1]) hl hc (tilt_pos ht hx) (tilt_pos ht he)
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab (k b t) (ell b t) (c b t) (eta b t) t x e
    hvar hG hD htotal
  have hconditions := conditions hb ht hx he
  have hlow := SoleAngleGrowth.balanced_envelope single R
    (small (k b t) (ell b t) (c b t) (eta b t) x e)
    (large (k b t) (ell b t) (c b t) (eta b t) x e)
    (nu (k b t) (ell b t) (c b t) (eta b t) x e)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).P)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).N)
    (qlo := 19/20) (qhi := 1131/1000) hR hQL hQU hp
    (small_le_large _ _ _ _ _ _) hconditions.1 (nu_between _ _ _ _ _ _) hconditions.2 (by norm_num)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).P_nonneg)
    (fun i => (blocks C ab (k b t) (ell b t) (c b t) (eta b t) x e i).N_nonneg)
    (angle ht) hP hN (single_parts C ab _ _ _ _ _ _) hpure
  exact hlow.trans (sum_minorant hab ht0 (fun i => (hp i).le) ha hP hN)

theorem norm_sorted (a b s : ℝ) : pairNorm (min a b) (max a b) s=pairNorm a b s := by
  rcases le_total a b with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h,pairNorm_symm]

def actualNu (b : Band) (t : ℝ) : Fin 4 → ℝ :=
  ![max 1 (tilt (eta b t) t),ell b t,c b t,c b t]

private theorem r38_V_sorted (R a b s : ℝ) :
    OrdinaryAngleConcavity.V R (min a b) (max a b) s=
      SingleAngleConcavity.Vnu R a b (max a b) s := by
  simp only [OrdinaryAngleConcavity.V,SingleAngleConcavity.Vnu,norm_sorted]

private theorem r38_Vnu_symm (R a b nu s : ℝ) :
    SingleAngleConcavity.Vnu R a b nu s=SingleAngleConcavity.Vnu R b a nu s := by
  simp only [SingleAngleConcavity.Vnu]
  rw [pairNorm_symm a b (-s),pairNorm_symm a b 0]

theorem pure_at_endpoint (atG : Bool) {b : Band} {R t : ℝ}
    (hb : b≠.low) (ht : t∈domain b) (i : Fin 4) :
    pure (single i) R
      (small (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (large (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (nu (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i) t=
    Vnu R (firstData b t (Real.sin t) (Real.cos t) i) (secondData b t i) (actualNu b t i) t := by
  rcases balanced_bounds hb ht with ⟨hk,hl0,hl1,hc0,hc1,hcl,he0,he1⟩
  have hlc : ell b t≤c b t := by linarith
  have ht0 : ExceptionalContactStress.tilt (eta b t) 0=1 := by
    simp [ExceptionalContactStress.tilt]
  cases atG <;> fin_cases i <;>
    simp only [endpointX,endpointE,ExceptionalContactBlocks.small,ExceptionalContactBlocks.large,
      ExceptionalContactBlocks.alpha,ExceptionalContactBlocks.beta,ExceptionalContactBlocks.single,
      ExceptionalContactBlocks.nu,actualNu,firstData,secondData,Fin.reduceFinMk,Fin.isValue,
      Matrix.cons_val,
      Bool.false_eq_true,↓reduceIte,hk,one_mul,ht0,SingleAngleConcavity.pure,r38_V_sorted]
  · rw [max_comm]; rfl
  · rw [min_eq_left hl1.le,max_eq_right hl1.le,r38_Vnu_symm]
  · rw [max_eq_right hlc]
  · rw [max_eq_right hc0.le]
  · rw [r38_Vnu_symm]; rfl
  · rw [min_eq_left hl1.le,max_eq_right hl1.le,r38_Vnu_symm]
  · rw [max_eq_right hlc]
  · rw [max_eq_right hc0.le]

theorem charge_le_pure (atG : Bool) {b : Band} {R t : ℝ}
    (hb : b≠.low) (ht : t∈domain b) (i : Fin 4) :
    charge R b t i≤pure (single i) R
      (small (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (large (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i)
      (nu (k b t) (ell b t) (c b t) (eta b t) (endpointX atG t) (endpointE atG t) i) t := by
  rw [pure_at_endpoint atG hb ht]
  have hp := (balanced_tilt hb ht (show t∈Icc 0 t from ⟨(angle ht).1,le_rfl⟩)).2
  have hnu : actualNu b t i≤nuData b t i := by
    fin_cases i
    · show max 1 (ExceptionalContactStress.tilt (eta b t) t)≤53/50
      exact max_le (by norm_num) hp.le
    all_goals exact le_rfl
  have hm := mul_le_mul_of_nonpos_right hnu (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp only [ExceptionalEScalarData.charge,SingleAngleConcavity.Vnu]
  linarith

theorem original_endpoint_lower (atG : Bool) {C : SignedCycle} {ab : Fin 4}
    {b : Band} {R t : ℝ} (hb : b≠.low) (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (ht : t∈domain b)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) :
    SoleBalancedEnvelope.minimumFour (charge R b t)≤
      ExceptionalContactSupport.increment C ab R (k b t) (ell b t) (c b t) (eta b t)
        (endpointX atG t) (endpointE atG t) := by
  obtain ⟨hx,he⟩ := endpoints_mem atG (angle ht).1
  exact original_lower hb hab hR hQL hQU ht hx he ha hvar hG hD htotal
    (fun i => (SoleBalancedEnvelope.minimumFour_le (charge R b t) i).trans (charge_le_pure atG hb ht i))

theorem scalar_endpoints {b : Band} {R t : ℝ} (hb : b≠.low) (ht : t∈domain b)
    (hR : 0≤R) (hQU : R^2≤qTrial) :
    0<ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t+
      SoleBalancedEnvelope.minimumFour (charge R b t) ∧
    0<ExceptionalContactSupport.atG R (k b t) (ell b t) (c b t) (eta b t) t+
      SoleBalancedEnvelope.minimumFour (charge R b t) := by
  have hcharges : ∀ i,0<ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t+
      charge R b t i := by
    intro i
    cases b
    · exact (hb rfl).elim
    · exact ExceptionalETaylor.endpoint_positive (.middle i)
        (by
          norm_num [ExceptionalEPolynomials.domain,ExceptionalEPolynomials.origin,
            ExceptionalEPolynomials.length,domain] at ht ⊢
          exact ht) hR hQU
    · exact ExceptionalETaylor.endpoint_positive (.high i)
        (by
          norm_num [ExceptionalEPolynomials.domain,ExceptionalEPolynomials.origin,
            ExceptionalEPolynomials.length,domain,frameCap] at ht ⊢
          exact ht) hR hQU
  have hE := SoleBalancedEnvelope.minimumFour_positive hcharges
  have hk := (balanced_bounds hb ht).1
  have heq : ExceptionalContactSupport.atG R (k b t) (ell b t) (c b t) (eta b t) t=
      ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t := by
    simp [ExceptionalContactSupport.atG,ExceptionalContactSupport.atE,hk,pairNorm_symm]
  exact ⟨hE,by simpa only [heq] using hE⟩

end SquaresInCircles.Eight.ExceptionalEBalanced
end
end
end
