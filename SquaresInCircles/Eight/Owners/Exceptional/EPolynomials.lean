module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.Interval
public import SquaresInCircles.Eight.Owners.Exceptional.ContactBlocks
public import SquaresInCircles.Eight.Owners.Exceptional.ECoefficients
public import SquaresInCircles.Eight.Owners.Positive.EContact
public import SquaresInCircles.Eight.Owners.Positive.ECycle
public import SquaresInCircles.Eight.Owners.Sole.SplitSupport

/-!
# Eight squares: ten whole-interval exceptional endpoint polynomials

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
open Polynomial WholeIntervalPolynomial ExceptionalECoefficients
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

/-! ## Packed polynomials

A polynomial `p` is packed at a base `B` as `⟨v, s, b, n⟩` when an integer list `l` with
`toPoly l = C s * p`, absolute sum at most `b` and at most `n` entries has value `v` at `B`.
Sums, products and powers act on the packed numbers, and when `2 b < B` the base-`B` digits
of `v` give back `l`. -/

private def absSum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs + absSum l

private theorem natAbs_le_absSum : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → x.natAbs ≤ absSum l
  | a :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [absSum]; omega
    · have := natAbs_le_absSum h; simp only [absSum]; omega

private theorem absSum_add : ∀ l m : List ℤ, absSum (Certificate.add l m) ≤ absSum l + absSum m
  | [], m => by simp [Certificate.add, absSum]
  | a :: l, [] => by simp [Certificate.add, absSum]
  | a :: l, b :: m => by
    have h1 := absSum_add l m
    have h2 := Int.natAbs_add_le a b
    simp only [Certificate.add, absSum]
    omega

private theorem absSum_smul (c : ℤ) :
    ∀ l : List ℤ, absSum (Certificate.smul c l) = c.natAbs * absSum l
  | [] => by simp [Certificate.smul, absSum]
  | a :: l => by simp only [Certificate.smul, absSum, absSum_smul c l, Int.natAbs_mul, Nat.mul_add]

private theorem absSum_mul : ∀ l m : List ℤ, absSum (Certificate.mul l m) ≤ absSum l * absSum m
  | [], _ => by simp [Certificate.mul, absSum]
  | _ :: _, [] => by simp [Certificate.mul, absSum]
  | a :: l, b :: m => by
    have h1 := absSum_add (Certificate.smul a (b :: m)) (0 :: Certificate.mul l (b :: m))
    have h2 := absSum_mul l (b :: m)
    rw [absSum_smul] at h1
    rw [Certificate.mul]
    calc _ ≤ _ := h1
      _ ≤ a.natAbs * absSum (b :: m) + absSum l * absSum (b :: m) := by
          simp only [absSum, Int.natAbs_zero, Nat.zero_add] at h2 ⊢; omega
      _ = absSum (a :: l) * absSum (b :: m) := by simp only [absSum]; ring

private theorem length_add : ∀ l m : List ℤ, (Certificate.add l m).length = max l.length m.length
  | [], m => by simp [Certificate.add]
  | a :: l, [] => by simp [Certificate.add]
  | a :: l, b :: m => by simp only [Certificate.add, List.length_cons, length_add l m]; omega

private theorem length_smul (c : ℤ) : ∀ l : List ℤ, (Certificate.smul c l).length = l.length
  | [] => rfl
  | a :: l => by simp only [Certificate.smul, List.length_cons, length_smul c l]

private theorem length_mul :
    ∀ l m : List ℤ, (Certificate.mul l m).length ≤ l.length + m.length - 1
  | [], _ => by simp [Certificate.mul]
  | _ :: _, [] => by simp [Certificate.mul]
  | a :: l, b :: m => by
    have h := length_mul l (b :: m)
    rw [Certificate.mul, length_add, length_smul]
    simp only [List.length_cons] at h ⊢
    omega

/-- The value of a coefficient list at `B`. -/
private def evalZ (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + B * evalZ B l

private theorem eval_toPoly (B : ℤ) : ∀ l : List ℤ, (toPoly l).eval (B : ℚ) = (evalZ B l : ℚ)
  | [] => by simp [toPoly, evalZ]
  | a :: l => by simp [toPoly, evalZ, eval_toPoly B l]

/-- A packed polynomial: value `v` at the base, scale `s`, absolute-sum bound `b`, length
bound `n`. -/
private structure KP where
  v : ℤ
  s : ℕ
  b : ℕ
  n : ℕ

private def KP.Rep (B : ℕ) (c : KP) (p : ℚ[X]) : Prop :=
  (c.s : ℚ) * p.eval (B : ℚ) = c.v ∧
    ∃ l : List ℤ, toPoly l = C (c.s : ℚ) * p ∧ absSum l ≤ c.b ∧ l.length ≤ c.n

private def KP.add (x y : KP) : KP :=
  ⟨x.v * (y.s / Nat.gcd x.s y.s : ℕ) + y.v * (x.s / Nat.gcd x.s y.s : ℕ),
    x.s * (y.s / Nat.gcd x.s y.s), x.b * (y.s / Nat.gcd x.s y.s) + y.b * (x.s / Nat.gcd x.s y.s),
    max x.n y.n⟩

private def KP.sub (x y : KP) : KP :=
  ⟨x.v * (y.s / Nat.gcd x.s y.s : ℕ) - y.v * (x.s / Nat.gcd x.s y.s : ℕ),
    x.s * (y.s / Nat.gcd x.s y.s), x.b * (y.s / Nat.gcd x.s y.s) + y.b * (x.s / Nat.gcd x.s y.s),
    max x.n y.n⟩

private def KP.mul (x y : KP) : KP := ⟨x.v * y.v, x.s * y.s, x.b * y.b, x.n + y.n - 1⟩

private def KP.one : KP := ⟨1, 1, 1, 1⟩

private def KP.pow (x : KP) : ℕ → KP
  | 0 => KP.one
  | k + 1 => (x.pow k).mul x

/-- `C q`. -/
private def KP.const (q : ℚ) : KP := ⟨q.num, q.den, q.num.natAbs, 1⟩

/-- The numeral `m`. -/
private def KP.ofNat (m : ℕ) : KP := ⟨m, 1, m, 1⟩

private def KP.zero : KP := ⟨0, 1, 0, 0⟩

/-- `X`. -/
private def KP.var (B : ℕ) : KP := ⟨B, 1, 1, 2⟩

private def KP.ofScaled (B : ℕ) (c : Scaled) : KP := ⟨evalZ B c.l, c.s, absSum c.l, c.l.length⟩

private theorem gcd_cross (a b : ℕ) : a * (b / Nat.gcd a b) = b * (a / Nat.gcd a b) := by
  rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_right a b), ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left a b),
    Nat.mul_comm]

/-- The common core of `add` and `sub`. -/
private theorem KP.rep_lin {B : ℕ} {x y : KP} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q)
    (u w : ℕ) (e : ℤ) (he : e.natAbs = 1) (key : x.s * u = y.s * w) :
    KP.Rep B ⟨x.v * u + e * (y.v * w), x.s * u, x.b * u + y.b * w, max x.n y.n⟩ (p + C (e : ℚ) * q) := by
  obtain ⟨hxv, lx, hlx, hbx, hnx⟩ := hx
  obtain ⟨hyv, ly, hly, hby, hny⟩ := hy
  have key' : (x.s : ℚ) * u = y.s * w := by exact_mod_cast key
  refine ⟨?_, Certificate.add (Certificate.smul u lx) (Certificate.smul (e * w) ly), ?_, ?_, ?_⟩
  · simp only [eval_add, eval_mul, eval_C]
    push_cast
    rw [← hxv, ← hyv]
    linear_combination (e * eval (B : ℚ) q) * key'
  · rw [Certificate.toPoly_add, Certificate.toPoly_smul, Certificate.toPoly_smul, hlx, hly]
    have hC : C ((x.s : ℚ) * u) = C ((y.s : ℚ) * w) := by rw [key']
    simp only [map_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at hC ⊢
    linear_combination (-(C (e : ℚ) * q)) * hC
  · have h1 := absSum_add (Certificate.smul u lx) (Certificate.smul (e * w) ly)
    rw [absSum_smul, absSum_smul, Int.natAbs_mul, he, Int.natAbs_natCast, Int.natAbs_natCast] at h1
    calc _ ≤ _ := h1
      _ ≤ u * x.b + 1 * w * y.b := Nat.add_le_add (Nat.mul_le_mul_left _ hbx)
          (Nat.mul_le_mul_left _ hby)
      _ = x.b * u + y.b * w := by ring
  · rw [length_add, length_smul, length_smul]
    dsimp only
    omega

private theorem KP.Rep.add {B : ℕ} {x y : KP} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q) :
    (x.add y).Rep B (p + q) := by
  have h := KP.rep_lin hx hy _ _ 1 rfl (gcd_cross x.s y.s)
  simp only [Int.cast_one, map_one, one_mul] at h
  exact h

private theorem KP.Rep.sub {B : ℕ} {x y : KP} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q) :
    (x.sub y).Rep B (p - q) := by
  have h := KP.rep_lin hx hy _ _ (-1) rfl (gcd_cross x.s y.s)
  simp only [Int.cast_neg, Int.cast_one, map_neg, map_one, neg_mul, one_mul,
    ← sub_eq_add_neg] at h
  exact h

private theorem KP.Rep.mul {B : ℕ} {x y : KP} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q) :
    (x.mul y).Rep B (p * q) := by
  obtain ⟨hxv, lx, hlx, hbx, hnx⟩ := hx
  obtain ⟨hyv, ly, hly, hby, hny⟩ := hy
  refine ⟨?_, Certificate.mul lx ly, ?_, ?_, ?_⟩
  · simp only [KP.mul, eval_mul, Int.cast_mul, Nat.cast_mul, ← hxv, ← hyv]; ring
  · rw [Certificate.toPoly_mul, hlx, hly]; simp only [KP.mul, Nat.cast_mul, map_mul]; ring
  · exact (absSum_mul lx ly).trans (Nat.mul_le_mul hbx hby)
  · have := length_mul lx ly
    simp only [KP.mul]
    omega

private theorem KP.rep_one {B : ℕ} : KP.one.Rep B 1 :=
  ⟨by simp [KP.one], [1], by simp [toPoly, KP.one], by simp [absSum, KP.one], by simp [KP.one]⟩

private theorem KP.Rep.pow {B : ℕ} {x : KP} {p : ℚ[X]} (hx : x.Rep B p) :
    ∀ k : ℕ, (x.pow k).Rep B (p ^ k)
  | 0 => by rw [pow_zero]; exact KP.rep_one
  | k + 1 => by rw [pow_succ]; exact (hx.pow k).mul hx

private theorem KP.rep_const {B : ℕ} (q : ℚ) : (KP.const q).Rep B (C q) :=
  ⟨by simp [KP.const], [q.num],
    by simp only [toPoly, KP.const, mul_zero, add_zero, ← map_mul, Rat.den_mul_eq_num],
    by simp [absSum, KP.const], by simp [KP.const]⟩

private theorem KP.rep_ofNat {B : ℕ} (m : ℕ) : (KP.ofNat m).Rep B (m : ℚ[X]) :=
  ⟨by simp [KP.ofNat], [(m : ℤ)], by simp [toPoly, KP.ofNat], by simp [absSum, KP.ofNat],
    by simp [KP.ofNat]⟩

private theorem KP.rep_one' {B : ℕ} : (KP.ofNat 1).Rep B 1 := by
  simpa using (KP.rep_ofNat (B := B) 1)

private theorem KP.rep_zero {B : ℕ} : KP.zero.Rep B 0 :=
  ⟨by simp [KP.zero], [], by simp [toPoly, KP.zero], by simp [absSum, KP.zero], by simp [KP.zero]⟩

private theorem KP.rep_var (B : ℕ) : (KP.var B).Rep B X :=
  ⟨by simp [KP.var], [0, 1], by simp [toPoly, KP.var], by simp [absSum, KP.var], by simp [KP.var]⟩

private theorem KP.rep_ofScaled (B : ℕ) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (KP.ofScaled B c).Rep B p := by
  refine ⟨?_, c.l, hc, le_rfl, le_rfl⟩
  have h := eval_toPoly B c.l
  rw [hc, eval_mul, eval_C] at h
  simpa [KP.ofScaled] using h

/-! ## Digits in base `2 ^ k` -/

/-- `x * 2 ^ m`, by a shift. -/
private def shl (x : ℤ) (m : ℕ) : ℤ :=
  match x with
  | .ofNat n => .ofNat (n <<< m)
  | .negSucc n => -.ofNat ((n + 1) <<< m)

private theorem shl_eq (x : ℤ) (m : ℕ) : shl x m = x * 2 ^ m := by
  cases x with
  | ofNat n => simp only [shl, Nat.shiftLeft_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | negSucc n => simp only [shl, Nat.shiftLeft_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring

/-- The remainder of `v` modulo `2 ^ k` in `[-2 ^ (k - 1), 2 ^ (k - 1))` and the quotient, by
masks and shifts. -/
private def bsplit (k : ℕ) (v : ℤ) : ℤ × ℤ :=
  match v with
  | .ofNat n =>
    if (n &&& (2 ^ k - 1)) < 2 ^ (k - 1) then (.ofNat (n &&& (2 ^ k - 1)), .ofNat (n >>> k))
    else (.ofNat (n &&& (2 ^ k - 1)) - .ofNat (2 ^ k), .ofNat (n >>> k) + 1)
  | .negSucc n =>
    if (n &&& (2 ^ k - 1)) < 2 ^ (k - 1) then (-.ofNat (n &&& (2 ^ k - 1)) - 1, -.ofNat (n >>> k))
    else (.ofNat (2 ^ k - 1 - (n &&& (2 ^ k - 1))), -.ofNat (n >>> k) - 1)

private theorem bsplit_spec {k : ℕ} (hk : 1 ≤ k) (v : ℤ) :
    (bsplit k v).1 + 2 ^ k * (bsplit k v).2 = v ∧ -(2 ^ (k - 1) : ℤ) ≤ (bsplit k v).1 ∧
      (bsplit k v).1 < 2 ^ (k - 1) := by
  have hP : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hPz : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by exact_mod_cast hP
  have hP1 : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  cases v with
  | ofNat n =>
    have hdm := Nat.div_add_mod n (2 ^ k)
    have hlt := Nat.mod_lt n (show 0 < 2 ^ k by positivity)
    simp only [bsplit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Int.ofNat_eq_natCast]
    generalize n % 2 ^ k = r at *
    generalize n / 2 ^ k = q at *
    have hdmz : (2 : ℤ) ^ k * (q : ℤ) + (r : ℤ) = n := by exact_mod_cast hdm
    have hltz : (r : ℤ) < 2 ^ k := by exact_mod_cast hlt
    have hr0 : (0 : ℤ) ≤ r := by positivity
    split_ifs with h
    · have h' : (r : ℤ) < 2 ^ (k - 1) := by exact_mod_cast h
      dsimp only
      refine ⟨by linarith, by linarith, h'⟩
    · have h' : (2 : ℤ) ^ (k - 1) ≤ r := by exact_mod_cast not_lt.1 h
      dsimp only
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩
  | negSucc n =>
    have hdm := Nat.div_add_mod n (2 ^ k)
    have hlt := Nat.mod_lt n (show 0 < 2 ^ k by positivity)
    simp only [bsplit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Int.ofNat_eq_natCast, Int.negSucc_eq]
    generalize n % 2 ^ k = r at *
    generalize n / 2 ^ k = q at *
    have hdmz : (2 : ℤ) ^ k * (q : ℤ) + (r : ℤ) = n := by exact_mod_cast hdm
    have hltz : (r : ℤ) < 2 ^ k := by exact_mod_cast hlt
    have hr0 : (0 : ℤ) ≤ r := by positivity
    split_ifs with h
    · have h' : (r : ℤ) < 2 ^ (k - 1) := by exact_mod_cast h
      dsimp only
      refine ⟨by linarith, by linarith, by linarith⟩
    · have h' : (2 : ℤ) ^ (k - 1) ≤ r := by exact_mod_cast not_lt.1 h
      have hle : r ≤ 2 ^ k - 1 := by omega
      dsimp only
      rw [Nat.cast_sub hle, Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩

private theorem bsplit_eq {k : ℕ} (hk : 1 ≤ k) {a w : ℤ} (ha1 : -(2 ^ (k - 1) : ℤ) ≤ a)
    (ha2 : a < 2 ^ (k - 1)) : bsplit k (a + 2 ^ k * w) = (a, w) := by
  obtain ⟨h1, h2, h3⟩ := bsplit_spec hk (a + 2 ^ k * w)
  have hPz : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  have hw : (bsplit k (a + 2 ^ k * w)).2 = w := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (bsplit k (a + 2 ^ k * w)).2 + 1 ≤ w := h
      nlinarith
    · have : w + 1 ≤ (bsplit k (a + 2 ^ k * w)).2 := h
      nlinarith
  refine Prod.ext ?_ hw
  rw [hw] at h1
  linarith

/-- `m` digits of `v` in base `2 ^ k`, the remainders balanced. -/
private def digs (k : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, v => (bsplit k v).1 :: digs k m (bsplit k v).2

private theorem bsplit_cons {k : ℕ} (hk : 1 ≤ k) {a : ℤ} (ha : 2 * a.natAbs < 2 ^ k) (w : ℤ) :
    bsplit k (a + 2 ^ k * w) = (a, w) := by
  have hP : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h : a.natAbs < 2 ^ (k - 1) := by omega
  have h' : (a.natAbs : ℤ) < ((2 ^ (k - 1) : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h'
  push_cast at h'
  exact bsplit_eq hk (by linarith [neg_abs_le a]) (by linarith [le_abs_self a])

private theorem digs_evalZ {k : ℕ} (hk : 1 ≤ k) :
    ∀ (m : ℕ) (l : List ℤ), (∀ x ∈ l, 2 * x.natAbs < 2 ^ k) → l.length ≤ m →
      digs k m (evalZ (2 ^ k) l) = l ++ List.replicate (m - l.length) 0
  | 0, l, _, hl => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]; rfl
  | m + 1, [], _, _ => by
    have h := bsplit_cons hk (a := 0) (by simp) 0
    simp only [mul_zero, add_zero] at h
    have ih := digs_evalZ hk m [] (by simp) (by simp)
    simp only [evalZ] at ih ⊢
    rw [digs, h, ih]
    simp [List.replicate_succ]
  | m + 1, a :: l, hb, hl => by
    have h := bsplit_cons hk (hb a List.mem_cons_self) (evalZ (2 ^ k) l)
    have ih := digs_evalZ hk m l (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (by simp only [List.length_cons] at hl; omega)
    simp only [evalZ]
    rw [digs, h, ih]
    simp

private theorem digs_getD {k : ℕ} (hk : 1 ≤ k) :
    ∀ (m : ℕ) (l : List ℤ), (∀ x ∈ l, 2 * x.natAbs < 2 ^ k) → ∀ i < m,
      (digs k m (evalZ (2 ^ k) l)).getD i 0 = l.getD i 0
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | m + 1, [], _, i, hi => by
    have h := bsplit_cons hk (a := 0) (by simp) 0
    simp only [mul_zero, add_zero] at h
    simp only [evalZ]
    rw [digs, h]
    rcases i with _ | i
    · rfl
    · have ih := digs_getD hk m [] (by simp) i (by omega)
      simp only [evalZ] at ih
      simpa using ih
  | m + 1, a :: l, hb, i, hi => by
    have h := bsplit_cons hk (hb a List.mem_cons_self) (evalZ (2 ^ k) l)
    simp only [evalZ]
    rw [digs, h]
    rcases i with _ | i
    · rfl
    · simpa using digs_getD hk m l (fun x hx => hb x (List.mem_cons_of_mem _ hx)) i (by omega)

private theorem toPoly_append_zeros : ∀ (l : List ℤ) (j : ℕ),
    toPoly (l ++ List.replicate j 0) = toPoly l
  | [], 0 => rfl
  | [], j + 1 => by
    have := toPoly_append_zeros [] j
    simp only [List.nil_append, toPoly] at this ⊢
    rw [List.replicate_succ]
    simp only [toPoly, this, Int.cast_zero, map_zero, mul_zero, add_zero]
  | a :: l, j => by
    rw [List.cons_append, toPoly, toPoly, toPoly_append_zeros l j]

/-- `m` digits of the value: an explicit list. -/
private def KP.digits (k : ℕ) (c : KP) (m : ℕ) : Scaled := ⟨digs k m c.v, c.s⟩

private theorem KP.Rep.witness {k : ℕ} {c : KP} {p : ℚ[X]} (hc : c.Rep (2 ^ k) p) :
    ∃ l : List ℤ, toPoly l = C (c.s : ℚ) * p ∧ absSum l ≤ c.b ∧ l.length ≤ c.n ∧
      evalZ (2 ^ k) l = c.v := by
  obtain ⟨hv, l, hl, hb, hn⟩ := hc
  refine ⟨l, hl, hb, hn, ?_⟩
  have h := eval_toPoly (2 ^ k) l
  rw [hl, eval_mul, eval_C] at h
  push_cast at h hv
  exact_mod_cast h.symm.trans hv

private theorem KP.Rep.digits {k m : ℕ} {c : KP} {p : ℚ[X]} (hk : 1 ≤ k) (hc : c.Rep (2 ^ k) p)
    (hb : 2 * c.b < 2 ^ k) (hm : c.n ≤ m) : (c.digits k m).Rep p := by
  obtain ⟨l, hl, hbl, hn, hv⟩ := hc.witness
  have hd := digs_evalZ hk m l (fun x hx => by have := natAbs_le_absSum hx; omega) (by omega)
  unfold Scaled.Rep
  simp only [KP.digits]
  rw [← hv, hd, toPoly_append_zeros, hl]

private theorem KP.Rep.digits_getD {k m : ℕ} {c : KP} {p : ℚ[X]} (hk : 1 ≤ k)
    (hc : c.Rep (2 ^ k) p) (hb : 2 * c.b < 2 ^ k) {i : ℕ} (hi : i < m) :
    (((c.digits k m).l.getD i 0 : ℤ) : ℚ) = c.s * p.coeff i := by
  obtain ⟨l, hl, hbl, hn, hv⟩ := hc.witness
  have hd := digs_getD hk m l (fun x hx => by have := natAbs_le_absSum hx; omega) i hi
  simp only [KP.digits]
  rw [← hv, hd, ← Certificate.coeff_toPoly, hl, coeff_C_mul]

/-! ## Chebyshev coefficients by the Joukowski map

With `B = 2 ^ k`, `X = B ^ 2 + 1` and `Y = 2 B`, the number `2 ∑ l_i X^i Y^(n-1-i)` equals
`B^(n-1) ∑ u_j (B^j + B^(-j))` for the Chebyshev coefficients `u = chebList l`: its high
digits are `2 u₀, u₁, u₂, …`. -/

/-- `(∑ l_i X^i Y^(n-1-i), n)` for `n = l.length`, `X = 2 ^ (2 k) + 1` and `Y = 2 ^ (k + 1)`. -/
private def kvJ (k : ℕ) : List ℤ → ℤ × ℕ
  | [] => (0, 0)
  | a :: l =>
    (shl a ((kvJ k l).2 * (k + 1)) + shl (kvJ k l).1 (2 * k) + (kvJ k l).1, (kvJ k l).2 + 1)

private theorem kvJ_snd (k : ℕ) : ∀ l : List ℤ, (kvJ k l).2 = l.length
  | [] => rfl
  | a :: l => by simp only [kvJ, kvJ_snd k l, List.length_cons]

private theorem kvJ_cons (k : ℕ) (a : ℤ) (l : List ℤ) :
    (kvJ k (a :: l)).1 = a * (2 ^ (k + 1)) ^ l.length + (2 ^ (2 * k) + 1) * (kvJ k l).1 := by
  simp only [kvJ, shl_eq, kvJ_snd]
  rw [mul_comm l.length (k + 1), pow_mul]
  ring

/-- `∑ l_i (z ^ (j + i) + z⁻¹ ^ (j + i))`. -/
private def jsum (z : ℚ) : ℕ → List ℤ → ℚ
  | _, [] => 0
  | j, a :: l => a * (z ^ j + z⁻¹ ^ j) + jsum z (j + 1) l

private theorem jsum_add (z : ℚ) :
    ∀ (j : ℕ) (l m : List ℤ), jsum z j (Certificate.add l m) = jsum z j l + jsum z j m
  | j, [], m => by simp [Certificate.add, jsum]
  | j, a :: l, [] => by simp [Certificate.add, jsum]
  | j, a :: l, b :: m => by
    simp only [Certificate.add, jsum, jsum_add z (j + 1) l m, Int.cast_add]; ring

private theorem jsum_shift {z : ℚ} (hz : z ≠ 0) :
    ∀ (j : ℕ) (l : List ℤ), jsum z j l + jsum z (j + 2) l = (z + z⁻¹) * jsum z (j + 1) l
  | j, [] => by simp [jsum]
  | j, a :: l => by
    have ih := jsum_shift hz (j + 1) l
    have hw : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    simp only [jsum]
    rw [show j + 2 + 1 = j + 1 + 2 by omega]
    linear_combination ih - ((a : ℚ) * (z ^ j + z⁻¹ ^ j)) * hw

private theorem jsum_twoX {z : ℚ} (hz : z ≠ 0) (u : List ℤ) :
    jsum z 0 (twoX u) = (z + z⁻¹) * jsum z 0 u := by
  cases u with
  | nil => simp [twoX, jsum]
  | cons u0 t =>
    have h := jsum_shift hz 0 t
    simp only [twoX, jsum_add, jsum, Int.cast_zero, Int.cast_mul, Int.cast_ofNat, zero_mul,
      zero_add, pow_zero, pow_one] at h ⊢
    linear_combination h

private theorem jsum_chebList {z : ℚ} (hz : z ≠ 0) (a : ℤ) (l : List ℤ) :
    jsum z 0 (chebList (a :: l)) =
      2 * (a * 2 ^ l.length) + (z + z⁻¹) * jsum z 0 (chebList l) := by
  simp only [Certificate.chebList, jsum_add, jsum_twoX hz]
  simp only [jsum]
  push_cast
  ring

private theorem kvJ_jsum (k : ℕ) : ∀ l : List ℤ,
    2 * (2 : ℚ) ^ k * (kvJ k l).1 = ((2 : ℚ) ^ k) ^ l.length * jsum (2 ^ k) 0 (chebList l)
  | [] => by simp [kvJ, Certificate.chebList, jsum]
  | a :: l => by
    have ih := kvJ_jsum k l
    have hz : (2 : ℚ) ^ k ≠ 0 := by positivity
    have hw : (2 : ℚ) ^ k * ((2 : ℚ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hz
    rw [jsum_chebList hz, kvJ_cons]
    push_cast
    rw [pow_succ (2 : ℚ) k, mul_comm 2 k, pow_mul, List.length_cons]
    linear_combination (((2 : ℚ) ^ k) ^ 2 + 1) * ih -
      (((2 : ℚ) ^ k) ^ l.length * jsum (2 ^ k) 0 (chebList l)) * hw

/-- The two halves of `jsum`. -/
private def jpos (z : ℚ) : ℕ → List ℤ → ℚ
  | _, [] => 0
  | j, a :: l => a * z ^ j + jpos z (j + 1) l

private def jneg (z : ℚ) : ℕ → List ℤ → ℚ
  | _, [] => 0
  | j, a :: l => a * z⁻¹ ^ j + jneg z (j + 1) l

private theorem jsum_eq (z : ℚ) : ∀ (j : ℕ) (l : List ℤ), jsum z j l = jpos z j l + jneg z j l
  | _, [] => by simp [jsum, jpos, jneg]
  | j, a :: l => by simp only [jsum, jpos, jneg, jsum_eq z (j + 1) l]; ring

private theorem jpos_eq (k : ℕ) :
    ∀ (j : ℕ) (l : List ℤ), jpos (2 ^ k) j l = ((2 : ℚ) ^ k) ^ j * (evalZ (2 ^ k) l : ℚ)
  | _, [] => by simp [jpos, evalZ]
  | j, a :: l => by simp only [jpos, evalZ, jpos_eq k (j + 1) l]; push_cast; ring

private theorem jneg_le {z : ℚ} (hz : 1 ≤ z) :
    ∀ (j : ℕ) (l : List ℤ), |jneg z j l| ≤ z⁻¹ ^ j * absSum l
  | _, [] => by simp [jneg, absSum]
  | j, a :: l => by
    have ih := jneg_le hz (j + 1) l
    have h0 : 0 ≤ z⁻¹ := by positivity
    have h1 : z⁻¹ ^ (j + 1) ≤ z⁻¹ ^ j :=
      pow_le_pow_of_le_one h0 (inv_le_one_of_one_le₀ hz) (by omega)
    have h2 : (0 : ℚ) ≤ absSum l := by positivity
    simp only [jneg, absSum]
    push_cast
    rw [Nat.cast_natAbs]
    calc |a * z⁻¹ ^ j + jneg z (j + 1) l| ≤ |(a : ℚ) * z⁻¹ ^ j| + |jneg z (j + 1) l| :=
          abs_add_le _ _
      _ ≤ |(a : ℚ)| * z⁻¹ ^ j + z⁻¹ ^ j * absSum l := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg h0 j)]
          gcongr
          exact ih.trans (mul_le_mul_of_nonneg_right h1 h2)
      _ = z⁻¹ ^ j * (((|a| : ℤ) : ℚ) + absSum l) := by push_cast; ring

private theorem length_twoX (u0 : ℤ) (t : List ℤ) : (twoX (u0 :: t)).length = t.length + 2 := by
  simp only [twoX, length_add, List.length_cons]; omega

private theorem length_chebList : ∀ l : List ℤ, (chebList l).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_chebList l
    simp only [Certificate.chebList, length_add, List.length_cons, List.length_nil]
    cases h : chebList l with
    | nil => rw [h] at ih; simp only [List.length_nil] at ih; simp [twoX, ← ih]
    | cons u0 t => rw [length_twoX]; rw [h] at ih; simp only [List.length_cons] at ih; omega

private theorem absSum_twoX : ∀ u : List ℤ, absSum (twoX u) ≤ 2 * absSum u
  | [] => by simp [twoX, absSum]
  | u0 :: t => by
    have h := absSum_add t (0 :: (2 * u0) :: t)
    simp only [twoX, absSum, Int.natAbs_zero, Int.natAbs_mul, zero_add] at h ⊢
    have h2 : (2 : ℤ).natAbs = 2 := rfl
    rw [h2] at h
    omega

private theorem absSum_chebList : ∀ l : List ℤ, absSum (chebList l) ≤ 2 ^ l.length * absSum l
  | [] => by simp [Certificate.chebList, absSum]
  | a :: l => by
    have ih := absSum_chebList l
    have h1 := absSum_add [a * ((2 ^ l.length : ℕ) : ℤ)] (twoX (chebList l))
    have h2 := absSum_twoX (chebList l)
    simp only [absSum, Int.natAbs_mul, Int.natAbs_natCast, Nat.add_zero] at h1
    simp only [Certificate.chebList, absSum, List.length_cons, pow_succ]
    calc _ ≤ _ := h1
      _ ≤ a.natAbs * 2 ^ l.length + 2 * (2 ^ l.length * absSum l) := by omega
      _ ≤ 2 ^ l.length * 2 * (a.natAbs + absSum l) := by
          nlinarith [Nat.zero_le (a.natAbs * 2 ^ l.length)]

/-- `(2 u₀, ∑_{j ≥ 1} |u_j|)` for the Chebyshev coefficients `u = chebList l`, read from the
digits of `2 kvJ`. -/
private def chebLow (k : ℕ) (l : List ℤ) : ℤ × ℕ :=
  ((digs k l.length (bsplit (k * (l.length - 1)) (2 * (kvJ k l).1)).2).headD 0,
    absSum (digs k l.length (bsplit (k * (l.length - 1)) (2 * (kvJ k l).1)).2).tail)

private theorem chebLow_eq {k : ℕ} (hk : 1 ≤ k) {l : List ℤ} (hn : 2 ≤ l.length)
    (hb : 4 * 2 ^ l.length * absSum l < 2 ^ k) :
    chebLow k l = (2 * (chebList l).headD 0, absSum (chebList l).tail) := by
  have hlen := length_chebList l
  have hA : 4 * absSum (chebList l) < 2 ^ k := by
    have := absSum_chebList l; nlinarith
  obtain ⟨u0, t, hut⟩ : ∃ u0 t, chebList l = u0 :: t := by
    cases h : chebList l with
    | nil => rw [h] at hlen; simp only [List.length_nil] at hlen; omega
    | cons u0 t => exact ⟨u0, t, rfl⟩
  rw [hut] at hlen hA ⊢
  simp only [List.length_cons, absSum] at hlen hA
  have hJ := kvJ_jsum k l
  rw [hut, jsum, jsum_eq, jpos_eq] at hJ
  set N := l.length - 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hlN : l.length = N + 1 := by omega
  have hB1 : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hB0 : (2 : ℚ) ^ k ≠ 0 := by positivity
  -- the high and low parts
  set Hi : ℤ := evalZ (2 ^ k) (2 * u0 :: t) with hHi
  set Lo : ℤ := 2 * (kvJ k l).1 - 2 ^ (k * N) * Hi with hLo
  have hLoq : (Lo : ℚ) = ((2 : ℚ) ^ k) ^ N * jneg (2 ^ k) (0 + 1) t := by
    have e : (2 : ℚ) ^ k * (2 * (kvJ k l).1) =
        (2 : ℚ) ^ k * (((2 : ℚ) ^ k) ^ N * Hi + ((2 : ℚ) ^ k) ^ N * jneg (2 ^ k) (0 + 1) t) := by
      rw [← mul_assoc, mul_comm _ (2 : ℚ), hJ, hlN, hHi]
      simp only [evalZ]
      push_cast
      ring
    have e' := mul_left_cancel₀ hB0 e
    rw [hLo]; push_cast
    rw [pow_mul, e']; ring
  have hLob : 2 * |(Lo : ℚ)| < ((2 : ℚ) ^ k) ^ N := by
    rw [hLoq, abs_mul, abs_of_nonneg (by positivity)]
    have h1 := jneg_le hB1 (0 + 1) t
    have h2 : (4 : ℚ) * absSum t < 2 ^ k := by
      have : 4 * absSum t < 2 ^ k := by omega
      exact_mod_cast this
    have h3 : ((2 : ℚ) ^ k)⁻¹ ^ (0 + 1) * (2 ^ k) = 1 := by simp [hB0]
    have hpos : (0 : ℚ) < ((2 : ℚ) ^ k) ^ N := by positivity
    calc 2 * (((2 : ℚ) ^ k) ^ N * |jneg (2 ^ k) (0 + 1) t|)
        ≤ 2 * (((2 : ℚ) ^ k) ^ N * (((2 : ℚ) ^ k)⁻¹ ^ (0 + 1) * absSum t)) := by gcongr
      _ < ((2 : ℚ) ^ k) ^ N := by
          have : ((2 : ℚ) ^ k)⁻¹ ^ (0 + 1) * absSum t < 1 / 2 := by
            rw [zero_add, pow_one, inv_mul_lt_iff₀ (by positivity)]; linarith
          nlinarith
  have hkN : 1 ≤ k * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hsplit : bsplit (k * N) (2 * (kvJ k l).1) = (Lo, Hi) := by
    have e : 2 * (kvJ k l).1 = Lo + 2 ^ (k * N) * Hi := by rw [hLo]; ring
    have hP : (2 : ℤ) ^ (k * N) = 2 * 2 ^ (k * N - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hLoz : 2 * |Lo| < 2 ^ (k * N) := by
      have : ((2 * |Lo| : ℤ) : ℚ) < ((2 ^ (k * N) : ℤ) : ℚ) := by
        push_cast; rw [pow_mul]; exact hLob
      exact_mod_cast this
    rw [e]
    exact bsplit_eq hkN (by linarith [neg_abs_le Lo]) (by linarith [le_abs_self Lo])
  have hdigs : digs k l.length Hi = 2 * u0 :: t := by
    have hb' : ∀ x ∈ 2 * u0 :: t, 2 * x.natAbs < 2 ^ k := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [Int.natAbs_mul]; simp only [Int.reduceAbs]; omega
      · have := natAbs_le_absSum hx; omega
    have := digs_evalZ hk l.length (2 * u0 :: t) hb' (by simp; omega)
    rw [hHi, this]
    simp; omega
  simp only [chebLow, hsplit, hdigs, ← hN, List.headD_cons, List.tail_cons]

private theorem sum_abs_getD : ∀ (D : ℕ) (t : List ℤ), t.length ≤ D →
    ∑ j : Fin D, |t.getD j.val 0| = (absSum t : ℤ)
  | 0, t, h => by rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]; simp [absSum]
  | D + 1, [], _ => by simp [absSum]
  | D + 1, a :: t, h => by
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons] at h
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
      sum_abs_getD D t (by omega), absSum, Nat.cast_add, Int.natCast_natAbs]

private theorem lowerZ_eq {D : ℕ} {u : List ℤ} (hu : u.length ≤ D + 1) :
    lowerZ D (fun j => u.getD j 0) = u.headD 0 - absSum u.tail := by
  cases u with
  | nil => simp [lowerZ, absSum]
  | cons a t =>
    simp only [List.length_cons] at hu
    simp only [lowerZ, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, List.tail_cons,
      sum_abs_getD D t (by omega)]

private theorem upperZ_eq {D : ℕ} {u : List ℤ} (hu : u.length ≤ D + 1) :
    upperZ D (fun j => u.getD j 0) = u.headD 0 + absSum u.tail := by
  cases u with
  | nil => simp [upperZ, absSum]
  | cons a t =>
    simp only [List.length_cons] at hu
    simp only [upperZ, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, List.tail_cons,
      sum_abs_getD D t (by omega)]

/-- The checks of `r < lowerOn D a b p` for an explicit list `c` of `centered a b p`. -/
private def lowOK (k D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (1 ≤ k) && decide (2 ≤ c.l.length) && decide (c.l.length ≤ D + 1) && decide (0 < c.s) &&
    decide (4 * 2 ^ c.l.length * absSum c.l < 2 ^ k) &&
    decide (r.num * c.s * 2 ^ c.l.length < r.den * ((chebLow k c.l).1 - 2 * (chebLow k c.l).2))

/-- The checks of `upperOn D a b p < r` for an explicit list `c` of `centered a b p`. -/
private def upOK (k D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (1 ≤ k) && decide (2 ≤ c.l.length) && decide (c.l.length ≤ D + 1) && decide (0 < c.s) &&
    decide (4 * 2 ^ c.l.length * absSum c.l < 2 ^ k) &&
    decide (r.den * ((chebLow k c.l).1 + 2 * (chebLow k c.l).2) < r.num * c.s * 2 ^ c.l.length)

private theorem lowOK_spec {k D : ℕ} {c : Scaled} {r a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (centered a b p)) (h : lowOK k D c r = true) :
    r < lowerOn D a b p ∧ centered a b p = expansion D (centered a b p) := by
  simp only [lowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hk, hn⟩, hD⟩, hs⟩, hb⟩, hr⟩ := h
  have hs' : c.s ≠ 0 := by omega
  refine ⟨?_, hc.eq_expansion hs' hD⟩
  rw [Certificate.lowerOn_eq_of_rep hc hs' hD,
    lowerZ_eq (by rw [length_chebList]; exact hD), lt_div_iff₀ (Certificate.scale_pos hs')]
  rw [chebLow_eq hk hn hb] at hr
  have hd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hr' := (Int.cast_lt (R := ℚ)).2 hr
  push_cast at hr' ⊢
  rw [← Rat.num_div_den r]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
  linarith

private theorem upOK_spec {k D : ℕ} {c : Scaled} {r a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (centered a b p)) (h : upOK k D c r = true) :
    upperOn D a b p < r ∧ centered a b p = expansion D (centered a b p) := by
  simp only [upOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hk, hn⟩, hD⟩, hs⟩, hb⟩, hr⟩ := h
  have hs' : c.s ≠ 0 := by omega
  refine ⟨?_, hc.eq_expansion hs' hD⟩
  rw [Certificate.upperOn_eq_of_rep hc hs' hD,
    upperZ_eq (by rw [length_chebList]; exact hD), div_lt_iff₀ (Certificate.scale_pos hs')]
  rw [chebLow_eq hk hn hb] at hr
  have hd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hr' := (Int.cast_lt (R := ℚ)).2 hr
  push_cast at hr' ⊢
  rw [← Rat.num_div_den r, div_mul_eq_mul_div, lt_div_iff₀ hd]
  linarith

/-! ## Newton steps on explicit lists -/

private theorem rep_coeff_mul {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (j : ℕ) :
    (a.s : ℚ) * p.coeff j = (a.l.getD j 0 : ℚ) := by
  have h := congrArg (fun q : ℚ[X] => q.coeff j) ha
  simp only [Certificate.coeff_toPoly, coeff_C_mul] at h
  exact h.symm

private def gcdAcc : List ℤ → ℕ → ℕ
  | [], g => g
  | x :: l, g => gcdAcc l (Nat.gcd x.natAbs g)

private theorem gcdAcc_dvd_acc : ∀ (l : List ℤ) (g : ℕ), gcdAcc l g ∣ g
  | [], _ => dvd_rfl
  | _ :: l, _ => (gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_right _ _)

private theorem gcdAcc_dvd_mem : ∀ (l : List ℤ) (g : ℕ), ∀ x ∈ l, ((gcdAcc l g : ℕ) : ℤ) ∣ x
  | [], _, _, hx => by simp at hx
  | _ :: l, _, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.natCast_dvd.2 ((gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_left _ _))
    · exact gcdAcc_dvd_mem l _ x hx

private theorem toPoly_map_div (g : ℤ) : ∀ l : List ℤ, (∀ x ∈ l, g ∣ x) →
    toPoly l = C (g : ℚ) * toPoly (l.map (fun x => x / g))
  | [], _ => by simp [toPoly]
  | x :: l, h => by
    have hx : (x : ℚ) = (g : ℚ) * ((x / g : ℤ) : ℚ) := by
      rw [← Int.cast_mul, Int.mul_ediv_cancel' (h x List.mem_cons_self)]
    rw [List.map_cons, toPoly, toPoly,
      toPoly_map_div g l (fun y hy => h y (List.mem_cons_of_mem _ hy)), hx, C_mul]
    ring

private theorem toPoly_map_div_zero : ∀ l : List ℤ, toPoly (l.map (fun x => x / (0 : ℤ))) = 0
  | [] => by simp [toPoly]
  | x :: l => by rw [List.map_cons, toPoly, toPoly_map_div_zero l, Int.ediv_zero]; simp

/-- The list and its scale divided by the gcd of the entries and the scale. -/
private def nrm (a : Scaled) : Scaled :=
  ⟨a.l.map (fun x => x / ((gcdAcc a.l a.s : ℕ) : ℤ)), a.s / gcdAcc a.l a.s⟩

private theorem rep_nrm {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : (nrm a).Rep p := by
  unfold Scaled.Rep at *
  rw [nrm]
  have h1 := toPoly_map_div ((gcdAcc a.l a.s : ℕ) : ℤ) a.l (gcdAcc_dvd_mem a.l a.s)
  have h2 : gcdAcc a.l a.s ∣ a.s := gcdAcc_dvd_acc a.l a.s
  generalize gcdAcc a.l a.s = g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hs : a.s = 0 := Nat.eq_zero_of_zero_dvd h2
    simp only [Nat.cast_zero, Nat.div_zero, map_zero, zero_mul] at h1 ⊢
    exact toPoly_map_div_zero a.l
  · have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hdiv : ((a.s / g : ℕ) : ℚ) = (a.s : ℚ) / g := Nat.cast_div h2 hgq
    apply mul_left_cancel₀ (show (C (g : ℚ) : ℚ[X]) ≠ 0 from C_ne_zero.2 hgq)
    push_cast at h1
    rw [← h1, ha, hdiv, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hgq]

/-- The first four entries. -/
private def trunc4 (a : Scaled) : Scaled :=
  ⟨[a.l.getD 0 0, a.l.getD 1 0, a.l.getD 2 0, a.l.getD 3 0], a.s⟩

private theorem rep_trunc4 {a : Scaled} {p : ℚ[X]}
    (h : ∀ j < 4, (a.l.getD j 0 : ℚ) = a.s * p.coeff j) :
    (trunc4 a).Rep (SoleScalarPolynomials.truncateThree p) := by
  unfold Scaled.Rep trunc4 SoleScalarPolynomials.truncateThree
  simp only [toPoly]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]
  simp only [C_mul, mul_zero, add_zero]
  ring

/-- `C (p.coeff 0)`. -/
private def const0 (a : Scaled) : Scaled := ⟨[a.l.getD 0 0], a.s⟩

private theorem rep_const0 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (const0 a).Rep (C (p.coeff 0)) := by
  unfold Scaled.Rep const0
  simp only [toPoly, mul_zero, add_zero]
  rw [← rep_coeff_mul ha 0, C_mul]

/-- `C (1 / p.coeff 0)`, when the constant coefficient is positive. -/
private def inv0 (a : Scaled) : Scaled := ⟨[(a.s : ℤ)], (a.l.getD 0 0).toNat⟩

private theorem rep_inv0 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0 < a.l.getD 0 0) (hs : a.s ≠ 0) : (inv0 a).Rep (C (1 / p.coeff 0)) := by
  unfold Scaled.Rep inv0
  have h := rep_coeff_mul ha 0
  have hs' : (a.s : ℚ) ≠ 0 := by exact_mod_cast hs
  have hl' : ((a.l.getD 0 0).toNat : ℚ) = (a.l.getD 0 0 : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hl.le
  have hp : p.coeff 0 = (a.l.getD 0 0 : ℚ) / a.s := by field_simp; linarith
  have hl0 : (a.l.getD 0 0 : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  simp only [toPoly, mul_zero, add_zero, Int.cast_natCast]
  rw [← C_mul, hl', hp]
  congr 1
  field_simp

/-- Integer numerator and denominator of the Newton iterates for `l0 / s`. -/
private def newtonPair (l0 : ℤ) (s : ℕ) : ℕ → ℤ × ℕ
  | 0 => (1, 1)
  | j + 1 =>
    let x := newtonPair l0 s j
    (x.1 ^ 2 * s + l0 * x.2 ^ 2, 2 * x.1.toNat * x.2 * s)

private theorem newtonPair_spec {l0 : ℤ} {s : ℕ} (hl : 0 < l0) (hs : 0 < s) :
    ∀ j, 0 < (newtonPair l0 s j).1 ∧ 0 < (newtonPair l0 s j).2 ∧
      SoleScalarPolynomials.newton ((l0 : ℚ) / s) j =
        ((newtonPair l0 s j).1 : ℚ) / (newtonPair l0 s j).2
  | 0 => by simp [newtonPair, SoleScalarPolynomials.newton]
  | j + 1 => by
    obtain ⟨h1, h2, h3⟩ := newtonPair_spec hl hs j
    simp only [newtonPair, SoleScalarPolynomials.newton]
    generalize newtonPair l0 s j = x at h1 h2 h3 ⊢
    obtain ⟨P, Q⟩ := x
    simp only at h1 h2 h3 ⊢
    have hP : ((P.toNat : ℕ) : ℚ) = (P : ℚ) := by exact_mod_cast Int.toNat_of_nonneg h1.le
    have hPn : 0 < P.toNat := by omega
    have hQz : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast h2
    refine ⟨add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (Int.natCast_nonneg _))
      (mul_pos hl (pow_pos hQz 2)), Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hPn) h2) hs, ?_⟩
    rw [h3]
    push_cast
    rw [hP]
    have hP0 : (P : ℚ) ≠ 0 := by exact_mod_cast h1.ne'
    have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast h2.ne'
    have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp

/-- `C (newton (p.coeff 0) 3)`. -/
private def newton3 (a : Scaled) : Scaled :=
  ⟨[(newtonPair (a.l.getD 0 0) a.s 3).1], (newtonPair (a.l.getD 0 0) a.s 3).2⟩

private theorem rep_newton3 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0 < a.l.getD 0 0) (hs : a.s ≠ 0) :
    (newton3 a).Rep (C (SoleScalarPolynomials.newton (p.coeff 0) 3)) := by
  unfold Scaled.Rep newton3
  have h := rep_coeff_mul ha 0
  have hs' : (a.s : ℚ) ≠ 0 := by exact_mod_cast hs
  have hp : p.coeff 0 = (a.l.getD 0 0 : ℚ) / a.s := by field_simp; linarith
  obtain ⟨_, h2, h3⟩ := newtonPair_spec hl (Nat.pos_of_ne_zero hs) 3
  have hQ : ((newtonPair (a.l.getD 0 0) a.s 3).2 : ℚ) ≠ 0 := by exact_mod_cast h2.ne'
  simp only [toPoly, mul_zero, add_zero]
  rw [hp, h3, ← C_mul]
  congr 1
  field_simp

/-! ## The scalars, packed

`fK k s cn` packs `(f s).comp (aff s cn)` at the base `2 ^ k`: the polynomial itself when
`cn = false`, its centered polynomial on `[0, length s]` when `cn = true`. -/

private def aff (s : ScalarCase) (cn : Bool) : ℚ[X] := if cn then affine 0 (length s) else X

/-- `C a + X`, composed. -/
private def affK (k : ℕ) (s : ScalarCase) (cn : Bool) (a : ℚ) : KP :=
  if cn then (KP.const (a + length s / 2)).add ((KP.const (length s / 2)).mul (KP.var (2 ^ k)))
  else (KP.const a).add (KP.var (2 ^ k))

private theorem affK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (a : ℚ) :
    (affK k s cn a).Rep (2 ^ k) ((C a + X).comp (aff s cn)) := by
  unfold affK aff
  split_ifs
  · have e : (C a + X).comp (affine 0 (length s)) = C (a + length s / 2) + C (length s / 2) * X := by
      simp only [add_comp, C_comp, X_comp, affine, zero_add, sub_zero, C_add]; ring
    rw [e]
    exact (KP.rep_const _).add ((KP.rep_const _).mul (KP.rep_var _))
  · rw [comp_X]
    exact (KP.rep_const _).add (KP.rep_var _)

/-- `a₀ - q (a₁ - q (a₂ - ⋯))`. -/
private def hornerK (q : KP) : List ℚ → KP
  | [] => KP.zero
  | [a] => KP.const a
  | a :: l => (KP.const a).sub (q.mul (hornerK q l))

private def hornerP (Q : ℚ[X]) : List ℚ → ℚ[X]
  | [] => 0
  | [a] => C a
  | a :: l => C a - Q * hornerP Q l

private theorem hornerK_rep {B : ℕ} {q : KP} {Q : ℚ[X]} (hq : q.Rep B Q) :
    ∀ l : List ℚ, (hornerK q l).Rep B (hornerP Q l)
  | [] => KP.rep_zero
  | [a] => KP.rep_const a
  | a :: b :: l => (KP.rep_const a).sub (hq.mul (hornerK_rep hq (b :: l)))

/-- `PositiveScalarPolynomials.sine` composed with `q`, by Horner's rule in `q ^ 2`. -/
private def sineK (q : KP) : KP :=
  q.mul (hornerK (q.mul q) [1, 1/6, 1/120, 1/5040, 1/362880, 1/39916800, 1/6227020800,
    1/1307674368000])

/-- `PositiveScalarPolynomials.cosine` composed with `q`. -/
private def cosineK (q : KP) : KP :=
  hornerK (q.mul q) [1, 1/2, 1/24, 1/720, 1/40320, 1/3628800, 1/479001600, 1/87178291200,
    1/20922789888000]

private theorem sineK_rep {B : ℕ} {q : KP} {Q : ℚ[X]} (hq : q.Rep B Q) :
    (sineK q).Rep B (PositiveScalarPolynomials.sine.comp Q) := by
  have e : PositiveScalarPolynomials.sine.comp Q = Q * hornerP (Q * Q) [1, 1/6, 1/120, 1/5040,
      1/362880, 1/39916800, 1/6227020800, 1/1307674368000] := by
    simp only [hornerP, PositiveScalarPolynomials.sine, sub_comp, add_comp, mul_comp, C_comp,
      X_comp, pow_comp, map_one]
    ring
  rw [e]
  exact hq.mul (hornerK_rep (hq.mul hq) _)

private theorem cosineK_rep {B : ℕ} {q : KP} {Q : ℚ[X]} (hq : q.Rep B Q) :
    (cosineK q).Rep B (PositiveScalarPolynomials.cosine.comp Q) := by
  have e : PositiveScalarPolynomials.cosine.comp Q = hornerP (Q * Q) [1, 1/2, 1/24, 1/720, 1/40320,
      1/3628800, 1/479001600, 1/87178291200, 1/20922789888000] := by
    simp only [hornerP, PositiveScalarPolynomials.cosine, sub_comp, add_comp, mul_comp, C_comp,
      X_comp, pow_comp, one_comp, map_one]
    ring
  rw [e]
  exact hornerK_rep (hq.mul hq) _

private def parK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP := affK k s cn (origin s)

private theorem parK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (parK k s cn).Rep (2 ^ k) ((parameter s).comp (aff s cn)) := affK_rep k s cn _

private def sinK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP := sineK (parK k s cn)
private def cosK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP := cosineK (parK k s cn)

private theorem sinK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (sinK k s cn).Rep (2 ^ k) ((sine s).comp (aff s cn)) := by
  rw [sine, comp_assoc]; exact sineK_rep (parK_rep k s cn)

private theorem cosK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (cosK k s cn).Rep (2 ^ k) ((cosine s).comp (aff s cn)) := by
  rw [cosine, comp_assoc]; exact cosineK_rep (parK_rep k s cn)

private def quadK (k : ℕ) (s : ScalarCase) (cn : Bool) (a b c : ℚ) : KP :=
  ((KP.const a).add ((KP.const b).mul (parK k s cn))).add ((KP.const c).mul ((parK k s cn).pow 2))

private theorem quadK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (a b c : ℚ) :
    (quadK k s cn a b c).Rep (2 ^ k)
      ((C a + C b * parameter s + C c * (parameter s) ^ 2).comp (aff s cn)) := by
  simp only [add_comp, mul_comp, C_comp, pow_comp]
  exact ((KP.rep_const a).add ((KP.rep_const b).mul (parK_rep k s cn))).add
    ((KP.rep_const c).mul ((parK_rep k s cn).pow 2))

private theorem lin_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (a b : ℚ) :
    ((KP.const a).add ((KP.const b).mul (parK k s cn))).Rep (2 ^ k)
      ((C a + C b * parameter s).comp (aff s cn)) := by
  simp only [add_comp, mul_comp, C_comp]
  exact (KP.rep_const a).add ((KP.rep_const b).mul (parK_rep k s cn))

private def kK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  if band s = .low then quadK k s cn (17253/20000) (67/100) (27/100) else KP.ofNat 1

private theorem kK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (kK k s cn).Rep (2 ^ k) ((ExceptionalEPolynomials.k s).comp (aff s cn)) := by
  unfold kK ExceptionalEPolynomials.k
  split_ifs
  · exact quadK_rep k s cn _ _ _
  · rw [one_comp]; exact KP.rep_one'

private def ellK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  match band s with
  | .low => quadK k s cn (50521/100000) (21/25) (1/2)
  | .middle => quadK k s cn (551/1000) (67/100) (21/100)
  | .high => (KP.const (7/10)).add ((KP.const (8/25)).mul (parK k s cn))

private theorem ellK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (ellK k s cn).Rep (2 ^ k) ((ell s).comp (aff s cn)) := by
  unfold ellK ell
  generalize band s = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · exact quadK_rep k s cn _ _ _
  · exact lin_rep k s cn _ _

private def cK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  match band s with
  | .low => quadK k s cn (17253/20000) (18/25) (3/10)
  | .middle => quadK k s cn (891/1000) (16/25) (1/50)
  | .high => KP.const (113/100)

private theorem cK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (cK k s cn).Rep (2 ^ k) ((c s).comp (aff s cn)) := by
  unfold cK c
  generalize band s = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · exact quadK_rep k s cn _ _ _
  · rw [C_comp]; exact KP.rep_const _

private def etaK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  match band s with
  | .low => quadK k s cn (131/500) (19/100) (2/25)
  | .middle => ((KP.const (61/200)).sub ((KP.const (1/50)).mul (parK k s cn))).add
      ((KP.const (7/200)).mul ((parK k s cn).pow 2))
  | .high => (KP.const (27/100)).add ((KP.const (2/25)).mul (parK k s cn))

private theorem etaK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (etaK k s cn).Rep (2 ^ k) ((eta s).comp (aff s cn)) := by
  unfold etaK eta
  generalize band s = b
  cases b
  · exact quadK_rep k s cn _ _ _
  · simp only [add_comp, sub_comp, mul_comp, C_comp, pow_comp]
    exact ((KP.rep_const _).sub ((KP.rep_const _).mul (parK_rep k s cn))).add
      ((KP.rep_const _).mul ((parK_rep k s cn).pow 2))
  · exact lin_rep k s cn _ _

private def pK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  (cosK k s cn).add ((etaK k s cn).mul (sinK k s cn))

private theorem pK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (pK k s cn).Rep (2 ^ k) ((p s).comp (aff s cn)) := by
  rw [p, add_comp, mul_comp]
  exact (cosK_rep k s cn).add ((etaK_rep k s cn).mul (sinK_rep k s cn))

private def firstK (k : ℕ) (s : ScalarCase) (cn : Bool) : Fin 4 → KP :=
  ![pK k s cn, kK k s cn, ellK k s cn, KP.ofNat 1]

private def secondK (k : ℕ) (s : ScalarCase) (cn : Bool) : Fin 4 → KP :=
  ![kK k s cn, ellK k s cn, cK k s cn, cK k s cn]

private theorem one_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (KP.ofNat 1).Rep (2 ^ k) ((1 : ℚ[X]).comp (aff s cn)) := by
  rw [one_comp]; exact KP.rep_one'

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

private def nuK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  ![KP.const (53/50), ellK k s cn, cK k s cn, cK k s cn] (negativeIndex s)

private theorem nuK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (nuK k s cn).Rep (2 ^ k) ((nu s).comp (aff s cn)) := by
  unfold nuK nu
  generalize negativeIndex s = i
  fin_cases i
  · show (KP.const (53/50)).Rep (2 ^ k) ((C (53/50)).comp (aff s cn))
    rw [C_comp]; exact KP.rep_const _
  · exact ellK_rep k s cn
  · exact cK_rep k s cn
  · exact cK_rep k s cn

private def outsideK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  (((((((KP.ofNat 3).mul (kK k s cn)).add ((KP.ofNat 2).mul (ellK k s cn))).add
    ((KP.ofNat 3).mul (cK k s cn))).add (KP.ofNat 1)).add ((KP.ofNat 2).mul (cosK k s cn))).add
    (((KP.ofNat 1).add ((KP.ofNat 2).mul (etaK k s cn))).mul (sinK k s cn))).add
    ((nuK k s cn).mul ((cosK k s cn).sub (KP.ofNat 1)))

private theorem outsideK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) :
    (outsideK k s cn).Rep (2 ^ k) ((outside s).comp (aff s cn)) := by
  have h1 : (KP.ofNat 1).Rep (2 ^ k) (1 : ℚ[X]) := KP.rep_one'
  have h2 : (KP.ofNat 2).Rep (2 ^ k) ((2 : ℕ) : ℚ[X]) := KP.rep_ofNat 2
  have h3 : (KP.ofNat 3).Rep (2 ^ k) ((3 : ℕ) : ℚ[X]) := KP.rep_ofNat 3
  unfold outsideK outside
  simp only [add_comp, mul_comp, sub_comp, one_comp, ofNat_comp]
  exact ((((((h3.mul (kK_rep k s cn)).add (h2.mul (ellK_rep k s cn))).add
    (h3.mul (cK_rep k s cn))).add h1).add (h2.mul (cosK_rep k s cn))).add
    ((h1.add (h2.mul (etaK_rep k s cn))).mul (sinK_rep k s cn))).add
    ((nuK_rep k s cn).mul ((cosK_rep k s cn).sub h1))

private def squaredNormK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 4) : KP :=
  if i = negativeIndex s then
    (((firstK k s cn i).pow 2).add ((secondK k s cn i).pow 2)).sub
      ((((KP.ofNat 2).mul (firstK k s cn i)).mul (secondK k s cn i)).mul (sinK k s cn))
  else ((firstK k s cn i).pow 2).add ((secondK k s cn i).pow 2)

private theorem squaredNormK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 4) :
    (squaredNormK k s cn i).Rep (2 ^ k) ((squaredNorm s i).comp (aff s cn)) := by
  unfold squaredNormK squaredNorm
  split_ifs
  · simp only [add_comp, sub_comp, mul_comp, pow_comp, ofNat_comp]
    exact (((firstK_rep k s cn i).pow 2).add ((secondK_rep k s cn i).pow 2)).sub
      ((((KP.rep_ofNat 2).mul (firstK_rep k s cn i)).mul (secondK_rep k s cn i)).mul
        (sinK_rep k s cn))
  · simp only [add_comp, pow_comp, sub_zero]
    exact ((firstK_rep k s cn i).pow 2).add ((secondK_rep k s cn i).pow 2)

private def rowSquareK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : KP :=
  if hi : i.val < 4 then squaredNormK k s cn ⟨i.val, hi⟩ else (KP.ofNat 1).add ((etaK k s cn).pow 2)

private theorem rowSquareK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) :
    (rowSquareK k s cn i).Rep (2 ^ k) ((rowSquare s i).comp (aff s cn)) := by
  unfold rowSquareK rowSquare
  split_ifs
  · exact squaredNormK_rep k s cn _
  · rw [add_comp, pow_comp]
    exact (one_rep k s cn).add ((etaK_rep k s cn).pow 2)

private def rowWeightK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : KP :=
  if i.val < 4 then KP.ofNat 1 else sinK k s cn

private theorem rowWeightK_rep (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) :
    (rowWeightK k s cn i).Rep (2 ^ k) ((rowWeight s i).comp (aff s cn)) := by
  unfold rowWeightK rowWeight
  split_ifs
  · exact one_rep k s cn
  · exact sinK_rep k s cn

/-! ### The Newton masses -/

/-- The four low digits of a packed polynomial. -/
private def low4 (k : ℕ) (c : KP) : Scaled := trunc4 (c.digits k 4)

private theorem low4_rep {k : ℕ} {c : KP} {q : ℚ[X]} (hk : 1 ≤ k) (hc : c.Rep (2 ^ k) q)
    (hb : 2 * c.b < 2 ^ k) : (low4 k c).Rep (SoleScalarPolynomials.truncateThree q) :=
  rep_trunc4 fun _ hj => hc.digits_getD hk hb hj

private def massInnerK (k : ℕ) (a : Scaled) : KP :=
  (KP.ofScaled (2 ^ k) (newton3 a)).mul
    ((((KP.ofNat 1).add ((KP.const (1/2)).mul ((KP.ofScaled (2 ^ k) (inv0 a)).mul
      ((KP.ofScaled (2 ^ k) a).sub (KP.ofScaled (2 ^ k) (const0 a)))))).sub
      ((KP.const (1/8)).mul (((KP.ofScaled (2 ^ k) (inv0 a)).mul
      ((KP.ofScaled (2 ^ k) a).sub (KP.ofScaled (2 ^ k) (const0 a)))).pow 2))).add
      ((KP.const (1/16)).mul (((KP.ofScaled (2 ^ k) (inv0 a)).mul
      ((KP.ofScaled (2 ^ k) a).sub (KP.ofScaled (2 ^ k) (const0 a)))).pow 3)))

/-- The four low coefficients of the row square. -/
private def rowLow (k : ℕ) (s : ScalarCase) (i : Fin 5) : Scaled := low4 k (rowSquareK k s false i)

/-- The digit bounds and the positive constant term behind `massAt`. -/
private def massGood (k : ℕ) (s : ScalarCase) (i : Fin 5) : Bool :=
  decide (1 ≤ k) && decide (2 * (rowSquareK k s false i).b < 2 ^ k) &&
    decide (0 < (rowLow k s i).l.getD 0 0) && decide (0 < (rowLow k s i).s) &&
    decide (2 * (massInnerK k (rowLow k s i)).b < 2 ^ k)

/-- The coefficients of `massAt`. -/
private def massList (k : ℕ) (s : ScalarCase) (i : Fin 5) : Scaled :=
  nrm (low4 k (massInnerK k (rowLow k s i)))

private theorem truncateThree_coeff_zero (q : ℚ[X]) :
    (SoleScalarPolynomials.truncateThree q).coeff 0 = q.coeff 0 := by
  simp [SoleScalarPolynomials.truncateThree]

private theorem massList_rep {k : ℕ} {s : ScalarCase} {i : Fin 5} (h : massGood k s i = true) :
    (massList k s i).Rep (massAt s i) := by
  simp only [massGood, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hk, hb1⟩, hl⟩, hs⟩, hb2⟩ := h
  have hr := rowSquareK_rep k s false i
  rw [aff, ite_eq_right Bool.false_ne_true, comp_X] at hr
  have ht : (rowLow k s i).Rep (SoleScalarPolynomials.truncateThree (rowSquare s i)) :=
    low4_rep hk hr hb1
  have hs' : (rowLow k s i).s ≠ 0 := by omega
  have hw := (KP.rep_ofScaled (2 ^ k) (rep_inv0 ht hl hs')).mul
    ((KP.rep_ofScaled (2 ^ k) ht).sub (KP.rep_ofScaled (2 ^ k) (rep_const0 ht)))
  have hm := (KP.rep_ofScaled (2 ^ k) (rep_newton3 ht hl hs')).mul
    ((((KP.rep_ofNat 1).add ((KP.rep_const (1/2)).mul hw)).sub
      ((KP.rep_const (1/8)).mul (hw.pow 2))).add ((KP.rep_const (1/16)).mul (hw.pow 3)))
  have h4 := rep_nrm (low4_rep hk hm hb2)
  rw [truncateThree_coeff_zero, Nat.cast_one] at h4
  exact h4

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

private def massK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : KP :=
  KP.ofScaled (2 ^ k) (if cn then cen s (massList k s i) else massList k s i)

private theorem massK_rep {k : ℕ} {s : ScalarCase} (cn : Bool) {i : Fin 5}
    (h : massGood k s i = true) :
    (massK k s cn i).Rep (2 ^ k) ((massAt s i).comp (aff s cn)) := by
  unfold massK aff
  split_ifs
  · exact KP.rep_ofScaled _ (cen_rep s (massList_rep h))
  · rw [comp_X]; exact KP.rep_ofScaled _ (massList_rep h)

/-! ### The certificate -/

private def massSK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  ((((massK k s cn 0).mul (massK k s cn 1)).mul (massK k s cn 2)).mul (massK k s cn 3)).mul
    (massK k s cn 4)

private def exceptK (k : ℕ) (s : ScalarCase) (cn : Bool) (i j : Fin 5) : KP :=
  if j = i then KP.ofNat 1 else massK k s cn j

private def massExceptK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : KP :=
  ((((exceptK k s cn i 0).mul (exceptK k s cn i 1)).mul (exceptK k s cn i 2)).mul
    (exceptK k s cn i 3)).mul (exceptK k s cn i 4)

private def termK (k : ℕ) (s : ScalarCase) (cn : Bool) (i : Fin 5) : KP :=
  ((rowWeightK k s cn i).mul ((rowSquareK k s cn i).add ((massK k s cn i).pow 2))).mul
    (massExceptK k s cn i)

private def certK (k : ℕ) (s : ScalarCase) (cn : Bool) : KP :=
  (((KP.ofNat 2).mul ((outsideK k s cn).sub (KP.const margin))).mul (massSK k s cn)).sub
    ((KP.const radiusUpper).mul (((((termK k s cn 0).add (termK k s cn 1)).add
      (termK k s cn 2)).add (termK k s cn 3)).add (termK k s cn 4)))

private def massesGood (k : ℕ) (s : ScalarCase) : Bool :=
  massGood k s 0 && massGood k s 1 && massGood k s 2 && massGood k s 3 && massGood k s 4

private theorem massesGood_spec {k : ℕ} {s : ScalarCase} (h : massesGood k s = true) (i : Fin 5) :
    massGood k s i = true := by
  simp only [massesGood, Bool.and_eq_true] at h
  fin_cases i
  exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]

private theorem certK_rep {k : ℕ} {s : ScalarCase} (cn : Bool) (h : massesGood k s = true) :
    (certK k s cn).Rep (2 ^ k) ((certificate s).comp (aff s cn)) := by
  have hm := fun i => massK_rep cn (massesGood_spec h i)
  have hx : ∀ i j : Fin 5, (exceptK k s cn i j).Rep (2 ^ k)
      ((if j = i then 1 else massAt s j).comp (aff s cn)) := by
    intro i j
    unfold exceptK
    split_ifs
    · exact one_rep k s cn
    · exact hm j
  have ht : ∀ i : Fin 5, (termK k s cn i).Rep (2 ^ k)
      ((rowWeight s i * (rowSquare s i + (massAt s i) ^ 2) * massExcept s i).comp (aff s cn)) := by
    intro i
    unfold termK massExceptK
    rw [massExcept, Fin.prod_univ_five]
    simp only [add_comp, mul_comp, pow_comp]
    exact ((rowWeightK_rep k s cn i).mul ((rowSquareK_rep k s cn i).add ((hm i).pow 2))).mul
      (((((hx i 0).mul (hx i 1)).mul (hx i 2)).mul (hx i 3)).mul (hx i 4))
  unfold certK massSK
  rw [certificate, mass, Fin.prod_univ_five, Fin.sum_univ_five]
  simp only [sub_comp, mul_comp, add_comp, C_comp, ofNat_comp, pow_comp]
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  have h3 := ht 3
  have h4 := ht 4
  simp only [add_comp, mul_comp, pow_comp] at h0 h1 h2 h3 h4
  exact (((KP.rep_ofNat 2).mul ((outsideK_rep k s cn).sub (KP.rep_const _))).mul
    (((((hm 0).mul (hm 1)).mul (hm 2)).mul (hm 3)).mul (hm 4))).sub
    ((KP.rep_const _).mul ((((h0.add h1).add h2).add h3).add h4))


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

/-- The bits of the base `2 ^ k`. -/
private def bits : ScalarCase → ℕ
  | .lowZero => 6000 | .lowReturn => 7000 | .middle _ => 8000 | .high _ => 7500

/-- The centered certificate, as an explicit list. -/
private def certList (k : ℕ) (s : ScalarCase) : Scaled :=
  (certK k s true).digits k (max (certK k s true).n 2)

/-- The certificate itself, as an explicit list. -/
private def certListU (k : ℕ) (s : ScalarCase) : Scaled :=
  (certK k s false).digits k (certK k s false).n

private def lowZeroOK (k : ℕ) : Bool :=
  decide (2 * (certK k .lowZero false).b < 2 ^ k) && decide (0 < (certK k .lowZero false).s) &&
    upOK k 45 (cen .lowZero (derivS (certListU k .lowZero))) (-49/1000) &&
    decide ((10 : ℤ) ^ (certListU k .lowZero).l.length * (certK k .lowZero false).s <
      20000 * ev10 (certListU k .lowZero).l)

private def middleBOK (k : ℕ) : Bool :=
  decide (2 * (certK k (.middle 2) false).b < 2 ^ k) && decide (0 < (certK k (.middle 2) false).s) &&
    decide (((certK k (.middle 2) false).s : ℤ) < 250 * (certListU k (.middle 2)).l.getD 0 0) &&
    lowOK k 45 (cen (.middle 2) (certListU k (.middle 2)).divX) (1/5)

/-- The certificate checks of one scalar case. -/
private def certOK (k : ℕ) (s : ScalarCase) : Bool :=
  decide (1 ≤ k) && massesGood k s && decide (2 * (certK k s true).b < 2 ^ k) &&
    decide (0 < (certK k s true).s) && decide ((certK k s true).n ≤ 46 + 1) &&
    (if s = .lowZero then lowZeroOK k else if s = .middle 2 then middleBOK k
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
      (if s = .lowZero then lowZeroOK (bits s) else if s = .middle 2 then middleBOK (bits s)
        else lowOK (bits s) 46 (certList (bits s) s) (1/1000)) = true := by
  have h := certOK_all s
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem length_digs (k : ℕ) : ∀ (m : ℕ) (v : ℤ), (digs k m v).length = m
  | 0, _ => rfl
  | m + 1, v => by simp only [digs, List.length_cons, length_digs k m]

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
  refine (certList_rep s).eq_expansion (by simp only [certList, KP.digits]; omega) ?_
  simp only [certList, KP.digits, length_digs]
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
    simp only [certListU, KP.digits]; omega
  have hsq : (0 : ℚ) < (certListU (bits .lowZero) .lowZero).s := by
    exact_mod_cast Nat.pos_of_ne_zero hs'
  rw [eval_of_rep hr hs', lt_div_iff₀ hsq]
  have he' := (Int.cast_lt (R := ℚ)).2 he
  have h10 := ev10_eq (certListU (bits .lowZero) .lowZero).l
  have hp : (0 : ℚ) < 10 ^ (certListU (bits .lowZero) .lowZero).l.length := by positivity
  simp only [certListU, KP.digits] at he' h10 hp ⊢
  push_cast at he' h10 hp ⊢
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
    simp only [certListU, KP.digits]; omega
  rw [hr.coeff hs' 0, lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hs')]
  have hc' := (Int.cast_lt (R := ℚ)).2 hc
  simp only [certListU, KP.digits] at hc' ⊢
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
