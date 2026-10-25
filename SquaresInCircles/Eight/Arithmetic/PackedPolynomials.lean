module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.Sole.ScalarPolynomials

/-!
# Eight squares: packed polynomial certificates

Whole-interval bounds of polynomials of high degree with big rational coefficients, computed by
the kernel on one integer per polynomial: a polynomial `p` is packed at the base `B = 2 ^ k` as
`⟨v, s, b, n⟩` (`Packed`, `Packed.Rep`) when an integer list `l` with `toPoly l = C s * p`,
absolute sum at most `b` and at most `n` entries has value `v` at `B`. Sums, products and powers
act on the packed numbers, and when `2 b < B` the balanced base-`B` digits of `v`, read by masks
and shifts, give back `l`.

The kernels outside Lean are slow on big numbers in ways Lean's is not: con-ron multiplies in a
time proportional to the size of the right factor times the size of the product, divides bit by
bit, takes a gcd in cubic time and computes `2 ^ n` a hundred times slower than `1 <<< n`, while
it shifts, masks and adds in linear time. So the right factor of every product of packed numbers is the one with fewer
digits (`Packed.mul`), digits are read with masks and shifts (`1 <<< k`, never `2 ^ k` for the big
exponents), the only divisions and gcds are of small scales, and no rational lists are evaluated.

* Packing: `Packed.add`, `sub` (the scales brought to their least common multiple: for the small
  scales of the base polynomials), `mul`, `pow`, `const q` (`C q`), `ofNat`, `ofInt`, `var B`
  (`X`), `ofList k l` (an integer list over the scale `1`, by shifts), `intSub a x` (`C a - x`)
  and `over x d` (`x / d`), each with its `Rep` lemma.
* Digits: `Packed.digits k c m` reads `m` balanced digits of `c` back as a `Scaled` list
  (`Packed.Rep.digits`, `Packed.Rep.digits_getD`).
* Bounds: `lowOK k D c r` and `upOK k D c r` check `r < lowerOn D a b p` and
  `upperOn D a b p < r` for a list `c` of `centered a b p` (`lowOK_spec`, `upOK_spec`); the
  Chebyshev coefficients are read off the digits of one number (the Joukowski map,
  `chebLow_eq`).
* Newton masses: `newtonList k c` is `SoleScalarPolynomials.newtonMass` of the polynomial packed
  in `c`, from its four low digits, by integer formulas: the three Newton steps in lowest terms
  (`newtonPQ`) and the cubic over the content of the coefficients (`massOf`); `newtonOK k c`
  checks what `newtonList_rep` needs.
* Sine and cosine: `sineK q` and `cosineK q` pack `PositiveScalarPolynomials.sine.comp Q` and
  `cosine.comp Q` by Horner's rule in `q²` with integer coefficients over `15!` and `16!`.
* Certificates: `certificateK O R w r m σ` packs `2 O ∏ mᵢ - R ∑ wᵢ (rᵢ + mᵢ²) ∏_{j ≠ i} mⱼ`
  for five masses `mᵢ = Mᵢ / σᵢ` given by integer lists over their scales, as
  `(2 O P - R ∑ wᵢ (rᵢ σᵢ + Mᵢ² / σᵢ) Eᵢ) / σ` with `P = ∏ Mᵢ`, `Eᵢ = ∏_{j ≠ i} Mⱼ` and
  `σ = ∏ σᵢ` (`certificateK_rep`, `fiveMasses_comp`): the product `σ` of the big scales enters
  no gcd.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PackedPolynomials
open Polynomial WholeIntervalPolynomial
open WholeIntervalPolynomial.Certificate (Scaled toPoly chebList twoX lowerZ upperZ)

/-! ## Integer coefficient lists -/

/-- The sum of the absolute values of the entries. -/
def absSum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs + absSum l

theorem natAbs_le_absSum : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → x.natAbs ≤ absSum l
  | a :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [absSum]; omega
    · have := natAbs_le_absSum h; simp only [absSum]; omega

theorem absSum_add : ∀ l m : List ℤ, absSum (Certificate.add l m) ≤ absSum l + absSum m
  | [], m => by simp [Certificate.add, absSum]
  | a :: l, [] => by simp [Certificate.add, absSum]
  | a :: l, b :: m => by
    have h1 := absSum_add l m
    have h2 := Int.natAbs_add_le a b
    simp only [Certificate.add, absSum]
    omega

theorem absSum_smul (c : ℤ) :
    ∀ l : List ℤ, absSum (Certificate.smul c l) = c.natAbs * absSum l
  | [] => by simp [Certificate.smul, absSum]
  | a :: l => by simp only [Certificate.smul, absSum, absSum_smul c l, Int.natAbs_mul, Nat.mul_add]

theorem absSum_mul : ∀ l m : List ℤ, absSum (Certificate.mul l m) ≤ absSum l * absSum m
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

theorem length_add : ∀ l m : List ℤ, (Certificate.add l m).length = max l.length m.length
  | [], m => by simp [Certificate.add]
  | a :: l, [] => by simp [Certificate.add]
  | a :: l, b :: m => by simp only [Certificate.add, List.length_cons, length_add l m]; omega

theorem length_smul (c : ℤ) : ∀ l : List ℤ, (Certificate.smul c l).length = l.length
  | [] => rfl
  | a :: l => by simp only [Certificate.smul, List.length_cons, length_smul c l]

theorem length_mul :
    ∀ l m : List ℤ, (Certificate.mul l m).length ≤ l.length + m.length - 1
  | [], _ => by simp [Certificate.mul]
  | _ :: _, [] => by simp [Certificate.mul]
  | a :: l, b :: m => by
    have h := length_mul l (b :: m)
    rw [Certificate.mul, length_add, length_smul]
    simp only [List.length_cons] at h ⊢
    omega

/-- The value of a coefficient list at `B`. -/
def evalZ (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + B * evalZ B l

theorem eval_toPoly (B : ℤ) : ∀ l : List ℤ, (toPoly l).eval (B : ℚ) = (evalZ B l : ℚ)
  | [] => by simp [toPoly, evalZ]
  | a :: l => by simp [toPoly, evalZ, eval_toPoly B l]

/-- `x * 2 ^ m`, by a shift. -/
def shl (x : ℤ) (m : ℕ) : ℤ :=
  match x with
  | .ofNat n => .ofNat (n <<< m)
  | .negSucc n => -.ofNat ((n + 1) <<< m)

theorem shl_eq (x : ℤ) (m : ℕ) : shl x m = x * 2 ^ m := by
  cases x with
  | ofNat n => simp only [shl, Nat.shiftLeft_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | negSucc n =>
    simp only [shl, Nat.shiftLeft_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring

/-- The value of a coefficient list at `2 ^ k`, by shifts. -/
def evalS (k : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + shl (evalS k l) k

theorem evalS_eq (k : ℕ) : ∀ l : List ℤ, evalS k l = evalZ (2 ^ k) l
  | [] => rfl
  | a :: l => by rw [evalS, evalZ, shl_eq, evalS_eq k l]; ring

/-! ## Packed polynomials -/

/-- A packed polynomial: value `v` at the base, scale `s`, absolute-sum bound `b`, length
bound `n`. -/
structure Packed where
  v : ℤ
  s : ℕ
  b : ℕ
  n : ℕ

/-- `c` packs `p` at the base `B`. -/
def Packed.Rep (B : ℕ) (c : Packed) (p : ℚ[X]) : Prop :=
  (c.s : ℚ) * p.eval (B : ℚ) = c.v ∧
    ∃ l : List ℤ, toPoly l = C (c.s : ℚ) * p ∧ absSum l ≤ c.b ∧ l.length ≤ c.n

/-- The sum, over the least common multiple of the scales. -/
def Packed.add (x y : Packed) : Packed :=
  ⟨x.v * (y.s / Nat.gcd x.s y.s : ℕ) + y.v * (x.s / Nat.gcd x.s y.s : ℕ),
    x.s * (y.s / Nat.gcd x.s y.s), x.b * (y.s / Nat.gcd x.s y.s) + y.b * (x.s / Nat.gcd x.s y.s),
    max x.n y.n⟩

/-- The difference, over the least common multiple of the scales. -/
def Packed.sub (x y : Packed) : Packed :=
  ⟨x.v * (y.s / Nat.gcd x.s y.s : ℕ) - y.v * (x.s / Nat.gcd x.s y.s : ℕ),
    x.s * (y.s / Nat.gcd x.s y.s), x.b * (y.s / Nat.gcd x.s y.s) + y.b * (x.s / Nat.gcd x.s y.s),
    max x.n y.n⟩

/-- The product; the factor with fewer digits is the right operand of `*`, which some kernels
multiply in time proportional to the size of the right operand times the size of the product. -/
def Packed.mul (x y : Packed) : Packed :=
  ⟨if x.n < y.n then y.v * x.v else x.v * y.v, x.s * y.s, x.b * y.b, x.n + y.n - 1⟩

/-- `1`. -/
def Packed.one : Packed := ⟨1, 1, 1, 1⟩

/-- `x ^ k`. -/
def Packed.pow (x : Packed) : ℕ → Packed
  | 0 => Packed.one
  | k + 1 => (x.pow k).mul x

/-- `C q`. -/
def Packed.const (q : ℚ) : Packed := ⟨q.num, q.den, q.num.natAbs, 1⟩

/-- The numeral `m`. -/
def Packed.ofNat (m : ℕ) : Packed := ⟨m, 1, m, 1⟩

/-- `0`. -/
def Packed.zero : Packed := ⟨0, 1, 0, 0⟩

/-- `X`. -/
def Packed.var (B : ℕ) : Packed := ⟨B, 1, 1, 2⟩

/-- The integer `m`. -/
def Packed.ofInt (m : ℤ) : Packed := ⟨m, 1, m.natAbs, 1⟩

/-- An integer list, packed by shifts at `2 ^ k`, over the scale `1`. -/
def Packed.ofList (k : ℕ) (l : List ℤ) : Packed := ⟨evalS k l, 1, absSum l, l.length⟩

/-- `C a - x`, over the scale of `x`. -/
def Packed.intSub (a : ℤ) (x : Packed) : Packed :=
  ⟨a * x.s - x.v, x.s, a.natAbs * x.s + x.b, max 1 x.n⟩

/-- `x / d`: the scale times `d`. -/
def Packed.over (x : Packed) (d : ℕ) : Packed := ⟨x.v, x.s * d, x.b, x.n⟩

private theorem gcd_cross (a b : ℕ) : a * (b / Nat.gcd a b) = b * (a / Nat.gcd a b) := by
  rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_right a b), ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left a b),
    Nat.mul_comm]

/-- The common core of `add` and `sub`. -/
private theorem Packed.rep_lin {B : ℕ} {x y : Packed} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q)
    (u w : ℕ) (e : ℤ) (he : e.natAbs = 1) (key : x.s * u = y.s * w) :
    Packed.Rep B ⟨x.v * u + e * (y.v * w), x.s * u, x.b * u + y.b * w, max x.n y.n⟩
      (p + C (e : ℚ) * q) := by
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

theorem Packed.Rep.add {B : ℕ} {x y : Packed} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q) :
    (x.add y).Rep B (p + q) := by
  have h := Packed.rep_lin hx hy _ _ 1 rfl (gcd_cross x.s y.s)
  simp only [Int.cast_one, map_one, one_mul] at h
  exact h

theorem Packed.Rep.sub {B : ℕ} {x y : Packed} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q) :
    (x.sub y).Rep B (p - q) := by
  have h := Packed.rep_lin hx hy _ _ (-1) rfl (gcd_cross x.s y.s)
  simp only [Int.cast_neg, Int.cast_one, map_neg, map_one, neg_mul, one_mul,
    ← sub_eq_add_neg] at h
  exact h

theorem Packed.Rep.mul {B : ℕ} {x y : Packed} {p q : ℚ[X]} (hx : x.Rep B p) (hy : y.Rep B q) :
    (x.mul y).Rep B (p * q) := by
  obtain ⟨hxv, lx, hlx, hbx, hnx⟩ := hx
  obtain ⟨hyv, ly, hly, hby, hny⟩ := hy
  refine ⟨?_, Certificate.mul lx ly, ?_, ?_, ?_⟩
  · have e : (if x.n < y.n then y.v * x.v else x.v * y.v) = x.v * y.v := by
      split_ifs <;> ring
    simp only [Packed.mul, e, eval_mul, Int.cast_mul, Nat.cast_mul, ← hxv, ← hyv]; ring
  · rw [Certificate.toPoly_mul, hlx, hly]; simp only [Packed.mul, Nat.cast_mul, map_mul]; ring
  · exact (absSum_mul lx ly).trans (Nat.mul_le_mul hbx hby)
  · have := length_mul lx ly
    simp only [Packed.mul]
    omega

theorem Packed.rep_one {B : ℕ} : Packed.one.Rep B 1 :=
  ⟨by simp [Packed.one], [1], by simp [toPoly, Packed.one], by simp [absSum, Packed.one],
    by simp [Packed.one]⟩

theorem Packed.Rep.pow {B : ℕ} {x : Packed} {p : ℚ[X]} (hx : x.Rep B p) :
    ∀ k : ℕ, (x.pow k).Rep B (p ^ k)
  | 0 => by rw [pow_zero]; exact Packed.rep_one
  | k + 1 => by rw [pow_succ]; exact (hx.pow k).mul hx

theorem Packed.rep_const {B : ℕ} (q : ℚ) : (Packed.const q).Rep B (C q) :=
  ⟨by simp [Packed.const], [q.num],
    by simp only [toPoly, Packed.const, mul_zero, add_zero, ← map_mul, Rat.den_mul_eq_num],
    by simp [absSum, Packed.const], by simp [Packed.const]⟩

theorem Packed.rep_ofNat {B : ℕ} (m : ℕ) : (Packed.ofNat m).Rep B (m : ℚ[X]) :=
  ⟨by simp [Packed.ofNat], [(m : ℤ)], by simp [toPoly, Packed.ofNat],
    by simp [absSum, Packed.ofNat], by simp [Packed.ofNat]⟩

theorem Packed.rep_one' {B : ℕ} : (Packed.ofNat 1).Rep B 1 := by
  simpa using (Packed.rep_ofNat (B := B) 1)

theorem Packed.rep_zero {B : ℕ} : Packed.zero.Rep B 0 :=
  ⟨by simp [Packed.zero], [], by simp [toPoly, Packed.zero], by simp [absSum, Packed.zero],
    by simp [Packed.zero]⟩

theorem Packed.rep_var (B : ℕ) : (Packed.var B).Rep B X :=
  ⟨by simp [Packed.var], [0, 1], by simp [toPoly, Packed.var], by simp [absSum, Packed.var],
    by simp [Packed.var]⟩

theorem Packed.rep_ofInt {B : ℕ} (m : ℤ) : (Packed.ofInt m).Rep B (C (m : ℚ)) :=
  ⟨by simp [Packed.ofInt], [m], by simp [toPoly, Packed.ofInt], by simp [absSum, Packed.ofInt],
    by simp [Packed.ofInt]⟩

theorem Packed.rep_ofList (k : ℕ) (l : List ℤ) : (Packed.ofList k l).Rep (2 ^ k) (toPoly l) := by
  refine ⟨?_, l, by simp [Packed.ofList], le_rfl, le_rfl⟩
  have h := eval_toPoly (2 ^ k) l
  push_cast at h
  simp only [Packed.ofList, evalS_eq, Nat.cast_one, one_mul, Nat.cast_pow, Nat.cast_ofNat, h]

theorem Packed.rep_ofList_of_rep (k : ℕ) {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (Packed.ofList k c.l).Rep (2 ^ k) (C (c.s : ℚ) * p) := by
  have h := Packed.rep_ofList k c.l
  rwa [show toPoly c.l = C (c.s : ℚ) * p from hc] at h

theorem Packed.Rep.intSub {B : ℕ} {x : Packed} {p : ℚ[X]} (hx : x.Rep B p) (a : ℤ) :
    (Packed.intSub a x).Rep B (C (a : ℚ) - p) := by
  obtain ⟨hxv, l, hl, hb, hn⟩ := hx
  refine ⟨?_, Certificate.add [a * x.s] (Certificate.smul (-1) l), ?_, ?_, ?_⟩
  · simp only [Packed.intSub, eval_sub, eval_C]
    push_cast
    rw [← hxv]
    ring
  · rw [Certificate.toPoly_add, Certificate.toPoly_smul, hl]
    simp only [toPoly, Packed.intSub, mul_zero, add_zero]
    push_cast
    simp only [map_mul, map_neg, map_one]
    ring
  · have h1 := absSum_add [a * x.s] (Certificate.smul (-1) l)
    rw [absSum_smul] at h1
    simp only [absSum, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_one,
      one_mul, add_zero] at h1
    simp only [Packed.intSub]
    omega
  · rw [length_add, length_smul]
    simp only [List.length_cons, List.length_nil, Packed.intSub]
    omega

theorem Packed.Rep.over {B d : ℕ} {x : Packed} {p : ℚ[X]} (hx : x.Rep B (C (d : ℚ) * p)) :
    (x.over d).Rep B p := by
  obtain ⟨hxv, l, hl, hb, hn⟩ := hx
  refine ⟨?_, l, ?_, hb, hn⟩
  · simp only [Packed.over, Nat.cast_mul]
    rw [← hxv, eval_mul, eval_C]
    ring
  · rw [hl]
    simp only [Packed.over, Nat.cast_mul, map_mul]
    ring

theorem Packed.Rep.of_eq {B : ℕ} {x : Packed} {p q : ℚ[X]} (hx : x.Rep B p) (e : p = q) :
    x.Rep B q :=
  e ▸ hx

/-! ## Digits in base `2 ^ k` -/

/-- The remainder of `v` modulo `2 ^ k` in `[-2 ^ (k - 1), 2 ^ (k - 1))` and the quotient, by
masks and shifts. -/
def bsplit (k : ℕ) (v : ℤ) : ℤ × ℤ :=
  match v with
  | .ofNat n =>
    if (n &&& ((1 <<< k) - 1)) < 1 <<< (k - 1) then
      (.ofNat (n &&& ((1 <<< k) - 1)), .ofNat (n >>> k))
    else (.ofNat (n &&& ((1 <<< k) - 1)) - .ofNat (1 <<< k), .ofNat (n >>> k) + 1)
  | .negSucc n =>
    if (n &&& ((1 <<< k) - 1)) < 1 <<< (k - 1) then
      (-.ofNat (n &&& ((1 <<< k) - 1)) - 1, -.ofNat (n >>> k))
    else (.ofNat ((1 <<< k) - 1 - (n &&& ((1 <<< k) - 1))), -.ofNat (n >>> k) - 1)

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
    simp only [bsplit, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Int.ofNat_eq_natCast]
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
    simp only [bsplit, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Int.ofNat_eq_natCast, Int.negSucc_eq]
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
def digs (k : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, v => (bsplit k v).1 :: digs k m (bsplit k v).2

theorem length_digs (k : ℕ) : ∀ (m : ℕ) (v : ℤ), (digs k m v).length = m
  | 0, _ => rfl
  | m + 1, v => by simp only [digs, List.length_cons, length_digs k m]

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
def Packed.digits (k : ℕ) (c : Packed) (m : ℕ) : Scaled := ⟨digs k m c.v, c.s⟩

private theorem Packed.Rep.witness {k : ℕ} {c : Packed} {p : ℚ[X]} (hc : c.Rep (2 ^ k) p) :
    ∃ l : List ℤ, toPoly l = C (c.s : ℚ) * p ∧ absSum l ≤ c.b ∧ l.length ≤ c.n ∧
      evalZ (2 ^ k) l = c.v := by
  obtain ⟨hv, l, hl, hb, hn⟩ := hc
  refine ⟨l, hl, hb, hn, ?_⟩
  have h := eval_toPoly (2 ^ k) l
  rw [hl, eval_mul, eval_C] at h
  push_cast at h hv
  exact_mod_cast h.symm.trans hv

theorem Packed.Rep.digits {k m : ℕ} {c : Packed} {p : ℚ[X]} (hk : 1 ≤ k) (hc : c.Rep (2 ^ k) p)
    (hb : 2 * c.b < 2 ^ k) (hm : c.n ≤ m) : (c.digits k m).Rep p := by
  obtain ⟨l, hl, hbl, hn, hv⟩ := hc.witness
  have hd := digs_evalZ hk m l (fun x hx => by have := natAbs_le_absSum hx; omega) (by omega)
  unfold Scaled.Rep
  simp only [Packed.digits]
  rw [← hv, hd, toPoly_append_zeros, hl]

theorem Packed.Rep.digits_getD {k m : ℕ} {c : Packed} {p : ℚ[X]} (hk : 1 ≤ k)
    (hc : c.Rep (2 ^ k) p) (hb : 2 * c.b < 2 ^ k) {i : ℕ} (hi : i < m) :
    (((c.digits k m).l.getD i 0 : ℤ) : ℚ) = c.s * p.coeff i := by
  obtain ⟨l, hl, hbl, hn, hv⟩ := hc.witness
  have hd := digs_getD hk m l (fun x hx => by have := natAbs_le_absSum hx; omega) i hi
  simp only [Packed.digits]
  rw [← hv, hd, ← Certificate.coeff_toPoly, hl, coeff_C_mul]

/-! ## Chebyshev coefficients by the Joukowski map

With `B = 2 ^ k`, `X = B ^ 2 + 1` and `Y = 2 B`, the number `2 ∑ l_i X^i Y^(n-1-i)` equals
`B^(n-1) ∑ u_j (B^j + B^(-j))` for the Chebyshev coefficients `u = chebList l`: its high
digits are `2 u₀, u₁, u₂, …`. -/

/-- `(∑ l_i X^i Y^(n-1-i), n)` for `n = l.length`, `X = 2 ^ (2 k) + 1` and `Y = 2 ^ (k + 1)`. -/
def kvJ (k : ℕ) : List ℤ → ℤ × ℕ
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
def chebLow (k : ℕ) (l : List ℤ) : ℤ × ℕ :=
  ((digs k l.length (bsplit (k * (l.length - 1)) (shl (kvJ k l).1 1)).2).headD 0,
    absSum (digs k l.length (bsplit (k * (l.length - 1)) (shl (kvJ k l).1 1)).2).tail)

theorem chebLow_eq {k : ℕ} (hk : 1 ≤ k) {l : List ℤ} (hn : 2 ≤ l.length)
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
  have e2 : shl (kvJ k l).1 1 = 2 * (kvJ k l).1 := by rw [shl_eq, pow_one, mul_comm]
  simp only [chebLow, e2, hsplit, hdigs, ← hN, List.headD_cons, List.tail_cons]

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
def lowOK (k D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (1 ≤ k) && decide (2 ≤ c.l.length) && decide (c.l.length ≤ D + 1) && decide (0 < c.s) &&
    decide (4 * 2 ^ c.l.length * absSum c.l < 2 ^ k) &&
    decide (r.num * c.s * 2 ^ c.l.length < r.den * ((chebLow k c.l).1 - 2 * (chebLow k c.l).2))

/-- The checks of `upperOn D a b p < r` for an explicit list `c` of `centered a b p`. -/
def upOK (k D : ℕ) (c : Scaled) (r : ℚ) : Bool :=
  decide (1 ≤ k) && decide (2 ≤ c.l.length) && decide (c.l.length ≤ D + 1) && decide (0 < c.s) &&
    decide (4 * 2 ^ c.l.length * absSum c.l < 2 ^ k) &&
    decide (r.den * ((chebLow k c.l).1 + 2 * (chebLow k c.l).2) < r.num * c.s * 2 ^ c.l.length)

theorem lowOK_spec {k D : ℕ} {c : Scaled} {r a b : ℚ} {p : ℚ[X]}
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

theorem upOK_spec {k D : ℕ} {c : Scaled} {r a b : ℚ} {p : ℚ[X]}
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

/-! ## Newton masses

`SoleScalarPolynomials.newtonMass v` depends on the four low coefficients `lᵢ / s` of `v` only:
it is `newton (l₀ / s) 3 (1 + w/2 - w²/8 + w³/16)` truncated to degree three, with
`w = (l₁ X + l₂ X² + l₃ X³) / l₀`. `massOf` computes it on integers: the Newton steps in lowest
terms after dividing `l₀` and `s` by their gcd, and the cubic times `16 m₀³` for the `mᵢ = lᵢ / c`
over the content `c` of the `lᵢ`. Its scale is then within a few bits of the least one, with no
gcd of big numbers. -/

theorem rep_coeff_mul {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (j : ℕ) :
    (a.s : ℚ) * p.coeff j = (a.l.getD j 0 : ℚ) := by
  have h := congrArg (fun q : ℚ[X] => q.coeff j) ha
  simp only [Certificate.coeff_toPoly, coeff_C_mul] at h
  exact h.symm

/-- The first four entries. -/
def trunc4 (a : Scaled) : Scaled :=
  ⟨[a.l.getD 0 0, a.l.getD 1 0, a.l.getD 2 0, a.l.getD 3 0], a.s⟩

theorem rep_trunc4 {a : Scaled} {p : ℚ[X]}
    (h : ∀ j < 4, (a.l.getD j 0 : ℚ) = a.s * p.coeff j) :
    (trunc4 a).Rep (SoleScalarPolynomials.truncateThree p) := by
  unfold Scaled.Rep trunc4 SoleScalarPolynomials.truncateThree
  simp only [toPoly]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]
  simp only [C_mul, mul_zero, add_zero]
  ring

theorem coeff_truncateThree (p : ℚ[X]) {j : ℕ} (hj : j < 4) :
    (SoleScalarPolynomials.truncateThree p).coeff j = p.coeff j := by
  unfold SoleScalarPolynomials.truncateThree
  interval_cases j <;> simp [coeff_C, coeff_X]

/-- Three Newton steps `x ↦ (x + v / x) / 2` from `1` for `v = L / S`, in lowest terms:
`newton (L / S) 3 = P / Q` (`newtonPQ_spec`). -/
def newtonPQ (L : ℤ) (S : ℕ) : ℤ × ℤ :=
  ((((S : ℤ) + L) ^ 2 + 4 * L * S) ^ 2 + 16 * L * S * ((S : ℤ) + L) ^ 2,
    8 * ((S : ℤ) + L) * (((S : ℤ) + L) ^ 2 + 4 * L * S) * S)

theorem newtonPQ_spec {L : ℤ} {S : ℕ} (hL : 0 < L) (hS : 0 < S) :
    0 < (newtonPQ L S).2 ∧
      SoleScalarPolynomials.newton ((L : ℚ) / S) 3 = ((newtonPQ L S).1 : ℚ) / (newtonPQ L S).2 := by
  have hS' : (0 : ℤ) < S := by exact_mod_cast hS
  have h1z : (0 : ℤ) < S + L := by linarith
  have h2z : (0 : ℤ) < ((S : ℤ) + L) ^ 2 + 4 * L * S :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (mul_pos (by norm_num) hL) hS')
  refine ⟨mul_pos (mul_pos (mul_pos (by norm_num) h1z) h2z) hS', ?_⟩
  have hSq : (0 : ℚ) < S := by exact_mod_cast hS
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have h1 : (0 : ℚ) < S + L := by linarith
  have h2 : (0 : ℚ) < ((S : ℚ) + L) ^ 2 + 4 * L * S :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (mul_pos (by norm_num) hLq) hSq)
  have hS0 := hSq.ne'
  have h10 := h1.ne'
  have h20 := h2.ne'
  have e1 : SoleScalarPolynomials.newton ((L : ℚ) / S) 1 = (S + L) / (2 * S) := by
    show (1 + (L : ℚ) / S / 1) / 2 = _
    field_simp
  have e2 : SoleScalarPolynomials.newton ((L : ℚ) / S) 2 =
      (((S : ℚ) + L) ^ 2 + 4 * L * S) / (4 * S * (S + L)) := by
    show (SoleScalarPolynomials.newton ((L : ℚ) / S) 1 +
      (L : ℚ) / S / SoleScalarPolynomials.newton ((L : ℚ) / S) 1) / 2 = _
    rw [e1]
    field_simp
    ring
  show (SoleScalarPolynomials.newton ((L : ℚ) / S) 2 +
    (L : ℚ) / S / SoleScalarPolynomials.newton ((L : ℚ) / S) 2) / 2 = _
  rw [e2]
  simp only [newtonPQ]
  push_cast
  field_simp
  ring

/-- `16 m₀³ + 8 m₀² W - 2 m₀ W² + W³`, which is `16 m₀³ (1 + w/2 - w²/8 + w³/16)` for
`W = m₀ w`. -/
def massCubic (m0 : ℤ) (W : List ℤ) : List ℤ :=
  Certificate.add [16 * m0 ^ 3] (Certificate.add (Certificate.smul (8 * m0 ^ 2) W)
    (Certificate.add (Certificate.smul (-2 * m0) (Certificate.mul W W))
      (Certificate.mul (Certificate.mul W W) W)))

private theorem toPoly_massCubic {m0 : ℤ} {W : List ℤ} {w : ℚ[X]} (hW : toPoly W = C (m0 : ℚ) * w) :
    toPoly (massCubic m0 W) =
      C (16 * (m0 : ℚ) ^ 3) * (1 + C (1/2) * w - C (1/8) * w ^ 2 + C (1/16) * w ^ 3) := by
  have h2 : C (1/2 : ℚ) * 2 = 1 := by
    rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  have h8 : C (1/8 : ℚ) * 8 = 1 := by
    rw [show (8 : ℚ[X]) = C 8 from (map_ofNat C 8).symm, ← C_mul]; norm_num
  have h16 : C (1/16 : ℚ) * 16 = 1 := by
    rw [show (16 : ℚ[X]) = C 16 from (map_ofNat C 16).symm, ← C_mul]; norm_num
  simp only [massCubic, Certificate.toPoly_add, Certificate.toPoly_smul, Certificate.toPoly_mul, hW,
    toPoly, mul_zero, add_zero]
  push_cast
  simp only [map_mul, map_pow, map_neg, map_ofNat]
  linear_combination (-8 * C (m0 : ℚ) ^ 3 * w) * h2 + (2 * C (m0 : ℚ) ^ 3 * w ^ 2) * h8 +
    (-(C (m0 : ℚ) ^ 3) * w ^ 3) * h16

/-- The Newton mass of `l₀ + l₁ X + l₂ X² + l₃ X³` over `s`, for a common divisor `g` of `l₀`
and `s` and a common divisor `c` of the `lᵢ`. -/
def massOfAux (l0 l1 l2 l3 : ℤ) (s g c : ℕ) : Scaled :=
  trunc4 ⟨Certificate.smul (newtonPQ (l0 / g) (s / g)).1
      (massCubic (l0 / c) [0, l1 / c, l2 / c, l3 / c]),
    ((newtonPQ (l0 / g) (s / g)).2 * (16 * (l0 / c) ^ 3)).toNat⟩

/-- The Newton mass from the four low coefficients of a polynomial over its scale. -/
def massOf (a : Scaled) : Scaled :=
  massOfAux (a.l.getD 0 0) (a.l.getD 1 0) (a.l.getD 2 0) (a.l.getD 3 0) a.s
    (Nat.gcd (a.l.getD 0 0).natAbs a.s)
    (Nat.gcd (Nat.gcd (Nat.gcd (a.l.getD 0 0).natAbs (a.l.getD 1 0).natAbs)
      (a.l.getD 2 0).natAbs) (a.l.getD 3 0).natAbs)

private theorem massOfAux_rep {v : ℚ[X]} {l0 l1 l2 l3 : ℤ} {s g c : ℕ}
    (h0 : (s : ℚ) * v.coeff 0 = l0) (h1 : (s : ℚ) * v.coeff 1 = l1)
    (h2 : (s : ℚ) * v.coeff 2 = l2) (h3 : (s : ℚ) * v.coeff 3 = l3)
    (hl : 0 < l0) (hs : 0 < s) (hg0 : (g : ℤ) ∣ l0) (hgs : g ∣ s)
    (hc0 : (c : ℤ) ∣ l0) (hc1 : (c : ℤ) ∣ l1) (hc2 : (c : ℤ) ∣ l2) (hc3 : (c : ℤ) ∣ l3) :
    (massOfAux l0 l1 l2 l3 s g c).Rep (SoleScalarPolynomials.newtonMass v) := by
  have hg : g ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hgs; omega
  have hc : c ≠ 0 := by rintro rfl; rw [Nat.cast_zero, zero_dvd_iff] at hc0; omega
  have hsq : (s : ℚ) ≠ 0 := by positivity
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hl0 : (l0 : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have cast_div : ∀ {d : ℕ} {x : ℤ}, (d : ℤ) ∣ x → (d : ℚ) ≠ 0 → ((x / d : ℤ) : ℚ) = x / d :=
    fun hx hd => by rw [Int.cast_div hx (by exact_mod_cast hd)]; push_cast; rfl
  -- the Newton steps
  have hL : 0 < l0 / (g : ℤ) := Int.ediv_pos_of_pos_of_dvd hl (by positivity) hg0
  have hS : 0 < s / g := Nat.div_pos (Nat.le_of_dvd hs hgs) (Nat.pos_of_ne_zero hg)
  obtain ⟨hQ, hN⟩ := newtonPQ_spec hL hS
  have hv0 : v.coeff 0 = ((l0 / g : ℤ) : ℚ) / ((s / g : ℕ) : ℚ) := by
    rw [cast_div hg0 hgq, Nat.cast_div hgs hgq]
    field_simp
    linarith
  -- the cubic
  have hm0 : 0 < l0 / (c : ℤ) := Int.ediv_pos_of_pos_of_dvd hl (by positivity) hc0
  have hW : toPoly [0, l1 / c, l2 / c, l3 / c] = C (((l0 / c : ℤ)) : ℚ) *
      (C (1 / v.coeff 0) * (SoleScalarPolynomials.truncateThree v - C (v.coeff 0))) := by
    have e : ∀ {x : ℤ}, (c : ℤ) ∣ x → ∀ j, (s : ℚ) * v.coeff j = x →
        (((x / c : ℤ)) : ℚ) = ((l0 / c : ℤ) : ℚ) * (1 / v.coeff 0) * v.coeff j := by
      intro x hx j hj
      rw [cast_div hx hcq, cast_div hc0 hcq]
      have e0 : v.coeff 0 = l0 / s := by field_simp; linarith
      have ej : v.coeff j = x / s := by field_simp; linarith
      rw [e0, ej]
      field_simp
    simp only [toPoly, SoleScalarPolynomials.truncateThree, Int.cast_zero, map_zero, mul_zero,
      add_zero, zero_add]
    rw [e hc1 1 h1, e hc2 2 h2, e hc3 3 h3]
    simp only [map_mul]
    ring
  have hE := toPoly_massCubic hW
  -- the product, before the truncation
  have hQ' : 0 < (newtonPQ (l0 / g) (s / g)).2 * (16 * (l0 / c) ^ 3) := by positivity
  have hfull : (⟨Certificate.smul (newtonPQ (l0 / g) (s / g)).1
      (massCubic (l0 / c) [0, l1 / c, l2 / c, l3 / c]),
      ((newtonPQ (l0 / g) (s / g)).2 * (16 * (l0 / c) ^ 3)).toNat⟩ : Scaled).Rep
      (C (SoleScalarPolynomials.newton (v.coeff 0) 3) *
        (1 + C (1/2) * (C (1 / v.coeff 0) * (SoleScalarPolynomials.truncateThree v -
          C (v.coeff 0))) - C (1/8) * (C (1 / v.coeff 0) * (SoleScalarPolynomials.truncateThree v -
          C (v.coeff 0))) ^ 2 + C (1/16) * (C (1 / v.coeff 0) *
          (SoleScalarPolynomials.truncateThree v - C (v.coeff 0))) ^ 3)) := by
    unfold Scaled.Rep
    have hn : ((((newtonPQ (l0 / g) (s / g)).2 * (16 * (l0 / c) ^ 3)).toNat : ℕ) : ℚ) =
        ((newtonPQ (l0 / g) (s / g)).2 : ℚ) * (16 * ((l0 / c : ℤ) : ℚ) ^ 3) := by
      have h := Int.toNat_of_nonneg hQ'.le
      have h' : ((((newtonPQ (l0 / g) (s / g)).2 * (16 * (l0 / c) ^ 3)).toNat : ℕ) : ℚ) =
          (((newtonPQ (l0 / g) (s / g)).2 * (16 * (l0 / c) ^ 3) : ℤ) : ℚ) := by
        exact_mod_cast h
      rw [h']
      push_cast
      ring
    have hQq : ((newtonPQ (l0 / g) (s / g)).2 : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    rw [Certificate.toPoly_smul, hE, hn, hv0, hN]
    simp only [← mul_assoc, ← C_mul]
    congr 2
    field_simp
  have hT := rep_trunc4 fun j _ => (rep_coeff_mul hfull j).symm
  unfold massOfAux SoleScalarPolynomials.newtonMass
  exact hT

theorem massOf_rep {a : Scaled} {v : ℚ[X]} (ha : a.Rep (SoleScalarPolynomials.truncateThree v))
    (hl : 0 < a.l.getD 0 0) (hs : 0 < a.s) :
    (massOf a).Rep (SoleScalarPolynomials.newtonMass v) := by
  have hj : ∀ j < 4, (a.s : ℚ) * v.coeff j = a.l.getD j 0 := fun j hj => by
    rw [← coeff_truncateThree v hj]
    exact rep_coeff_mul ha j
  have d1 := Nat.gcd_dvd_left (Nat.gcd (Nat.gcd (a.l.getD 0 0).natAbs (a.l.getD 1 0).natAbs)
    (a.l.getD 2 0).natAbs) (a.l.getD 3 0).natAbs
  have d2 := Nat.gcd_dvd_left (Nat.gcd (a.l.getD 0 0).natAbs (a.l.getD 1 0).natAbs)
    (a.l.getD 2 0).natAbs
  exact massOfAux_rep (hj 0 (by norm_num)) (hj 1 (by norm_num)) (hj 2 (by norm_num))
    (hj 3 (by norm_num)) hl hs (Int.natCast_dvd.2 (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)
    (Int.natCast_dvd.2 (d1.trans (d2.trans (Nat.gcd_dvd_left _ _))))
    (Int.natCast_dvd.2 (d1.trans (d2.trans (Nat.gcd_dvd_right _ _))))
    (Int.natCast_dvd.2 (d1.trans (Nat.gcd_dvd_right _ _)))
    (Int.natCast_dvd.2 (Nat.gcd_dvd_right _ _))

/-- The four low digits of a packed polynomial: its truncation to degree three. -/
def low4 (k : ℕ) (c : Packed) : Scaled := trunc4 (c.digits k 4)

theorem low4_rep {k : ℕ} {c : Packed} {q : ℚ[X]} (hk : 1 ≤ k) (hc : c.Rep (2 ^ k) q)
    (hb : 2 * c.b < 2 ^ k) : (low4 k c).Rep (SoleScalarPolynomials.truncateThree q) :=
  rep_trunc4 fun _ hj => hc.digits_getD hk hb hj

/-- The checks behind `newtonList`: the digit bound and a positive constant term. -/
def newtonOK (k : ℕ) (c : Packed) : Bool :=
  decide (1 ≤ k) && decide (2 * c.b < 2 ^ k) && decide (0 < (low4 k c).l.getD 0 0) &&
    decide (0 < (low4 k c).s)

/-- The Newton mass of the polynomial packed in `c`, from its four low digits. -/
def newtonList (k : ℕ) (c : Packed) : Scaled := massOf (low4 k c)

theorem newtonList_rep {k : ℕ} {c : Packed} {q : ℚ[X]} (hc : c.Rep (2 ^ k) q)
    (h : newtonOK k c = true) : (newtonList k c).Rep (SoleScalarPolynomials.newtonMass q) := by
  simp only [newtonOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hb⟩, hl⟩, hs⟩ := h
  exact massOf_rep (low4_rep hk hc hb) hl hs

/-! ## Sine and cosine

The Taylor polynomials `PositiveScalarPolynomials.sine` and `cosine` times `15!` and `16!` have
integer coefficients: Horner's rule in `q²` on them, then the scale times `15!` or `16!`. -/

/-- `a₀ - q (a₁ - q (a₂ - ⋯))`. -/
def hornerZ (q : Packed) : List ℤ → Packed
  | [] => Packed.zero
  | [a] => Packed.ofInt a
  | a :: l => Packed.intSub a (q.mul (hornerZ q l))

/-- The polynomial of `hornerZ`. -/
def hornerPZ (Q : ℚ[X]) : List ℤ → ℚ[X]
  | [] => 0
  | [a] => C (a : ℚ)
  | a :: l => C (a : ℚ) - Q * hornerPZ Q l

theorem hornerZ_rep {B : ℕ} {q : Packed} {Q : ℚ[X]} (hq : q.Rep B Q) :
    ∀ l : List ℤ, (hornerZ q l).Rep B (hornerPZ Q l)
  | [] => Packed.rep_zero
  | [a] => Packed.rep_ofInt a
  | a :: b :: l => (hq.mul (hornerZ_rep hq (b :: l))).intSub a

/-- `PositiveScalarPolynomials.sine` composed with `q`: `q (15!/1! - q² (15!/3! - ⋯)) / 15!`. -/
def sineK (q : Packed) : Packed :=
  (q.mul (hornerZ (q.mul q) [1307674368000, 217945728000, 10897286400, 259459200, 3603600,
    32760, 210, 1])).over 1307674368000

/-- `PositiveScalarPolynomials.cosine` composed with `q`: `(16!/0! - q² (16!/2! - ⋯)) / 16!`. -/
def cosineK (q : Packed) : Packed :=
  (hornerZ (q.mul q) [20922789888000, 10461394944000, 871782912000, 29059430400, 518918400,
    5765760, 43680, 240, 1]).over 20922789888000

theorem sineK_rep {B : ℕ} {q : Packed} {Q : ℚ[X]} (hq : q.Rep B Q) :
    (sineK q).Rep B (PositiveScalarPolynomials.sine.comp Q) := by
  refine Packed.Rep.over ((hq.mul (hornerZ_rep (hq.mul hq) _)).of_eq ?_)
  have c3 : C (1307674368000 : ℚ) * C (1/6) = C 217945728000 := by rw [← C_mul]; norm_num
  have c5 : C (1307674368000 : ℚ) * C (1/120) = C 10897286400 := by rw [← C_mul]; norm_num
  have c7 : C (1307674368000 : ℚ) * C (1/5040) = C 259459200 := by rw [← C_mul]; norm_num
  have c9 : C (1307674368000 : ℚ) * C (1/362880) = C 3603600 := by rw [← C_mul]; norm_num
  have c11 : C (1307674368000 : ℚ) * C (1/39916800) = C 32760 := by rw [← C_mul]; norm_num
  have c13 : C (1307674368000 : ℚ) * C (1/6227020800) = C 210 := by rw [← C_mul]; norm_num
  have c15 : C (1307674368000 : ℚ) * C (1/1307674368000) = 1 := by rw [← C_mul]; norm_num
  simp only [hornerPZ, PositiveScalarPolynomials.sine, sub_comp, add_comp, mul_comp, C_comp,
    X_comp, pow_comp, Int.cast_ofNat, Int.cast_one, map_one, Nat.cast_ofNat]
  linear_combination Q ^ 3 * c3 - Q ^ 5 * c5 + Q ^ 7 * c7 - Q ^ 9 * c9 + Q ^ 11 * c11 -
    Q ^ 13 * c13 + Q ^ 15 * c15

theorem cosineK_rep {B : ℕ} {q : Packed} {Q : ℚ[X]} (hq : q.Rep B Q) :
    (cosineK q).Rep B (PositiveScalarPolynomials.cosine.comp Q) := by
  refine Packed.Rep.over ((hornerZ_rep (hq.mul hq) _).of_eq ?_)
  have c2 : C (20922789888000 : ℚ) * C (1/2) = C 10461394944000 := by rw [← C_mul]; norm_num
  have c4 : C (20922789888000 : ℚ) * C (1/24) = C 871782912000 := by rw [← C_mul]; norm_num
  have c6 : C (20922789888000 : ℚ) * C (1/720) = C 29059430400 := by rw [← C_mul]; norm_num
  have c8 : C (20922789888000 : ℚ) * C (1/40320) = C 518918400 := by rw [← C_mul]; norm_num
  have c10 : C (20922789888000 : ℚ) * C (1/3628800) = C 5765760 := by rw [← C_mul]; norm_num
  have c12 : C (20922789888000 : ℚ) * C (1/479001600) = C 43680 := by rw [← C_mul]; norm_num
  have c14 : C (20922789888000 : ℚ) * C (1/87178291200) = C 240 := by rw [← C_mul]; norm_num
  have c16 : C (20922789888000 : ℚ) * C (1/20922789888000) = 1 := by rw [← C_mul]; norm_num
  simp only [hornerPZ, PositiveScalarPolynomials.cosine, sub_comp, add_comp, mul_comp, C_comp,
    X_comp, pow_comp, one_comp, Int.cast_ofNat, Int.cast_one, map_one, Nat.cast_ofNat]
  linear_combination Q ^ 2 * c2 - Q ^ 4 * c4 + Q ^ 6 * c6 - Q ^ 8 * c8 + Q ^ 10 * c10 -
    Q ^ 12 * c12 + Q ^ 14 * c14 - Q ^ 16 * c16

/-! ## Certificates with five Newton masses -/

/-- `m₀ m₁ m₂ m₃ m₄`. -/
def prod5 (m : Fin 5 → Packed) : Packed := ((((m 0).mul (m 1)).mul (m 2)).mul (m 3)).mul (m 4)

/-- The product of the `m j` with `j ≠ i`, in the order of `prod5`. -/
def except5 (m : Fin 5 → Packed) : Fin 5 → Packed
  | 0 => (((m 1).mul (m 2)).mul (m 3)).mul (m 4)
  | 1 => (((m 0).mul (m 2)).mul (m 3)).mul (m 4)
  | 2 => (((m 0).mul (m 1)).mul (m 3)).mul (m 4)
  | 3 => (((m 0).mul (m 1)).mul (m 2)).mul (m 4)
  | 4 => (((m 0).mul (m 1)).mul (m 2)).mul (m 3)

/-- `f 0 + f 1 + f 2 + f 3 + f 4`. -/
def sum5 (f : Fin 5 → Packed) : Packed := ((((f 0).add (f 1)).add (f 2)).add (f 3)).add (f 4)

/-- `2 O ∏ mᵢ - R ∑ wᵢ (rᵢ + mᵢ²) ∏_{j ≠ i} mⱼ` for the masses `mᵢ = Mᵢ / σᵢ`, the `Mᵢ` packed in
`m i` over the scale `1`: `(2 O P - R ∑ wᵢ (rᵢ σᵢ + Mᵢ² / σᵢ) Eᵢ) / σ` with `P = ∏ Mᵢ`,
`Eᵢ = ∏_{j ≠ i} Mⱼ` and `σ = ∏ σᵢ`. The sums bring to a common multiple the scales of `O`, `R`,
`wᵢ`, `rᵢ` and one `σᵢ` at a time, a gcd with at most one big argument. -/
def certificateK (O R : Packed) (w r m : Fin 5 → Packed) (σ : Fin 5 → ℕ) : Packed :=
  ((((Packed.ofNat 2).mul O).mul (prod5 m)).sub
    (R.mul (sum5 fun i => (w i).mul ((((r i).mul (Packed.ofNat (σ i))).add
      (((m i).mul (m i)).over (σ i))).mul (except5 m i))))).over (σ 0 * σ 1 * σ 2 * σ 3 * σ 4)

theorem certificateK_rep {B : ℕ} {O R : Packed} {w r m : Fin 5 → Packed} {σ : Fin 5 → ℕ}
    {PO PR : ℚ[X]} {pw pr pm : Fin 5 → ℚ[X]} (hO : O.Rep B PO) (hR : R.Rep B PR)
    (hw : ∀ i, (w i).Rep B (pw i)) (hr : ∀ i, (r i).Rep B (pr i))
    (hm : ∀ i, (m i).Rep B (C (σ i : ℚ) * pm i)) :
    (certificateK O R w r m σ).Rep B
      (2 * PO * (pm 0 * pm 1 * pm 2 * pm 3 * pm 4) - PR *
        (pw 0 * (pr 0 + pm 0 ^ 2) * (pm 1 * pm 2 * pm 3 * pm 4) +
          pw 1 * (pr 1 + pm 1 ^ 2) * (pm 0 * pm 2 * pm 3 * pm 4) +
          pw 2 * (pr 2 + pm 2 ^ 2) * (pm 0 * pm 1 * pm 3 * pm 4) +
          pw 3 * (pr 3 + pm 3 ^ 2) * (pm 0 * pm 1 * pm 2 * pm 4) +
          pw 4 * (pr 4 + pm 4 ^ 2) * (pm 0 * pm 1 * pm 2 * pm 3))) := by
  have ht : ∀ (i : Fin 5) {E : ℚ[X]}, (except5 m i).Rep B E →
      ((w i).mul ((((r i).mul (Packed.ofNat (σ i))).add (((m i).mul (m i)).over (σ i))).mul
        (except5 m i))).Rep B (pw i * ((pr i * ((σ i : ℕ) : ℚ[X]) + C (σ i : ℚ) * pm i ^ 2) * E)) :=
    fun i _ hE => (hw i).mul ((((hr i).mul (Packed.rep_ofNat _)).add
      (Packed.Rep.over (((hm i).mul (hm i)).of_eq (by ring)))).mul hE)
  have h := ((((Packed.rep_ofNat 2).mul hO).mul ((((((hm 0).mul (hm 1)).mul (hm 2)).mul
    (hm 3)).mul (hm 4)))).sub
    (hR.mul (((((ht 0 ((((hm 1).mul (hm 2)).mul (hm 3)).mul (hm 4))).add
      (ht 1 ((((hm 0).mul (hm 2)).mul (hm 3)).mul (hm 4)))).add
      (ht 2 ((((hm 0).mul (hm 1)).mul (hm 3)).mul (hm 4)))).add
      (ht 3 ((((hm 0).mul (hm 1)).mul (hm 2)).mul (hm 4)))).add
      (ht 4 ((((hm 0).mul (hm 1)).mul (hm 2)).mul (hm 3))))))
  refine Packed.Rep.over (h.of_eq ?_)
  simp only [map_mul, map_natCast, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The certificate of five masses composed with `q`, in the form of `certificateK_rep`. -/
theorem fiveMasses_comp (O R : ℚ[X]) (w r m : Fin 5 → ℚ[X]) (q : ℚ[X]) :
    (2 * O * ∏ i, m i - R * ∑ i, w i * (r i + m i ^ 2) * ∏ j, if j = i then 1 else m j).comp q =
      2 * O.comp q * ((m 0).comp q * (m 1).comp q * (m 2).comp q * (m 3).comp q * (m 4).comp q) -
        R.comp q *
          ((w 0).comp q * ((r 0).comp q + (m 0).comp q ^ 2) *
              ((m 1).comp q * (m 2).comp q * (m 3).comp q * (m 4).comp q) +
            (w 1).comp q * ((r 1).comp q + (m 1).comp q ^ 2) *
              ((m 0).comp q * (m 2).comp q * (m 3).comp q * (m 4).comp q) +
            (w 2).comp q * ((r 2).comp q + (m 2).comp q ^ 2) *
              ((m 0).comp q * (m 1).comp q * (m 3).comp q * (m 4).comp q) +
            (w 3).comp q * ((r 3).comp q + (m 3).comp q ^ 2) *
              ((m 0).comp q * (m 1).comp q * (m 2).comp q * (m 4).comp q) +
            (w 4).comp q * ((r 4).comp q + (m 4).comp q ^ 2) *
              ((m 0).comp q * (m 1).comp q * (m 2).comp q * (m 3).comp q)) := by
  simp only [Fin.prod_univ_five, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte, one_mul,
    mul_one, sub_comp, mul_comp, add_comp, pow_comp, ofNat_comp]
  ring

end SquaresInCircles.Eight.PackedPolynomials
