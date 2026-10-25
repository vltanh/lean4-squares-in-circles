module

public import SquaresInCircles.Eight.TableFree.HighOrderTaylor
public import SquaresInCircles.Eight.TableFree.RoundedBinomialEnclosure
public import SquaresInCircles.Eight.TableFree.TensorRadicalExpression
public import Mathlib.Algebra.BigOperators.ModEq

/-!
# Packed bivariate Taylor models

Rounded Taylor models on `[-1, 1]²` that the kernel evaluates with natural-number arithmetic
only (`+`, `*`, `-`, `/`, `%`, bit operations), so the certificates stay small and run in a few
seconds.

A `Config` fixes a scale `2 ^ K`, a total degree `B`, and a digit width `w`. A `Model` stores a
bivariate polynomial `(U - V) / 2 ^ K`, where `U` and `V` hold the nonnegative and the negative
parts of the coefficients as base-`2 ^ w` digits (`X ^ i Y ^ j` at digit `S i + j`, `S = 2 B + 1`),
an error `e / 2 ^ K`, and a flag `ok` collecting every check made while building it.
`m.Contains c x y v` says that if `ok` holds, the model is well formed (`Model.Good`) and
`|v - m.val c x y| ≤ e / 2 ^ K`.

## API

* Configurations: `Config`, `Config.Valid` (`1 ≤ B`, `K + 2 < w`).
* Models and containment: `Model`, `Model.val`, `Model.Good`, `Model.Contains`.
* Operations, each with a containment lemma `Model.contains_*` (the products and the functions
  below ask `|x| ≤ 1`, `|y| ≤ 1`): `Model.neg`, `widen`, `ofInt`, `lit` (a rational `n / d`),
  `X`, `Y`, `one`, `add`, `mul` (truncated to degree `B`, the tail and the rounding added to the
  error), `pow`, `horner`, `sin` and `cos` (the Taylor polynomials `S13`, `C14` of
  `HighOrderTaylor` and their remainders, for arguments checked to lie in `[0, frameCap]`),
  `sinPoly`, `cosPoly` (without the remainder), `sqrt` and `inv` (binomial series around a
  rounded center, with the remainder of `RoundedBinomialEnclosure`).
* Bounds: `Model.lowerZ`, `Model.upperZ`, `Model.bounds` (integer bounds by the coefficient sum).
* Bernstein test: `bernCheck c n m τ` checks `τ ≤ 2 ^ K · val` on `[-1, 1]²` through the
  Bernstein coefficients of degree `n` in each variable, computed by packed Horner steps;
  `bernCheck_sound`.
* Expressions: `QL` (rational literals whose `toQ` is syntactically the literal of a frozen
  formula), `IE ι` (literals, variables, `+`, `-`, `*`, `^`, the seed literals `seed0/1/2`, `sin`,
  `cos`, `sqrt`, `inv`) with `IE.value`, `IE.SeedsOK`, the evaluation `IE.eval c w` into models
  and `IE.eval_sound`; the bridges `IE.toExpression`, `IE.value_toExpression` (to
  `TensorPolynomialEnclosure.Expression`) and `IE.toExpr`, `IE.value_toExpr` (to
  `TensorRadicalExpression.Expr`).
* Certificates: `check c n w e num den strict`, with `check_sound`, `check_lt` (strict:
  `num / den < value`) and `check_le`, for variables `w i` containing `v i` on `[-1, 1]²`.
* Seeds: `nearestRoot_eq` characterizes `TensorPolynomialEnclosure.nearestRoot`; `seedCheck` and
  `seedCheck_sound` prove `nearestRoot r = m / 10 ^ 8` from constant models.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.PackedModels
open Polynomial

/-! ## Digits in base `2 ^ w` -/

/-- Digit `m` of `N` in base `2 ^ w`. -/
def digit (w N m : ℕ) : ℕ := N / (2 ^ w) ^ m % 2 ^ w

theorem digit_lt (w N m : ℕ) : digit w N m < 2 ^ w := Nat.mod_lt _ (by positivity)

theorem digit_zero_right (w N : ℕ) : digit w N 0 = N % 2 ^ w := by simp [digit]

theorem digit_succ (w N m : ℕ) : digit w N (m + 1) = digit w (N / 2 ^ w) m := by
  simp only [digit, pow_succ', Nat.div_div_eq_div_mul]

theorem digit_of_lt {w N m : ℕ} (h : N < (2 ^ w) ^ m) : digit w N m = 0 := by
  simp [digit, Nat.div_eq_of_lt h]

theorem testBit_digit {w N m k : ℕ} (hk : k < w) :
    (digit w N m).testBit k = N.testBit (w * m + k) := by
  rw [digit, Nat.testBit_mod_two_pow, ← pow_mul, Nat.testBit_div_two_pow]
  simp [hk, Nat.add_comm]

theorem testBit_eq_digit {w : ℕ} (hw : 0 < w) (N i : ℕ) :
    N.testBit i = (digit w N (i / w)).testBit (i % w) := by
  rw [testBit_digit (Nat.mod_lt _ hw), Nat.div_add_mod]

/-- Two numbers with the same digits are equal. -/
theorem eq_of_digit_eq {w : ℕ} (hw : 0 < w) {A B : ℕ} (h : ∀ m, digit w A m = digit w B m) :
    A = B :=
  Nat.eq_of_testBit_eq fun i => by rw [testBit_eq_digit hw, testBit_eq_digit hw B, h]

theorem digit_land (w A B m : ℕ) : digit w (A &&& B) m = digit w A m &&& digit w B m := by
  simp only [digit, Nat.and_div_two_pow, ← pow_mul, Nat.and_mod_two_pow]

theorem digit_shiftRight (w A k m : ℕ) : digit w (A >>> (w * k)) m = digit w A (m + k) := by
  simp only [digit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_mul, ← pow_add]
  congr 3
  ring

/-- `∑ u < n, f u`, by recursion. -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ u ∈ Finset.range n, f u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih, Finset.sum_range_succ]

section Base
variable {b : ℕ}

theorem sum_digits_lt (hb : 0 < b) (e : ℕ → ℕ) (he : ∀ u, e u < b) :
    ∀ n, ∑ u ∈ Finset.range n, e u * b ^ u < b ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := sum_digits_lt hb e he n
    have h3 : (e n + 1) * b ^ n ≤ b * b ^ n := Nat.mul_le_mul_right _ (he n)
    nlinarith

theorem div_mod_sum (hb : 0 < b) (e : ℕ → ℕ) (he : ∀ u, e u < b) :
    ∀ n k, (∑ u ∈ Finset.range n, e u * b ^ u) / b ^ k % b = if k < n then e k else 0
  | 0, k => by simp
  | n + 1, k => by
    rw [Finset.sum_range_succ]
    have hS := sum_digits_lt hb e he n
    rcases lt_trichotomy k n with hk | hk | hk
    · rw [ite_eq_left (by omega)]
      have hd := div_mod_sum hb e he n k
      rw [ite_eq_left hk] at hd
      have hpow : b ^ n = b ^ k * b ^ (n - k) := by rw [← pow_add]; congr 1; omega
      rw [hpow, ← mul_assoc, mul_comm (e n) (b ^ k), mul_assoc,
        Nat.add_mul_div_left _ _ (pow_pos hb k), Nat.add_mod, hd]
      have hm : e n * b ^ (n - k) % b = 0 :=
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (dvd_pow_self b (by omega)) _)
      rw [hm, add_zero]
      exact Nat.mod_eq_of_lt (he k)
    · subst hk
      rw [ite_eq_left (by omega), mul_comm (e k), Nat.add_mul_div_left _ _ (pow_pos hb k),
        Nat.div_eq_of_lt hS, zero_add]
      exact Nat.mod_eq_of_lt (he k)
    · rw [ite_eq_right (by omega)]
      have hlt : ∑ u ∈ Finset.range n, e u * b ^ u + e n * b ^ n < b ^ k := by
        have h := sum_digits_lt hb e he (n + 1)
        rw [Finset.sum_range_succ] at h
        exact h.trans_le (Nat.pow_le_pow_right hb (by omega))
      rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

/-- Base-`b` expansion of a number below `b ^ n`. -/
theorem eq_sum_digits (hb : 0 < b) : ∀ (n N : ℕ), N < b ^ n →
    N = ∑ u ∈ Finset.range n, N / b ^ u % b * b ^ u
  | 0, N, h => by simpa using h
  | n + 1, N, h => by
    have hq : N / b < b ^ n := by
      rw [Nat.div_lt_iff_lt_mul hb]; rw [pow_succ] at h; linarith
    have ih := eq_sum_digits hb n (N / b) hq
    rw [Finset.sum_range_succ']
    have hterm : ∀ u ∈ Finset.range n, N / b ^ (u + 1) % b * b ^ (u + 1) =
        b * (N / b / b ^ u % b * b ^ u) := by
      intro u _
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← ih]
    simp only [pow_zero, Nat.div_one, mul_one]
    exact (Nat.div_add_mod N b).symm.trans (by ring)

end Base

/-! ## Configurations and packed numbers -/

/-- A model works at the fixed-point scale `2 ^ K`, keeps total degree `≤ B`, and packs
coefficients as base-`2 ^ w` digits, the coefficient of `X^i Y^j` at digit `S i + j`. -/
structure Config where
  K : ℕ
  B : ℕ
  w : ℕ

namespace Config
/-- The stride `2 B + 1`: a product of two models of degree `≤ B` does not overlap rows. -/
def S (c : Config) : ℕ := 2 * c.B + 1
/-- The base `2 ^ w`. -/
def b (c : Config) : ℕ := 2 ^ c.w
theorem b_pos (c : Config) : 0 < c.b := by unfold b; positivity
theorem S_pos (c : Config) : 0 < c.S := by unfold S; omega
end Config

/-- `∑_{i, j < S} d i j · b ^ (S i + j)`. -/
def pack (c : Config) (d : ℕ → ℕ → ℕ) : ℕ :=
  sumTo (fun i => sumTo (fun j => d i j * c.b ^ (c.S * i + j)) c.S) c.S

theorem double_sum_eq (S : ℕ) (hS : 0 < S) (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ)
    (hfg : ∀ i j, j < S → f i j = g (S * i + j)) :
    ∀ I, ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range S, f i j = ∑ u ∈ Finset.range (S * I), g u
  | 0 => by simp
  | I + 1 => by
    rw [Finset.sum_range_succ, double_sum_eq S hS f g hfg I, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl fun j hj => hfg I j (Finset.mem_range.mp hj)

theorem pack_eq_sum (c : Config) (d : ℕ → ℕ → ℕ) :
    pack c d = ∑ u ∈ Finset.range (c.S * c.S), d (u / c.S) (u % c.S) * c.b ^ u := by
  unfold pack
  simp only [sumTo_eq]
  apply double_sum_eq c.S c.S_pos
  intro i j hj
  have h1 : (c.S * i + j) / c.S = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ c.S_pos, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (c.S * i + j) % c.S = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [h1, h2]

/-- A number fits the box of `S × S` digits. -/
def Box (c : Config) (N : ℕ) : Prop := N < c.b ^ (c.S * c.S)

theorem pack_box (c : Config) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) : Box c (pack c d) := by
  rw [Box, pack_eq_sum]
  exact sum_digits_lt c.b_pos _ (fun u => hd _ _) _

theorem digit_pack (c : Config) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) (m : ℕ) :
    digit c.w (pack c d) m = if m < c.S * c.S then d (m / c.S) (m % c.S) else 0 := by
  rw [pack_eq_sum, digit]
  exact div_mod_sum c.b_pos (fun u => d (u / c.S) (u % c.S)) (fun u => hd _ _) _ _

theorem digit_pack_ij (c : Config) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) {i j : ℕ}
    (hi : i < c.S) (hj : j < c.S) : digit c.w (pack c d) (c.S * i + j) = d i j := by
  rw [digit_pack c hd, ite_eq_left (by nlinarith)]
  have h1 : (c.S * i + j) / c.S = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ c.S_pos, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (c.S * i + j) % c.S = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [h1, h2]

/-- The digits of a number of the box, as a coefficient function. -/
def coeffs (c : Config) (N : ℕ) (i j : ℕ) : ℕ := digit c.w N (c.S * i + j)

theorem pack_coeffs {c : Config} {N : ℕ} (h : Box c N) : pack c (coeffs c N) = N := by
  rw [pack_eq_sum]
  conv_rhs => rw [eq_sum_digits c.b_pos _ N h]
  apply Finset.sum_congr rfl
  intro u _
  simp only [coeffs, digit, Config.b]
  rw [Nat.div_add_mod]

/-! ## Natural bivariate polynomials

`NB = ℕ[X][X]`: the outer variable is `X`, the inner one `Y`. A packed number of the box is
the value of such a polynomial at `X = b ^ S`, `Y = b` (`evB`), and its digits are the
coefficients (`poly`). -/

abbrev NB := Polynomial (Polynomial ℕ)

/-- The coefficient of `X^i Y^j`. -/
def cf (P : NB) (i j : ℕ) : ℕ := (P.coeff i).coeff j

theorem cf_add (P Q : NB) (i j : ℕ) : cf (P + Q) i j = cf P i j + cf Q i j := by simp [cf]

/-- The polynomial with coefficient function `d` on the box. -/
def ofFun (c : Config) (d : ℕ → ℕ → ℕ) : NB :=
  ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, monomial i (monomial j (d i j))

theorem coeff_ofFun (c : Config) (d : ℕ → ℕ → ℕ) (i : ℕ) : (ofFun c d).coeff i =
    if i < c.S then ∑ j ∈ Finset.range c.S, monomial j (d i j) else 0 := by
  simp only [ofFun, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hi : i < c.S
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro k hk
    have : k ≠ i := fun h => hi (h ▸ Finset.mem_range.mp hk)
    simp [this]

theorem cf_ofFun (c : Config) (d : ℕ → ℕ → ℕ) (i j : ℕ) :
    cf (ofFun c d) i j = if i < c.S ∧ j < c.S then d i j else 0 := by
  rw [cf, coeff_ofFun]
  by_cases hi : i < c.S
  · rw [ite_eq_left hi, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hj : j < c.S
    · rw [ite_eq_left ⟨hi, hj⟩, Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [ite_eq_right (fun h => hj h.2)]
      apply Finset.sum_eq_zero
      intro k hk
      have : k ≠ j := fun h => hj (h ▸ Finset.mem_range.mp hk)
      simp [this]
  · rw [ite_eq_right hi, ite_eq_right (fun h => hi h.1)]
    simp

theorem ofFun_congr (c : Config) {d d' : ℕ → ℕ → ℕ}
    (h : ∀ i j, i < c.S → j < c.S → d i j = d' i j) : ofFun c d = ofFun c d' := by
  unfold ofFun
  exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    rw [h i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]

theorem ext_cf {P Q : NB} (h : ∀ i j, cf P i j = cf Q i j) : P = Q :=
  Polynomial.ext fun i => Polynomial.ext fun j => h i j

/-- All coefficients lie in the box `i, j < S`. -/
def BoxSupp (c : Config) (P : NB) : Prop := ∀ i j, cf P i j ≠ 0 → i < c.S ∧ j < c.S

/-- All coefficients lie on the triangle `i + j ≤ B`. -/
def Tri (c : Config) (P : NB) : Prop := ∀ i j, cf P i j ≠ 0 → i + j ≤ c.B

theorem Tri.boxSupp {c : Config} {P : NB} (h : Tri c P) : BoxSupp c P := fun i j hij => by
  have := h i j hij; unfold Config.S; omega

theorem eq_ofFun {c : Config} {P : NB} (h : BoxSupp c P) : P = ofFun c (cf P) := by
  apply ext_cf; intro i j
  rw [cf_ofFun]
  by_cases hij : i < c.S ∧ j < c.S
  · rw [ite_eq_left hij]
  · rw [ite_eq_right hij]
    by_contra hne
    exact hij (h i j hne)

/-- Evaluation of a natural bivariate polynomial in a commutative semiring. -/
def ev {R : Type*} [CommSemiring R] (x y : R) : NB →+* R :=
  eval₂RingHom (eval₂RingHom (Nat.castRingHom R) y) x

theorem ev_monomial {R : Type*} [CommSemiring R] (x y : R) (i j a : ℕ) :
    ev x y (monomial i (monomial j a)) = (a : R) * x ^ i * y ^ j := by
  simp only [ev, coe_eval₂RingHom, eval₂_monomial, eq_natCast]
  ring

theorem ev_ofFun {R : Type*} [CommSemiring R] (c : Config) (d : ℕ → ℕ → ℕ) (x y : R) :
    ev x y (ofFun c d) =
      ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, (d i j : R) * x ^ i * y ^ j := by
  simp only [ofFun, map_sum, ev_monomial]

/-- The packed value `P(b ^ S, b)`. -/
def evB (c : Config) : NB →+* ℕ := ev (c.b ^ c.S) c.b

theorem evB_ofFun (c : Config) (d : ℕ → ℕ → ℕ) : evB c (ofFun c d) = pack c d := by
  rw [evB, ev_ofFun, pack]
  simp only [sumTo_eq, Nat.cast_id]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The digits of a packed number as a polynomial. -/
def poly (c : Config) (N : ℕ) : NB := ofFun c (coeffs c N)

theorem cf_poly (c : Config) (N i j : ℕ) :
    cf (poly c N) i j = if i < c.S ∧ j < c.S then digit c.w N (c.S * i + j) else 0 :=
  cf_ofFun c _ i j

theorem cf_poly_lt (c : Config) (N i j : ℕ) : cf (poly c N) i j < c.b := by
  rw [cf_poly]; split_ifs
  · exact digit_lt _ _ _
  · exact c.b_pos

theorem poly_boxSupp (c : Config) (N : ℕ) : BoxSupp c (poly c N) := fun i j h => by
  rw [cf_poly] at h; by_contra hc; exact h (ite_eq_right hc)

theorem evB_poly {c : Config} {N : ℕ} (h : Box c N) : evB c (poly c N) = N := by
  rw [poly, evB_ofFun, pack_coeffs h]

theorem box_evB {c : Config} {P : NB} (hP : BoxSupp c P) (hlt : ∀ i j, cf P i j < c.b) :
    Box c (evB c P) := by
  rw [eq_ofFun hP, evB_ofFun]; exact pack_box c hlt

theorem poly_evB {c : Config} {P : NB} (hP : BoxSupp c P) (hlt : ∀ i j, cf P i j < c.b) :
    poly c (evB c P) = P := by
  have h1 : evB c P = pack c (cf P) := by
    conv_lhs => rw [eq_ofFun hP]
    exact evB_ofFun c _
  rw [h1, poly]
  conv_rhs => rw [eq_ofFun hP]
  apply ofFun_congr
  intro i j hi hj
  exact digit_pack_ij c hlt hi hj

/-- The digit sum. -/
def dsum (P : NB) : ℕ := ev 1 1 P

theorem dsum_ofFun (c : Config) (d : ℕ → ℕ → ℕ) :
    dsum (ofFun c d) = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, d i j := by
  rw [dsum, ev_ofFun]; simp

theorem cf_le_dsum {c : Config} {P : NB} (hP : BoxSupp c P) (i j : ℕ) : cf P i j ≤ dsum P := by
  by_cases h : cf P i j = 0
  · rw [h]; exact Nat.zero_le _
  · have hij := hP i j h
    rw [eq_ofFun hP, dsum_ofFun, ← eq_ofFun hP]
    calc cf P i j ≤ ∑ j ∈ Finset.range c.S, cf P i j :=
          Finset.single_le_sum (f := fun j => cf P i j) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr hij.2)
      _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range c.S, cf P i j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hij.1)

theorem cf_mul_eq_zero {P Q : NB} {a b : ℕ} (hP : ∀ i j, cf P i j ≠ 0 → i + j ≤ a)
    (hQ : ∀ i j, cf Q i j ≠ 0 → i + j ≤ b) (i j : ℕ) (h : a + b < i + j) : cf (P * Q) i j = 0 := by
  simp only [cf, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  by_cases h1 : cf P x.1 y.1 = 0
  · simp only [cf] at h1; rw [h1, zero_mul]
  · by_cases h2 : cf Q x.2 y.2 = 0
    · simp only [cf] at h2; rw [h2, mul_zero]
    · have := hP _ _ h1
      have := hQ _ _ h2
      omega

/-- A product of two triangle polynomials stays in the box (the stride is `2 B + 1`). -/
theorem Tri.mul_boxSupp {c : Config} {P Q : NB} (hP : Tri c P) (hQ : Tri c Q) :
    BoxSupp c (P * Q) := by
  intro i j h
  by_contra hc
  apply h
  apply cf_mul_eq_zero hP hQ
  unfold Config.S at hc; omega

/-- The digits of a product of packed triangle numbers are the coefficients of the product,
when its coefficients stay below the base. -/
theorem poly_mul {c : Config} {U V : ℕ} (hU : Box c U) (hV : Box c V)
    (tU : Tri c (poly c U)) (tV : Tri c (poly c V))
    (hs : dsum (poly c U) * dsum (poly c V) < c.b) :
    Box c (U * V) ∧ poly c (U * V) = poly c U * poly c V := by
  have hsupp := tU.mul_boxSupp tV
  have hlt : ∀ i j, cf (poly c U * poly c V) i j < c.b := fun i j =>
    (cf_le_dsum hsupp i j).trans_lt (by rw [dsum, map_mul]; exact hs)
  have he : U * V = evB c (poly c U * poly c V) := by rw [map_mul, evB_poly hU, evB_poly hV]
  rw [he]
  exact ⟨box_evB hsupp hlt, poly_evB hsupp hlt⟩

theorem BoxSupp.add {c : Config} {P Q : NB} (hP : BoxSupp c P) (hQ : BoxSupp c Q) :
    BoxSupp c (P + Q) := fun i j h => by
  rw [cf_add] at h
  by_cases h1 : cf P i j = 0
  · rw [h1, zero_add] at h; exact hQ i j h
  · exact hP i j h1

theorem Tri.add {c : Config} {P Q : NB} (hP : Tri c P) (hQ : Tri c Q) : Tri c (P + Q) :=
  fun i j h => by
  rw [cf_add] at h
  by_cases h1 : cf P i j = 0
  · rw [h1, zero_add] at h; exact hQ i j h
  · exact hP i j h1

theorem poly_add {c : Config} {U V : ℕ} (hU : Box c U) (hV : Box c V)
    (hs : dsum (poly c U) + dsum (poly c V) < c.b) :
    Box c (U + V) ∧ poly c (U + V) = poly c U + poly c V := by
  have hsupp := (poly_boxSupp c U).add (poly_boxSupp c V)
  have hlt : ∀ i j, cf (poly c U + poly c V) i j < c.b := fun i j =>
    (cf_le_dsum hsupp i j).trans_lt (by rw [dsum, map_add]; exact hs)
  have he : U + V = evB c (poly c U + poly c V) := by rw [map_add, evB_poly hU, evB_poly hV]
  rw [he]
  exact ⟨box_evB hsupp hlt, poly_evB hsupp hlt⟩

/-! ## Digitwise algebra of packed numbers -/

theorem pack_add (c : Config) (d₁ d₂ : ℕ → ℕ → ℕ) :
    pack c d₁ + pack c d₂ = pack c (fun i j => d₁ i j + d₂ i j) := by
  simp only [pack_eq_sum, ← Finset.sum_add_distrib, add_mul]

theorem pack_mul_const (c : Config) (d : ℕ → ℕ → ℕ) (k : ℕ) :
    pack c d * k = pack c (fun i j => d i j * k) := by
  simp only [pack_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by ring

theorem pack_sub (c : Config) {d₁ d₂ : ℕ → ℕ → ℕ} (h : ∀ i j, d₂ i j ≤ d₁ i j) :
    pack c d₁ - pack c d₂ = pack c (fun i j => d₁ i j - d₂ i j) := by
  have : pack c d₂ + pack c (fun i j => d₁ i j - d₂ i j) = pack c d₁ := by
    rw [pack_add]; congr 1; funext i j; have := h i j; omega
  omega

theorem pack_congr (c : Config) {d₁ d₂ : ℕ → ℕ → ℕ}
    (h : ∀ i j, i < c.S → j < c.S → d₁ i j = d₂ i j) : pack c d₁ = pack c d₂ := by
  unfold pack
  simp only [sumTo_eq]
  exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    rw [h i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]

theorem coeffs_pack (c : Config) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) {i j : ℕ}
    (hi : i < c.S) (hj : j < c.S) : coeffs c (pack c d) i j = d i j :=
  digit_pack_ij c hd hi hj

theorem eq_pack_coeffs {c : Config} {N : ℕ} (h : Box c N) : N = pack c (coeffs c N) :=
  (pack_coeffs h).symm

theorem coeffs_lt (c : Config) (N i j : ℕ) : coeffs c N i j < c.b := digit_lt _ _ _

/-- The triangle indicator. -/
def tri (c : Config) (i j : ℕ) : Prop := i + j ≤ c.B

instance (c : Config) (i j : ℕ) : Decidable (tri c i j) := inferInstanceAs (Decidable (_ ≤ _))

/-- A number of the box whose digits vanish off the triangle. -/
def OnTri (c : Config) (N : ℕ) : Prop :=
  Box c N ∧ ∀ i j, i < c.S → j < c.S → ¬ tri c i j → coeffs c N i j = 0

theorem tri_poly {c : Config} {N : ℕ} (h : OnTri c N) : Tri c (poly c N) := by
  intro i j hij
  rw [cf_poly] at hij
  split_ifs at hij with hb
  · by_contra hc; exact hij (h.2 i j hb.1 hb.2 hc)
  · exact absurd rfl hij

theorem onTri_of_poly {c : Config} {N : ℕ} (hb : Box c N) (h : Tri c (poly c N)) : OnTri c N := by
  refine ⟨hb, fun i j hi hj hij => ?_⟩
  by_contra hne
  exact hij (h i j (by rw [cf_poly, ite_eq_left ⟨hi, hj⟩]; exact hne))

/-- Packed patterns: the triangle with a fixed digit `k`. -/
def triPattern (c : Config) (k : ℕ) : ℕ := pack c (fun i j => if i + j ≤ c.B then k else 0)

theorem coeffs_triPattern (c : Config) {k : ℕ} (hk : k < c.b) {i j : ℕ} (hi : i < c.S)
    (hj : j < c.S) : coeffs c (triPattern c k) i j = if tri c i j then k else 0 := by
  rw [triPattern, coeffs_pack c (fun i j => by split_ifs <;> [exact hk; exact c.b_pos]) hi hj]
  rfl

theorem box_of_le {c : Config} {A B : ℕ} (h : A ≤ B) (hB : Box c B) : Box c A :=
  lt_of_le_of_lt h hB

theorem coeffs_land (c : Config) (A B i j : ℕ) :
    coeffs c (A &&& B) i j = coeffs c A i j &&& coeffs c B i j := digit_land _ _ _ _

/-- Digitwise conjunction with a pattern: a box number. -/
theorem land_pattern {c : Config} {A P : ℕ} (hP : Box c P) {f : ℕ → ℕ → ℕ}
    (hf : ∀ i j, i < c.S → j < c.S → coeffs c A i j &&& coeffs c P i j = f i j)
    (_hflt : ∀ i j, f i j < c.b) : A &&& P = pack c f := by
  have hb : Box c (A &&& P) := box_of_le Nat.and_le_right hP
  rw [eq_pack_coeffs hb]
  apply pack_congr
  intro i j hi hj
  rw [coeffs_land, hf i j hi hj]

theorem land_full {w x : ℕ} (hx : x < 2 ^ w) : x &&& (2 ^ w - 1) = x :=
  Nat.and_two_pow_sub_one_of_lt_two_pow hx

/-- Keeping the digits on the triangle. -/
def triMask (c : Config) : ℕ := triPattern c (c.b - 1)

theorem truncate_eq {c : Config} {A : ℕ} :
    A &&& triMask c = pack c (fun i j => if tri c i j then coeffs c A i j else 0) := by
  have hbm : c.b - 1 < c.b := Nat.sub_lt c.b_pos one_pos
  apply land_pattern (P := triMask c) (pack_box c (fun i j => by split_ifs <;> omega))
  · intro i j hi hj
    rw [triMask, coeffs_triPattern c hbm hi hj]
    split_ifs
    · exact land_full (coeffs_lt c A i j)
    · exact Nat.and_zero _
  · intro i j; split_ifs
    · exact coeffs_lt c A i j
    · exact c.b_pos

theorem testBit_two_pow_sub_two_pow {w K i : ℕ} (hK : K ≤ w) :
    (2 ^ w - 2 ^ K).testBit i = (decide (K ≤ i) && decide (i < w)) := by
  have h : 2 ^ w - 2 ^ K = (2 ^ (w - K) - 1) * 2 ^ K := by
    rw [Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hK]
  rw [h, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h1 : K ≤ i <;> simp [h1]; omega

theorem land_high {w K x : ℕ} (hK : K ≤ w) (hx : x < 2 ^ w) :
    x &&& (2 ^ w - 2 ^ K) = 2 ^ K * (x / 2 ^ K) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_two_pow_sub_two_pow hK, Nat.testBit_two_pow_mul,
    Nat.testBit_div_two_pow]
  by_cases h1 : K ≤ i
  · by_cases h2 : i < w
    · simp [h1, h2, Nat.sub_add_cancel h1]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1, h2, this, Nat.sub_add_cancel h1]
  · simp [h1]

/-- Clearing the low `K` bits of every triangle digit. -/
def hiMask (c : Config) : ℕ := triPattern c (c.b - 2 ^ c.K)

/-- `(A &&& hiMask) >>> K` divides every triangle digit by `2 ^ K` (rounding down). -/
theorem round_eq {c : Config} (hK : c.K ≤ c.w) (A : ℕ) :
    (A &&& hiMask c) >>> c.K = pack c (fun i j => if tri c i j then coeffs c A i j / 2 ^ c.K else 0) := by
  have hbm : c.b - 2 ^ c.K < c.b := Nat.sub_lt c.b_pos (by positivity)
  have h1 : A &&& hiMask c = pack c (fun i j => if tri c i j then 2 ^ c.K * (coeffs c A i j / 2 ^ c.K) else 0) := by
    apply land_pattern (P := hiMask c) (pack_box c (fun i j => by split_ifs <;> omega))
    · intro i j hi hj
      rw [hiMask, coeffs_triPattern c hbm hi hj]
      split_ifs
      · exact land_high hK (coeffs_lt c A i j)
      · exact Nat.and_zero _
    · intro i j; split_ifs
      · exact lt_of_le_of_lt (Nat.mul_div_le _ _) (coeffs_lt c A i j)
      · exact c.b_pos
  have h2 : pack c (fun i j => if tri c i j then 2 ^ c.K * (coeffs c A i j / 2 ^ c.K) else 0) =
      pack c (fun i j => if tri c i j then coeffs c A i j / 2 ^ c.K else 0) * 2 ^ c.K := by
    rw [pack_mul_const]; congr 1; funext i j; split_ifs <;> ring
  rw [h1, h2, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by positivity)]

/-! ## Sign normalization

`normalize c U V` returns digitwise `(max (u - v) 0, max (v - u) 0)` for triangle numbers with
digits below `2 ^ (w - 1)`: it adds `2 ^ (w - 1)` to every triangle digit of `U - V` (no borrow),
reads the sign from the top bit of each digit, and splits by masks. -/

theorem topbit_eq {c : Config} (hw : 1 ≤ c.w) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) :
    (pack c d >>> (c.w - 1)) &&& triPattern c 1 =
      pack c (fun i j => if tri c i j then d i j / 2 ^ (c.w - 1) else 0) := by
  have hb2 : 2 ≤ c.b := by
    unfold Config.b; calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ c.w := Nat.pow_le_pow_right (by norm_num) hw
  have hbw : (c.b : ℕ) = 2 ^ (c.w - 1) * 2 := by
    unfold Config.b; rw [← pow_succ, Nat.sub_add_cancel hw]
  have hq : ∀ i j, d i j / 2 ^ (c.w - 1) < 2 := fun i j => by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hbw]; exact hd i j
  have h1 : ∀ i j, (if i + j ≤ c.B then 1 else 0) < c.b := fun i j => by split_ifs <;> omega
  have h2 : ∀ i j, (if tri c i j then d i j / 2 ^ (c.w - 1) else 0) < c.b := fun i j => by
    split_ifs
    · exact lt_of_lt_of_le (hq i j) hb2
    · exact c.b_pos
  apply eq_of_digit_eq (show 0 < c.w by omega)
  intro m
  rw [digit_land, triPattern, digit_pack c h1, digit_pack c h2]
  by_cases hm : m < c.S * c.S
  · rw [ite_eq_left hm, ite_eq_left hm]
    by_cases ht : tri c (m / c.S) (m % c.S)
    · have ht' : m / c.S + m % c.S ≤ c.B := ht
      rw [ite_eq_left ht', ite_eq_left ht, Nat.and_one_is_mod]
      have hdm := digit_pack c hd m
      rw [ite_eq_left hm] at hdm
      rw [← hdm]
      simp only [digit, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ c.w from dvd_pow_self 2 (by omega)),
        show (2 : ℕ) ^ c.w = 2 ^ (c.w - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hw],
        Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    · have ht' : ¬ m / c.S + m % c.S ≤ c.B := ht
      rw [ite_eq_right ht', ite_eq_right ht, Nat.and_zero]
  · rw [ite_eq_right hm, ite_eq_right hm, Nat.and_zero]

theorem div_half_eq {u v h : ℕ} (hu : u < h) (hv : v < h) :
    (u + h - v) / h = if v ≤ u then 1 else 0 := by
  have hh : 0 < h := by omega
  split_ifs with huv
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- Splitting `U - V` into its positive and negative digit parts. -/
def normalize (c : Config) (U V : ℕ) : ℕ × ℕ :=
  let O := triPattern c (2 ^ (c.w - 1))
  let W := U + O - V
  let G := (W >>> (c.w - 1)) &&& triPattern c 1
  let Sm := G * (c.b - 1)
  let Nm := triMask c - Sm
  ((W &&& Sm) - (O &&& Sm), (O &&& Nm) - (W &&& Nm))

theorem pack_restrict {c : Config} {N : ℕ} (h : OnTri c N) :
    N = pack c (fun i j => if tri c i j then coeffs c N i j else 0) := by
  conv_lhs => rw [eq_pack_coeffs h.1]
  apply pack_congr
  intro i j hi hj
  split_ifs with ht
  · rfl
  · exact h.2 i j hi hj ht

theorem onTri_pack {c : Config} {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b)
    (h0 : ∀ i j, ¬ tri c i j → d i j = 0) : OnTri c (pack c d) :=
  ⟨pack_box c hd, fun i j hi hj ht => by rw [coeffs_pack c hd hi hj]; exact h0 i j ht⟩

theorem normalize_spec {c : Config} (hw : 2 ≤ c.w) {U V : ℕ} (hU : OnTri c U) (hV : OnTri c V)
    (hu : ∀ i j, coeffs c U i j < 2 ^ (c.w - 1)) (hv : ∀ i j, coeffs c V i j < 2 ^ (c.w - 1)) :
    (normalize c U V).1 = pack c (fun i j => if tri c i j then coeffs c U i j - coeffs c V i j else 0) ∧
    (normalize c U V).2 = pack c (fun i j => if tri c i j then coeffs c V i j - coeffs c U i j else 0) := by
  set h := 2 ^ (c.w - 1) with hh
  have hbw : c.b = h * 2 := by
    unfold Config.b; rw [hh, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have hh0 : 0 < h := by positivity
  have hb1 : c.b - 1 < c.b := Nat.sub_lt c.b_pos one_pos
  -- the shifted difference `W`
  set dW : ℕ → ℕ → ℕ := fun i j => if tri c i j then coeffs c U i j + h - coeffs c V i j else 0 with hdW
  have hdW_lt : ∀ i j, dW i j < c.b := fun i j => by
    simp only [hdW]; split_ifs
    · have := hu i j; have := hv i j; omega
    · exact c.b_pos
  have hO : triPattern c h = pack c (fun i j => if tri c i j then h else 0) := rfl
  have hW : U + triPattern c h - V = pack c dW := by
    rw [pack_restrict hU, pack_restrict hV, hO, pack_add, pack_sub]
    · apply pack_congr; intro i j _ _; simp only [hdW]; split_ifs <;> rfl
    · intro i j; split_ifs
      · have := hv i j; omega
      · exact le_rfl
  -- the sign digits
  set g : ℕ → ℕ → ℕ := fun i j => if tri c i j then dW i j / h else 0 with hg
  have hG : (pack c dW >>> (c.w - 1)) &&& triPattern c 1 = pack c g := topbit_eq (by omega) hdW_lt
  have hg_val : ∀ i j, tri c i j → g i j = if coeffs c V i j ≤ coeffs c U i j then 1 else 0 := fun i j ht => by
    simp only [hg, hdW, ite_eq_left ht]; exact div_half_eq (hu i j) (hv i j)
  have hg_lt : ∀ i j, g i j * (c.b - 1) < c.b := fun i j => by
    by_cases ht : tri c i j
    · rw [hg_val i j ht]; split_ifs <;> omega
    · simp only [hg, ite_eq_right ht, zero_mul]; exact c.b_pos
  have hSm : pack c g * (c.b - 1) = pack c (fun i j => g i j * (c.b - 1)) := pack_mul_const _ _ _
  have hNm : triMask c - pack c (fun i j => g i j * (c.b - 1)) =
      pack c (fun i j => (if i + j ≤ c.B then c.b - 1 else 0) - g i j * (c.b - 1)) := by
    rw [triMask, triPattern, pack_sub]
    intro i j
    by_cases ht : tri c i j
    · have ht' : i + j ≤ c.B := ht
      rw [ite_eq_left ht', hg_val i j ht]; split_ifs <;> omega
    · have ht' : ¬ i + j ≤ c.B := ht
      simp only [hg, ite_eq_right ht, ite_eq_right ht', zero_mul, le_refl]
  have hNm_lt : ∀ i j, (if i + j ≤ c.B then c.b - 1 else 0) - g i j * (c.b - 1) < c.b :=
    fun i j => by split_ifs <;> omega
  have hO_lt : ∀ i j, (if tri c i j then h else 0) < c.b := fun i j => by
    split_ifs <;> omega
  -- digitwise conjunctions
  have land_mask : ∀ x k, x < c.b → k = 0 ∨ k = c.b - 1 → x &&& k = if k = 0 then 0 else x := by
    intro x k hx hk
    rcases hk with rfl | rfl
    · simp
    · rw [ite_eq_right (by omega)]; exact land_full hx
  have key : ∀ (P : ℕ) (p : ℕ → ℕ → ℕ) (q : ℕ → ℕ → ℕ), (∀ i j, p i j < c.b) → (∀ i j, q i j < c.b) →
      (∀ i j, q i j = 0 ∨ q i j = c.b - 1) → P = pack c p →
      P &&& pack c q = pack c (fun i j => if q i j = 0 then 0 else p i j) := by
    intro P p q hp hq hq01 hP
    apply land_pattern (pack_box c hq)
    · intro i j hi hj
      rw [hP, coeffs_pack c hp hi hj, coeffs_pack c hq hi hj, land_mask _ _ (hp i j) (hq01 i j)]
    · intro i j; split_ifs
      · exact c.b_pos
      · exact hp i j
  have hq1 : ∀ i j, g i j * (c.b - 1) = 0 ∨ g i j * (c.b - 1) = c.b - 1 := fun i j => by
    by_cases ht : tri c i j
    · rw [hg_val i j ht]; split_ifs <;> simp
    · simp [hg, ite_eq_right ht]
  have hq2 : ∀ i j, (if i + j ≤ c.B then c.b - 1 else 0) - g i j * (c.b - 1) = 0 ∨
      (if i + j ≤ c.B then c.b - 1 else 0) - g i j * (c.b - 1) = c.b - 1 := fun i j => by
    by_cases ht : tri c i j
    · have ht' : i + j ≤ c.B := ht
      rw [ite_eq_left ht', hg_val i j ht]; split_ifs <;> simp
    · have ht' : ¬ i + j ≤ c.B := ht
      simp [ite_eq_right ht']
  simp only [normalize]
  rw [hW, hG, hSm, hNm, key _ dW _ hdW_lt hg_lt hq1 rfl, key _ _ _ hO_lt hg_lt hq1 hO,
    key _ _ _ hO_lt hNm_lt hq2 hO, key _ dW _ hdW_lt hNm_lt hq2 rfl]
  constructor
  · rw [pack_sub]
    · apply pack_congr; intro i j _ _
      by_cases ht : tri c i j
      · have ht' : i + j ≤ c.B := ht
        simp only [hdW, hg_val i j ht, ite_eq_left ht]
        have := hu i j; have := hv i j
        split_ifs <;> omega
      · simp only [hdW, hg, ite_eq_right ht]; simp
    · intro i j
      by_cases ht : tri c i j
      · simp only [hdW, hg_val i j ht, ite_eq_left ht]; split_ifs <;> omega
      · simp only [hdW, hg, ite_eq_right ht]; simp
  · rw [pack_sub]
    · apply pack_congr; intro i j _ _
      by_cases ht : tri c i j
      · have ht' : i + j ≤ c.B := ht
        simp only [hdW, hg_val i j ht, ite_eq_left ht, ite_eq_left ht']
        have := hu i j; have := hv i j
        split_ifs <;> omega
      · have ht' : ¬ i + j ≤ c.B := ht
        simp only [hdW, hg, ite_eq_right ht, ite_eq_right ht']; simp
    · intro i j
      by_cases ht : tri c i j
      · have ht' : i + j ≤ c.B := ht
        simp only [hdW, hg_val i j ht, ite_eq_left ht, ite_eq_left ht']; split_ifs <;> omega
      · have ht' : ¬ i + j ≤ c.B := ht
        simp only [hdW, hg, ite_eq_right ht, ite_eq_right ht']; simp

/-! ## Digit sums and real values of packed numbers -/

/-- The digit sum of a number of the box. -/
def dsumN (c : Config) (N : ℕ) : ℕ := ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, coeffs c N i j

/-- The real polynomial `∑ coeffs · x^i y^j`. -/
def evalN (c : Config) (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, (coeffs c N i j : ℝ) * x ^ i * y ^ j

theorem dsumN_eq (c : Config) (N : ℕ) : dsumN c N = dsum (poly c N) := by
  rw [poly, dsum_ofFun]; rfl

theorem evalN_eq (c : Config) (N : ℕ) (x y : ℝ) : evalN c N x y = ev x y (poly c N) := by
  rw [poly, ev_ofFun]; rfl

theorem dsumN_pack (c : Config) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) :
    dsumN c (pack c d) = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, d i j :=
  Finset.sum_congr rfl fun _ hi => Finset.sum_congr rfl fun _ hj =>
    coeffs_pack c hd (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

theorem evalN_pack (c : Config) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b) (x y : ℝ) :
    evalN c (pack c d) x y =
      ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, (d i j : ℝ) * x ^ i * y ^ j :=
  Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    rw [coeffs_pack c hd (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]

theorem abs_evalN_le (c : Config) (N : ℕ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |evalN c N x y| ≤ dsumN c N := by
  unfold evalN dsumN
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_pow]
  have h1 : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have h2 : |y| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
  have h3 : (0 : ℝ) ≤ coeffs c N i j := Nat.cast_nonneg _
  calc (coeffs c N i j : ℝ) * |x| ^ i * |y| ^ j ≤ (coeffs c N i j : ℝ) * 1 * 1 := by
        gcongr
    _ = _ := by ring

theorem coeffs_le_dsumN (c : Config) (N : ℕ) {i j : ℕ} (hi : i < c.S) (hj : j < c.S) :
    coeffs c N i j ≤ dsumN c N :=
  (Finset.single_le_sum (f := fun j => coeffs c N i j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)).trans
    (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range c.S, coeffs c N i j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi))

/-- The modulus `2 ^ w - 1`: a number is congruent to its digit sum. -/
def Config.M (c : Config) : ℕ := c.b - 1

theorem dsumN_eq_sum (c : Config) (N : ℕ) :
    dsumN c N = ∑ u ∈ Finset.range (c.S * c.S), coeffs c N (u / c.S) (u % c.S) := by
  unfold dsumN
  apply double_sum_eq c.S c.S_pos
  intro i j hj
  have h1 : (c.S * i + j) / c.S = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ c.S_pos, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (c.S * i + j) % c.S = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [h1, h2]

theorem mod_eq_dsumN {c : Config} {N : ℕ} (h : Box c N) (hs : dsumN c N < c.M) :
    N % c.M = dsumN c N := by
  have hb1 : c.b ≡ 1 [MOD c.M] := Nat.modEq_sub c.b_pos
  have hN : N ≡ dsumN c N [MOD c.M] := by
    conv_lhs => rw [eq_pack_coeffs h, pack_eq_sum]
    rw [dsumN_eq_sum]
    apply Nat.ModEq.sum
    intro u _
    simpa using (Nat.ModEq.pow u hb1).mul_left (coeffs c N (u / c.S) (u % c.S))
  rw [hN, Nat.mod_eq_of_lt hs]

/-! ## Models -/

/-- The checks on a configuration: digits are wide enough for every product. -/
structure Config.Valid (c : Config) : Prop where
  B_pos : 1 ≤ c.B
  K_lt : c.K + 2 < c.w

/-- A packed Taylor model: the polynomial `(U - V) / 2 ^ K` read digitwise, an error bound
`e / 2 ^ K`, and `ok`, the conjunction of the checks made while building it. -/
structure Model where
  U : ℕ
  V : ℕ
  e : ℕ
  ok : Bool

namespace Model

/-- The polynomial of a model at a point. -/
def val (c : Config) (m : Model) (x y : ℝ) : ℝ := (evalN c m.U x y - evalN c m.V x y) / 2 ^ c.K

/-- The invariant of a model whose checks passed. -/
structure Good (c : Config) (m : Model) : Prop where
  triU : OnTri c m.U
  triV : OnTri c m.V
  small : dsumN c m.U + dsumN c m.V < 2 ^ (c.w - 2)

/-- `m` encloses the value `v` at `(x, y)`. -/
def Contains (c : Config) (m : Model) (x y v : ℝ) : Prop :=
  m.ok = true → m.Good c ∧ |v - m.val c x y| ≤ (m.e : ℝ) / 2 ^ c.K

/-- The digit sum `‖U‖ + ‖V‖`, computed modulo `2 ^ w - 1`. -/
def size (c : Config) (m : Model) : ℕ := m.U % c.M + m.V % c.M

end Model

theorem lim_lt_M {c : Config} (hc : c.Valid) : 2 ^ (c.w - 2) < c.M := by
  unfold Config.M Config.b
  have h1 : 2 ^ (c.w - 2) * 4 = 2 ^ c.w := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel (by have := hc.K_lt; omega)]
  have h2 : 1 ≤ 2 ^ (c.w - 2) := Nat.one_le_two_pow
  omega

theorem Model.Good.size_eq {c : Config} (hc : c.Valid) {m : Model} (h : m.Good c) :
    m.size c = dsumN c m.U + dsumN c m.V := by
  have hl := lim_lt_M hc
  unfold Model.size
  rw [mod_eq_dsumN h.triU.1 (by have := h.small; omega),
    mod_eq_dsumN h.triV.1 (by have := h.small; omega)]

theorem digit_le_dsumN {c : Config} {N : ℕ} (hN : Box c N) (m : ℕ) :
    digit c.w N m ≤ dsumN c N := by
  by_cases hm : m < c.S * c.S
  · have hq : m / c.S < c.S := by
      rw [Nat.div_lt_iff_lt_mul c.S_pos]; exact hm
    have hr : m % c.S < c.S := Nat.mod_lt _ c.S_pos
    have := coeffs_le_dsumN c N hq hr
    rwa [coeffs, Nat.div_add_mod] at this
  · rw [digit_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right c.b_pos (by omega)))]
    exact Nat.zero_le _

theorem coeffs_le_dsumN' {c : Config} {N : ℕ} (hN : Box c N) (i j : ℕ) :
    coeffs c N i j ≤ dsumN c N := digit_le_dsumN hN _

theorem Model.Good.coeffs_lt {c : Config} {m : Model} (h : m.Good c) (i j : ℕ) :
    coeffs c m.U i j < 2 ^ (c.w - 2) ∧ coeffs c m.V i j < 2 ^ (c.w - 2) := by
  have h1 := coeffs_le_dsumN' h.triU.1 i j
  have h2 := coeffs_le_dsumN' h.triV.1 i j
  have := h.small
  omega

theorem abs_val_le {c : Config} {m : Model} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |m.val c x y| ≤ ((dsumN c m.U + dsumN c m.V : ℕ) : ℝ) / 2 ^ c.K := by
  unfold Model.val
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ c.K)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := abs_evalN_le c m.U hx hy
  have h2 := abs_evalN_le c m.V hx hy
  push_cast
  calc |evalN c m.U x y - evalN c m.V x y| ≤ |evalN c m.U x y| + |evalN c m.V x y| :=
        abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-! ## Basic operations -/

theorem evalN_onTri {c : Config} {N : ℕ} (h : OnTri c N) (x y : ℝ) :
    evalN c N x y = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      (if tri c i j then (coeffs c N i j : ℝ) else 0) * x ^ i * y ^ j :=
  Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    split_ifs with ht
    · rfl
    · rw [h.2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) ht]; simp

theorem dsumN_onTri {c : Config} {N : ℕ} (h : OnTri c N) :
    dsumN c N = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      (if tri c i j then coeffs c N i j else 0) :=
  Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
    split_ifs with ht
    · rfl
    · exact h.2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) ht

/-- A single digit `a` at `(i₀, j₀)`. -/
theorem pack_single (c : Config) {i₀ j₀ : ℕ} (hi : i₀ < c.S) (hj : j₀ < c.S) (a : ℕ) :
    pack c (fun i j => if i = i₀ ∧ j = j₀ then a else 0) = a * c.b ^ (c.S * i₀ + j₀) := by
  unfold pack
  simp only [sumTo_eq]
  rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
  · simp
  · intro j _ hj'; simp [hj']
  · intro h; exact absurd (Finset.mem_range.mpr hj) h
  · intro i _ hi'
    exact Finset.sum_eq_zero fun j _ => by simp [hi']
  · intro h; exact absurd (Finset.mem_range.mpr hi) h

theorem single_props (c : Config) {i₀ j₀ a : ℕ} (hij : i₀ + j₀ ≤ c.B) (ha : a < c.b) :
    OnTri c (a * c.b ^ (c.S * i₀ + j₀)) ∧ dsumN c (a * c.b ^ (c.S * i₀ + j₀)) = a ∧
      ∀ x y : ℝ, evalN c (a * c.b ^ (c.S * i₀ + j₀)) x y = a * x ^ i₀ * y ^ j₀ := by
  have hd : ∀ i j, (if i = i₀ ∧ j = j₀ then a else 0) < c.b := fun i j => by
    split_ifs <;> omega
  have hi : i₀ < c.S := by unfold Config.S; omega
  have hj : j₀ < c.S := by unfold Config.S; omega
  rw [← pack_single c hi hj]
  refine ⟨onTri_pack hd fun i j ht => ?_, ?_, fun x y => ?_⟩
  · rw [ite_eq_right]; rintro ⟨rfl, rfl⟩; exact ht hij
  · rw [dsumN_pack c hd, Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj'; simp [hj']
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · intro i _ hi'; exact Finset.sum_eq_zero fun j _ => by simp [hi']
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · rw [evalN_pack c hd, Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj'; simp [hj']
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · intro i _ hi'; exact Finset.sum_eq_zero fun j _ => by simp [hi']
    · intro h; exact absurd (Finset.mem_range.mpr hi) h

theorem const_props (c : Config) {a : ℕ} (ha : a < c.b) :
    OnTri c a ∧ dsumN c a = a ∧ ∀ x y : ℝ, evalN c a x y = a := by
  have h := single_props c (i₀ := 0) (j₀ := 0) (Nat.zero_le _) ha
  simp only [mul_zero, add_zero, pow_zero, mul_one] at h
  exact h

namespace Model

/-- `-m`. -/
def neg (m : Model) : Model := ⟨m.V, m.U, m.e, m.ok⟩

/-- `m` with its error enlarged by `r / 2 ^ K`. -/
def widen (m : Model) (r : ℕ) : Model := ⟨m.U, m.V, m.e + r, m.ok⟩

/-- The constant `z / 2 ^ K` with error `e / 2 ^ K`. -/
def ofInt (c : Config) (z : ℤ) (e : ℕ) (ok : Bool) : Model :=
  if 0 ≤ z then ⟨z.toNat, 0, e, ok && Nat.blt z.toNat (2 ^ (c.w - 2))⟩
  else ⟨0, (-z).toNat, e, ok && Nat.blt (-z).toNat (2 ^ (c.w - 2))⟩

/-- The rational `n / d`, rounded down to the scale `2 ^ K`. -/
def lit (c : Config) (n : ℤ) (d : ℕ) : Model :=
  ofInt c (n * 2 ^ c.K / d) (if n * 2 ^ c.K % d = 0 then 0 else 1) (Nat.blt 0 d)

/-- The variable `x`. -/
def X (c : Config) : Model := ⟨2 ^ c.K * c.b ^ c.S, 0, 0, true⟩
/-- The variable `y`. -/
def Y (c : Config) : Model := ⟨2 ^ c.K * c.b, 0, 0, true⟩

theorem contains_neg {c : Config} {m : Model} {x y v : ℝ} (h : m.Contains c x y v) :
    m.neg.Contains c x y (-v) := by
  intro hok
  obtain ⟨hg, he⟩ := h hok
  refine ⟨⟨hg.triV, hg.triU, by simp only [neg]; have := hg.small; omega⟩, ?_⟩
  have : m.neg.val c x y = -m.val c x y := by simp only [val, neg]; ring
  rw [this, show -v - -m.val c x y = -(v - m.val c x y) by ring, abs_neg]
  exact he

theorem contains_widen {c : Config} {m : Model} {x y v w : ℝ} (h : m.Contains c x y v) (r : ℕ)
    (hvw : |w - v| ≤ (r : ℝ) / 2 ^ c.K) : (m.widen r).Contains c x y w := by
  intro hok
  obtain ⟨hg, he⟩ := h hok
  refine ⟨⟨hg.triU, hg.triV, hg.small⟩, ?_⟩
  have h1 := abs_sub_le w v (m.val c x y)
  show |w - m.val c x y| ≤ ((m.e + r : ℕ) : ℝ) / 2 ^ c.K
  push_cast
  rw [add_div]
  linarith

theorem lim_le_b (c : Config) : 2 ^ (c.w - 2) ≤ c.b :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

theorem contains_ofInt {c : Config} (z : ℤ) (e : ℕ) (ok : Bool) {x y v : ℝ}
    (hv : |v - (z : ℝ) / 2 ^ c.K| ≤ (e : ℝ) / 2 ^ c.K) : (ofInt c z e ok).Contains c x y v := by
  have h0 := const_props c (a := 0) c.b_pos
  unfold ofInt
  split_ifs with hz
  · intro hok
    simp only [Bool.and_eq_true, Nat.blt_eq] at hok
    have h1 := const_props c (lt_of_lt_of_le hok.2 (lim_le_b c))
    refine ⟨⟨h1.1, h0.1, by rw [h1.2.1, h0.2.1]; omega⟩, ?_⟩
    have hval : ∀ ok', val c ⟨z.toNat, 0, e, ok'⟩ x y = (z : ℝ) / 2 ^ c.K := by
      intro ok'
      simp only [val, h1.2.2, h0.2.2, Nat.cast_zero, sub_zero]
      congr 1; exact_mod_cast Int.toNat_of_nonneg hz
    rw [hval]; exact hv
  · intro hok
    simp only [Bool.and_eq_true, Nat.blt_eq] at hok
    have h1 := const_props c (lt_of_lt_of_le hok.2 (lim_le_b c))
    refine ⟨⟨h0.1, h1.1, by rw [h1.2.1, h0.2.1]; omega⟩, ?_⟩
    have hval : ∀ ok', val c ⟨0, (-z).toNat, e, ok'⟩ x y = (z : ℝ) / 2 ^ c.K := by
      intro ok'
      simp only [val, h1.2.2, h0.2.2, Nat.cast_zero, zero_sub]
      have : ((-z).toNat : ℝ) = -z := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [this]; ring
    rw [hval]; exact hv

theorem contains_lit (c : Config) (n : ℤ) (d : ℕ) {x y : ℝ} :
    (lit c n d).Contains c x y ((n : ℝ) / d) := by
  unfold lit
  by_cases hd : d = 0
  · intro hok; simp [ofInt, hd] at hok
  · apply contains_ofInt
    have hdpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
    set z := n * 2 ^ c.K / d
    set r := n * 2 ^ c.K % d
    have hdiv : n * 2 ^ c.K = d * z + r := (Int.mul_ediv_add_emod _ _).symm
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
    have hr1 : r < d := Int.emod_lt_of_pos _ hdpos
    have hdivR : (n : ℝ) * 2 ^ c.K = d * z + r := by exact_mod_cast hdiv
    have hdiff : (n : ℝ) / d - z / 2 ^ c.K = r / (d * 2 ^ c.K) := by
      field_simp; linarith
    rw [hdiff, abs_of_nonneg (by positivity)]
    split_ifs with hr
    · rw [hr]; simp
    · rw [Nat.cast_one, div_le_div_iff₀ (by positivity) h2K, one_mul]
      have : (r : ℝ) ≤ d := by exact_mod_cast hr1.le
      nlinarith

theorem contains_X {c : Config} (hc : c.Valid) (x y : ℝ) : (X c).Contains c x y x := by
  intro _
  have hK : 2 ^ c.K < 2 ^ (c.w - 2) := Nat.pow_lt_pow_right (by norm_num) (by have := hc.K_lt; omega)
  have h1 := single_props c (i₀ := 1) (j₀ := 0) (by have := hc.B_pos; omega)
    (lt_of_lt_of_le hK (lim_le_b c))
  have h0 := const_props c (a := 0) c.b_pos
  simp only [mul_one, add_zero] at h1
  refine ⟨⟨h1.1, h0.1, by show dsumN c (2 ^ c.K * c.b ^ c.S) + dsumN c 0 < _; rw [h1.2.1, h0.2.1]; omega⟩, ?_⟩
  simp only [X, val, h1.2.2, h0.2.2]
  push_cast
  rw [show (2 : ℝ) ^ c.K * x ^ 1 * y ^ 0 - 0 = 2 ^ c.K * x by ring,
    mul_div_cancel_left₀ _ (by positivity)]
  simp

theorem contains_Y {c : Config} (hc : c.Valid) (x y : ℝ) : (Y c).Contains c x y y := by
  intro _
  have hK : 2 ^ c.K < 2 ^ (c.w - 2) := Nat.pow_lt_pow_right (by norm_num) (by have := hc.K_lt; omega)
  have h1 := single_props c (i₀ := 0) (j₀ := 1) (by have := hc.B_pos; omega)
    (lt_of_lt_of_le hK (lim_le_b c))
  have h0 := const_props c (a := 0) c.b_pos
  simp only [mul_zero, zero_add, pow_one] at h1
  refine ⟨⟨h1.1, h0.1, by show dsumN c (2 ^ c.K * c.b) + dsumN c 0 < _; rw [h1.2.1, h0.2.1]; omega⟩, ?_⟩
  simp only [Y, val, h1.2.2, h0.2.2]
  push_cast
  rw [show (2 : ℝ) ^ c.K * x ^ 0 * y - 0 = 2 ^ c.K * y by ring,
    mul_div_cancel_left₀ _ (by positivity)]
  simp

end Model

/-! ## Sums and products of models -/

/-- Properties of `normalize` used below. -/
theorem normalize_props {c : Config} (hc : c.Valid) {U V : ℕ} (hU : OnTri c U) (hV : OnTri c V)
    (hs : dsumN c U + dsumN c V < 2 ^ (c.w - 2)) :
    OnTri c (normalize c U V).1 ∧ OnTri c (normalize c U V).2 ∧
    dsumN c (normalize c U V).1 + dsumN c (normalize c U V).2 ≤ dsumN c U + dsumN c V ∧
    ∀ x y : ℝ, evalN c (normalize c U V).1 x y - evalN c (normalize c U V).2 x y =
      evalN c U x y - evalN c V x y := by
  have hw : 2 ≤ c.w := by have := hc.K_lt; omega
  have hlim : 2 ^ (c.w - 2) ≤ 2 ^ (c.w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hu : ∀ i j, coeffs c U i j < 2 ^ (c.w - 1) := fun i j => by
    have := coeffs_le_dsumN' hU.1 i j; omega
  have hv : ∀ i j, coeffs c V i j < 2 ^ (c.w - 1) := fun i j => by
    have := coeffs_le_dsumN' hV.1 i j; omega
  obtain ⟨h1, h2⟩ := normalize_spec hw hU hV hu hv
  have hlt : ∀ (p q : ℕ → ℕ → ℕ), (∀ i j, p i j < c.b) →
      ∀ i j, (if tri c i j then p i j - q i j else 0) < c.b := fun p q hp i j => by
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (hp i j)
    · exact c.b_pos
  have hcU : ∀ i j, coeffs c U i j < c.b := coeffs_lt c U
  have hcV : ∀ i j, coeffs c V i j < c.b := coeffs_lt c V
  have hP := hlt _ (coeffs c V) hcU
  have hN := hlt _ (coeffs c U) hcV
  rw [h1, h2]
  refine ⟨onTri_pack hP (fun i j ht => by simp [ht]), onTri_pack hN (fun i j ht => by simp [ht]),
    ?_, fun x y => ?_⟩
  · rw [dsumN_pack c hP, dsumN_pack c hN, dsumN_onTri hU, dsumN_onTri hV,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs <;> omega
  · rw [evalN_pack c hP, evalN_pack c hN, evalN_onTri hU, evalN_onTri hV,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rcases le_total (coeffs c V i j) (coeffs c U i j) with h | h
      · rw [Nat.sub_eq_zero_of_le h]; push_cast [h]; ring
      · rw [Nat.sub_eq_zero_of_le h]; push_cast [h]; ring
    · simp

namespace Model

/-- `a + b`. -/
def add (c : Config) (a b : Model) : Model :=
  let x := normalize c (a.U + b.U) (a.V + b.V)
  ⟨x.1, x.2, a.e + b.e, a.ok && b.ok && Nat.blt (a.size c + b.size c) (2 ^ (c.w - 2))⟩

/-- `U + V` of two triangle numbers with small digit sums. -/
theorem onTri_add {c : Config} {U V : ℕ} (hU : OnTri c U) (hV : OnTri c V)
    (hs : dsumN c U + dsumN c V < c.b) :
    OnTri c (U + V) ∧ dsumN c (U + V) = dsumN c U + dsumN c V ∧
      ∀ x y : ℝ, evalN c (U + V) x y = evalN c U x y + evalN c V x y := by
  have hd : ∀ i j, (if tri c i j then coeffs c U i j + coeffs c V i j else 0) < c.b := fun i j => by
    split_ifs
    · have := coeffs_le_dsumN' hU.1 i j; have := coeffs_le_dsumN' hV.1 i j; omega
    · exact c.b_pos
  have he : U + V = pack c (fun i j => if tri c i j then coeffs c U i j + coeffs c V i j else 0) := by
    conv_lhs => rw [pack_restrict hU, pack_restrict hV]
    rw [pack_add]
    apply pack_congr; intro i j _ _
    by_cases ht : tri c i j <;> simp [ht]
  rw [he]
  refine ⟨onTri_pack hd (fun i j ht => by simp [ht]), ?_, fun x y => ?_⟩
  · rw [dsumN_pack c hd, dsumN_onTri hU, dsumN_onTri hV, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · rw [evalN_pack c hd, evalN_onTri hU, evalN_onTri hV, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> push_cast <;> ring

theorem contains_add {c : Config} (hc : c.Valid) {a b : Model} {x y v w : ℝ}
    (ha : a.Contains c x y v) (hb : b.Contains c x y w) : (add c a b).Contains c x y (v + w) := by
  intro hok
  simp only [add, Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨hoa, hob⟩, hs⟩ := hok
  obtain ⟨ga, ea⟩ := ha hoa
  obtain ⟨gb, eb⟩ := hb hob
  rw [ga.size_eq hc, gb.size_eq hc] at hs
  have hlb := lim_le_b c
  obtain ⟨hU1, hU2, hU3⟩ := onTri_add ga.triU gb.triU (by omega)
  obtain ⟨hV1, hV2, hV3⟩ := onTri_add ga.triV gb.triV (by omega)
  obtain ⟨n1, n2, n3, n4⟩ := normalize_props hc hU1 hV1 (by omega)
  refine ⟨⟨n1, n2, by simp only [add]; omega⟩, ?_⟩
  have hval : (add c a b).val c x y = a.val c x y + b.val c x y := by
    simp only [val, add]
    rw [n4, hU3, hV3]
    ring
  rw [hval]
  simp only [add]
  push_cast
  rw [add_div]
  have := abs_add_le (v - a.val c x y) (w - b.val c x y)
  rw [show v - a.val c x y + (w - b.val c x y) = v + w - (a.val c x y + b.val c x y) by ring] at this
  linarith

end Model

theorem raw_mul {c : Config} (_hc : c.Valid) {a b : Model} (ga : a.Good c) (gb : b.Good c)
    (hs : (dsumN c a.U + dsumN c a.V) * (dsumN c b.U + dsumN c b.V) < 2 ^ (c.w - 2)) :
    Box c (a.U * b.U + a.V * b.V) ∧ Box c (a.U * b.V + a.V * b.U) ∧
    dsumN c (a.U * b.U + a.V * b.V) + dsumN c (a.U * b.V + a.V * b.U) =
      (dsumN c a.U + dsumN c a.V) * (dsumN c b.U + dsumN c b.V) ∧
    ∀ x y : ℝ, evalN c (a.U * b.U + a.V * b.V) x y - evalN c (a.U * b.V + a.V * b.U) x y =
      (evalN c a.U x y - evalN c a.V x y) * (evalN c b.U x y - evalN c b.V x y) := by
  have hlb := Model.lim_le_b c
  have tU := tri_poly ga.triU; have tV := tri_poly ga.triV
  have tU' := tri_poly gb.triU; have tV' := tri_poly gb.triV
  simp only [dsumN_eq] at hs ⊢
  simp only [evalN_eq]
  have hAB : dsum (poly c a.U) * dsum (poly c b.U) < c.b := by nlinarith
  have hA'B' : dsum (poly c a.V) * dsum (poly c b.V) < c.b := by nlinarith
  have hAB' : dsum (poly c a.U) * dsum (poly c b.V) < c.b := by nlinarith
  have hA'B : dsum (poly c a.V) * dsum (poly c b.U) < c.b := by nlinarith
  obtain ⟨b1, p1⟩ := poly_mul ga.triU.1 gb.triU.1 tU tU' hAB
  obtain ⟨b2, p2⟩ := poly_mul ga.triV.1 gb.triV.1 tV tV' hA'B'
  obtain ⟨b3, p3⟩ := poly_mul ga.triU.1 gb.triV.1 tU tV' hAB'
  obtain ⟨b4, p4⟩ := poly_mul ga.triV.1 gb.triU.1 tV tU' hA'B
  have d1 : dsum (poly c (a.U * b.U)) = dsum (poly c a.U) * dsum (poly c b.U) := by
    rw [p1, dsum, map_mul]; rfl
  have d2 : dsum (poly c (a.V * b.V)) = dsum (poly c a.V) * dsum (poly c b.V) := by
    rw [p2, dsum, map_mul]; rfl
  have d3 : dsum (poly c (a.U * b.V)) = dsum (poly c a.U) * dsum (poly c b.V) := by
    rw [p3, dsum, map_mul]; rfl
  have d4 : dsum (poly c (a.V * b.U)) = dsum (poly c a.V) * dsum (poly c b.U) := by
    rw [p4, dsum, map_mul]; rfl
  obtain ⟨b5, p5⟩ := poly_add b1 b2 (by rw [d1, d2]; nlinarith)
  obtain ⟨b6, p6⟩ := poly_add b3 b4 (by rw [d3, d4]; nlinarith)
  refine ⟨b5, b6, ?_, fun x y => ?_⟩
  · have e5 : dsum (poly c (a.U * b.U + a.V * b.V)) =
        dsum (poly c (a.U * b.U)) + dsum (poly c (a.V * b.V)) := by rw [p5, dsum, map_add]; rfl
    have e6 : dsum (poly c (a.U * b.V + a.V * b.U)) =
        dsum (poly c (a.U * b.V)) + dsum (poly c (a.V * b.U)) := by rw [p6, dsum, map_add]; rfl
    rw [e5, e6, d1, d2, d3, d4]; ring
  · rw [p5, p6, map_add, map_add, p1, p2, p3, p4]
    simp only [map_mul]; ring

theorem trunc_props {c : Config} {N : ℕ} (_hN : Box c N) :
    OnTri c (N &&& triMask c) ∧ dsumN c (N &&& triMask c) ≤ dsumN c N ∧
    ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 →
      |evalN c N x y - evalN c (N &&& triMask c) x y| ≤
        (dsumN c N : ℝ) - dsumN c (N &&& triMask c) := by
  have hd : ∀ i j, (if tri c i j then coeffs c N i j else 0) < c.b := fun i j => by
    split_ifs
    · exact coeffs_lt c N i j
    · exact c.b_pos
  rw [truncate_eq]
  refine ⟨onTri_pack hd (fun i j ht => by simp [ht]), ?_, fun x y hx hy => ?_⟩
  · rw [dsumN_pack c hd]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by split_ifs <;> simp
  · rw [evalN_pack c hd, dsumN_pack c hd]
    unfold evalN dsumN
    push_cast
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h1 : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    have h2 : |y| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    split_ifs
    · simp
    · simp only [zero_mul, sub_zero]
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_pow]
      have h3 : (0 : ℝ) ≤ coeffs c N i j := Nat.cast_nonneg _
      calc (coeffs c N i j : ℝ) * |x| ^ i * |y| ^ j ≤ (coeffs c N i j : ℝ) * 1 * 1 := by gcongr
        _ = _ := by ring

theorem frac_bound (p q : ℕ) (hq : 0 < q) :
    0 ≤ (p : ℝ) / q - ((p / q : ℕ) : ℝ) ∧ (p : ℝ) / q - ((p / q : ℕ) : ℝ) < 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h := Nat.div_add_mod p q
  have hr : p % q < q := Nat.mod_lt _ hq
  have hR : (p : ℝ) = q * ((p / q : ℕ) : ℝ) + ((p % q : ℕ) : ℝ) := by exact_mod_cast h.symm
  have hrR : ((p % q : ℕ) : ℝ) < q := by exact_mod_cast hr
  rw [hR, add_div, mul_div_cancel_left₀ _ hqR.ne']
  constructor
  · have : (0 : ℝ) ≤ ((p % q : ℕ) : ℝ) / q := by positivity
    linarith
  · have : ((p % q : ℕ) : ℝ) / q < 1 := (div_lt_one hqR).mpr hrR
    linarith

theorem round_props {c : Config} (hc : c.Valid) {P N : ℕ} (hP : OnTri c P) (hN : OnTri c N) :
    OnTri c ((P &&& hiMask c) >>> c.K) ∧ OnTri c ((N &&& hiMask c) >>> c.K) ∧
    dsumN c ((P &&& hiMask c) >>> c.K) + dsumN c ((N &&& hiMask c) >>> c.K) ≤
      dsumN c P + dsumN c N ∧
    ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 →
      |(evalN c P x y - evalN c N x y) / 2 ^ c.K -
        (evalN c ((P &&& hiMask c) >>> c.K) x y - evalN c ((N &&& hiMask c) >>> c.K) x y)| ≤
        ((c.S * c.S : ℕ) : ℝ) := by
  have hK : c.K ≤ c.w := by have := hc.K_lt; omega
  have hd : ∀ (Q : ℕ) i j, (if tri c i j then coeffs c Q i j / 2 ^ c.K else 0) < c.b :=
    fun Q i j => by
    split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (coeffs_lt c Q i j)
    · exact c.b_pos
  rw [round_eq hK, round_eq hK]
  refine ⟨onTri_pack (hd P) (fun i j ht => by simp [ht]), onTri_pack (hd N) (fun i j ht => by simp [ht]),
    ?_, fun x y hx hy => ?_⟩
  · rw [dsumN_pack c (hd P), dsumN_pack c (hd N), dsumN_onTri hP, dsumN_onTri hN,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact Nat.add_le_add (Nat.div_le_self _ _) (Nat.div_le_self _ _)
    · exact le_rfl
  · have key : (evalN c P x y - evalN c N x y) / 2 ^ c.K -
        (evalN c (pack c fun i j => if tri c i j then coeffs c P i j / 2 ^ c.K else 0) x y -
          evalN c (pack c fun i j => if tri c i j then coeffs c N i j / 2 ^ c.K else 0) x y) =
        ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
          (if tri c i j then
            (((coeffs c P i j : ℝ) / 2 ^ c.K - ((coeffs c P i j / 2 ^ c.K : ℕ) : ℝ)) -
              ((coeffs c N i j : ℝ) / 2 ^ c.K - ((coeffs c N i j / 2 ^ c.K : ℕ) : ℝ)))
           else 0) * (x ^ i * y ^ j) := by
      rw [evalN_onTri hP, evalN_onTri hN, evalN_pack c (hd P), evalN_pack c (hd N)]
      simp only [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> push_cast <;> ring
    rw [key]
    calc _ ≤ ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, (1 : ℝ) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          have h1 : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
          have h2 : |y| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
          rw [abs_mul, abs_mul, abs_pow, abs_pow]
          have hδ : |(if tri c i j then
            (((coeffs c P i j : ℝ) / 2 ^ c.K - ((coeffs c P i j / 2 ^ c.K : ℕ) : ℝ)) -
              ((coeffs c N i j : ℝ) / 2 ^ c.K - ((coeffs c N i j / 2 ^ c.K : ℕ) : ℝ)))
           else 0)| ≤ 1 := by
            split_ifs
            · have fp := frac_bound (coeffs c P i j) (2 ^ c.K) (by positivity)
              have fn := frac_bound (coeffs c N i j) (2 ^ c.K) (by positivity)
              push_cast at fp fn
              rw [abs_le]; constructor <;> linarith [fp.1, fp.2, fn.1, fn.2]
            · simp
          have hxy : |x| ^ i * |y| ^ j ≤ 1 := (mul_le_mul h1 h2 (by positivity) zero_le_one).trans_eq (one_mul 1)
          exact (mul_le_mul hδ hxy (by positivity) zero_le_one).trans (by norm_num)
      _ = ((c.S * c.S : ℕ) : ℝ) := by simp

namespace Model

/-- The number of digits of the box, a bound on the rounding error of a product. -/
def boxCount (c : Config) : ℕ := c.S * c.S

/-- `a * b`: the exact product of the polynomials, cut to total degree `B` (the cut part goes
into the error), normalized and rounded to the scale `2 ^ K`. -/
def mul (c : Config) (a b : Model) : Model :=
  let sa := a.size c
  let sb := b.size c
  let U := a.U * b.U + a.V * b.V
  let V := a.U * b.V + a.V * b.U
  let Ut := U &&& triMask c
  let Vt := V &&& triMask c
  let kept := Ut % c.M + Vt % c.M
  let x := normalize c Ut Vt
  ⟨(x.1 &&& hiMask c) >>> c.K, (x.2 &&& hiMask c) >>> c.K,
    (sa * sb - kept + a.e * sb + b.e * sa + a.e * b.e + (2 ^ c.K - 1)) / 2 ^ c.K + boxCount c,
    a.ok && b.ok && Nat.blt (sa * sb) (2 ^ (c.w - 2))⟩

theorem ceil_div_ge (n q : ℕ) (hq : 0 < q) : (n : ℝ) / q ≤ (((n + (q - 1)) / q : ℕ) : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hqR]
  have h := Nat.div_add_mod (n + (q - 1)) q
  have hr : (n + (q - 1)) % q < q := Nat.mod_lt _ hq
  have : n ≤ q * ((n + (q - 1)) / q) := by omega
  rw [mul_comm]
  exact_mod_cast this

theorem contains_mul {c : Config} (hc : c.Valid) {a b : Model} {x y v w : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (ha : a.Contains c x y v) (hb : b.Contains c x y w) : (mul c a b).Contains c x y (v * w) := by
  intro hok
  simp only [mul, Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨hoa, hob⟩, hs⟩ := hok
  obtain ⟨ga, ea⟩ := ha hoa
  obtain ⟨gb, eb⟩ := hb hob
  have hsa := ga.size_eq hc
  have hsb := gb.size_eq hc
  rw [hsa, hsb] at hs
  have hlM := lim_lt_M hc
  obtain ⟨bU, bV, hsum, hval⟩ := raw_mul hc ga gb hs
  obtain ⟨t1, t2, t3⟩ := trunc_props bU
  obtain ⟨u1, u2, u3⟩ := trunc_props bV
  have hkU := mod_eq_dsumN t1.1 (by omega)
  have hkV := mod_eq_dsumN u1.1 (by omega)
  obtain ⟨n1, n2, n3, n4⟩ := normalize_props hc t1 u1 (by omega)
  obtain ⟨r1, r2, r3, r4⟩ := round_props hc n1 n2
  -- name the pieces of the product
  generalize hU : a.U * b.U + a.V * b.V = U at *
  generalize hV : a.U * b.V + a.V * b.U = V at *
  generalize hUt : U &&& triMask c = Ut at *
  generalize hVt : V &&& triMask c = Vt at *
  generalize hP : (normalize c Ut Vt).1 = P at *
  generalize hN : (normalize c Ut Vt).2 = N at *
  generalize hRP : (P &&& hiMask c) >>> c.K = RP at *
  generalize hRN : (N &&& hiMask c) >>> c.K = RN at *
  have hm : mul c a b = ⟨RP, RN, (a.size c * b.size c - (Ut % c.M + Vt % c.M) + a.e * b.size c +
      b.e * a.size c + a.e * b.e + (2 ^ c.K - 1)) / 2 ^ c.K + boxCount c,
      a.ok && b.ok && Nat.blt (a.size c * b.size c) (2 ^ (c.w - 2))⟩ := by
    simp only [mul, hU, hV, hUt, hVt, hP, hN, hRP, hRN]
  rw [hm, hsa, hsb, hkU, hkV]
  refine ⟨⟨r1, r2, by simp only; omega⟩, ?_⟩
  -- the error budget
  set SA := dsumN c a.U + dsumN c a.V with hSA
  set SB := dsumN c b.U + dsumN c b.V with hSB
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hA := abs_val_le (m := a) (c := c) hx hy
  have hB := abs_val_le (m := b) (c := c) hx hy
  set A := a.val c x y with hAdef
  set B := b.val c x y with hBdef
  have hprod : evalN c U x y - evalN c V x y = 2 ^ c.K * A * (2 ^ c.K * B) := by
    rw [hval]; simp only [hAdef, hBdef, val]; field_simp
  have hcut : |(evalN c U x y - evalN c V x y) - (evalN c Ut x y - evalN c Vt x y)| ≤
      (SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt) := by
    have e1 := t3 x y hx hy
    have e2 := u3 x y hx hy
    have hS : ((SA * SB : ℕ) : ℝ) = (dsumN c U : ℝ) + dsumN c V := by rw [← hsum]; push_cast; ring
    push_cast at hS
    calc _ = |(evalN c U x y - evalN c Ut x y) - (evalN c V x y - evalN c Vt x y)| := by ring_nf
      _ ≤ |evalN c U x y - evalN c Ut x y| + |evalN c V x y - evalN c Vt x y| := abs_sub _ _
      _ ≤ _ := by rw [hS]; linarith
  have hround := r4 x y hx hy
  rw [n4] at hround
  have hR : val c ⟨RP, RN, 0, true⟩ x y = (evalN c RP x y - evalN c RN x y) / 2 ^ c.K := rfl
  show |v * w - (evalN c RP x y - evalN c RN x y) / 2 ^ c.K| ≤ _
  -- |v w - A B|
  have hvA : |v - A| ≤ (a.e : ℝ) / 2 ^ c.K := ea
  have hwB : |w - B| ≤ (b.e : ℝ) / 2 ^ c.K := eb
  have hA' : |A| ≤ (SA : ℝ) / 2 ^ c.K := by simpa [hSA] using hA
  have hB' : |B| ≤ (SB : ℝ) / 2 ^ c.K := by simpa [hSB] using hB
  have hvw : |v * w - A * B| ≤ ((a.e : ℝ) * b.e + a.e * SB + b.e * SA) / (2 ^ c.K * 2 ^ c.K) := by
    have e : v * w - A * B = (v - A) * (w - B) + (v - A) * B + A * (w - B) := by ring
    rw [e]
    have i1 : |(v - A) * (w - B)| ≤ (a.e : ℝ) / 2 ^ c.K * (b.e / 2 ^ c.K) := by
      rw [abs_mul]; exact mul_le_mul hvA hwB (abs_nonneg _) (by positivity)
    have i2 : |(v - A) * B| ≤ (a.e : ℝ) / 2 ^ c.K * (SB / 2 ^ c.K) := by
      rw [abs_mul]; exact mul_le_mul hvA hB' (abs_nonneg _) (by positivity)
    have i3 : |A * (w - B)| ≤ (SA : ℝ) / 2 ^ c.K * (b.e / 2 ^ c.K) := by
      rw [abs_mul]; exact mul_le_mul hA' hwB (abs_nonneg _) (by positivity)
    calc _ ≤ |(v - A) * (w - B)| + |(v - A) * B| + |A * (w - B)| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by
          have : ((a.e : ℝ) * b.e + a.e * SB + b.e * SA) / (2 ^ c.K * 2 ^ c.K) =
              (a.e : ℝ) / 2 ^ c.K * (b.e / 2 ^ c.K) + (a.e : ℝ) / 2 ^ c.K * (SB / 2 ^ c.K) +
                (SA : ℝ) / 2 ^ c.K * (b.e / 2 ^ c.K) := by field_simp
          rw [this]; linarith
  -- the cut and the rounding
  have hT : |A * B - (evalN c Ut x y - evalN c Vt x y) / (2 ^ c.K * 2 ^ c.K)| ≤
      ((SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt)) / (2 ^ c.K * 2 ^ c.K) := by
    rw [show A * B - (evalN c Ut x y - evalN c Vt x y) / (2 ^ c.K * 2 ^ c.K) =
      ((evalN c U x y - evalN c V x y) - (evalN c Ut x y - evalN c Vt x y)) / (2 ^ c.K * 2 ^ c.K) by
        rw [hprod]; field_simp]
    have h4K : (0 : ℝ) < 2 ^ c.K * 2 ^ c.K := by positivity
    rw [abs_div, abs_of_pos h4K]
    exact div_le_div_of_nonneg_right hcut h4K.le
  have hRnd : |(evalN c Ut x y - evalN c Vt x y) / (2 ^ c.K * 2 ^ c.K) -
      (evalN c RP x y - evalN c RN x y) / 2 ^ c.K| ≤ ((c.S * c.S : ℕ) : ℝ) / 2 ^ c.K := by
    rw [show (evalN c Ut x y - evalN c Vt x y) / (2 ^ c.K * 2 ^ c.K) -
        (evalN c RP x y - evalN c RN x y) / 2 ^ c.K =
        ((evalN c Ut x y - evalN c Vt x y) / 2 ^ c.K - (evalN c RP x y - evalN c RN x y)) / 2 ^ c.K by
        field_simp]
    rw [abs_div, abs_of_pos h2K]
    exact div_le_div_of_nonneg_right hround h2K.le
  -- the error field
  have hle : dsumN c Ut + dsumN c Vt ≤ SA * SB := by omega
  have hceil := ceil_div_ge (SA * SB - (dsumN c Ut + dsumN c Vt) + a.e * SB + b.e * SA + a.e * b.e)
    (2 ^ c.K) (by positivity)
  have hcast : (((SA * SB - (dsumN c Ut + dsumN c Vt) + a.e * SB + b.e * SA + a.e * b.e : ℕ)) : ℝ) =
      ((SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt)) + a.e * SB + b.e * SA + a.e * b.e := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_sub hle]; push_cast; ring
  rw [hcast] at hceil
  push_cast at hceil
  have hgoal : |v * w - (evalN c RP x y - evalN c RN x y) / 2 ^ c.K| ≤
      (((SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt)) + a.e * SB + b.e * SA + a.e * b.e) / (2 ^ c.K * 2 ^ c.K)
        + ((c.S * c.S : ℕ) : ℝ) / 2 ^ c.K := by
    have := abs_sub_le (v * w) (A * B) ((evalN c RP x y - evalN c RN x y) / 2 ^ c.K)
    have := abs_sub_le (A * B) ((evalN c Ut x y - evalN c Vt x y) / (2 ^ c.K * 2 ^ c.K))
      ((evalN c RP x y - evalN c RN x y) / 2 ^ c.K)
    have hsplit : (((SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt)) + a.e * SB + b.e * SA + a.e * b.e) /
        (2 ^ c.K * 2 ^ c.K) = ((a.e : ℝ) * b.e + a.e * SB + b.e * SA) / (2 ^ c.K * 2 ^ c.K) +
        ((SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt)) / (2 ^ c.K * 2 ^ c.K) := by ring
    rw [hsplit]; linarith
  have hdiv : (((SA * SB : ℝ) - (dsumN c Ut + dsumN c Vt)) + a.e * SB + b.e * SA + a.e * b.e) /
      (2 ^ c.K * 2 ^ c.K) ≤
      ((((SA * SB - (dsumN c Ut + dsumN c Vt) + a.e * SB + b.e * SA + a.e * b.e + (2 ^ c.K - 1)) /
        2 ^ c.K : ℕ)) : ℝ) / 2 ^ c.K := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hceil h2K.le
  show _ ≤ ((((SA * SB - (dsumN c Ut + dsumN c Vt) + a.e * SB + b.e * SA + a.e * b.e +
      (2 ^ c.K - 1)) / 2 ^ c.K + boxCount c : ℕ)) : ℝ) / 2 ^ c.K
  rw [Nat.cast_add, add_div]
  simp only [boxCount] at hgoal ⊢
  linarith

end Model

/-! ## Polynomials, sine and cosine of models -/

namespace Model

/-- The constant `1`. -/
def one (c : Config) : Model := ofInt c (2 ^ c.K) 0 true

theorem contains_one (c : Config) (x y : ℝ) : (one c).Contains c x y 1 := by
  apply contains_ofInt
  have : ((2 ^ c.K : ℤ) : ℝ) / 2 ^ c.K = 1 := by push_cast; exact div_self (by positivity)
  rw [this]; simp

/-- `a ^ n`, by repeated products. -/
def pow (c : Config) (a : Model) : ℕ → Model
  | 0 => one c
  | 1 => a
  | n + 2 => mul c (pow c a (n + 1)) a

theorem contains_pow {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) : ∀ n, (pow c a n).Contains c x y (v ^ n)
  | 0 => by simpa [pow] using contains_one c x y
  | 1 => by simpa [pow] using ha
  | n + 2 => by
    rw [pow, pow_succ]
    exact contains_mul hc hx hy (contains_pow hc hx hy ha (n + 1)) ha

/-- `∑ (n_k / d_k) v ^ k` by Horner's rule. -/
def horner (c : Config) (a : Model) : List (ℤ × ℕ) → Model
  | [] => ofInt c 0 0 true
  | q :: l => add c (lit c q.1 q.2) (mul c a (horner c a l))

/-- The real value of Horner's rule. -/
def hornerVal (v : ℝ) : List (ℤ × ℕ) → ℝ
  | [] => 0
  | q :: l => (q.1 : ℝ) / q.2 + v * hornerVal v l

theorem contains_horner {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) : ∀ l, (horner c a l).Contains c x y (hornerVal v l)
  | [] => contains_ofInt 0 0 true (by simp [hornerVal])
  | q :: l => by
    rw [horner, hornerVal]
    exact contains_add hc (contains_lit c q.1 q.2)
      (contains_mul hc hx hy ha (contains_horner hc hx hy ha l))

/-- `S13` and `C14` as Horner coefficients in `v ^ 2`. -/
def sinCoeffs : List (ℤ × ℕ) :=
  [(1, 1), (-1, 6), (1, 120), (-1, 5040), (1, 362880), (-1, 39916800), (1, 6227020800)]
def cosCoeffs : List (ℤ × ℕ) :=
  [(1, 1), (-1, 2), (1, 24), (-1, 720), (1, 40320), (-1, 3628800), (1, 479001600),
    (-1, 87178291200)]

theorem sinCoeffs_val (v : ℝ) : v * hornerVal (v * v) sinCoeffs = HighOrderTaylor.S13 v := by
  simp only [sinCoeffs, hornerVal, HighOrderTaylor.S13, HighOrderTaylor.S11, Arithmetic.sin9,
    Arithmetic.sin7]
  push_cast; ring

theorem cosCoeffs_val (v : ℝ) : hornerVal (v * v) cosCoeffs = HighOrderTaylor.C14 v := by
  simp only [cosCoeffs, hornerVal, HighOrderTaylor.C14, HighOrderTaylor.C12, Arithmetic.cos10,
    Arithmetic.cos8]
  push_cast; ring

/-- `⌈(7/10)^15 / 15! · 2^K⌉` and `⌈(7/10)^16 / 16! · 2^K⌉`. -/
def sinRem (c : Config) : ℕ := (7 ^ 15 * 2 ^ c.K + (10 ^ 15 * 1307674368000 - 1)) / (10 ^ 15 * 1307674368000)
def cosRem (c : Config) : ℕ := (7 ^ 16 * 2 ^ c.K + (10 ^ 16 * 20922789888000 - 1)) / (10 ^ 16 * 20922789888000)

/-- `sin v` for `v ∈ [0, 7/10]`. -/
def sin (c : Config) (a : Model) : Model := widen (mul c a (horner c (mul c a a) sinCoeffs)) (sinRem c)
/-- `cos v` for `v ∈ [0, 7/10]`. -/
def cos (c : Config) (a : Model) : Model := widen (horner c (mul c a a) cosCoeffs) (cosRem c)

theorem sinRem_ge (c : Config) : ((7 : ℝ) / 10) ^ 15 / 1307674368000 ≤ (sinRem c : ℝ) / 2 ^ c.K := by
  have h := ceil_div_ge (7 ^ 15 * 2 ^ c.K) (10 ^ 15 * 1307674368000) (by positivity)
  have e : ((7 : ℝ) / 10) ^ 15 / 1307674368000 * 2 ^ c.K =
      ((7 ^ 15 * 2 ^ c.K : ℕ) : ℝ) / ((10 ^ 15 * 1307674368000 : ℕ) : ℝ) := by push_cast; ring
  rw [le_div_iff₀ (by positivity), e]
  exact h

theorem cosRem_ge (c : Config) : ((7 : ℝ) / 10) ^ 16 / 20922789888000 ≤ (cosRem c : ℝ) / 2 ^ c.K := by
  have h := ceil_div_ge (7 ^ 16 * 2 ^ c.K) (10 ^ 16 * 20922789888000) (by positivity)
  have e : ((7 : ℝ) / 10) ^ 16 / 20922789888000 * 2 ^ c.K =
      ((7 ^ 16 * 2 ^ c.K : ℕ) : ℝ) / ((10 ^ 16 * 20922789888000 : ℕ) : ℝ) := by push_cast; ring
  rw [le_div_iff₀ (by positivity), e]
  exact h

theorem contains_sin {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) (hv : v ∈ Set.Icc 0 frameCap) :
    (sin c a).Contains c x y (Real.sin v) := by
  have h := contains_mul hc hx hy ha (contains_horner hc hx hy (contains_mul hc hx hy ha ha) sinCoeffs)
  rw [sinCoeffs_val] at h
  apply contains_widen h
  have hlo := HighOrderTaylor.S15_le_sin hv.1
  have hhi := HighOrderTaylor.sin_le_S13 hv.1
  have hp := pow_le_pow_left₀ hv.1 hv.2 15
  have hr := sinRem_ge c
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  simp only [HighOrderTaylor.S15, frameCap] at hlo hp
  have : v ^ 15 / 1307674368000 ≤ ((7 : ℝ) / 10) ^ 15 / 1307674368000 := by gcongr
  linarith

theorem contains_cos {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) (hv : v ∈ Set.Icc 0 frameCap) :
    (cos c a).Contains c x y (Real.cos v) := by
  have h := contains_horner hc hx hy (contains_mul hc hx hy ha ha) cosCoeffs
  rw [cosCoeffs_val] at h
  apply contains_widen h
  have hlo := HighOrderTaylor.C14_le_cos hv.1
  have hhi := HighOrderTaylor.cos_le_C16 hv.1
  have hp := pow_le_pow_left₀ hv.1 hv.2 16
  have hr := cosRem_ge c
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  simp only [HighOrderTaylor.C16, frameCap] at hhi hp
  have : v ^ 16 / 20922789888000 ≤ ((7 : ℝ) / 10) ^ 16 / 20922789888000 := by gcongr
  linarith

end Model

/-! ## Bernstein lower bounds

For `f` of degree `≤ n`, `hom n f u w = ∑_{I ≤ n} f_I u^I w^(n-I)` is its homogenization. The
polynomial `(X - 1)^i (X + 1)^(n - i)` homogenizes to `(u - w)^i (u + w)^(n - i)`, which is
`x ^ i` at `u = (1 + x)/2`, `w = (1 - x)/2`. -/

/-- The homogenization of a real polynomial of degree `≤ n`. -/
def hom (n : ℕ) (f : ℝ[X]) (u w : ℝ) : ℝ :=
  ∑ I ∈ Finset.range (n + 1), f.coeff I * u ^ I * w ^ (n - I)

theorem hom_X_add_mul (n : ℕ) (f : ℝ[X]) (hf : f.natDegree ≤ n) (a u w : ℝ) :
    hom (n + 1) ((X + C a) * f) u w = (u + a * w) * hom n f u w := by
  have hc : ∀ I, ((X + C a) * f).coeff I =
      (if I = 0 then 0 else f.coeff (I - 1)) + a * f.coeff I := by
    intro I
    rw [add_mul, coeff_add, coeff_C_mul]
    rcases I with _ | I
    · simp
    · rw [coeff_X_mul]; simp
  have hzero : f.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  unfold hom
  have h1 : ∑ I ∈ Finset.range (n + 1 + 1), ((X + C a) * f).coeff I * u ^ I * w ^ (n + 1 - I) =
      ∑ I ∈ Finset.range (n + 1 + 1), (if I = 0 then 0 else f.coeff (I - 1)) * u ^ I * w ^ (n + 1 - I) +
        a * ∑ I ∈ Finset.range (n + 1 + 1), f.coeff I * u ^ I * w ^ (n + 1 - I) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun I _ => by rw [hc]; ring
  rw [h1, Finset.sum_range_succ', Finset.sum_range_succ _ (n + 1), hzero]
  simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, ite_eq_left, zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hI' : I < n + 1 := Finset.mem_range.mp hI
  rw [show n + 1 - (I + 1) = n - I by omega, show n + 1 - I = n - I + 1 by omega]
  ring

theorem hom_one (u w : ℝ) : hom 0 1 u w = 1 := by simp [hom]

theorem natDegree_X_add_pow_mul (i j : ℕ) :
    ((X - C (1 : ℝ)) ^ i * (X + C 1) ^ j).natDegree ≤ i + j := by
  refine (natDegree_mul_le).trans ?_
  have h1 : ((X - C (1 : ℝ)) ^ i).natDegree ≤ i := by
    refine (natDegree_pow_le).trans ?_
    have : (X - C (1 : ℝ)).natDegree ≤ 1 := natDegree_X_sub_C_le 1
    nlinarith
  have h2 : ((X + C (1 : ℝ)) ^ j).natDegree ≤ j := by
    refine (natDegree_pow_le).trans ?_
    have : (X + C (1 : ℝ)).natDegree ≤ 1 := (natDegree_X_add_C 1).le
    nlinarith
  omega

theorem hom_factors (u w : ℝ) : ∀ i j : ℕ,
    hom (i + j) ((X - C 1) ^ i * (X + C 1) ^ j) u w = (u - w) ^ i * (u + w) ^ j
  | 0, 0 => by simp [hom]
  | 0, j + 1 => by
    have ih := hom_factors u w 0 j
    rw [pow_zero, one_mul] at ih ⊢
    rw [zero_add] at ih ⊢
    rw [pow_succ', hom_X_add_mul j _ (by simp) 1, ih]
    ring
  | i + 1, j => by
    have ih := hom_factors u w i j
    rw [show i + 1 + j = (i + j) + 1 by omega, pow_succ', mul_assoc,
      show X - C (1 : ℝ) = X + C (-1) by rw [map_neg]; ring,
      hom_X_add_mul (i + j) _ (by
        have := natDegree_X_add_pow_mul i j
        rwa [show X - C (1 : ℝ) = X + C (-1) by rw [map_neg]; ring] at this) (-1)]
    rw [show X + C (-1 : ℝ) = X - C 1 by rw [map_neg]; ring, ih]
    ring

/-- The Bernstein form: `(X - 1)^i (X + 1)^(n - i)` homogenized at `u = (1 + x)/2`. -/
theorem hom_factor_eval (n i : ℕ) (hi : i ≤ n) (x : ℝ) :
    hom n ((X - C 1) ^ i * (X + C 1) ^ (n - i)) ((1 + x) / 2) ((1 - x) / 2) = x ^ i := by
  have h := hom_factors ((1 + x) / 2) ((1 - x) / 2) i (n - i)
  rw [Nat.add_sub_cancel' hi] at h
  rw [h]
  rw [show (1 + x) / 2 - (1 - x) / 2 = x by ring, show (1 + x) / 2 + (1 - x) / 2 = 1 by ring]
  simp

/-! ### The packed Bernstein transform -/

/-- `(1 + Z) ^ m` packed, `Z = 2 ^ s`. -/
def binomPow (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => binomPow s m + (binomPow s m <<< s)

/-- `x (1 + Z + ⋯ + Z ^ m)` packed, `Z = 2 ^ s`. -/
def spread (s x : ℕ) : ℕ → ℕ
  | 0 => x
  | m + 1 => x + (spread s x m <<< s)

/-- One Horner step `G ↦ G (Z - 1) + P (1 + Z) ^ m`, signed parts kept apart. -/
def hstep (s : ℕ) (G P : ℕ × ℕ) (q : ℕ) : ℕ × ℕ :=
  ((G.1 <<< s) + G.2 + P.1 * q, (G.2 <<< s) + G.1 + P.2 * q)

/-- Horner's rule over the slices `k - 1, …, 0`; slice `l` is `(A >>> (t l)) &&& mask`. -/
def stage (s t mask n A B : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, G => G
  | k + 1, G => stage s t mask n A B k
      (hstep s G ((A >>> (t * k)) &&& mask, (B >>> (t * k)) &&& mask) (binomPow s (n - k)))

/-- Natural polynomials in `Z`: `(1 + Z) ^ m` and `x (1 + ⋯ + Z ^ m)`. -/
theorem binomPow_eq (c : Config) (Z : NB) (s : ℕ) (hZ : evB c Z = 2 ^ s) :
    ∀ m, binomPow s m = evB c ((1 + Z) ^ m)
  | 0 => by simp [binomPow]
  | m + 1 => by
    rw [binomPow, binomPow_eq c Z s hZ m, Nat.shiftLeft_eq, pow_succ, map_mul, map_add, map_one, hZ]
    ring

theorem evB_CC (c : Config) (x : ℕ) : evB c (C (C x)) = x := by simp [evB, ev]

theorem spread_eq (c : Config) (Z : NB) (s x : ℕ) (hZ : evB c Z = 2 ^ s) :
    ∀ m, spread s x m = evB c (C (C x) * ∑ k ∈ Finset.range (m + 1), Z ^ k)
  | 0 => by simp [spread]
  | m + 1 => by
    rw [spread, spread_eq c Z s x hZ m, Nat.shiftLeft_eq, ← hZ, ← map_mul]
    have : C (C x) * ∑ k ∈ Finset.range (m + 1 + 1), Z ^ k =
        C (C x) + C (C x) * (∑ k ∈ Finset.range (m + 1), Z ^ k) * Z := by
      rw [Finset.sum_range_succ', mul_add, Finset.mul_sum, mul_assoc, Finset.sum_mul]
      simp only [pow_zero, mul_one, pow_succ]
      rw [add_comm, Finset.mul_sum]
    rw [this, map_add, evB_CC]

theorem evB_Y (c : Config) : evB c (C X) = 2 ^ c.w := by
  simp [evB, ev, Config.b]

theorem evB_X (c : Config) : evB c X = 2 ^ (c.w * c.S) := by
  simp [evB, ev, Config.b, pow_mul]

/-- The polynomial side of `stage`. -/
def pstage (Z : NB) (sl : ℕ → NB × NB) (n : ℕ) : ℕ → NB × NB → NB × NB
  | 0, G => G
  | k + 1, G => pstage Z sl n k
      (G.1 * Z + G.2 + (sl k).1 * (1 + Z) ^ (n - k), G.2 * Z + G.1 + (sl k).2 * (1 + Z) ^ (n - k))

theorem stage_eq (c : Config) (Z : NB) (s t mask n A B : ℕ) (hZ : evB c Z = 2 ^ s)
    (sl : ℕ → NB × NB)
    (hsl : ∀ l, ((A >>> (t * l)) &&& mask) = evB c (sl l).1 ∧ ((B >>> (t * l)) &&& mask) = evB c (sl l).2) :
    ∀ k (G : NB × NB), stage s t mask n A B k (evB c G.1, evB c G.2) =
      (evB c (pstage Z sl n k G).1, evB c (pstage Z sl n k G).2)
  | 0, G => rfl
  | k + 1, G => by
    rw [stage, pstage, ← stage_eq c Z s t mask n A B hZ sl hsl k]
    congr 1
    simp only [hstep, (hsl k).1, (hsl k).2, binomPow_eq c Z s hZ, Nat.shiftLeft_eq, map_add,
      map_mul, hZ]

theorem spread_sum (s x : ℕ) : ∀ m, spread s x m = ∑ k ∈ Finset.range (m + 1), x * (2 ^ s) ^ k
  | 0 => by simp [spread]
  | m + 1 => by
    rw [spread, spread_sum s x m, Nat.shiftLeft_eq, Finset.sum_range_succ' _ (m + 1), Finset.sum_mul]
    simp only [pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

theorem binomPow_sum (s : ℕ) (m : ℕ) :
    binomPow s m = ∑ k ∈ Finset.range (m + 1), m.choose k * (2 ^ s) ^ k := by
  have h : ∀ m, binomPow s m = (2 ^ s + 1) ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [binomPow, ih, Nat.shiftLeft_eq, pow_succ]; ring
  rw [h, add_pow]
  exact Finset.sum_congr rfl fun k _ => by simp only [one_pow, mul_one, Nat.cast_id]; ring

theorem sum_range_ite_le {M : Type*} [AddCommMonoid M] {m S : ℕ} (hm : m < S) (F : ℕ → M) :
    ∑ i ∈ Finset.range S, (if i ≤ m then F i else 0) = ∑ i ∈ Finset.range (m + 1), F i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- A product of a column sum and a row sum is a packed rectangle. -/
theorem pack_rect (c : Config) (f g : ℕ → ℕ) {mI mJ : ℕ} (hI : mI < c.S) (hJ : mJ < c.S) :
    (∑ i ∈ Finset.range (mI + 1), f i * (c.b ^ c.S) ^ i) * (∑ j ∈ Finset.range (mJ + 1), g j * c.b ^ j) =
      pack c (fun i j => if i ≤ mI ∧ j ≤ mJ then f i * g j else 0) := by
  unfold pack
  simp only [sumTo_eq]
  rw [Finset.sum_mul_sum]
  have : ∀ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      (if i ≤ mI ∧ j ≤ mJ then f i * g j else 0) * c.b ^ (c.S * i + j) =
      if i ≤ mI then ∑ j ∈ Finset.range (mJ + 1), f i * (c.b ^ c.S) ^ i * (g j * c.b ^ j) else 0 := by
    intro i _
    split_ifs with hi
    · rw [← sum_range_ite_le hJ]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ≤ mJ
      · rw [ite_eq_left ⟨hi, hj⟩, ite_eq_left hj, pow_add, pow_mul]; ring
      · rw [ite_eq_right (fun h => hj h.2), ite_eq_right hj, zero_mul]
    · exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (fun h => hi h.1), zero_mul]
  rw [Finset.sum_congr rfl this, sum_range_ite_le hI]

theorem spread_col (c : Config) (x m : ℕ) (hm : m < c.S) :
    spread (c.w * c.S) x m = pack c (fun i j => if i ≤ m ∧ j ≤ 0 then x * 1 else 0) := by
  rw [← pack_rect c (fun _ => x) (fun _ => 1) hm c.S_pos, spread_sum]
  simp [Config.b, pow_mul]

theorem spread_row (c : Config) (x m : ℕ) (hm : m < c.S) :
    spread c.w x m = pack c (fun i j => if i ≤ 0 ∧ j ≤ m then 1 * x else 0) := by
  rw [← pack_rect c (fun _ => 1) (fun _ => x) c.S_pos hm, spread_sum]
  simp [Config.b]

theorem coeffs_shiftRight (c : Config) (A l i j : ℕ) :
    coeffs c (A >>> (c.w * l)) i j = digit c.w A (c.S * i + j + l) := by
  rw [coeffs, digit_shiftRight]

/-- Digits under a mask of whole digits `b - 1` or `0`. -/
theorem land_mask_pack {c : Config} (A : ℕ) (q : ℕ → ℕ → Prop) [∀ i j, Decidable (q i j)] :
    A &&& pack c (fun i j => if q i j then c.b - 1 else 0) =
      pack c (fun i j => if q i j then coeffs c A i j else 0) := by
  have hq : ∀ i j, (if q i j then c.b - 1 else 0) < c.b := fun i j => by
    split_ifs
    · exact Nat.sub_lt c.b_pos one_pos
    · exact c.b_pos
  apply land_pattern (pack_box c hq)
  · intro i j hi hj
    rw [coeffs_pack c hq hi hj]
    split_ifs
    · exact land_full (coeffs_lt c A i j)
    · exact Nat.and_zero _
  · intro i j; split_ifs
    · exact coeffs_lt c A i j
    · exact c.b_pos

/-- Column `l` of a packed number, moved to column `0`. -/
theorem slice_col (c : Config) (A l : ℕ) :
    (A >>> (c.w * l)) &&& spread (c.w * c.S) (c.b - 1) c.B =
      pack c (fun i j => if i ≤ c.B ∧ j ≤ 0 then coeffs c A i l else 0) := by
  rw [spread_col c _ _ (by unfold Config.S; omega)]
  simp only [mul_one]
  rw [land_mask_pack]
  apply pack_congr; intro i j _ _
  split_ifs with h
  · rw [coeffs_shiftRight, show j = 0 by omega, add_zero]; rfl
  · rfl

/-- Row `l` of a packed number, moved to row `0`. -/
theorem slice_row (c : Config) (A l n : ℕ) (hn : n < c.S) :
    (A >>> (c.w * c.S * l)) &&& spread c.w (c.b - 1) n =
      pack c (fun i j => if i ≤ 0 ∧ j ≤ n then coeffs c A l j else 0) := by
  rw [spread_row c _ _ hn]
  simp only [one_mul]
  rw [land_mask_pack, mul_assoc]
  apply pack_congr; intro i j _ _
  split_ifs with h
  · rw [coeffs_shiftRight, show i = 0 by omega, mul_zero, zero_add, add_comm]; rfl
  · rfl

/-- Natural coefficients as real ones. -/
def toR : NB →+* Polynomial (Polynomial ℝ) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Nat.castRingHom ℝ))

/-- The coefficient of `X^i Y^j` of a real bivariate polynomial. -/
def cfR (P : Polynomial (Polynomial ℝ)) (i j : ℕ) : ℝ := (P.coeff i).coeff j

theorem cfR_toR (P : NB) (i j : ℕ) : cfR (toR P) i j = cf P i j := by
  simp [cfR, toR, cf, coeff_map]

theorem cfR_sub (P Q : Polynomial (Polynomial ℝ)) (i j : ℕ) :
    cfR (P - Q) i j = cfR P i j - cfR Q i j := by simp [cfR]

theorem pstage_real (Z : NB) (sl : ℕ → NB × NB) (n : ℕ) : ∀ (k : ℕ) (G : NB × NB),
    toR (pstage Z sl n k G).1 - toR (pstage Z sl n k G).2 =
      (toR G.1 - toR G.2) * (toR Z - 1) ^ k +
        ∑ l ∈ Finset.range k, (toR (sl l).1 - toR (sl l).2) * (toR Z - 1) ^ l * (1 + toR Z) ^ (n - l)
  | 0, G => by simp [pstage]
  | k + 1, G => by
    rw [pstage, pstage_real Z sl n k, Finset.sum_range_succ]
    simp only [map_add, map_mul, map_pow, map_one]
    ring

theorem pstage_dsum (Z : NB) (hZ : dsum Z = 1) (sl : ℕ → NB × NB) (n : ℕ) : ∀ (k : ℕ) (G : NB × NB),
    dsum (pstage Z sl n k G).1 + dsum (pstage Z sl n k G).2 =
      (dsum G.1 + dsum G.2) * 2 ^ k +
        ∑ l ∈ Finset.range k, (dsum (sl l).1 + dsum (sl l).2) * 2 ^ (n - l) * 2 ^ l
  | 0, G => by simp [pstage]
  | k + 1, G => by
    rw [pstage, pstage_dsum Z hZ sl n k, Finset.sum_range_succ]
    have h1 : dsum (1 + Z) = 2 := by rw [dsum, map_add, map_one, ← dsum, hZ]
    simp only [dsum, map_add, map_mul, map_pow] at h1 hZ ⊢
    rw [h1, hZ]
    ring

/-- Degrees at most `a` in `X` and `d` in `Y`. -/
def Deg (a d : ℕ) (P : NB) : Prop := ∀ i j, cf P i j ≠ 0 → i ≤ a ∧ j ≤ d

theorem Deg.mono {a d a' d' : ℕ} {P : NB} (h : Deg a d P) (ha : a ≤ a') (hd : d ≤ d') :
    Deg a' d' P := fun i j hij => ⟨(h i j hij).1.trans ha, (h i j hij).2.trans hd⟩

theorem Deg.add {a d : ℕ} {P Q : NB} (hP : Deg a d P) (hQ : Deg a d Q) : Deg a d (P + Q) :=
  fun i j h => by
  rw [cf_add] at h
  by_cases h1 : cf P i j = 0
  · rw [h1, zero_add] at h; exact hQ i j h
  · exact hP i j h1

theorem Deg.zero (a d : ℕ) : Deg a d 0 := fun i j h => by simp [cf] at h

theorem Deg.mul {a d a' d' : ℕ} {P Q : NB} (hP : Deg a d P) (hQ : Deg a' d' Q) :
    Deg (a + a') (d + d') (P * Q) := by
  intro i j h
  by_contra hc
  apply h
  simp only [cf, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  by_cases h1 : cf P x.1 y.1 = 0
  · simp only [cf] at h1; rw [h1, zero_mul]
  · by_cases h2 : cf Q x.2 y.2 = 0
    · simp only [cf] at h2; rw [h2, mul_zero]
    · have := hP _ _ h1
      have := hQ _ _ h2
      omega

theorem Deg.one : Deg 0 0 (1 : NB) := fun i j h => by
  simp only [cf, Polynomial.coeff_one] at h
  split_ifs at h with hi
  · rw [Polynomial.coeff_one] at h; split_ifs at h with hj
    · exact ⟨by omega, by omega⟩
    · exact absurd rfl h
  · exact absurd (by simp) h

theorem Deg.Y : Deg 0 1 (C X : NB) := fun i j h => by
  simp only [cf, Polynomial.coeff_C] at h
  split_ifs at h with hi
  · rw [Polynomial.coeff_X] at h; split_ifs at h with hj
    · exact ⟨by omega, by omega⟩
    · exact absurd rfl h
  · exact absurd (by simp) h

theorem Deg.X : Deg 1 0 (X : NB) := fun i j h => by
  simp only [cf, Polynomial.coeff_X] at h
  split_ifs at h with hi
  · rw [Polynomial.coeff_one] at h; split_ifs at h with hj
    · exact ⟨by omega, by omega⟩
    · exact absurd rfl h
  · exact absurd (by simp) h

theorem Deg.pow {a d : ℕ} {P : NB} (h : Deg a d P) : ∀ m, Deg (a * m) (d * m) (P ^ m)
  | 0 => by simpa using Deg.one
  | m + 1 => by
    rw [pow_succ, show a * (m + 1) = a * m + a by ring, show d * (m + 1) = d * m + d by ring]
    exact (Deg.pow h m).mul h

theorem Deg.boxSupp {c : Config} {a d : ℕ} {P : NB} (h : Deg a d P) (ha : a < c.S) (hd : d < c.S) :
    BoxSupp c P := fun i j hij => ⟨lt_of_le_of_lt (h i j hij).1 ha, lt_of_le_of_lt (h i j hij).2 hd⟩

theorem Deg.ofFun {c : Config} {a d : ℕ} {f : ℕ → ℕ → ℕ} (h : ∀ i j, ¬ (i ≤ a ∧ j ≤ d) → f i j = 0) :
    Deg a d (ofFun c f) := fun i j hij => by
  rw [cf_ofFun] at hij
  split_ifs at hij
  · by_contra hc; exact hij (h i j hc)
  · exact absurd rfl hij

/-- Stage 1 (`Z = Y`): degrees stay `≤ (a, n)`. -/
theorem pstageY_deg {a n : ℕ} (sl : ℕ → NB × NB) (hsl : ∀ l, Deg a 0 (sl l).1 ∧ Deg a 0 (sl l).2) :
    ∀ k (G : NB × NB), k ≤ n → Deg a (n - k) G.1 → Deg a (n - k) G.2 →
      Deg a n (pstage (C X) sl n k G).1 ∧ Deg a n (pstage (C X) sl n k G).2
  | 0, G, _, h1, h2 => by simpa [pstage] using And.intro h1 h2
  | k + 1, G, hk, h1, h2 => by
    rw [pstage]
    have hZ : Deg 0 (n - k) ((1 + C X : NB) ^ (n - k)) := by
      simpa using ((Deg.one.mono le_rfl (Nat.zero_le 1)).add Deg.Y).pow (n - k)
    apply pstageY_deg sl hsl k _ (by omega)
    · have t1 : Deg a (n - k) (G.1 * C X) := (h1.mul Deg.Y).mono (by omega) (by omega)
      have t2 : Deg a (n - k) G.2 := h2.mono le_rfl (by omega)
      have t3 : Deg a (n - k) ((sl k).1 * (1 + C X) ^ (n - k)) :=
        ((hsl k).1.mul hZ).mono (by omega) (by omega)
      exact (t1.add t2).add t3
    · have t1 : Deg a (n - k) (G.2 * C X) := (h2.mul Deg.Y).mono (by omega) (by omega)
      have t2 : Deg a (n - k) G.1 := h1.mono le_rfl (by omega)
      have t3 : Deg a (n - k) ((sl k).2 * (1 + C X) ^ (n - k)) :=
        ((hsl k).2.mul hZ).mono (by omega) (by omega)
      exact (t1.add t2).add t3

/-- Stage 2 (`Z = X`): degrees stay `≤ (n, d)`. -/
theorem pstageX_deg {d n : ℕ} (sl : ℕ → NB × NB) (hsl : ∀ l, Deg 0 d (sl l).1 ∧ Deg 0 d (sl l).2) :
    ∀ k (G : NB × NB), k ≤ n → Deg (n - k) d G.1 → Deg (n - k) d G.2 →
      Deg n d (pstage X sl n k G).1 ∧ Deg n d (pstage X sl n k G).2
  | 0, G, _, h1, h2 => by simpa [pstage] using And.intro h1 h2
  | k + 1, G, hk, h1, h2 => by
    rw [pstage]
    have hZ : Deg (n - k) 0 ((1 + X : NB) ^ (n - k)) := by
      simpa using ((Deg.one.mono (Nat.zero_le 1) le_rfl).add Deg.X).pow (n - k)
    apply pstageX_deg sl hsl k _ (by omega)
    · have t1 : Deg (n - k) d (G.1 * X) := (h1.mul Deg.X).mono (by omega) (by omega)
      have t2 : Deg (n - k) d G.2 := h2.mono (by omega) le_rfl
      have t3 : Deg (n - k) d ((sl k).1 * (1 + X) ^ (n - k)) :=
        ((hsl k).1.mul hZ).mono (by omega) (by omega)
      exact (t1.add t2).add t3
    · have t1 : Deg (n - k) d (G.2 * X) := (h2.mul Deg.X).mono (by omega) (by omega)
      have t2 : Deg (n - k) d G.1 := h1.mono (by omega) le_rfl
      have t3 : Deg (n - k) d ((sl k).2 * (1 + X) ^ (n - k)) :=
        ((hsl k).2.mul hZ).mono (by omega) (by omega)
      exact (t1.add t2).add t3

theorem topbit_mask {c : Config} (hw : 1 ≤ c.w) {d : ℕ → ℕ → ℕ} (hd : ∀ i j, d i j < c.b)
    (e : ℕ → ℕ → Prop) [∀ i j, Decidable (e i j)] :
    (pack c d >>> (c.w - 1)) &&& pack c (fun i j => if e i j then 1 else 0) =
      pack c (fun i j => if e i j then d i j / 2 ^ (c.w - 1) else 0) := by
  have hb2 : 2 ≤ c.b := by
    unfold Config.b; calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ c.w := Nat.pow_le_pow_right (by norm_num) hw
  have hbw : (c.b : ℕ) = 2 ^ (c.w - 1) * 2 := by
    unfold Config.b; rw [← pow_succ, Nat.sub_add_cancel hw]
  have hq : ∀ i j, d i j / 2 ^ (c.w - 1) < 2 := fun i j => by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hbw]; exact hd i j
  have h1 : ∀ i j, (if e i j then 1 else 0) < c.b := fun i j => by split_ifs <;> omega
  have h2 : ∀ i j, (if e i j then d i j / 2 ^ (c.w - 1) else 0) < c.b := fun i j => by
    split_ifs
    · exact lt_of_lt_of_le (hq i j) hb2
    · exact c.b_pos
  apply eq_of_digit_eq (show 0 < c.w by omega)
  intro m
  rw [digit_land, digit_pack c h1, digit_pack c h2]
  by_cases hm : m < c.S * c.S
  · rw [ite_eq_left hm, ite_eq_left hm]
    by_cases ht : e (m / c.S) (m % c.S)
    · rw [ite_eq_left ht, ite_eq_left ht, Nat.and_one_is_mod]
      have hdm := digit_pack c hd m
      rw [ite_eq_left hm] at hdm
      rw [← hdm]
      simp only [digit, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ c.w from dvd_pow_self 2 (by omega)),
        show (2 : ℕ) ^ c.w = 2 ^ (c.w - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hw],
        Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    · rw [ite_eq_right ht, ite_eq_right ht, Nat.and_zero]
  · rw [ite_eq_right hm, ite_eq_right hm, Nat.and_zero]

/-- The square `I, J ≤ n`. -/
def sq (n : ℕ) (i j : ℕ) : Prop := i ≤ n ∧ j ≤ n

instance (n i j : ℕ) : Decidable (sq n i j) := inferInstanceAs (Decidable (_ ∧ _))

/-- The sign test: `p - q ≥ 0` on the square, read from the top bits of `p + 2^(w-1) - q`. -/
theorem sign_test {c : Config} (hw : 1 ≤ c.w) {n : ℕ} {p q : ℕ → ℕ → ℕ}
    (hp : ∀ i j, p i j < 2 ^ (c.w - 1)) (hq : ∀ i j, q i j < 2 ^ (c.w - 1))
    (h : ((pack c (fun i j => if sq n i j then p i j else 0) +
        pack c (fun i j => if sq n i j then 2 ^ (c.w - 1) else 0) -
        pack c (fun i j => if sq n i j then q i j else 0)) >>> (c.w - 1)) &&&
          pack c (fun i j => if sq n i j then 1 else 0) =
        pack c (fun i j => if sq n i j then 1 else 0))
    {i j : ℕ} (hi : i < c.S) (hj : j < c.S) (hij : sq n i j) : q i j ≤ p i j := by
  have hbw : c.b = 2 ^ (c.w - 1) * 2 := by
    unfold Config.b; rw [← pow_succ, Nat.sub_add_cancel hw]
  have hd : ∀ i j, (if sq n i j then p i j + 2 ^ (c.w - 1) - q i j else 0) < c.b := fun i j => by
    split_ifs
    · have := hp i j; have := hq i j; omega
    · exact c.b_pos
  have hW : pack c (fun i j => if sq n i j then p i j else 0) +
      pack c (fun i j => if sq n i j then 2 ^ (c.w - 1) else 0) -
      pack c (fun i j => if sq n i j then q i j else 0) =
      pack c (fun i j => if sq n i j then p i j + 2 ^ (c.w - 1) - q i j else 0) := by
    rw [pack_add, pack_sub]
    · apply pack_congr; intro i j _ _; split_ifs <;> rfl
    · intro i j; split_ifs
      · have := hq i j; omega
      · exact le_rfl
  rw [hW, topbit_mask hw hd] at h
  have hb2 : 2 ≤ c.b := by have := @Nat.one_le_two_pow (c.w - 1); omega
  have h1 : ∀ i j, (if sq n i j then 1 else 0) < c.b := fun i j => by split_ifs <;> omega
  have h2 : ∀ i j, (if sq n i j then (if sq n i j then p i j + 2 ^ (c.w - 1) - q i j else 0) /
      2 ^ (c.w - 1) else 0) < c.b := fun i j => by
    split_ifs
    · have := hp i j; have := hq i j
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    · exact c.b_pos
  have := congrArg (fun N => coeffs c N i j) h
  rw [coeffs_pack c h2 hi hj, coeffs_pack c h1 hi hj, ite_eq_left hij, ite_eq_left hij,
    ite_eq_left hij] at this
  have hq' := hq i j
  by_contra hlt
  push Not at hlt
  have : (p i j + 2 ^ (c.w - 1) - q i j) / 2 ^ (c.w - 1) = 0 :=
    Nat.div_eq_of_lt (by omega)
  omega

/-! ### Linear algebra of the transform -/

theorem hom_add (n : ℕ) (f g : ℝ[X]) (u w : ℝ) : hom n (f + g) u w = hom n f u w + hom n g u w := by
  simp only [hom, coeff_add, add_mul, Finset.sum_add_distrib]

theorem hom_C_mul (n : ℕ) (a : ℝ) (f : ℝ[X]) (u w : ℝ) : hom n (C a * f) u w = a * hom n f u w := by
  simp only [hom, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem hom_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → ℝ[X]) (u w : ℝ) :
    hom n (∑ k ∈ s, f k) u w = ∑ k ∈ s, hom n (f k) u w := by
  simp only [hom, finsetSum_coeff, Finset.sum_mul]
  exact Finset.sum_comm

/-- The Bernstein factor `(X - 1)^l (X + 1)^(n - l)`. -/
def factor (n l : ℕ) : ℝ[X] := (X - C 1) ^ l * (X + C 1) ^ (n - l)

theorem toR_X : toR (X : NB) = X := by simp [toR]
theorem toR_Y : toR (C X : NB) = C X := by simp [toR]

theorem outer_factor (n l : ℕ) :
    (toR (X : NB) - 1) ^ l * (1 + toR (X : NB)) ^ (n - l) = (factor n l).map C := by
  simp [factor, toR_X, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, add_comm]

theorem inner_factor (n l : ℕ) :
    (toR (C X : NB) - 1) ^ l * (1 + toR (C X : NB)) ^ (n - l) = C (factor n l) := by
  simp [factor, toR_Y, map_mul, map_pow, map_sub, map_add, add_comm]

theorem cfR_mul_C (T : Polynomial (Polynomial ℝ)) (f : ℝ[X]) (i j : ℕ) :
    cfR (T * C f) i j = (T.coeff i * f).coeff j := by
  simp [cfR, coeff_mul_C]

theorem cfR_C_mul_map (s f : ℝ[X]) (I J : ℕ) :
    cfR (C s * f.map C) I J = s.coeff J * f.coeff I := by
  simp [cfR, coeff_C_mul, coeff_map, coeff_mul_C]

/-- The two slices of the transform. -/
def colSlices (c : Config) (U V l : ℕ) : NB × NB :=
  (ofFun c (fun i j => if i ≤ c.B ∧ j ≤ 0 then coeffs c U i l else 0),
   ofFun c (fun i j => if i ≤ c.B ∧ j ≤ 0 then coeffs c V i l else 0))

def rowSlices (c : Config) (n A B l : ℕ) : NB × NB :=
  (ofFun c (fun i j => if i ≤ 0 ∧ j ≤ n then coeffs c A l j else 0),
   ofFun c (fun i j => if i ≤ 0 ∧ j ≤ n then coeffs c B l j else 0))

theorem toR_ofFun (c : Config) (f : ℕ → ℕ → ℕ) :
    toR (ofFun c f) = ∑ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S,
      monomial i (monomial j (f i j : ℝ)) := by
  simp [ofFun, toR, Polynomial.map_monomial]

theorem coeff_toR_ofFun (c : Config) (f : ℕ → ℕ → ℕ) (i : ℕ) :
    (toR (ofFun c f)).coeff i =
      if i < c.S then ∑ j ∈ Finset.range c.S, monomial j (f i j : ℝ) else 0 := by
  rw [toR_ofFun, finsetSum_coeff]
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hi : i < c.S
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · rw [ite_eq_right hi]
    exact Finset.sum_eq_zero fun k hk => by
      have : k ≠ i := fun h => hi (h ▸ Finset.mem_range.mp hk)
      simp [this]

theorem colSlices_coeff (c : Config) (U V l i : ℕ) (hi : i ≤ c.B) :
    (toR (colSlices c U V l).1 - toR (colSlices c U V l).2).coeff i =
      C ((coeffs c U i l : ℝ) - coeffs c V i l) := by
  have hiS : i < c.S := by unfold Config.S; omega
  rw [coeff_sub, colSlices, coeff_toR_ofFun, coeff_toR_ofFun, ite_eq_left hiS, ite_eq_left hiS,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single 0]
  · simp [hi]
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.mpr c.S_pos) h

theorem colSlices_coeff_gt (c : Config) (U V l i : ℕ) (hi : c.B < i) :
    (toR (colSlices c U V l).1 - toR (colSlices c U V l).2).coeff i = 0 := by
  rw [coeff_sub, colSlices, coeff_toR_ofFun, coeff_toR_ofFun]
  split_ifs
  · rw [← Finset.sum_sub_distrib]
    have : ¬ i ≤ c.B := by omega
    exact Finset.sum_eq_zero fun j _ => by simp [this]
  · simp

theorem rowSlices_eq (c : Config) {n : ℕ} (A B l : ℕ) (_hl : l < c.S) :
    toR (rowSlices c n A B l).1 - toR (rowSlices c n A B l).2 =
      C (∑ j ∈ Finset.range c.S, monomial j
        (if j ≤ n then (coeffs c A l j : ℝ) - coeffs c B l j else 0)) := by
  apply Polynomial.ext; intro i
  rw [coeff_sub, rowSlices, coeff_toR_ofFun, coeff_toR_ofFun, coeff_C]
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left c.S_pos, ite_eq_left c.S_pos, ite_eq_left rfl, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ≤ n <;> simp [hj]
  · rw [ite_eq_right hi]
    split_ifs
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun j _ => by simp [show ¬ i ≤ 0 by omega]
    · simp

/-! ### The two stages -/

theorem dsum_ofFun_col (c : Config) (U l : ℕ) :
    dsum (ofFun c (fun i j => if i ≤ c.B ∧ j ≤ 0 then coeffs c U i l else 0)) =
      ∑ i ∈ Finset.range c.S, if i ≤ c.B then coeffs c U i l else 0 := by
  rw [dsum_ofFun]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [show ¬ j ≤ 0 by omega]
  · intro h; exact absurd (Finset.mem_range.mpr (Config.S_pos c)) h

theorem dsum_ofFun_row (c : Config) (n A l : ℕ) :
    dsum (ofFun c (fun i j => if i ≤ 0 ∧ j ≤ n then coeffs c A l j else 0)) =
      ∑ j ∈ Finset.range c.S, if j ≤ n then coeffs c A l j else 0 := by
  rw [dsum_ofFun, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [show ¬ i ≤ 0 by omega]
  · intro h; exact absurd (Finset.mem_range.mpr (Config.S_pos c)) h

theorem sum_cols_le (c : Config) (U : ℕ) :
    ∑ l ∈ Finset.range (c.B + 1), ∑ i ∈ Finset.range c.S, (if i ≤ c.B then coeffs c U i l else 0) ≤
      dsumN c U := by
  unfold dsumN
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ l ∈ Finset.range (c.B + 1), (if i ≤ c.B then coeffs c U i l else 0)
      ≤ ∑ l ∈ Finset.range (c.B + 1), coeffs c U i l :=
        Finset.sum_le_sum fun l _ => by split_ifs <;> simp
    _ ≤ ∑ l ∈ Finset.range c.S, coeffs c U i l :=
        Finset.sum_le_sum_of_subset (fun x hx => by
          simp only [Finset.mem_range] at hx ⊢; unfold Config.S; omega)

theorem sum_rows_le (c : Config) (n A : ℕ) :
    ∑ l ∈ Finset.range (c.B + 1), ∑ j ∈ Finset.range c.S, (if j ≤ n then coeffs c A l j else 0) ≤
      dsumN c A := by
  unfold dsumN
  calc ∑ l ∈ Finset.range (c.B + 1), ∑ j ∈ Finset.range c.S, (if j ≤ n then coeffs c A l j else 0)
      ≤ ∑ l ∈ Finset.range (c.B + 1), ∑ j ∈ Finset.range c.S, coeffs c A l j :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => by split_ifs <;> simp
    _ ≤ _ := Finset.sum_le_sum_of_subset (fun x hx => by
        simp only [Finset.mem_range] at hx ⊢; unfold Config.S; omega)

theorem pow_sub_mul_pow {n l : ℕ} (h : l ≤ n) : 2 ^ (n - l) * 2 ^ l = 2 ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

/-- The packed stage 1 and the polynomial stages. -/
def stage1 (c : Config) (n U V : ℕ) : ℕ × ℕ :=
  stage c.w c.w (spread (c.w * c.S) (c.b - 1) c.B) n U V (c.B + 1) (0, 0)
def stage2 (c : Config) (n A B : ℕ) : ℕ × ℕ :=
  stage (c.w * c.S) (c.w * c.S) (spread c.w (c.b - 1) n) n A B (c.B + 1) (0, 0)
def pstage1 (c : Config) (n U V : ℕ) : NB × NB := pstage (C X) (colSlices c U V) n (c.B + 1) (0, 0)
def pstage2 (c : Config) (n A B : ℕ) : NB × NB := pstage X (rowSlices c n A B) n (c.B + 1) (0, 0)

/-- Stage 1: the columns of `(U, V)` give natural polynomials `P` with `(Y - 1, Y + 1)`
factors. -/
theorem stage1_props {c : Config} {n : ℕ} (hBn : c.B < n) (U V : ℕ) :
    stage1 c n U V = (evB c (pstage1 c n U V).1, evB c (pstage1 c n U V).2) ∧
      Deg c.B n (pstage1 c n U V).1 ∧ Deg c.B n (pstage1 c n U V).2 ∧
      dsum (pstage1 c n U V).1 + dsum (pstage1 c n U V).2 ≤ 2 ^ n * (dsumN c U + dsumN c V) ∧
      toR (pstage1 c n U V).1 - toR (pstage1 c n U V).2 = ∑ l ∈ Finset.range (c.B + 1),
        (toR (colSlices c U V l).1 - toR (colSlices c U V l).2) * C (factor n l) := by
  unfold stage1 pstage1
  set P := pstage (C X) (colSlices c U V) n (c.B + 1) (0, 0) with hPdef
  set G := stage c.w c.w (spread (c.w * c.S) (c.b - 1) c.B) n U V (c.B + 1) (0, 0) with hGdef
  have hsl : ∀ l, ((U >>> (c.w * l)) &&& spread (c.w * c.S) (c.b - 1) c.B) =
      evB c (colSlices c U V l).1 ∧
      ((V >>> (c.w * l)) &&& spread (c.w * c.S) (c.b - 1) c.B) = evB c (colSlices c U V l).2 :=
    fun l => ⟨by rw [slice_col, colSlices, evB_ofFun], by rw [slice_col, colSlices, evB_ofFun]⟩
  have hG : G = (evB c P.1, evB c P.2) := by
    have := stage_eq c (C X) c.w c.w _ n U V (evB_Y c) _ hsl (c.B + 1) (0, 0)
    simpa only [map_zero] using this
  have hdeg := pstageY_deg (a := c.B) (n := n) (colSlices c U V)
    (fun l => ⟨Deg.ofFun (fun i j h => by rw [ite_eq_right h]),
      Deg.ofFun (fun i j h => by rw [ite_eq_right h])⟩) (c.B + 1) (0, 0) (by omega)
    (Deg.zero _ _) (Deg.zero _ _)
  refine ⟨hG, hdeg.1, hdeg.2, ?_, ?_⟩
  · have hd := pstage_dsum (C X) (by simp [dsum, ev]) (colSlices c U V) n (c.B + 1) (0, 0)
    simp only [map_zero, dsum, zero_add, zero_mul] at hd
    have : ∀ l ∈ Finset.range (c.B + 1), (ev (1 : ℕ) 1 (colSlices c U V l).1 +
        ev 1 1 (colSlices c U V l).2) * 2 ^ (n - l) * 2 ^ l =
        2 ^ n * ((∑ i ∈ Finset.range c.S, if i ≤ c.B then coeffs c U i l else 0) +
          ∑ i ∈ Finset.range c.S, if i ≤ c.B then coeffs c V i l else 0) := by
      intro l hl
      have hl' : l ≤ n := by have := Finset.mem_range.mp hl; omega
      rw [← dsum, ← dsum, colSlices, dsum_ofFun_col, dsum_ofFun_col, mul_assoc,
        pow_sub_mul_pow hl']
      ring
    show dsum P.1 + dsum P.2 ≤ _
    simp only [dsum]
    rw [hd, Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_add_distrib]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add (sum_cols_le c U) (sum_cols_le c V))
  · have h := pstage_real (C X) (colSlices c U V) n (c.B + 1) (0, 0)
    simp only [map_zero, sub_zero, zero_mul, zero_add] at h
    show toR P.1 - toR P.2 = _
    rw [h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, inner_factor]

/-- Stage 2: the rows of the stage-1 output give `Q` with `(X - 1, X + 1)` factors. -/
theorem stage2_props {c : Config} {n : ℕ} (hBn : c.B < n) (hnS : n < c.S) (A B : ℕ) :
    stage2 c n A B = (evB c (pstage2 c n A B).1, evB c (pstage2 c n A B).2) ∧
      Deg n n (pstage2 c n A B).1 ∧ Deg n n (pstage2 c n A B).2 ∧
      dsum (pstage2 c n A B).1 + dsum (pstage2 c n A B).2 ≤ 2 ^ n * (dsumN c A + dsumN c B) ∧
      toR (pstage2 c n A B).1 - toR (pstage2 c n A B).2 = ∑ l ∈ Finset.range (c.B + 1),
        (toR (rowSlices c n A B l).1 - toR (rowSlices c n A B l).2) * (factor n l).map C := by
  unfold stage2 pstage2
  set Q := pstage X (rowSlices c n A B) n (c.B + 1) (0, 0) with hQdef
  set H := stage (c.w * c.S) (c.w * c.S) (spread c.w (c.b - 1) n) n A B (c.B + 1) (0, 0) with hHdef
  have hsl : ∀ l, ((A >>> (c.w * c.S * l)) &&& spread c.w (c.b - 1) n) =
      evB c (rowSlices c n A B l).1 ∧
      ((B >>> (c.w * c.S * l)) &&& spread c.w (c.b - 1) n) = evB c (rowSlices c n A B l).2 :=
    fun l => ⟨by rw [slice_row c _ _ _ hnS, rowSlices, evB_ofFun],
      by rw [slice_row c _ _ _ hnS, rowSlices, evB_ofFun]⟩
  have hH : H = (evB c Q.1, evB c Q.2) := by
    have := stage_eq c X (c.w * c.S) (c.w * c.S) _ n A B (evB_X c) _ hsl (c.B + 1) (0, 0)
    simpa only [map_zero] using this
  have hdeg := pstageX_deg (d := n) (n := n) (rowSlices c n A B)
    (fun l => ⟨Deg.ofFun (fun i j h => by rw [ite_eq_right h]),
      Deg.ofFun (fun i j h => by rw [ite_eq_right h])⟩) (c.B + 1) (0, 0) (by omega)
    (Deg.zero _ _) (Deg.zero _ _)
  refine ⟨hH, hdeg.1, hdeg.2, ?_, ?_⟩
  · have hd := pstage_dsum X (by simp [dsum, ev]) (rowSlices c n A B) n (c.B + 1) (0, 0)
    simp only [map_zero, dsum, zero_add, zero_mul] at hd
    have : ∀ l ∈ Finset.range (c.B + 1), (ev (1 : ℕ) 1 (rowSlices c n A B l).1 +
        ev 1 1 (rowSlices c n A B l).2) * 2 ^ (n - l) * 2 ^ l =
        2 ^ n * ((∑ j ∈ Finset.range c.S, if j ≤ n then coeffs c A l j else 0) +
          ∑ j ∈ Finset.range c.S, if j ≤ n then coeffs c B l j else 0) := by
      intro l hl
      have hl' : l ≤ n := by have := Finset.mem_range.mp hl; omega
      rw [← dsum, ← dsum, rowSlices, dsum_ofFun_row, dsum_ofFun_row, mul_assoc,
        pow_sub_mul_pow hl']
      ring
    show dsum Q.1 + dsum Q.2 ≤ _
    simp only [dsum]
    rw [hd, Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_add_distrib]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add (sum_rows_le c n A) (sum_rows_le c n B))
  · have h := pstage_real X (rowSlices c n A B) n (c.B + 1) (0, 0)
    simp only [map_zero, sub_zero, zero_mul, zero_add] at h
    show toR Q.1 - toR Q.2 = _
    rw [h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, outer_factor]

/-! ### The Bernstein check -/

/-- The packed transform: stage 1 over the columns, stage 2 over the rows. -/
def bernR (c : Config) (n U V : ℕ) : ℕ × ℕ :=
  stage2 c n (stage1 c n U V).1 (stage1 c n U V).2

/-- All degree-`n` Bernstein coefficients of the model polynomial are at least `τ / 2 ^ K`. -/
def bernCheck (c : Config) (n : ℕ) (m : Model) (τ : ℕ) : Bool :=
  let H := bernR c n m.U m.V
  let ones2 := spread (c.w * c.S) 1 n * spread c.w 1 n
  let bin2 := binomPow (c.w * c.S) n * binomPow c.w n
  Nat.blt c.B n && Nat.blt n c.S && Nat.blt (4 ^ n * m.size c + τ * 4 ^ n) (2 ^ (c.w - 2)) &&
    Nat.beq ((((H.1 + (ones2 <<< (c.w - 1))) - (H.2 + τ * bin2)) >>> (c.w - 1)) &&& ones2) ones2

theorem cfR_sum (s : Finset ℕ) (F : ℕ → Polynomial (Polynomial ℝ)) (I J : ℕ) :
    cfR (∑ l ∈ s, F l) I J = ∑ l ∈ s, cfR (F l) I J := by
  simp [cfR, finsetSum_coeff]

theorem factor_hom (n l : ℕ) (hl : l ≤ n) (x : ℝ) :
    hom n (factor n l) ((1 + x) / 2) ((1 - x) / 2) = x ^ l := hom_factor_eval n l hl x

/-- The packed numbers of the two stages, as polynomials. -/
theorem bern_poly {c : Config} {n : ℕ} (hBn : c.B < n) (hnS : n < c.S) {U V : ℕ} (σ : ℕ)
    (hσ : dsumN c U + dsumN c V ≤ σ) (hsz : 4 ^ n * σ < 2 ^ (c.w - 2)) :
    poly c (stage1 c n U V).1 = (pstage1 c n U V).1 ∧ poly c (stage1 c n U V).2 = (pstage1 c n U V).2 ∧
    poly c (bernR c n U V).1 = (pstage2 c n (stage1 c n U V).1 (stage1 c n U V).2).1 ∧
    poly c (bernR c n U V).2 = (pstage2 c n (stage1 c n U V).1 (stage1 c n U V).2).2 ∧
    Box c (bernR c n U V).1 ∧ Box c (bernR c n U V).2 ∧
    Deg c.B n (pstage1 c n U V).1 ∧ Deg c.B n (pstage1 c n U V).2 ∧
    Deg n n (pstage2 c n (stage1 c n U V).1 (stage1 c n U V).2).1 ∧
    Deg n n (pstage2 c n (stage1 c n U V).1 (stage1 c n U V).2).2 ∧
    dsum (pstage2 c n (stage1 c n U V).1 (stage1 c n U V).2).1 +
      dsum (pstage2 c n (stage1 c n U V).1 (stage1 c n U V).2).2 ≤ 4 ^ n * σ := by
  have hlb := Model.lim_le_b c
  have hBS : c.B < c.S := by unfold Config.S; omega
  obtain ⟨hG, dP1, dP2, sP, _⟩ := stage1_props (c := c) hBn U V
  obtain ⟨hH, dQ1, dQ2, sQ, _⟩ := stage2_props (c := c) hBn hnS (stage1 c n U V).1 (stage1 c n U V).2
  set P := pstage1 c n U V with hPdef
  set G := stage1 c n U V with hGdef
  set Q := pstage2 c n G.1 G.2 with hQdef
  have h4 : 2 ^ n * 2 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
  have hP : dsum P.1 + dsum P.2 < c.b := by
    calc dsum P.1 + dsum P.2 ≤ 2 ^ n * (dsumN c U + dsumN c V) := sP
      _ ≤ 2 ^ n * σ := Nat.mul_le_mul_left _ hσ
      _ ≤ 4 ^ n * σ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) n)
      _ < c.b := lt_of_lt_of_le hsz hlb
  have bP1 := dP1.boxSupp hBS hnS
  have bP2 := dP2.boxSupp hBS hnS
  have lP1 : ∀ i j, cf P.1 i j < c.b := fun i j => lt_of_le_of_lt (cf_le_dsum bP1 i j) (by omega)
  have lP2 : ∀ i j, cf P.2 i j < c.b := fun i j => lt_of_le_of_lt (cf_le_dsum bP2 i j) (by omega)
  have pG1 : poly c G.1 = P.1 := by rw [hG]; exact poly_evB bP1 lP1
  have pG2 : poly c G.2 = P.2 := by rw [hG]; exact poly_evB bP2 lP2
  have hsQ : dsum Q.1 + dsum Q.2 ≤ 4 ^ n * σ := by
    calc dsum Q.1 + dsum Q.2 ≤ 2 ^ n * (dsumN c G.1 + dsumN c G.2) := sQ
      _ = 2 ^ n * (dsum P.1 + dsum P.2) := by rw [dsumN_eq, dsumN_eq, pG1, pG2]
      _ ≤ 2 ^ n * (2 ^ n * σ) := Nat.mul_le_mul_left _ (sP.trans (Nat.mul_le_mul_left _ hσ))
      _ = 4 ^ n * σ := by rw [← mul_assoc, h4]
  have bQ1 := dQ1.boxSupp hnS hnS
  have bQ2 := dQ2.boxSupp hnS hnS
  have lQ1 : ∀ i j, cf Q.1 i j < c.b := fun i j => lt_of_le_of_lt (cf_le_dsum bQ1 i j) (by omega)
  have lQ2 : ∀ i j, cf Q.2 i j < c.b := fun i j => lt_of_le_of_lt (cf_le_dsum bQ2 i j) (by omega)
  have hR : bernR c n U V = (evB c Q.1, evB c Q.2) := hH
  refine ⟨pG1, pG2, ?_, ?_, ?_, ?_, dP1, dP2, dQ1, dQ2, hsQ⟩
  · rw [hR]; exact poly_evB bQ1 lQ1
  · rw [hR]; exact poly_evB bQ2 lQ2
  · rw [hR]; exact box_evB bQ1 lQ1
  · rw [hR]; exact box_evB bQ2 lQ2

theorem coeffs_of_poly {c : Config} {N : ℕ} {P : NB} (h : poly c N = P) {i j : ℕ} (hi : i < c.S)
    (hj : j < c.S) : coeffs c N i j = cf P i j := by
  rw [← h, cf_poly, ite_eq_left ⟨hi, hj⟩]; rfl

/-- The homogenized transform equals the model polynomial. -/
theorem bern_identity {c : Config} {n : ℕ} (hBn : c.B < n) (hnS : n < c.S) {U V G₁ G₂ : ℕ}
    (hU : OnTri c U) (hV : OnTri c V) {P₁ P₂ Q₁ Q₂ : NB}
    (hP : toR P₁ - toR P₂ = ∑ l ∈ Finset.range (c.B + 1),
      (toR (colSlices c U V l).1 - toR (colSlices c U V l).2) * C (factor n l))
    (hQ : toR Q₁ - toR Q₂ = ∑ l ∈ Finset.range (c.B + 1),
      (toR (rowSlices c n G₁ G₂ l).1 - toR (rowSlices c n G₁ G₂ l).2) * (factor n l).map C)
    (hG₁ : poly c G₁ = P₁) (hG₂ : poly c G₂ = P₂) (x y : ℝ) :
    ∑ I ∈ Finset.range (n + 1), ∑ J ∈ Finset.range (n + 1),
      ((cf Q₁ I J : ℝ) - cf Q₂ I J) * (((1 + x) / 2) ^ I * ((1 - x) / 2) ^ (n - I)) *
        (((1 + y) / 2) ^ J * ((1 - y) / 2) ^ (n - J)) =
      evalN c U x y - evalN c V x y := by
  have hBS : c.B < c.S := by unfold Config.S; omega
  set u := (1 + x) / 2
  set w := (1 - x) / 2
  set u' := (1 + y) / 2
  set w' := (1 - y) / 2
  set cc : ℕ → ℕ → ℝ := fun i j => (coeffs c U i j : ℝ) - coeffs c V i j with hcc
  -- coefficients of `P`
  have hPc : ∀ l J, l ≤ c.B → (cf P₁ l J : ℝ) - cf P₂ l J =
      ∑ l' ∈ Finset.range (c.B + 1), cc l l' * (factor n l').coeff J := by
    intro l J hl
    rw [← cfR_toR, ← cfR_toR, ← cfR_sub, hP, cfR_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [cfR_mul_C, colSlices_coeff c U V l' l hl, coeff_C_mul]
  -- coefficients of `Q`
  have hQc : ∀ I J, J ≤ n → (cf Q₁ I J : ℝ) - cf Q₂ I J =
      ∑ l ∈ Finset.range (c.B + 1), ((cf P₁ l J : ℝ) - cf P₂ l J) * (factor n l).coeff I := by
    intro I J hJ
    rw [← cfR_toR, ← cfR_toR, ← cfR_sub, hQ, cfR_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l < c.S := by have := Finset.mem_range.mp hl; omega
    rw [rowSlices_eq c G₁ G₂ l hl', cfR_C_mul_map, finsetSum_coeff]
    congr 1
    rw [Finset.sum_eq_single J]
    · rw [coeff_monomial, ite_eq_left rfl, ite_eq_left hJ, coeffs_of_poly hG₁ hl' (by omega),
        coeffs_of_poly hG₂ hl' (by omega)]
    · intro j _ hj; rw [coeff_monomial, ite_eq_right hj]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  -- the homogenized sums
  have hx : ∀ l, l ≤ c.B → ∑ I ∈ Finset.range (n + 1), (factor n l).coeff I * u ^ I * w ^ (n - I) =
      x ^ l := fun l hl => factor_hom n l (by omega) x
  have hy : ∀ l, l ≤ c.B → ∑ J ∈ Finset.range (n + 1), (factor n l).coeff J * u' ^ J * w' ^ (n - J) =
      y ^ l := fun l hl => factor_hom n l (by omega) y
  calc ∑ I ∈ Finset.range (n + 1), ∑ J ∈ Finset.range (n + 1),
        ((cf Q₁ I J : ℝ) - cf Q₂ I J) * (u ^ I * w ^ (n - I)) * (u' ^ J * w' ^ (n - J))
      = ∑ I ∈ Finset.range (n + 1), ∑ J ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (c.B + 1),
          ((factor n l).coeff I * u ^ I * w ^ (n - I)) *
            ((∑ l' ∈ Finset.range (c.B + 1), cc l l' * (factor n l').coeff J) *
              (u' ^ J * w' ^ (n - J))) := by
        refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J hJ => ?_
        rw [hQc I J (by have := Finset.mem_range.mp hJ; omega), Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [hPc l J (by have := Finset.mem_range.mp hl; omega)]
        ring
    _ = ∑ l ∈ Finset.range (c.B + 1), (∑ I ∈ Finset.range (n + 1),
          (factor n l).coeff I * u ^ I * w ^ (n - I)) *
          ∑ J ∈ Finset.range (n + 1), ((∑ l' ∈ Finset.range (c.B + 1), cc l l' * (factor n l').coeff J) *
              (u' ^ J * w' ^ (n - J))) := by
        rw [Finset.sum_congr rfl fun I _ => Finset.sum_comm, Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.sum_mul_sum _ _ _ _).symm
    _ = ∑ l ∈ Finset.range (c.B + 1), (∑ I ∈ Finset.range (n + 1),
          (factor n l).coeff I * u ^ I * w ^ (n - I)) *
          ∑ l' ∈ Finset.range (c.B + 1), cc l l' * ∑ J ∈ Finset.range (n + 1),
            (factor n l').coeff J * u' ^ J * w' ^ (n - J) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 1
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun J _ => by ring
    _ = ∑ l ∈ Finset.range (c.B + 1), ∑ l' ∈ Finset.range (c.B + 1), cc l l' * x ^ l * y ^ l' := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [hx l (by have := Finset.mem_range.mp hl; omega), Finset.mul_sum]
        refine Finset.sum_congr rfl fun l' hl' => ?_
        rw [hy l' (by have := Finset.mem_range.mp hl'; omega)]
        ring
    _ = evalN c U x y - evalN c V x y := by
        rw [evalN_onTri hU, evalN_onTri hV, ← Finset.sum_sub_distrib, ← sum_range_ite_le hBS]
        refine Finset.sum_congr rfl fun i hi' => ?_
        have hiS := Finset.mem_range.mp hi'
        rw [← Finset.sum_sub_distrib]
        by_cases hi : i ≤ c.B
        · rw [ite_eq_left hi, ← sum_range_ite_le hBS]
          refine Finset.sum_congr rfl fun j hj' => ?_
          have hjS := Finset.mem_range.mp hj'
          by_cases hj : j ≤ c.B
          · rw [ite_eq_left hj]
            by_cases ht : tri c i j
            · rw [ite_eq_left ht, ite_eq_left ht]
              show ((coeffs c U i j : ℝ) - coeffs c V i j) * x ^ i * y ^ j = _
              ring
            · rw [ite_eq_right ht, ite_eq_right ht]
              have h1 := hU.2 i j hiS hjS ht
              have h2 := hV.2 i j hiS hjS ht
              show ((coeffs c U i j : ℝ) - coeffs c V i j) * x ^ i * y ^ j = _
              rw [h1, h2]; simp
          · have ht : ¬ tri c i j := fun h => hj (by unfold tri at h; omega)
            rw [ite_eq_right hj, ite_eq_right ht, ite_eq_right ht]; simp
        · rw [ite_eq_right hi]
          symm
          refine Finset.sum_eq_zero fun j _ => ?_
          have ht : ¬ tri c i j := fun h => hi (by unfold tri at h; omega)
          rw [ite_eq_right ht, ite_eq_right ht]; simp

theorem pack_of_poly {c : Config} {n N : ℕ} {P : NB} (hN : Box c N) (hp : poly c N = P)
    (hD : Deg n n P) : N = pack c (fun I J => if sq n I J then cf P I J else 0) := by
  conv_lhs => rw [eq_pack_coeffs hN]
  apply pack_congr
  intro I J hI hJ
  rw [coeffs_of_poly hp hI hJ]
  split_ifs with hs
  · rfl
  · by_contra hne; exact hs (hD I J hne)

theorem ones2_eq (c : Config) {n : ℕ} (hn : n < c.S) :
    spread (c.w * c.S) 1 n * spread c.w 1 n = pack c (fun I J => if sq n I J then 1 else 0) := by
  rw [spread_sum, spread_sum]
  have := pack_rect c (fun _ => 1) (fun _ => 1) hn hn
  simp only [Config.b, ← pow_mul, mul_one] at this ⊢
  rw [this]
  rfl

theorem bin2_eq (c : Config) {n : ℕ} (hn : n < c.S) :
    binomPow (c.w * c.S) n * binomPow c.w n =
      pack c (fun I J => if sq n I J then n.choose I * n.choose J else 0) := by
  rw [binomPow_sum, binomPow_sum]
  have := pack_rect c (fun i => n.choose i) (fun j => n.choose j) hn hn
  simp only [Config.b, ← pow_mul] at this ⊢
  rw [this]
  rfl

theorem choose_mul_le (n i j : ℕ) : n.choose i * n.choose j ≤ 4 ^ n := by
  calc n.choose i * n.choose j ≤ 2 ^ n * 2 ^ n :=
        Nat.mul_le_mul (Nat.choose_le_two_pow n i) (Nat.choose_le_two_pow n j)
    _ = 4 ^ n := by rw [← mul_pow]; norm_num

/-- **The Bernstein check.** If it passes, the model polynomial is at least `τ / 2 ^ K` on the
square `[-1, 1]²`. -/
theorem bernCheck_sound {c : Config} (hc : c.Valid) {n τ : ℕ} {m : Model} (hg : m.Good c)
    (h : bernCheck c n m τ = true) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (τ : ℝ) ≤ evalN c m.U x y - evalN c m.V x y := by
  simp only [bernCheck, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hBn, hnS⟩, hsz⟩, hsign⟩ := h
  rw [hg.size_eq hc] at hsz
  set σ := dsumN c m.U + dsumN c m.V with hσ
  have hsz' : 4 ^ n * σ < 2 ^ (c.w - 2) := by omega
  obtain ⟨pG1, pG2, pH1, pH2, bH1, bH2, _, _, dQ1, dQ2, sQ⟩ :=
    bern_poly (c := c) hBn hnS (U := m.U) (V := m.V) σ le_rfl hsz'
  obtain ⟨_, _, _, _, rP⟩ := stage1_props (c := c) hBn m.U m.V
  obtain ⟨_, _, _, _, rQ⟩ := stage2_props (c := c) hBn hnS (stage1 c n m.U m.V).1
    (stage1 c n m.U m.V).2
  set Q := pstage2 c n (stage1 c n m.U m.V).1 (stage1 c n m.U m.V).2 with hQ
  have hw : 1 ≤ c.w := by have := hc.K_lt; omega
  have hlim : 2 ^ (c.w - 2) ≤ 2 ^ (c.w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have bQ1 := dQ1.boxSupp hnS hnS
  have bQ2 := dQ2.boxSupp hnS hnS
  -- the sign test
  have key : ∀ I J, I ≤ n → J ≤ n → cf Q.2 I J + τ * (n.choose I * n.choose J) ≤ cf Q.1 I J := by
    intro I J hI hJ
    have hp : ∀ i j, cf Q.1 i j < 2 ^ (c.w - 1) := fun i j => by
      have := cf_le_dsum bQ1 i j; omega
    have hq : ∀ i j, cf Q.2 i j + τ * (n.choose i * n.choose j) < 2 ^ (c.w - 1) := fun i j => by
      have h1 := cf_le_dsum bQ2 i j
      have h2 := Nat.mul_le_mul_left τ (choose_mul_le n i j)
      have h3 : τ * 4 ^ n = 4 ^ n * τ := mul_comm _ _
      nlinarith
    have hH1 := pack_of_poly bH1 pH1 dQ1
    have hH2 := pack_of_poly bH2 pH2 dQ2
    have hA : (bernR c n m.U m.V).1 + (spread (c.w * c.S) 1 n * spread c.w 1 n) <<< (c.w - 1) =
        pack c (fun i j => if sq n i j then cf Q.1 i j else 0) +
          pack c (fun i j => if sq n i j then 2 ^ (c.w - 1) else 0) := by
      rw [hH1, ones2_eq c hnS, Nat.shiftLeft_eq, pack_mul_const]
      congr 1
      apply pack_congr; intro i j _ _; split_ifs <;> simp
    have hB : (bernR c n m.U m.V).2 + τ * (binomPow (c.w * c.S) n * binomPow c.w n) =
        pack c (fun i j => if sq n i j then cf Q.2 i j + τ * (n.choose i * n.choose j) else 0) := by
      rw [hH2, bin2_eq c hnS, mul_comm τ, pack_mul_const, pack_add]
      apply pack_congr; intro i j _ _; split_ifs <;> ring
    rw [hA, hB, ones2_eq c hnS] at hsign
    exact sign_test hw (p := fun i j => cf Q.1 i j)
      (q := fun i j => cf Q.2 i j + τ * (n.choose i * n.choose j)) hp hq hsign (by omega) (by omega)
      ⟨hI, hJ⟩
  -- the Bernstein form
  have hid := bern_identity hBn hnS hg.triU hg.triV rP rQ pG1 pG2 x y
  rw [← hid]
  have hu : 0 ≤ (1 + x) / 2 := by have := (abs_le.mp hx).1; linarith
  have hw' : 0 ≤ (1 - x) / 2 := by have := (abs_le.mp hx).2; linarith
  have hu' : 0 ≤ (1 + y) / 2 := by have := (abs_le.mp hy).1; linarith
  have hw'' : 0 ≤ (1 - y) / 2 := by have := (abs_le.mp hy).2; linarith
  have hsum : ∀ z : ℝ, ∑ I ∈ Finset.range (n + 1),
      (n.choose I : ℝ) * (((1 + z) / 2) ^ I * ((1 - z) / 2) ^ (n - I)) = 1 := fun z => by
    have := add_pow ((1 + z) / 2) ((1 - z) / 2) n
    calc ∑ I ∈ Finset.range (n + 1), (n.choose I : ℝ) * (((1 + z) / 2) ^ I * ((1 - z) / 2) ^ (n - I))
        = ∑ I ∈ Finset.range (n + 1), ((1 + z) / 2) ^ I * ((1 - z) / 2) ^ (n - I) * (n.choose I : ℝ) :=
          Finset.sum_congr rfl fun I _ => by ring
      _ = ((1 + z) / 2 + (1 - z) / 2) ^ n := this.symm
      _ = 1 := by rw [show (1 + z) / 2 + (1 - z) / 2 = (1 : ℝ) by ring, one_pow]
  calc (τ : ℝ) = ∑ I ∈ Finset.range (n + 1), ∑ J ∈ Finset.range (n + 1),
        (τ : ℝ) * ((n.choose I : ℝ) * (((1 + x) / 2) ^ I * ((1 - x) / 2) ^ (n - I))) *
          ((n.choose J : ℝ) * (((1 + y) / 2) ^ J * ((1 - y) / 2) ^ (n - J))) := by
        rw [← Finset.sum_mul_sum, ← Finset.mul_sum, hsum x, hsum y]; ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun I hI => Finset.sum_le_sum fun J hJ => ?_
        have hk := key I J (by have := Finset.mem_range.mp hI; omega)
          (by have := Finset.mem_range.mp hJ; omega)
        have hk' : (τ : ℝ) * ((n.choose I : ℝ) * (n.choose J : ℝ)) ≤ (cf Q.1 I J : ℝ) - cf Q.2 I J := by
          have : ((cf Q.2 I J + τ * (n.choose I * n.choose J) : ℕ) : ℝ) ≤ (cf Q.1 I J : ℝ) := by
            exact_mod_cast hk
          push_cast at this; linarith
        have hwI : 0 ≤ ((1 + x) / 2) ^ I * ((1 - x) / 2) ^ (n - I) := by positivity
        have hwJ : 0 ≤ ((1 + y) / 2) ^ J * ((1 - y) / 2) ^ (n - J) := by positivity
        calc (τ : ℝ) * ((n.choose I : ℝ) * (((1 + x) / 2) ^ I * ((1 - x) / 2) ^ (n - I))) *
              ((n.choose J : ℝ) * (((1 + y) / 2) ^ J * ((1 - y) / 2) ^ (n - J)))
            = ((τ : ℝ) * ((n.choose I : ℝ) * (n.choose J : ℝ))) *
                (((1 + x) / 2) ^ I * ((1 - x) / 2) ^ (n - I)) *
                (((1 + y) / 2) ^ J * ((1 - y) / 2) ^ (n - J)) := by ring
          _ ≤ ((cf Q.1 I J : ℝ) - cf Q.2 I J) * (((1 + x) / 2) ^ I * ((1 - x) / 2) ^ (n - I)) *
                (((1 + y) / 2) ^ J * ((1 - y) / 2) ^ (n - J)) := by gcongr

/-! ## Ranges of models -/

theorem evalN_split {c : Config} {N : ℕ} (hN : Box c N) (x y : ℝ) {hx : |x| ≤ 1} {hy : |y| ≤ 1} :
    |evalN c N x y - (N % c.b : ℕ)| ≤ (dsumN c N : ℝ) - (N % c.b : ℕ) := by
  have h00 : N % c.b = coeffs c N 0 0 := by simp [coeffs, digit_zero_right, Config.b]
  set d := coeffs c N
  have hd : ∀ i j, d i j < c.b := coeffs_lt c N
  set d' : ℕ → ℕ → ℕ := fun i j => if i = 0 ∧ j = 0 then 0 else d i j
  have hd' : ∀ i j, d' i j < c.b := fun i j => by simp only [d']; split_ifs <;> [exact c.b_pos; exact hd i j]
  have hsplit : ∀ i j, d i j = d' i j + (if i = 0 ∧ j = 0 then d 0 0 else 0) := fun i j => by
    simp only [d']; split_ifs with h
    · rw [h.1, h.2]; ring
    · ring
  have hS := c.S_pos
  have hev : evalN c N x y = evalN c (pack c d') x y + d 0 0 := by
    rw [← pack_coeffs hN]
    rw [evalN_pack c hd, evalN_pack c hd']
    have : ∀ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, (d i j : ℝ) * x ^ i * y ^ j =
        ∑ j ∈ Finset.range c.S, (d' i j : ℝ) * x ^ i * y ^ j +
          ∑ j ∈ Finset.range c.S, ((if i = 0 ∧ j = 0 then d 0 0 else 0 : ℕ) : ℝ) * x ^ i * y ^ j := by
      intro i _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hsplit i j]; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_range.mpr hS) h
    · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [hi]
    · intro h; exact absurd (Finset.mem_range.mpr hS) h
  have hds : dsumN c N = dsumN c (pack c d') + d 0 0 := by
    conv_lhs => rw [← pack_coeffs hN]
    rw [dsumN_pack c hd, dsumN_pack c hd']
    have : ∀ i ∈ Finset.range c.S, ∑ j ∈ Finset.range c.S, d i j =
        ∑ j ∈ Finset.range c.S, d' i j + ∑ j ∈ Finset.range c.S, (if i = 0 ∧ j = 0 then d 0 0 else 0) := by
      intro i _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hsplit i j
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_range.mpr hS) h
    · intro i _ hi; exact Finset.sum_eq_zero fun j _ => by simp [hi]
    · intro h; exact absurd (Finset.mem_range.mpr hS) h
  rw [h00, hev, hds]
  push_cast
  rw [add_sub_cancel_right, add_sub_cancel_right]
  exact abs_evalN_le c _ hx hy

namespace Model

/-- Lower and upper bounds of the value of a model, at the scale `2 ^ K`. -/
def lowerZ (c : Config) (m : Model) : ℤ := 2 * (m.U % c.b : ℕ) - m.size c - m.e
def upperZ (c : Config) (m : Model) : ℤ := m.size c - 2 * (m.V % c.b : ℕ) + m.e

theorem bounds {c : Config} (hc : c.Valid) {m : Model} {x y v : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h : m.Contains c x y v) (hok : m.ok = true) :
    (m.lowerZ c : ℝ) / 2 ^ c.K ≤ v ∧ v ≤ (m.upperZ c : ℝ) / 2 ^ c.K := by
  obtain ⟨hg, he⟩ := h hok
  have h1 := evalN_split hg.triU.1 x y (hx := hx) (hy := hy)
  have h2 := evalN_split hg.triV.1 x y (hx := hx) (hy := hy)
  have hs := hg.size_eq hc
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hv := abs_le.mp he
  simp only [val] at hv
  rw [abs_le] at h1 h2
  unfold lowerZ upperZ
  rw [hs]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_add]
  constructor
  · rw [div_le_iff₀ h2K]
    have : (evalN c m.U x y - evalN c m.V x y) / 2 ^ c.K * 2 ^ c.K = evalN c m.U x y - evalN c m.V x y :=
      div_mul_cancel₀ _ h2K.ne'
    have h3 : v * 2 ^ c.K ≥ (evalN c m.U x y - evalN c m.V x y) - m.e := by
      have := hv.1
      rw [show v - (evalN c m.U x y - evalN c m.V x y) / 2 ^ c.K =
        (v * 2 ^ c.K - (evalN c m.U x y - evalN c m.V x y)) / 2 ^ c.K by field_simp] at this
      rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right h2K] at this
      linarith
    linarith [h1.1, h2.2]
  · rw [le_div_iff₀ h2K]
    have h3 : v * 2 ^ c.K ≤ (evalN c m.U x y - evalN c m.V x y) + m.e := by
      have := hv.2
      rw [show v - (evalN c m.U x y - evalN c m.V x y) / 2 ^ c.K =
        (v * 2 ^ c.K - (evalN c m.U x y - evalN c m.V x y)) / 2 ^ c.K by field_simp] at this
      rw [div_le_div_iff_of_pos_right h2K] at this
      linarith
    linarith [h1.2, h2.1]

end Model

/-! ## Square roots and reciprocals of models

`v = base · (1 + h)` with `|h| ≤ s < 19/200`; the binomial series of `(1 + h)^(1/2)` or
`(1 + h)^(-1)` to degree 12 with the remainder `|c₁₃| s^13 / (1 - s)`
(`RoundedBinomialEnclosure.binomial_remainder`). -/

namespace Model
open RoundedBinomialEnclosure

def rootCoeffs : List (ℤ × ℕ) :=
  [(1, 1), (1, 2), (-1, 8), (1, 16), (-5, 128), (7, 256), (-21, 1024), (33, 2048),
    (-429, 32768), (715, 65536), (-2431, 262144), (4199, 524288), (-29393, 4194304)]
def invCoeffs : List (ℤ × ℕ) :=
  [(1, 1), (-1, 1), (1, 1), (-1, 1), (1, 1), (-1, 1), (1, 1), (-1, 1), (1, 1), (-1, 1),
    (1, 1), (-1, 1), (1, 1)]

theorem hornerVal_eq_realHorner (v : ℝ) :
    ∀ l : List (ℤ × ℕ), hornerVal v l = realHorner v (l.map fun q => (q.1 : ℚ) / q.2)
  | [] => rfl
  | q :: l => by
    simp only [hornerVal, List.map_cons, realHorner, hornerVal_eq_realHorner v l]
    push_cast; rfl

theorem rootCoeffs_eq : rootCoeffs.map (fun q => (q.1 : ℚ) / q.2) = coefficients .root := by
  simp [rootCoeffs, coefficients, List.ofFn_succ, coefficient, exponent]; norm_num

theorem invCoeffs_eq : invCoeffs.map (fun q => (q.1 : ℚ) / q.2) = coefficients .inverse := by
  simp [invCoeffs, coefficients, List.ofFn_succ, coefficient, exponent]; norm_num

theorem coefficient_root_13 : coefficient .root 13 = 52003 / 8388608 := by
  simp [coefficient, exponent]; norm_num

theorem coefficient_inverse_13 : coefficient .inverse 13 = -1 := by
  simp [coefficient, exponent]; norm_num

/-- `⌈a / d⌉`. -/
def cdiv (a d : ℕ) : ℕ := (a + (d - 1)) / d

/-- The binomial remainder `num · s^13 / (den (1 - s))`, `s = sN / 2^K`, in units `2^-K`. -/
def binomTail (c : Config) (num den sN : ℕ) : ℕ :=
  cdiv (num * sN ^ 13) (den * 2 ^ (11 * c.K) * (2 ^ c.K - sN))

/-- The square root of `N` rounded down, bit by bit from bit `k - 1` (for `N < 4 ^ k`); unlike
`Nat.sqrt`, the kernel evaluates it. -/
def isqrt (N : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | k + 1, r => isqrt N k (if (r + 2 ^ k) * (r + 2 ^ k) ≤ N then r + 2 ^ k else r)

/-- `√v`. -/
def sqrt (c : Config) (a : Model) : Model :=
  let c0 := (a.U % c.b : ℕ) - (a.V % c.b : ℕ)
  let r := isqrt (c0 * 2 ^ c.K) c.w 0
  let h := add c (mul c a (lit c (2 ^ (2 * c.K)) (r * r))) (ofInt c (-(2 ^ c.K)) 0 true)
  let sN := h.size c + h.e
  let body := widen (horner c h rootCoeffs) (binomTail c 52003 8388608 sN)
  let res := mul c (ofInt c r 0 true) body
  ⟨res.U, res.V, res.e, res.ok && Nat.blt 0 r && Nat.blt (200 * sN) (19 * 2 ^ c.K)⟩

/-- `1 / v`. -/
def inv (c : Config) (a : Model) : Model :=
  let c0 := (a.U % c.b : ℕ) - (a.V % c.b : ℕ)
  let h := add c (mul c a (lit c (2 ^ c.K) c0)) (ofInt c (-(2 ^ c.K)) 0 true)
  let sN := h.size c + h.e
  let body := widen (horner c h invCoeffs) (binomTail c 1 1 sN)
  let res := mul c (lit c (2 ^ c.K) c0) body
  ⟨res.U, res.V, res.e, res.ok && Nat.blt 0 c0 && Nat.blt (200 * sN) (19 * 2 ^ c.K)⟩

theorem cdiv_ge (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d ≤ (cdiv a d : ℝ) := ceil_div_ge a d hd

/-- The span of a model with a passed check. -/
theorem span {c : Config} (hc : c.Valid) {m : Model} {x y v : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (h : m.Contains c x y v) (hok : m.ok = true) :
    |v| ≤ ((m.size c + m.e : ℕ) : ℝ) / 2 ^ c.K := by
  obtain ⟨hg, he⟩ := h hok
  have hv := abs_val_le (m := m) (c := c) hx hy
  rw [hg.size_eq hc]
  push_cast
  rw [add_div]
  have := abs_sub_abs_le_abs_sub v (m.val c x y)
  push_cast at hv
  linarith

theorem tail_bound (c : Config) {num den sN : ℕ} (hden : 0 < den) (hs : sN < 2 ^ c.K) :
    (num : ℝ) / den * ((sN : ℝ) / 2 ^ c.K) ^ 13 / (1 - (sN : ℝ) / 2 ^ c.K) ≤
      (binomTail c num den sN : ℝ) / 2 ^ c.K := by
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hsR : (sN : ℝ) < 2 ^ c.K := by exact_mod_cast hs
  have hpos : 0 < den * 2 ^ (11 * c.K) * (2 ^ c.K - sN) := by
    have : 0 < 2 ^ c.K - sN := by omega
    positivity
  have h := cdiv_ge (num * sN ^ 13) (den * 2 ^ (11 * c.K) * (2 ^ c.K - sN)) hpos
  rw [le_div_iff₀ h2K]
  refine le_trans (le_of_eq ?_) h
  have hsub : ((2 ^ c.K - sN : ℕ) : ℝ) = 2 ^ c.K - sN := by
    rw [Nat.cast_sub hs.le]; push_cast; ring
  push_cast [hsub]
  have h1 : (1 : ℝ) - sN / 2 ^ c.K = (2 ^ c.K - sN) / 2 ^ c.K := by field_simp
  rw [h1]
  have h3 : (2 : ℝ) ^ c.K - sN ≠ 0 := by linarith
  field_simp
  ring

end Model

namespace Model
open RoundedBinomialEnclosure

theorem mul_ok {c : Config} {a b : Model} (h : (mul c a b).ok = true) : a.ok = true ∧ b.ok = true := by
  simp only [mul, Bool.and_eq_true] at h; exact h.1

theorem add_ok {c : Config} {a b : Model} (h : (add c a b).ok = true) : a.ok = true ∧ b.ok = true := by
  simp only [add, Bool.and_eq_true] at h; exact h.1

theorem horner_ok {c : Config} {a : Model} {q : ℤ × ℕ} {l : List (ℤ × ℕ)}
    (h : (horner c a (q :: l)).ok = true) : a.ok = true := by
  rw [horner] at h
  exact (mul_ok (add_ok h).2).1

theorem widen_ok {m : Model} {r : ℕ} (h : (widen m r).ok = true) : m.ok = true := h

/-- The binomial step shared by `√` and `1/·`. -/
theorem binom_step {c : Config} (hc : c.Valid) {h : Model} {x y hv : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hh : h.Contains c x y hv) (hok : h.ok = true) (hsN : 200 * (h.size c + h.e) < 19 * 2 ^ c.K)
    (e : Exponent) (l : List (ℤ × ℕ)) (hl : l.map (fun q => (q.1 : ℚ) / q.2) = coefficients e)
    (num den : ℕ) (hden : 0 < den) (hc13 : |(coefficient e 13 : ℝ)| = num / den) :
    (widen (horner c h l) (binomTail c num den (h.size c + h.e))).Contains c x y
      ((1 + hv) ^ (exponent e : ℝ)) ∧ 0 < 1 + hv := by
  set sN := h.size c + h.e
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hsp := span hc hx hy hh hok
  have hsN' : sN < 2 ^ c.K := by omega
  have hs1 : (sN : ℝ) / 2 ^ c.K < 1 := by
    rw [div_lt_one h2K]; exact_mod_cast hsN'
  have hs0 : (0 : ℝ) ≤ (sN : ℝ) / 2 ^ c.K := by positivity
  refine ⟨contains_widen (contains_horner hc hx hy hh l) _ ?_, ?_⟩
  · rw [hornerVal_eq_realHorner, hl]
    have hb := binomial_remainder e hs0 hs1 hsp
    rw [hc13] at hb
    exact hb.trans (tail_bound c hden hsN')
  · have := (abs_le.mp hsp).1; linarith

theorem contains_sqrt {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) : (sqrt c a).Contains c x y (Real.sqrt v) := by
  intro hok
  simp only [sqrt, Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨hres, hr⟩, hsN⟩ := hok
  set r := isqrt (((a.U % c.b : ℕ) - (a.V % c.b : ℕ)) * 2 ^ c.K) c.w 0
  set h := add c (mul c a (lit c (2 ^ (2 * c.K)) (r * r))) (ofInt c (-(2 ^ c.K)) 0 true)
  have hh : h.Contains c x y (v * (((2 ^ (2 * c.K) : ℤ) : ℝ) / ((r * r : ℕ) : ℝ)) + -1) :=
    contains_add hc (contains_mul hc hx hy ha (contains_lit c _ _))
      (contains_ofInt _ 0 true (by push_cast; rw [neg_div, div_self (by positivity)]; simp))
  have hbody := mul_ok hres
  have hhok : h.ok = true := horner_ok (widen_ok hbody.2)
  obtain ⟨hB, hpos⟩ := binom_step hc hx hy hh hhok hsN .root rootCoeffs rootCoeffs_eq 52003 8388608
    (by norm_num) (by rw [coefficient_root_13]; norm_num)
  have hfac : (ofInt c (r : ℤ) 0 true).Contains c x y ((r : ℝ) / 2 ^ c.K) :=
    contains_ofInt _ 0 true (by simp)
  have hm := contains_mul hc hx hy hfac hB
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hval : (r : ℝ) / 2 ^ c.K * (1 + (v * (((2 ^ (2 * c.K) : ℤ) : ℝ) / ((r * r : ℕ) : ℝ)) + -1)) ^
      (exponent .root : ℝ) = Real.sqrt v := by
    have e1 : 1 + (v * (((2 ^ (2 * c.K) : ℤ) : ℝ) / ((r * r : ℕ) : ℝ)) + -1) =
        v * ((2 ^ c.K / r) ^ 2) := by
      push_cast
      rw [show (2 : ℝ) ^ (2 * c.K) = (2 ^ c.K) ^ 2 by rw [← pow_mul, mul_comm]]
      field_simp
      ring
    have hv0 : 0 ≤ v := by
      rw [e1] at hpos
      have : 0 < (2 ^ c.K / (r : ℝ)) ^ 2 := by positivity
      by_contra hneg; push Not at hneg; nlinarith
    rw [e1, show (exponent .root : ℝ) = 1 / 2 by simp [exponent], ← Real.sqrt_eq_rpow,
      Real.sqrt_mul hv0, Real.sqrt_sq (by positivity)]
    field_simp
  rw [← hval]
  obtain ⟨hg, he⟩ := hm hres
  exact ⟨⟨hg.triU, hg.triV, hg.small⟩, he⟩

theorem contains_inv {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) : (inv c a).Contains c x y (1 / v) := by
  intro hok
  simp only [inv, Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨hres, hc0⟩, hsN⟩ := hok
  set c0 := (a.U % c.b : ℕ) - (a.V % c.b : ℕ)
  set h := add c (mul c a (lit c (2 ^ c.K) c0)) (ofInt c (-(2 ^ c.K)) 0 true)
  have hh : h.Contains c x y (v * (((2 ^ c.K : ℤ) : ℝ) / (c0 : ℝ)) + -1) :=
    contains_add hc (contains_mul hc hx hy ha (contains_lit c _ _))
      (contains_ofInt _ 0 true (by push_cast; rw [neg_div, div_self (by positivity)]; simp))
  have hbody := mul_ok hres
  have hhok : h.ok = true := horner_ok (widen_ok hbody.2)
  obtain ⟨hB, hpos⟩ := binom_step hc hx hy hh hhok hsN .inverse invCoeffs invCoeffs_eq 1 1
    (by norm_num) (by rw [coefficient_inverse_13]; norm_num)
  have hm := contains_mul hc hx hy (contains_lit c (2 ^ c.K) c0) hB
  have hc0R : (0 : ℝ) < c0 := by exact_mod_cast hc0
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hval : ((2 ^ c.K : ℤ) : ℝ) / (c0 : ℝ) *
      (1 + (v * (((2 ^ c.K : ℤ) : ℝ) / (c0 : ℝ)) + -1)) ^ (exponent .inverse : ℝ) = 1 / v := by
    have e1 : 1 + (v * (((2 ^ c.K : ℤ) : ℝ) / (c0 : ℝ)) + -1) = v * (2 ^ c.K / c0) := by
      push_cast; ring
    have hv0 : 0 < v := by
      rw [e1] at hpos
      have : 0 < (2 : ℝ) ^ c.K / c0 := by positivity
      by_contra hneg; push Not at hneg; nlinarith
    rw [e1, show (exponent .inverse : ℝ) = -1 by simp [exponent], Real.rpow_neg_one]
    push_cast
    field_simp
  rw [← hval]
  obtain ⟨hg, he⟩ := hm hres
  exact ⟨⟨hg.triU, hg.triV, hg.small⟩, he⟩

end Model

/-! ## Expressions -/

/-- Rational literals, written so that `toQ` is syntactically the literal of a frozen formula:
`nat n` is the cast `(n : ℚ)` of an expression numeral, `num n` the numeral `n : ℚ`, `q n d` and
`qneg n d` the literals `n / d` and `-n / d`, and sums, differences and products of such. -/
inductive QL where
  | nat (n : ℕ)
  | num (n : ℕ)
  | q (n d : ℕ)
  | qneg (n d : ℕ)
  | frac (n : ℤ) (d : ℕ)
  | neg (a : QL)
  | add (a b : QL)
  | sub (a b : QL)
  | mul (a b : QL)

def QL.toQ : QL → ℚ
  | .nat n => (n : ℚ)
  | .num n => (OfNat.ofNat n : ℚ)
  | .q n d => (OfNat.ofNat n : ℚ) / (OfNat.ofNat d : ℚ)
  | .qneg n d => -(OfNat.ofNat n : ℚ) / (OfNat.ofNat d : ℚ)
  | .frac n d => (n : ℚ) / (d : ℚ)
  | .neg a => -a.toQ
  | .add a b => a.toQ + b.toQ
  | .sub a b => a.toQ - b.toQ
  | .mul a b => a.toQ * b.toQ

/-- The exact value as an unreduced fraction. -/
def QL.eval : QL → ℤ × ℕ
  | .nat n | .num n => ((n : ℤ), 1)
  | .q n d => ((n : ℤ), d)
  | .qneg n d => (-(n : ℤ), d)
  | .frac n d => (n, d)
  | .neg a => (-a.eval.1, a.eval.2)
  | .add a b => (a.eval.1 * b.eval.2 + b.eval.1 * a.eval.2, a.eval.2 * b.eval.2)
  | .sub a b => (a.eval.1 * b.eval.2 - b.eval.1 * a.eval.2, a.eval.2 * b.eval.2)
  | .mul a b => (a.eval.1 * b.eval.1, a.eval.2 * b.eval.2)

theorem QL.ofNat_eq (n : ℕ) : (OfNat.ofNat n : ℚ) = (n : ℚ) := rfl

theorem QL.eval_spec : ∀ q : QL, q.eval.2 ≠ 0 → (q.toQ : ℝ) = (q.eval.1 : ℝ) / q.eval.2
  | .nat n, _ => by simp [toQ, eval]
  | .num n, _ => by simp [toQ, eval, QL.ofNat_eq]
  | .q n d, _ => by simp [toQ, eval, QL.ofNat_eq]
  | .qneg n d, _ => by simp [toQ, eval, QL.ofNat_eq, neg_div]
  | .frac n d, _ => by simp [toQ, eval]
  | .neg a, h => by
    simp only [toQ, eval] at h ⊢
    rw [Rat.cast_neg, QL.eval_spec a h]; push_cast; ring
  | .add a b, h => by
    simp only [toQ, eval] at h ⊢
    have ha : a.eval.2 ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have hb : b.eval.2 ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    rw [Rat.cast_add, QL.eval_spec a ha, QL.eval_spec b hb]
    have : (a.eval.2 : ℝ) ≠ 0 := by exact_mod_cast ha
    have : (b.eval.2 : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast; field_simp
  | .sub a b, h => by
    simp only [toQ, eval] at h ⊢
    have ha : a.eval.2 ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have hb : b.eval.2 ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    rw [Rat.cast_sub, QL.eval_spec a ha, QL.eval_spec b hb]
    have : (a.eval.2 : ℝ) ≠ 0 := by exact_mod_cast ha
    have : (b.eval.2 : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast; field_simp
  | .mul a b, h => by
    simp only [toQ, eval] at h ⊢
    have ha : a.eval.2 ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have hb : b.eval.2 ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    rw [Rat.cast_mul, QL.eval_spec a ha, QL.eval_spec b hb]
    push_cast; ring

/-- Expressions evaluated by models. `seed0/1/2 ρ m` are the literals `ρ`, `ρ ^ 2`, `1 / ρ ^ 2`
of a frozen formula with `ρ = m / 10 ^ 8`. -/
inductive IE (ι : Type) where
  | lit (q : QL)
  | var (i : ι)
  | add (a b : IE ι)
  | neg (a : IE ι)
  | mul (a b : IE ι)
  | pow (a : IE ι) (n : ℕ)
  | seed0 (ρ : ℚ) (m : ℕ)
  | seed1 (ρ : ℚ) (m : ℕ)
  | seed2 (ρ : ℚ) (m : ℕ)
  | sin (a : IE ι)
  | cos (a : IE ι)
  | sqrt (a : IE ι)
  | inv (a : IE ι)

namespace IE
variable {ι : Type}

instance : Add (IE ι) := ⟨.add⟩
instance : Neg (IE ι) := ⟨.neg⟩
instance : Sub (IE ι) := ⟨fun a b => .add a (.neg b)⟩
instance : Mul (IE ι) := ⟨.mul⟩
instance : Pow (IE ι) ℕ := ⟨.pow⟩
instance (n : ℕ) : OfNat (IE ι) n := ⟨.lit (.nat n)⟩
instance : Div (IE ι) := ⟨fun a b => .mul a (.inv b)⟩

/-- The real value. -/
def value (v : ι → ℝ) : IE ι → ℝ
  | .lit q => (q.toQ : ℝ)
  | .var i => v i
  | .add a b => value v a + value v b
  | .neg a => -value v a
  | .mul a b => value v a * value v b
  | .pow a n => value v a ^ n
  | .seed0 ρ _ => ((ρ : ℚ) : ℝ)
  | .seed1 ρ _ => ((ρ ^ 2 : ℚ) : ℝ)
  | .seed2 ρ _ => ((1 / ρ ^ 2 : ℚ) : ℝ)
  | .sin a => Real.sin (value v a)
  | .cos a => Real.cos (value v a)
  | .sqrt a => Real.sqrt (value v a)
  | .inv a => 1 / value v a

/-- Every seed is `m / 10 ^ 8`. -/
def SeedsOK : IE ι → Prop
  | .lit _ | .var _ => True
  | .add a b | .mul a b => SeedsOK a ∧ SeedsOK b
  | .neg a | .pow a _ | .sin a | .cos a | .sqrt a | .inv a => SeedsOK a
  | .seed0 ρ m | .seed1 ρ m | .seed2 ρ m => ρ = (m : ℚ) / 100000000

/-- No seed literal. -/
def seedFree : IE ι → Bool
  | .lit _ | .var _ => true
  | .add a b | .mul a b => seedFree a && seedFree b
  | .neg a | .pow a _ | .sin a | .cos a | .sqrt a | .inv a => seedFree a
  | .seed0 _ _ | .seed1 _ _ | .seed2 _ _ => false

theorem seedsOK_of_seedFree : ∀ e : IE ι, e.seedFree = true → e.SeedsOK
  | .lit _, _ | .var _, _ => trivial
  | .add a b, h | .mul a b, h => by
    simp only [seedFree, Bool.and_eq_true] at h
    exact ⟨seedsOK_of_seedFree a h.1, seedsOK_of_seedFree b h.2⟩
  | .neg a, h | .pow a _, h | .sin a, h | .cos a, h | .sqrt a, h | .inv a, h =>
    seedsOK_of_seedFree a h

section SeedsOK
variable (a b : IE ι)
@[simp] theorem seedsOK_add : (a + b).SeedsOK ↔ a.SeedsOK ∧ b.SeedsOK := Iff.rfl
@[simp] theorem seedsOK_sub : (a - b).SeedsOK ↔ a.SeedsOK ∧ b.SeedsOK := Iff.rfl
@[simp] theorem seedsOK_mul : (a * b).SeedsOK ↔ a.SeedsOK ∧ b.SeedsOK := Iff.rfl
@[simp] theorem seedsOK_div : (a / b).SeedsOK ↔ a.SeedsOK ∧ b.SeedsOK := Iff.rfl
@[simp] theorem seedsOK_neg : (-a).SeedsOK ↔ a.SeedsOK := Iff.rfl
@[simp] theorem seedsOK_pow (n : ℕ) : (a ^ n).SeedsOK ↔ a.SeedsOK := Iff.rfl
@[simp] theorem seedsOK_ofNat (n : ℕ) : (OfNat.ofNat n : IE ι).SeedsOK := trivial
@[simp] theorem seedsOK_lit (q : QL) : (IE.lit q : IE ι).SeedsOK := trivial
@[simp] theorem seedsOK_var (i : ι) : (IE.var i : IE ι).SeedsOK := trivial
end SeedsOK

/-- Sine and cosine with the range check `[0, 7/10]` on the argument. -/
def guardTrig (c : Config) (a r : Model) : Model :=
  ⟨r.U, r.V, r.e, r.ok && a.ok && decide (0 ≤ a.lowerZ c) && decide (10 * a.upperZ c ≤ 7 * 2 ^ c.K)⟩

/-- The model of an expression. -/
def eval (c : Config) (w : ι → Model) : IE ι → Model
  | .lit q => Model.lit c q.eval.1 q.eval.2
  | .var i => w i
  | .add a b => Model.add c (eval c w a) (eval c w b)
  | .neg a => Model.neg (eval c w a)
  | .mul a b => Model.mul c (eval c w a) (eval c w b)
  | .pow a n => Model.pow c (eval c w a) n
  | .seed0 _ m => Model.lit c m 100000000
  | .seed1 _ m => Model.lit c (m * m : ℕ) 10000000000000000
  | .seed2 _ m => Model.lit c 10000000000000000 (m * m)
  | .sin a => guardTrig c (eval c w a) (Model.sin c (eval c w a))
  | .cos a => guardTrig c (eval c w a) (Model.cos c (eval c w a))
  | .sqrt a => Model.sqrt c (eval c w a)
  | .inv a => Model.inv c (eval c w a)


theorem trig_range {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (ha : a.Contains c x y v) (hok : a.ok = true) (h0 : 0 ≤ a.lowerZ c)
    (h1 : 10 * a.upperZ c ≤ 7 * 2 ^ c.K) : v ∈ Set.Icc 0 frameCap := by
  obtain ⟨hl, hu⟩ := Model.bounds hc hx hy ha hok
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  constructor
  · exact le_trans (div_nonneg (by exact_mod_cast h0) h2K.le) hl
  · refine hu.trans ?_
    rw [div_le_iff₀ h2K, frameCap]
    have : (10 : ℝ) * a.upperZ c ≤ 7 * 2 ^ c.K := by exact_mod_cast h1
    linarith

theorem eval_sound {c : Config} (hc : c.Valid) {w : ι → Model} {v : ι → ℝ} {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hw : ∀ i, (w i).Contains c x y (v i)) :
    ∀ e : IE ι, e.SeedsOK → (e.eval c w).Contains c x y (e.value v)
  | .lit q, _ => by
    intro hok
    have hd : q.eval.2 ≠ 0 := by
      intro h0
      simp only [eval, Model.lit, h0] at hok
      simp [Model.ofInt] at hok
    rw [value, QL.eval_spec q hd]
    exact Model.contains_lit c _ _ hok
  | .var i, _ => hw i
  | .add a b, hs => Model.contains_add hc (eval_sound hc hx hy hw a hs.1) (eval_sound hc hx hy hw b hs.2)
  | .neg a, hs => Model.contains_neg (eval_sound hc hx hy hw a hs)
  | .mul a b, hs => Model.contains_mul hc hx hy (eval_sound hc hx hy hw a hs.1)
      (eval_sound hc hx hy hw b hs.2)
  | .pow a n, hs => Model.contains_pow hc hx hy (eval_sound hc hx hy hw a hs) n
  | .seed0 ρ m, hs => by
    simp only [SeedsOK] at hs
    simp only [eval, value, hs]
    have := Model.contains_lit c (m : ℤ) 100000000 (x := x) (y := y)
    push_cast at this ⊢; exact this
  | .seed1 ρ m, hs => by
    simp only [SeedsOK] at hs
    simp only [eval, value, hs]
    have := Model.contains_lit c ((m * m : ℕ) : ℤ) 10000000000000000 (x := x) (y := y)
    convert this using 2; push_cast; ring
  | .seed2 ρ m, hs => by
    simp only [SeedsOK] at hs
    simp only [eval, value, hs]
    have := Model.contains_lit c (10000000000000000 : ℤ) (m * m) (x := x) (y := y)
    convert this using 2; push_cast; ring
  | .sin a, hs => by
    intro hok
    simp only [eval, guardTrig, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hr, haok⟩, h0⟩, h1⟩ := hok
    have ha := eval_sound hc hx hy hw a hs
    have hv := trig_range hc hx hy ha haok h0 h1
    obtain ⟨hg, he⟩ := Model.contains_sin hc hx hy ha hv hr
    exact ⟨⟨hg.triU, hg.triV, hg.small⟩, he⟩
  | .cos a, hs => by
    intro hok
    simp only [eval, guardTrig, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hr, haok⟩, h0⟩, h1⟩ := hok
    have ha := eval_sound hc hx hy hw a hs
    have hv := trig_range hc hx hy ha haok h0 h1
    obtain ⟨hg, he⟩ := Model.contains_cos hc hx hy ha hv hr
    exact ⟨⟨hg.triU, hg.triV, hg.small⟩, he⟩
  | .sqrt a, hs => Model.contains_sqrt hc hx hy (eval_sound hc hx hy hw a hs)
  | .inv a, hs => Model.contains_inv hc hx hy (eval_sound hc hx hy hw a hs)

/-- The formula of the draft's polynomial expressions (`TensorPolynomialEnclosure`). -/
def toExpression : IE ι → TensorPolynomialEnclosure.Expression ι
  | .lit q => .literal q.toQ
  | .var i => .variable i
  | .add a b => .add a.toExpression b.toExpression
  | .neg a => .neg a.toExpression
  | .mul a b => .mul a.toExpression b.toExpression
  | .pow a n => .power a.toExpression n
  | .seed0 ρ _ => .literal ρ
  | .seed1 ρ _ => .literal (ρ ^ 2)
  | .seed2 ρ _ => .literal (1 / ρ ^ 2)
  | _ => .literal 0

/-- No sine, cosine, root or reciprocal. -/
def IsPoly : IE ι → Prop
  | .lit _ | .var _ | .seed0 _ _ | .seed1 _ _ | .seed2 _ _ => True
  | .add a b | .mul a b => IsPoly a ∧ IsPoly b
  | .neg a | .pow a _ => IsPoly a
  | _ => False

/-- `IsPoly` as a computable test. -/
def poly : IE ι → Bool
  | .lit _ | .var _ | .seed0 _ _ | .seed1 _ _ | .seed2 _ _ => true
  | .add a b | .mul a b => poly a && poly b
  | .neg a | .pow a _ => poly a
  | _ => false

theorem isPoly_of_poly : ∀ e : IE ι, e.poly = true → e.IsPoly
  | .lit _, _ | .var _, _ | .seed0 _ _, _ | .seed1 _ _, _ | .seed2 _ _, _ => trivial
  | .add a b, h | .mul a b, h => by
    simp only [poly, Bool.and_eq_true] at h
    exact ⟨isPoly_of_poly a h.1, isPoly_of_poly b h.2⟩
  | .neg a, h | .pow a _, h => isPoly_of_poly a h
  | .sin _, h | .cos _, h | .sqrt _, h | .inv _, h => by simp [poly] at h

theorem value_toExpression (v : ι → ℝ) : ∀ e : IE ι, e.IsPoly →
    (e.toExpression).value v = e.value v
  | .lit q, _ => rfl
  | .var i, _ => rfl
  | .add a b, h => by
    simp only [toExpression, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpression v a h.1, value_toExpression v b h.2]
  | .neg a, h => by
    simp only [toExpression, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpression v a h]
  | .mul a b, h => by
    simp only [toExpression, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpression v a h.1, value_toExpression v b h.2]
  | .pow a n, h => by
    simp only [toExpression, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpression v a h]
  | .seed0 _ _, _ => rfl
  | .seed1 _ _, _ => rfl
  | .seed2 _ _, _ => rfl
  | .sin _, h | .cos _, h | .sqrt _, h | .inv _, h => absurd h (by simp [IsPoly])

/-- `toExpression` with the variables replaced by formulas. -/
def toExpressionWith {κ : Type} (σ : ι → TensorPolynomialEnclosure.Expression κ) :
    IE ι → TensorPolynomialEnclosure.Expression κ
  | .lit q => .literal q.toQ
  | .var i => σ i
  | .add a b => .add (a.toExpressionWith σ) (b.toExpressionWith σ)
  | .neg a => .neg (a.toExpressionWith σ)
  | .mul a b => .mul (a.toExpressionWith σ) (b.toExpressionWith σ)
  | .pow a n => .power (a.toExpressionWith σ) n
  | .seed0 ρ _ => .literal ρ
  | .seed1 ρ _ => .literal (ρ ^ 2)
  | .seed2 ρ _ => .literal (1 / ρ ^ 2)
  | _ => .literal 0

theorem value_toExpressionWith {κ : Type} (v : κ → ℝ) (σ : ι → TensorPolynomialEnclosure.Expression κ) :
    ∀ e : IE ι, e.IsPoly →
      (e.toExpressionWith σ).value v = e.value (fun i => (σ i).value v)
  | .lit q, _ => rfl
  | .var i, _ => rfl
  | .add a b, h => by
    simp only [toExpressionWith, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpressionWith v σ a h.1, value_toExpressionWith v σ b h.2]
  | .neg a, h => by
    simp only [toExpressionWith, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpressionWith v σ a h]
  | .mul a b, h => by
    simp only [toExpressionWith, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpressionWith v σ a h.1, value_toExpressionWith v σ b h.2]
  | .pow a n, h => by
    simp only [toExpressionWith, TensorPolynomialEnclosure.Expression.value, value,
      value_toExpressionWith v σ a h]
  | .seed0 _ _, _ => rfl
  | .seed1 _ _, _ => rfl
  | .seed2 _ _, _ => rfl
  | .sin _, h | .cos _, h | .sqrt _, h | .inv _, h => absurd h (by simp [IsPoly])

/-- The septic majorant `TensorPolynomialEnclosure.Expression.H7`. -/
def H7 (a : IE ι) : IE ι :=
  1+a*(.lit (.q 1 2)+a*(.lit (.qneg 1 8)+a*(.lit (.q 1 16)+a*(.lit (.qneg 5 128)+
    a*(.lit (.q 7 256)+a*(.lit (.qneg 21 1024)+a*.lit (.q 33 2048)))))))

/-- `TensorPolynomialEnclosure.Expression.sqrtUpper` with the seed `ρ = m / 10 ^ 8`. -/
def sqrtUpper (ρ : ℚ) (m : ℕ) (a : IE ι) : IE ι := .seed0 ρ m*H7 ((a-.seed1 ρ m)*.seed2 ρ m)

theorem toExpression_sqrtUpper (w : ι → TensorPolynomialEnclosure.Enclosure) (m : ℕ) (a : IE ι) :
    (sqrtUpper (TensorPolynomialEnclosure.rootSeed
      (TensorPolynomialEnclosure.Expression.enclose w a.toExpression)) m a).toExpression=
      TensorPolynomialEnclosure.Expression.sqrtUpper w a.toExpression := rfl

theorem toExpressionWith_sqrtUpper {κ : Type} (σ : ι → TensorPolynomialEnclosure.Expression κ)
    (w : κ → TensorPolynomialEnclosure.Enclosure) (m : ℕ) (a : IE ι) :
    (sqrtUpper (TensorPolynomialEnclosure.rootSeed
      (TensorPolynomialEnclosure.Expression.enclose w (a.toExpressionWith σ))) m a).toExpressionWith σ=
      TensorPolynomialEnclosure.Expression.sqrtUpper w (a.toExpressionWith σ) := rfl

/-- The models of `sqrtUpper` do not depend on the formula `ρ` of the seed. -/
theorem eval_sqrtUpper (c : Config) (w : ι → Model) (ρ ρ' : ℚ) (m : ℕ) (a : IE ι) :
    (sqrtUpper ρ m a).eval c w=(sqrtUpper ρ' m a).eval c w := rfl

theorem seedsOK_sqrtUpper {ρ : ℚ} {m : ℕ} {a : IE ι} (hρ : ρ=(m:ℚ)/100000000) (ha : a.SeedsOK) :
    (sqrtUpper ρ m a).SeedsOK := by
  have hx : ((a-.seed1 ρ m)*.seed2 ρ m).SeedsOK := ⟨⟨ha,hρ⟩,hρ⟩
  exact ⟨hρ,trivial,hx,trivial,hx,trivial,hx,trivial,hx,trivial,hx,trivial,hx,trivial,hx,trivial⟩

/-- The formula of the draft's radical expressions (`TensorRadicalExpression`). -/
def toExpr : IE ι → TensorRadicalExpression.Expr ι
  | .lit q => .literal q.toQ
  | .var i => .variable i
  | .add a b => .add a.toExpr b.toExpr
  | .neg a => .neg a.toExpr
  | .mul a b => .mul a.toExpr b.toExpr
  | .pow a n => .power a.toExpr n
  | .seed0 ρ _ => .literal ρ
  | .seed1 ρ _ => .literal (ρ ^ 2)
  | .seed2 ρ _ => .literal (1 / ρ ^ 2)
  | .sin a => .sine a.toExpr
  | .cos a => .cosine a.toExpr
  | .sqrt a => .root a.toExpr
  | .inv a => .reciprocal a.toExpr

theorem value_toExpr (v : ι → ℝ) : ∀ e : IE ι,
    TensorRadicalExpression.Expr.value v e.toExpr = e.value v
  | .lit _ => rfl
  | .var _ => rfl
  | .add a b => by
    simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a, value_toExpr v b]
  | .neg a => by simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a]
  | .mul a b => by
    simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a, value_toExpr v b]
  | .pow a n => by simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a]
  | .seed0 _ _ => rfl
  | .seed1 _ _ => rfl
  | .seed2 _ _ => rfl
  | .sin a => by simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a]
  | .cos a => by simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a]
  | .sqrt a => by simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a]
  | .inv a => by simp only [toExpr, TensorRadicalExpression.Expr.value, value, value_toExpr v a]

end IE

/-! ## Checks -/

/-- The kernel check: the expression exceeds `num / den` on `[-1, 1]²` (by a margin
`2 ^ -K` when `strict`). -/
def check {ι : Type} (c : Config) (n : ℕ) (w : ι → Model) (e : IE ι) (num den : ℕ) (strict : Bool) :
    Bool :=
  let m := e.eval c w
  m.ok && Nat.blt 0 den &&
    bernCheck c n m (Model.cdiv (num * 2 ^ c.K) den + m.e + (if strict then 1 else 0))

theorem check_sound {ι : Type} {c : Config} (hc : c.Valid) {n : ℕ} {w : ι → Model} {e : IE ι}
    {num den : ℕ} {strict : Bool} (h : check c n w e num den strict = true) {v : ι → ℝ}
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hw : ∀ i, (w i).Contains c x y (v i))
    (hs : e.SeedsOK) :
    (num : ℝ) / den + (if strict then 1 else 0) / 2 ^ c.K ≤ e.value v := by
  simp only [check, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hok, hden⟩, hb⟩ := h
  obtain ⟨hg, he⟩ := IE.eval_sound hc hx hy hw e hs hok
  have hB := bernCheck_sound hc hg hb hx hy
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  have hceil := Model.cdiv_ge (num * 2 ^ c.K) den hden
  have hv := (abs_le.mp he).1
  simp only [Model.val] at hv
  set q := Model.cdiv (num * 2 ^ c.K) den
  set E := (e.eval c w).e
  set D := evalN c (e.eval c w).U x y - evalN c (e.eval c w).V x y
  have hstep : (num : ℝ) / den = (((num * 2 ^ c.K : ℕ) : ℝ) / den) / 2 ^ c.K := by
    push_cast; field_simp
  have h3 : (num : ℝ) / den ≤ (q : ℝ) / 2 ^ c.K := by
    rw [hstep]; exact div_le_div_of_nonneg_right hceil h2K.le
  cases strict
  · simp only [Bool.false_eq_true, ite_false, add_zero, zero_div] at hB ⊢
    push_cast at hB
    have : ((q : ℝ) + E) / 2 ^ c.K ≤ D / 2 ^ c.K := div_le_div_of_nonneg_right hB h2K.le
    rw [add_div] at this
    linarith
  · simp only [ite_true] at hB ⊢
    push_cast at hB
    have : ((q : ℝ) + E + 1) / 2 ^ c.K ≤ D / 2 ^ c.K := div_le_div_of_nonneg_right hB h2K.le
    rw [add_div, add_div] at this
    linarith

theorem check_lt {ι : Type} {c : Config} (hc : c.Valid) {n : ℕ} {w : ι → Model} {e : IE ι}
    {num den : ℕ} (h : check c n w e num den true = true) {v : ι → ℝ}
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hw : ∀ i, (w i).Contains c x y (v i))
    (hs : e.SeedsOK) : (num : ℝ) / den < e.value v := by
  have := check_sound hc h hx hy hw hs
  simp only [ite_true] at this
  have : (0 : ℝ) < 1 / 2 ^ c.K := by positivity
  linarith

theorem check_le {ι : Type} {c : Config} (hc : c.Valid) {n : ℕ} {w : ι → Model} {e : IE ι}
    {num den : ℕ} {strict : Bool} (h : check c n w e num den strict = true) {v : ι → ℝ}
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hw : ∀ i, (w i).Contains c x y (v i))
    (hs : e.SeedsOK) : (num : ℝ) / den ≤ e.value v := by
  have := check_sound hc h hx hy hw hs
  have : (0 : ℝ) ≤ (if strict then 1 else 0) / 2 ^ c.K := by split_ifs <;> positivity
  linarith

/-! ## Seeds of the draft's square-root majorant -/

/-- `nearestRoot r` is `m / 10 ^ 8` when `(m - 1/2)² ≤ 10^16 r < (m + 1/2)²`. -/
theorem nearestRoot_eq {r : ℚ} (hr : 0 ≤ r) {m : ℕ} (hm : 1 ≤ m)
    (hlo : ((m : ℚ) - 1 / 2) ^ 2 ≤ r * 10000000000000000)
    (hhi : r * 10000000000000000 < ((m : ℚ) + 1 / 2) ^ 2) :
    TensorPolynomialEnclosure.nearestRoot r = (m : ℚ) / 100000000 := by
  rw [TensorPolynomialEnclosure.nearestRoot]
  set N := r.num.natAbs * 10000000000000000 / r.den with hN
  set R := r * 10000000000000000 with hR
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnum : (r.num.natAbs : ℚ) = r.num := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hr)]
  have hrq : r = r.num / r.den := (Rat.num_div_den r).symm
  have hNle : (N : ℚ) ≤ R := by
    have h1 : (N : ℚ) * r.den ≤ (r.num.natAbs * 10000000000000000 : ℕ) := by
      exact_mod_cast Nat.div_mul_le_self _ _
    rw [hR, hrq]
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    push_cast at h1; rw [hnum] at h1; linarith
  have hNlt : R < N + 1 := by
    have h1 : ((r.num.natAbs * 10000000000000000 : ℕ) : ℚ) < r.den * (N + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ _ r.den_pos
    rw [hR, hrq, div_mul_eq_mul_div, div_lt_iff₀ hden]
    push_cast at h1; rw [hnum] at h1; linarith [mul_comm (r.den : ℚ) ((N : ℚ) + 1)]
  set n := Nat.sqrt N
  have hn1 : n * n ≤ N := Nat.sqrt_le N
  have hn2 : N < (n + 1) * (n + 1) := Nat.lt_succ_sqrt N
  have hn1' : (n : ℚ) ^ 2 ≤ R := by
    have : ((n * n : ℕ) : ℚ) ≤ N := by exact_mod_cast hn1
    push_cast at this; nlinarith
  have hn2' : R < ((n : ℚ) + 1) ^ 2 := by
    have : ((N : ℕ) : ℚ) + 1 ≤ (((n + 1) * (n + 1) : ℕ) : ℚ) := by exact_mod_cast hn2
    push_cast at this; nlinarith
  have hsq : ∀ a b : ℚ, 0 ≤ b → a ^ 2 < b ^ 2 → a < b := fun a b hb h =>
    lt_of_pow_lt_pow_left₀ 2 hb h
  have hm0 : (0 : ℚ) ≤ (m : ℚ) - 1 / 2 := by
    have : (1 : ℚ) ≤ m := by exact_mod_cast hm
    linarith
  split_ifs with hcase
  · -- result `n`
    have h1 : (m : ℚ) - 1 / 2 < n + 1 / 2 := hsq _ _ (by positivity) (lt_of_le_of_lt hlo hcase)
    have h2 : (n : ℚ) < m + 1 / 2 := hsq _ _ (by positivity) (lt_of_le_of_lt hn1' hhi)
    have : n = m := by
      have a1 : m < n + 1 := by exact_mod_cast (show (m : ℚ) < n + 1 by linarith)
      have a2 : n < m + 1 := by exact_mod_cast (show (n : ℚ) < m + 1 by linarith)
      omega
    rw [this]
  · -- result `n + 1`
    push Not at hcase
    have h1 : (n : ℚ) + 1 / 2 < m + 1 / 2 := hsq _ _ (by positivity) (lt_of_le_of_lt hcase hhi)
    have h2 : (m : ℚ) - 1 / 2 < n + 1 := hsq _ _ (by positivity) (lt_of_le_of_lt hlo hn2')
    have : n + 1 = m := by
      have a1 : n < m := by exact_mod_cast (show (n : ℚ) < m by linarith)
      have a2 : m < n + 2 := by exact_mod_cast (show (m : ℚ) < n + 2 by linarith)
      omega
    rw [← this]

/-- The seed check: the expression (evaluated at a point by constant models) has the square root
`m / 10^8` in the sense of `nearestRoot`. -/
def seedCheck {ι : Type} (c : Config) (w : ι → Model) (e : IE ι) (m : ℕ) : Bool :=
  let r := e.eval c w
  r.ok && Nat.ble 1 m &&
    decide ((2 * (m : ℤ) - 1) ^ 2 * 2 ^ c.K ≤ 4 * 10000000000000000 * r.lowerZ c) &&
    decide (4 * 10000000000000000 * r.upperZ c < (2 * (m : ℤ) + 1) ^ 2 * 2 ^ c.K)

/-- A candidate seed for `seedCheck`: the nearest root, in units of `10 ^ -8`, of the lower end
of the expression's range. -/
def seedOf {ι : Type} (c : Config) (w : ι → Model) (e : IE ι) : ℕ :=
  let N := ((e.eval c w).lowerZ c).toNat * 10000000000000000 / 2 ^ c.K
  let n := Model.isqrt N 64 0
  if N < n * n + n then n else n + 1

theorem seedCheck_sound {ι : Type} {c : Config} (hc : c.Valid) {w : ι → Model} {e : IE ι} {m : ℕ}
    (h : seedCheck c w e m = true) {v : ι → ℝ} (hw : ∀ i, (w i).Contains c 0 0 (v i))
    (hs : e.SeedsOK) {r : ℚ} (hr : (r : ℝ) = e.value v) (hr0 : 0 ≤ r) :
    TensorPolynomialEnclosure.nearestRoot r = (m : ℚ) / 100000000 := by
  simp only [seedCheck, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hm⟩, hlo⟩, hhi⟩ := h
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  obtain ⟨hl, hu⟩ := Model.bounds hc h0 h0 (IE.eval_sound hc h0 h0 hw e hs) hok
  rw [← hr] at hl hu
  have h2K : (0 : ℝ) < 2 ^ c.K := by positivity
  apply nearestRoot_eq hr0 hm
  · have hlo' : ((2 * (m : ℤ) - 1) ^ 2 * 2 ^ c.K : ℝ) ≤ 4 * 10000000000000000 * (e.eval c w).lowerZ c := by
      exact_mod_cast hlo
    have : ((e.eval c w).lowerZ c : ℝ) ≤ r * 2 ^ c.K := by rwa [div_le_iff₀ h2K] at hl
    have key : ((m : ℝ) - 1 / 2) ^ 2 ≤ r * 10000000000000000 := by
      have : ((2 * (m : ℝ) - 1) ^ 2) * 2 ^ c.K ≤ 4 * 10000000000000000 * (r * 2 ^ c.K) := by
        push_cast at hlo'; nlinarith
      nlinarith
    have key' : ((((m : ℚ) - 1 / 2) ^ 2 : ℚ) : ℝ) ≤ ((r * 10000000000000000 : ℚ) : ℝ) := by
      push_cast; exact key
    exact Rat.cast_le.mp key'
  · have hhi' : (4 * 10000000000000000 * (e.eval c w).upperZ c : ℝ) < (2 * (m : ℤ) + 1) ^ 2 * 2 ^ c.K := by
      exact_mod_cast hhi
    have : r * 2 ^ c.K ≤ ((e.eval c w).upperZ c : ℝ) := by rwa [le_div_iff₀ h2K] at hu
    have key : r * 10000000000000000 < ((m : ℝ) + 1 / 2) ^ 2 := by
      have : 4 * 10000000000000000 * (r * 2 ^ c.K) < ((2 * (m : ℝ) + 1) ^ 2) * 2 ^ c.K := by
        push_cast at hhi'; nlinarith
      nlinarith
    have key' : ((r * 10000000000000000 : ℚ) : ℝ) < ((((m : ℚ) + 1 / 2) ^ 2 : ℚ) : ℝ) := by
      push_cast; exact key
    exact Rat.cast_lt.mp key'

namespace Model
/-- `S13` and `C14` of a model, without the remainder (for points). -/
def sinPoly (c : Config) (a : Model) : Model := mul c a (horner c (mul c a a) sinCoeffs)
def cosPoly (c : Config) (a : Model) : Model := horner c (mul c a a) cosCoeffs

theorem contains_sinPoly {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) : (sinPoly c a).Contains c x y (HighOrderTaylor.S13 v) := by
  have h := contains_mul hc hx hy ha (contains_horner hc hx hy (contains_mul hc hx hy ha ha) sinCoeffs)
  rwa [sinCoeffs_val] at h

theorem contains_cosPoly {c : Config} (hc : c.Valid) {a : Model} {x y v : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (ha : a.Contains c x y v) : (cosPoly c a).Contains c x y (HighOrderTaylor.C14 v) := by
  have h := contains_horner hc hx hy (contains_mul hc hx hy ha ha) cosCoeffs
  rwa [cosCoeffs_val] at h
end Model

end SquaresInCircles.Eight.TableFree.PackedModels
