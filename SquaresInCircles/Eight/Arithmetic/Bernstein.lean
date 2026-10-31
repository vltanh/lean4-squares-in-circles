module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Eight squares: Bernstein rows

A polynomial `p` with rational coefficients (`QPoly`) is bounded below on an interval `[lo, hi]`
by its coefficients in the Bernstein basis: after the substitution `x = lo + (hi - lo) t`, write
`p` as `∑ bᵢ C(n, i) tⁱ (1 - t)ⁿ⁻ⁱ`; the basis polynomials are nonnegative on `[0, 1]` and sum
to `1` (`bernsteinBasis_sum`), so `p` is at least the least `bᵢ` there (`bernstein_lower`).

A `BernsteinRow` stores an interval, a polynomial, a degree and a list of coefficients. It is
valid with the margin `m` (`BernsteinRow.Valid`) when the interval is nondegenerate, the
coefficients are the Bernstein coefficients of the polynomial on the interval, and each of them
is at least `m`. The polynomial is then at least `m` on the interval
(`BernsteinRow.Valid.sound`), and positive there if `m > 0` (`BernsteinRow.Valid.positive`).

The quartic rows of the circle duals (`Candidate/Dual.lean`) are rows of this kind;
`BernsteinCheck.lean` decides their validity. The central-band polynomials instead use
quadratic lower bounds and square completion (`CentralBandPolynomials.lean`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Arithmetic

/-- A polynomial with rational coefficients, listed from the constant term up. -/
abbrev QPoly := List ℚ

/-- The value of a polynomial at a real point, by Horner's rule. -/
def QPoly.eval : QPoly → ℝ → ℝ
  | [], _ => 0
  | a::p, x => (a : ℝ) + x * QPoly.eval p x

/-- The Bernstein basis polynomial `C(n, i) tⁱ (1 - t)ⁿ⁻ⁱ`. -/
def bernsteinBasis (n i : ℕ) (t : ℝ) : ℝ :=
  (n.choose i : ℝ) * t^i * (1-t)^(n-i)

theorem bernsteinBasis_nonneg {n i : ℕ} {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ bernsteinBasis n i t := by
  unfold bernsteinBasis
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _)) (pow_nonneg h1 _)

/-- The Bernstein basis of degree `n` sums to `1`, by the binomial theorem. -/
theorem bernsteinBasis_sum (n : ℕ) (t : ℝ) :
    ∑ i ∈ Finset.range (n+1), bernsteinBasis n i t = 1 := by
  calc
    _ = (t+(1-t))^n := by
      simpa [bernsteinBasis,mul_assoc,mul_comm,mul_left_comm] using
        (add_pow t (1-t) n).symm
    _ = 1 := by simp

/-- The polynomial `∑ bᵢ C(n, i) tⁱ (1 - t)ⁿ⁻ⁱ` of degree `n` with the Bernstein coefficients
`b`. -/
def bernsteinEval (n : ℕ) (b : ℕ → ℚ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (b i : ℝ) * bernsteinBasis n i t

/-- On `[0, 1]` a Bernstein form is at least every lower bound of its coefficients. -/
theorem bernstein_lower {n : ℕ} {b : ℕ → ℚ} {m : ℚ} {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (hb : ∀ i, i ≤ n → m ≤ b i) :
    (m : ℝ) ≤ bernsteinEval n b t := by
  calc
    (m : ℝ) = ∑ i ∈ Finset.range (n+1), (m : ℝ)*bernsteinBasis n i t := by
      rw [← Finset.mul_sum,bernsteinBasis_sum,mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hb' : (m : ℝ) ≤ b i := by exact_mod_cast hb i hi'
      exact mul_le_mul_of_nonneg_right hb' (bernsteinBasis_nonneg ht)

/-- An interval, a polynomial, a degree and the Bernstein coefficients of the polynomial on the
interval. -/
structure BernsteinRow where
  interval : QInterval
  polynomial : QPoly
  degree : ℕ
  coefficients : List ℚ

/-- The `i`-th Bernstein coefficient of a row, `0` past the end of its list. -/
def BernsteinRow.coefficient (r : BernsteinRow) (i : ℕ) : ℚ :=
  r.coefficients.getD i 0

/-- The row is valid with the margin `m`: its interval is nondegenerate, the polynomial at
`lo + (hi - lo) t` equals the Bernstein form of the coefficients at `t` for every real `t`, and
every coefficient up to the degree is at least `m`. -/
structure BernsteinRow.Valid (r : BernsteinRow) (margin : ℚ) : Prop where
  interval_order : r.interval.lo < r.interval.hi
  expansion : ∀ t : ℝ,
    r.polynomial.eval ((r.interval.lo : ℝ)+(r.interval.hi-r.interval.lo : ℚ)*t) =
      bernsteinEval r.degree r.coefficient t
  coefficient_lower : ∀ i, i ≤ r.degree → margin ≤ r.coefficient i

/-- On the interval of a valid row its polynomial is at least the margin. -/
theorem BernsteinRow.Valid.sound {r : BernsteinRow} {margin : ℚ}
    (hr : r.Valid margin) {x : ℝ} (hx : r.interval.Mem x) :
    (margin : ℝ) ≤ r.polynomial.eval x := by
  have hd : (0 : ℝ) < (r.interval.hi-r.interval.lo : ℚ) := by
    exact_mod_cast sub_pos.mpr hr.interval_order
  let t := (x-r.interval.lo)/(r.interval.hi-r.interval.lo : ℚ)
  have ht : 0 ≤ t ∧ t ≤ 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hd.le
    · apply (div_le_one hd).mpr
      push_cast
      linarith [hx.2]
  have he : (r.interval.lo : ℝ)+(r.interval.hi-r.interval.lo : ℚ)*t = x := by
    dsimp [t]
    field_simp [ne_of_gt hd]
    ring
  have h := bernstein_lower ht hr.coefficient_lower
  rw [← hr.expansion t,he] at h
  exact h

/-- With a positive margin the polynomial of a valid row is positive on its interval. -/
theorem BernsteinRow.Valid.positive {r : BernsteinRow} {margin : ℚ}
    (hr : r.Valid margin) (hm : 0 < margin) {x : ℝ} (hx : r.interval.Mem x) :
    0 < r.polynomial.eval x := by
  have hm' : (0 : ℝ) < margin := by exact_mod_cast hm
  exact hm'.trans_le (hr.sound hx)

end SquaresInCircles.Eight.Arithmetic
