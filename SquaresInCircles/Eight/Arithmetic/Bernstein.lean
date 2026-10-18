module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Polynomial identities and continuous Bernstein certificates

The certificate stores the polynomial being proved, all exact Bernstein
coefficients, and an algebraic identity.  Checking positive numbers alone
does not construct a certificate.  In particular, source-report reserve
lists are not accepted in place of the identity.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Arithmetic

abbrev QPoly := List ℚ

def QPoly.eval : QPoly → ℝ → ℝ
  | [], _ => 0
  | a::p, x => (a : ℝ) + x * QPoly.eval p x

def bernsteinBasis (n i : ℕ) (t : ℝ) : ℝ :=
  (n.choose i : ℝ) * t^i * (1-t)^(n-i)

theorem bernsteinBasis_nonneg {n i : ℕ} {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ bernsteinBasis n i t := by
  unfold bernsteinBasis
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _)) (pow_nonneg h1 _)

/-- The binomial theorem gives the partition of unity, including t = 0,1. -/
theorem bernsteinBasis_sum (n : ℕ) (t : ℝ) :
    ∑ i ∈ Finset.range (n+1), bernsteinBasis n i t = 1 := by
  calc
    _ = (t+(1-t))^n := by
      simpa [bernsteinBasis,mul_assoc,mul_comm,mul_left_comm] using
        (add_pow t (1-t) n).symm
    _ = 1 := by simp

def bernsteinEval (n : ℕ) (b : ℕ → ℚ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (b i : ℝ) * bernsteinBasis n i t

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

theorem bernstein_positive {n : ℕ} {b : ℕ → ℚ} {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (hb : ∀ i, i ≤ n → 0 < b i) :
    0 < bernsteinEval n b t := by
  have hsum : ∃ i ∈ Finset.range (n+1), 0 < bernsteinBasis n i t := by
    by_contra hn
    push Not at hn
    have hz : ∑ i ∈ Finset.range (n+1), bernsteinBasis n i t ≤ 0 :=
      Finset.sum_nonpos (fun i hi => hn i hi)
    rw [bernsteinBasis_sum] at hz
    norm_num at hz
  obtain ⟨j,hj,hjpos⟩ := hsum
  unfold bernsteinEval
  apply Finset.sum_pos'
  · intro i hi
    have hbi : (0 : ℝ) < b i := by
      exact_mod_cast (hb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    exact mul_nonneg hbi.le (bernsteinBasis_nonneg ht)
  · refine ⟨j,hj,mul_pos ?_ hjpos⟩
    exact_mod_cast hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

structure BernsteinRow where
  interval : QInterval
  polynomial : QPoly
  degree : ℕ
  coefficients : List ℚ
  deriving Repr

def BernsteinRow.coefficient (r : BernsteinRow) (i : ℕ) : ℚ :=
  r.coefficients.getD i 0

/-- A finite certificate has an exact expansion, an explicit coefficient
count, and arithmetic comparisons.  The identity is proved by ring arithmetic
in each generated row; it is not inferred from provenance metadata. -/
structure BernsteinRow.Valid (r : BernsteinRow) (margin : ℚ) : Prop where
  interval_order : r.interval.lo < r.interval.hi
  coefficient_count : r.coefficients.length = r.degree + 1
  expansion : ∀ t : ℝ,
    r.polynomial.eval ((r.interval.lo : ℝ)+(r.interval.hi-r.interval.lo : ℚ)*t) =
      bernsteinEval r.degree r.coefficient t
  coefficient_lower : ∀ i, i ≤ r.degree → margin ≤ r.coefficient i

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

theorem BernsteinRow.Valid.positive {r : BernsteinRow} {margin : ℚ}
    (hr : r.Valid margin) (hm : 0 < margin) {x : ℝ} (hx : r.interval.Mem x) :
    0 < r.polynomial.eval x := by
  have hm' : (0 : ℝ) < margin := by exact_mod_cast hm
  exact hm'.trans_le (hr.sound hx)

/-- Singleton cells use direct evaluation; they remain in a closed cover. -/
structure PointRow where
  point : ℚ
  polynomial : QPoly
  deriving Repr

def PointRow.Valid (r : PointRow) (margin : ℚ) : Prop :=
  (margin : ℝ) ≤ r.polynomial.eval (r.point : ℝ)

theorem PointRow.sound {r : PointRow} {margin : ℚ} (hr : r.Valid margin)
    {x : ℝ} (hx : (QInterval.point r.point).Mem x) :
    (margin : ℝ) ≤ r.polynomial.eval x := by
  have he : x = (r.point : ℝ) := le_antisymm hx.2 hx.1
  rw [he]
  exact hr

/-- A semantic lower comparison attaches the certified polynomial to the
actual real expression of a row.  Downstream users must supply this comparison
from interval/Taylor/support soundness. -/
theorem positive_of_polynomial_lower {r : BernsteinRow} {margin : ℚ}
    (hr : r.Valid margin) (hm : 0 < margin) {f : ℝ → ℝ}
    (hmodel : ∀ x, r.interval.Mem x → r.polynomial.eval x ≤ f x)
    {x : ℝ} (hx : r.interval.Mem x) : 0 < f x :=
  (hr.positive hm hx).trans_le (hmodel x hx)

end SquaresInCircles.Eight.Arithmetic
