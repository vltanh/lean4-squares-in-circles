module

public import SquaresInCircles.Eight.Arithmetic.Bernstein

/-!
# Eight squares: a Boolean test for Bernstein rows

`BernsteinRow.check` decides the three conditions of `BernsteinRow.Valid` (`Bernstein.lean`) by
exact rational arithmetic on coefficient lists. The expansion identity is tested
coefficientwise: the polynomial is moved to `[0, 1]` by Horner's rule (`QPoly.compLinear`), the
Bernstein form is expanded in powers of `t` (`QPoly.bernsteinSum`), and every coefficient of the
difference (`BernsteinRow.residual`) must vanish. The kernel evaluates the test, and
`BernsteinRow.valid_of_check` turns its success into `Valid`. The central-band polynomials use quadratic lower bounds and square completion
in `CentralBandPolynomials.lean`.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic

namespace QPoly

/-- Coefficientwise sum. -/
def add : QPoly → QPoly → QPoly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

/-- Multiplication by a constant. -/
def smul (c : ℚ) (p : QPoly) : QPoly := p.map (c * ·)

/-- Multiplication by `a + b X`. -/
def mulLinear (a b : ℚ) (p : QPoly) : QPoly := add (smul a p) (0 :: smul b p)

/-- The composition `p (a + b X)`, by Horner's rule. -/
def compLinear (a b : ℚ) : QPoly → QPoly
  | [] => []
  | c :: p => add [c] (mulLinear a b (compLinear a b p))

/-- `(1 - X) ^ j`. -/
def complementPower : ℕ → QPoly
  | 0 => [1]
  | j + 1 => mulLinear 1 (-1) (complementPower j)

/-- `X ^ i * (1 - X) ^ j`. -/
def powers : ℕ → ℕ → QPoly
  | 0, j => complementPower j
  | i + 1, j => 0 :: powers i j

/-- The first `m` terms `b k * C(n, k) * X ^ k * (1 - X) ^ (n - k)` of a Bernstein form. -/
def bernsteinSum (n : ℕ) (b : ℕ → ℚ) : ℕ → QPoly
  | 0 => []
  | m + 1 => add (bernsteinSum n b m) (smul (b m * n.choose m) (powers m (n - m)))

theorem eval_add (p q : QPoly) (x : ℝ) : (add p q).eval x = p.eval x + q.eval x := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q => simp only [add, eval, ih, Rat.cast_add]; ring

theorem eval_smul (c : ℚ) (p : QPoly) (x : ℝ) : (smul c p).eval x = c * p.eval x := by
  induction p with
  | nil => simp [smul, eval]
  | cons a p ih =>
    simp only [smul, List.map_cons, eval, Rat.cast_mul] at ih ⊢
    rw [ih]; ring

theorem eval_mulLinear (a b : ℚ) (p : QPoly) (x : ℝ) :
    (mulLinear a b p).eval x = (a + b * x) * p.eval x := by
  simp only [mulLinear, eval_add, eval_smul, eval, Rat.cast_zero]; ring

theorem eval_compLinear (a b : ℚ) (p : QPoly) (x : ℝ) :
    (compLinear a b p).eval x = p.eval (a + b * x) := by
  induction p with
  | nil => simp [compLinear, eval]
  | cons c p ih => simp only [compLinear, eval_add, eval_mulLinear, ih, eval]; ring

theorem eval_complementPower (j : ℕ) (x : ℝ) : (complementPower j).eval x = (1 - x) ^ j := by
  induction j with
  | zero => simp [complementPower, eval]
  | succ j ih => simp only [complementPower, eval_mulLinear, ih]; push_cast; ring

theorem eval_powers (i j : ℕ) (x : ℝ) : (powers i j).eval x = x ^ i * (1 - x) ^ j := by
  induction i with
  | zero => simp [powers, eval_complementPower]
  | succ i ih => simp only [powers, eval, ih]; push_cast; ring

theorem eval_bernsteinSum (n : ℕ) (b : ℕ → ℚ) (m : ℕ) (x : ℝ) :
    (bernsteinSum n b m).eval x = ∑ k ∈ Finset.range m, (b k : ℝ) * bernsteinBasis n k x := by
  induction m with
  | zero => simp [bernsteinSum, eval]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [bernsteinSum, eval_add, eval_smul, eval_powers, bernsteinBasis]
    push_cast; ring

theorem eval_eq_zero {p : QPoly} (h : p.all (fun c => c == 0) = true) (x : ℝ) :
    p.eval x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [eval, h.1, ih h.2]

end QPoly

/-- The coefficients of `p (lo + (hi - lo) t)` minus those of the Bernstein form of the row. -/
def BernsteinRow.residual (r : BernsteinRow) : QPoly :=
  QPoly.add (r.polynomial.compLinear r.interval.lo (r.interval.hi - r.interval.lo))
    (QPoly.smul (-1) (QPoly.bernsteinSum r.degree r.coefficient (r.degree + 1)))

/-- The three conditions of `BernsteinRow.Valid`, as a Boolean test. -/
def BernsteinRow.check (r : BernsteinRow) (margin : ℚ) : Bool :=
  decide (r.interval.lo < r.interval.hi) &&
    (List.range (r.degree + 1)).all (fun i => decide (margin ≤ r.coefficient i)) &&
    r.residual.all (fun c => c == 0)

/-- A row that passes the test is valid. -/
theorem BernsteinRow.valid_of_check {r : BernsteinRow} {margin : ℚ}
    (h : r.check margin = true) : r.Valid margin := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨horder, hmargin⟩, hres⟩ := h
  refine ⟨horder, fun t => ?_, fun i hi => ?_⟩
  · have h0 := QPoly.eval_eq_zero hres t
    rw [residual, QPoly.eval_add, QPoly.eval_smul, QPoly.eval_compLinear,
      QPoly.eval_bernsteinSum] at h0
    rw [bernsteinEval]
    push_cast at h0 ⊢
    linarith
  · have := List.all_eq_true.mp hmargin i (List.mem_range.mpr (Nat.lt_succ_of_le hi))
    simpa using this

/-- Positivity on the row interval, with the interval endpoints named. -/
theorem BernsteinRow.Valid.positive_of_eq {r : BernsteinRow} {margin : ℚ} (hr : r.Valid margin)
    (hm : 0 < margin) {lo hi : ℚ} (hI : r.interval = ⟨lo, hi⟩) {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ hi) : 0 < r.polynomial.eval x :=
  hr.positive hm (by rw [hI]; exact hx)

end SquaresInCircles.Eight.Arithmetic
