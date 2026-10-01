import SquaresInCircles.Six.Analytic.FixedDiagonalVertex

/-!
# The diagonal remainder

The sum `remainder w s d` of the pair lines `line w` and `line (-s)`, the
diagonal term `diagonalValue w s d` and `2 pairBase` is nonnegative on the
domain `DiagonalDomain w s d`, and vanishes only at `w = s = 0`, `d = π/4`. In
the cap case of the support of D it is at least `(3/200)(|w| + |s|)`: the cap
bound with the steeper lines `pairLine` leaves `(|w| + |s|)/40`, and replacing
them by `line` costs at most `(|w| + |s|)/100`. In the vertex case it is
positive.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

def remainder (w s d : ℝ) : ℝ :=
  line w+line (-s)+diagonalValue w s d+2*pairBase

lemma line_loss_bound (w s : ℝ) :
    pairLine w+pairLine (-s)-(line w+line (-s))≤(|w|+|s|)/100 := by
  have hw := line_decrease w
  have hs := line_decrease (-s)
  rw [neg_neg] at hs
  have hwm : max (-w) 0≤|w| := max_le (neg_le_abs w) (abs_nonneg w)
  have hsm : max s 0≤|s| := max_le (le_abs_self s) (abs_nonneg s)
  linarith

/-- With the cap term of D for the diagonal term, the remainder is at least
`(3/200)(|w| + |s|)`. -/
theorem fixed_diagonal_cap_lower {w s d : ℝ} (hd : DiagonalDomain w s d) :
    (3/200)*(|w|+|s|)≤line w+line (-s)+diagonalCap w s d+2*pairBase := by
  have hcap := diagonal_cap_remainder_lower hd
  have hloss := line_loss_bound w s
  linarith

lemma fixed_diagonal_cap_zero {w s d : ℝ} (hd : DiagonalDomain w s d)
    (heq : line w+line (-s)+diagonalCap w s d+2*pairBase=0) :
    w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  have h := fixed_diagonal_cap_lower hd
  rw [heq] at h
  have hw : w=0 := abs_eq_zero.mp (by nlinarith [abs_nonneg w,abs_nonneg s])
  have hs : s=0 := abs_eq_zero.mp (by nlinarith [abs_nonneg w,abs_nonneg s])
  subst w
  subst s
  have hold : pairLine 0+pairLine (-0)+diagonalCap 0 0 d+2*pairBase=0 := by
    simpa [line,pairLine] using heq
  exact diagonal_cap_zero_iff hd hold

/-- The diagonal remainder is nonnegative, in the cap and in the vertex case. -/
theorem remainder_nonnegative {w s d : ℝ} (hd : DiagonalDomain w s d) :
    0≤remainder w s d := by
  rw [remainder,diagonal_value_formula hd]
  by_cases hc : 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
  · rw [ite_eq_left hc]
    have hh := fixed_diagonal_cap_lower hd
    nlinarith [abs_nonneg w,abs_nonneg s]
  · rw [ite_eq_right hc]
    exact (fixed_diagonal_vertex_positive hd (le_of_not_ge hc)).le

/-- The diagonal remainder vanishes only at the angles of the model. -/
theorem remainder_zero {w s d : ℝ} (hd : DiagonalDomain w s d)
    (heq : remainder w s d=0) : w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  rw [remainder,diagonal_value_formula hd] at heq
  by_cases hc : 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
  · rw [ite_eq_left hc] at heq
    exact fixed_diagonal_cap_zero hd heq
  · rw [ite_eq_right hc] at heq
    have hh := fixed_diagonal_vertex_positive hd (le_of_not_ge hc)
    linarith

/-- The angle domains of the pairs N, W and E, S give the domain of the diagonal
remainder. -/
lemma pair_domains_diagonal_domain {no wo eo so : Bool} {n w e s d : ℝ}
    (hNW : Domain no wo n w) (hES : Domain eo so (-e) (-s))
    (hd : 1/2≤d ∧ d≤Real.pi/4) : DiagonalDomain w s d := by
  have hw := hNW.2
  have hs := hES.2
  refine ⟨?_,?_,hd⟩
  · cases wo <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hw
    all_goals constructor <;> linarith [hw.1,hw.2]
  · cases so <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hs
    all_goals constructor <;> linarith [hs.1,hs.2]

end SquaresInCircles.Six.Analytic.FixedPair
