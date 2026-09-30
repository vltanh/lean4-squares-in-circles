module
public import SquaresInCircles.Six.Analytic.FixedDiagonalVertex

@[expose] public section

/-!
# Fixed-pair diagonal remainder, with its actual line coefficients

The changed negative-side slope costs at most (|w|+|s|)/100. The analytic
cap estimate has reserve (|w|+|s|)/40 and therefore retains 3(|w|+|s|)/200.
The vertex case uses FixedDiagonalVertex, not the old line's positivity.
The only zero is w=s=0, d=pi/4. The domain reduction remains an explicit input.
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

/-- The cap reserve remains positive after paying the change of pair line. -/
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

/-- No old pair-envelope theorem or computational classification is used. -/
theorem remainder_nonnegative {w s d : ℝ} (hd : DiagonalDomain w s d) :
    0≤remainder w s d := by
  rw [remainder,diagonal_value_formula hd]
  by_cases hc : 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
  · rw [if_pos hc]
    have hh := fixed_diagonal_cap_lower hd
    nlinarith [abs_nonneg w,abs_nonneg s]
  · rw [if_neg hc]
    exact (fixed_diagonal_vertex_positive hd (le_of_not_ge hc)).le

/-- Exact angle rigidity for the corrected fixed-pair remainder. -/
theorem remainder_zero {w s d : ℝ} (hd : DiagonalDomain w s d)
    (heq : remainder w s d=0) : w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  rw [remainder,diagonal_value_formula hd] at heq
  by_cases hc : 2*Six.radius*|Real.sin (diagonalDelta w s d)|≤1
  · rw [if_pos hc] at heq
    exact fixed_diagonal_cap_zero hd heq
  · rw [if_neg hc] at heq
    have hh := fixed_diagonal_vertex_positive hd (le_of_not_ge hc)
    linarith

/-- The bit-dependent pair ranges imply the required helper rectangle. -/
lemma pair_domains_diagonal_domain {no wo eo so : Bool} {n w e s d : ℝ}
    (hNW : Domain no wo n w) (hES : Domain eo so (-e) (-s))
    (hd : 1/2≤d ∧ d≤Real.pi/4) : DiagonalDomain w s d := by
  have hw := hNW.2
  have hs := hES.2
  refine ⟨?_,?_,hd⟩
  · cases wo <;> simp only [Bool.false_eq_true,if_false,if_true] at hw
    all_goals constructor <;> linarith [hw.1,hw.2]
  · cases so <;> simp only [Bool.false_eq_true,if_false,if_true] at hs
    all_goals constructor <;> linarith [hs.1,hs.2]

end SquaresInCircles.Six.Analytic.FixedPair
