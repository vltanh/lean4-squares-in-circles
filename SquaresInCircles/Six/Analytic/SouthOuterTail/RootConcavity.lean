module
public import SquaresInCircles.Six.Analytic.SouthOuterTail.Root

@[expose] public section

/-!
# Concavity of the cardinal-wing tail slice

For x in [0,2/5], the west-root correction is P(sign*sin x). Its two
polynomial derivative bounds suffice: no square-root differentiation is
needed. A>=21/25 and B>=0 on the negative-angle branch, or B>=-7/20 on the
positive branch, make the entire slice concave. Both estimates use the same
whole interval, not a branch-and-bound cover.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail

def rootSign (negative : Bool) : ℝ := if negative then -1 else 1

def cardinalSlice (negative : Bool) (a b K x : ℝ) : ℝ :=
  K+a*Real.cos x+b*Real.sin x-
    CandidateWestTail.radiusBound*rootPolynomial (rootSign negative*Real.sin x)

lemma cardinal_slice_concave (negative : Bool) {a b K : ℝ}
    (ha : 21/25 ≤ a) (hb : if negative then 0 ≤ b else -(7/20) ≤ b) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (cardinalSlice negative a b K) := by
  let f' : ℝ → ℝ := fun x => -a*Real.sin x+b*Real.cos x-
    CandidateWestTail.radiusBound*rootFirst (rootSign negative*Real.sin x)*
      (rootSign negative*Real.cos x)
  let f'' : ℝ → ℝ := fun x => -a*Real.cos x-b*Real.sin x+
    CandidateWestTail.radiusBound*(rootFirst (rootSign negative*Real.sin x)*
      (rootSign negative*Real.sin x)-rootSecond (rootSign negative*Real.sin x)*Real.cos x^2)
  have hf (x : ℝ) : HasDerivAt (cardinalSlice negative a b K) (f' x) x := by
    have hr := (root_hasDeriv (rootSign negative*Real.sin x)).comp x
      ((Real.hasDerivAt_sin x).const_mul (rootSign negative))
    convert ((((Real.hasDerivAt_cos x).const_mul a).const_add K).add
      ((Real.hasDerivAt_sin x).const_mul b)).sub
      (hr.const_mul CandidateWestTail.radiusBound) using 1 <;>
      dsimp [cardinalSlice,f'] <;> ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have hP := (root_first_hasDeriv (rootSign negative*Real.sin x)).comp x
      ((Real.hasDerivAt_sin x).const_mul (rootSign negative))
    have hC := (Real.hasDerivAt_cos x).const_mul (rootSign negative)
    have hr := (hP.mul hC).const_mul CandidateWestTail.radiusBound
    convert (((Real.hasDerivAt_sin x).const_mul (-a)).add
      ((Real.hasDerivAt_cos x).const_mul b)).sub hr using 1 <;>
      cases negative <;> dsimp [f',f'',rootSign] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/5))
    (f' := f') (f'' := f'')
    (by dsimp [cardinalSlice,rootPolynomial,rootOffset]; fun_prop)
  · intro x _; exact (hf x).hasDerivWithinAt
  · intro x _; exact (hff x).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hsq := mul_nonneg (sub_nonneg.mpr h.2)
      (show 0 ≤ 2/5+x by linarith [h.1])
    have hc : 23/25 ≤ Real.cos x := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h.1
      (by linarith [h.2,Real.pi_gt_d2])
    have hs1 : Real.sin x ≤ 2/5 := (Real.sin_le h.1).trans h.2
    have ht : -(2/5) ≤ rootSign negative*Real.sin x ∧
        rootSign negative*Real.sin x ≤ 2/5 := by
      cases negative <;> dsimp [rootSign] <;> constructor <;> linarith
    have hp := root_derivative_bounds ht
    have hA := mul_nonneg (show 0 ≤ a-21/25 by linarith)
      (show 0 ≤ Real.cos x by linarith)
    have hC2 : Real.cos x^2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (Real.sin x)]
    have hQ := mul_nonneg
      (show 0 ≤ rootSecond (rootSign negative*Real.sin x)+1/4 by linarith [hp.2.2])
      (sq_nonneg (Real.cos x))
    cases negative
    · simp only [rootSign,Bool.false_eq_true,if_false,one_mul] at hp hQ hb
      have hP := mul_nonpos_of_nonpos_of_nonneg hp.2.1 hs0
      have hB := mul_nonneg (show 0 ≤ b+7/20 by linarith) hs0
      dsimp [f'',rootSign,CandidateWestTail.radiusBound]
      nlinarith only [hc,hA,hC2,hQ,hP,hB,hs1]
    · simp only [rootSign,if_true,neg_one_mul] at hp hQ hb
      have hP := mul_nonneg (show 0 ≤ rootFirst (-Real.sin x)+21/50 by linarith [hp.1]) hs0
      have hB := mul_nonneg hb hs0
      dsimp [f'',rootSign,CandidateWestTail.radiusBound]
      nlinarith only [hc,hA,hC2,hQ,hP,hB,hs1]

end SquaresInCircles.Six.Analytic.SouthOuterTail
