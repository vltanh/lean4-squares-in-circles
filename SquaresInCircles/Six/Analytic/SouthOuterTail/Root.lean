module
public import SquaresInCircles.Six.Analytic.CandidateWestTail.Support

@[expose] public section

/-!
# One polynomial majorant for the final west resultant

The west resultant has squared length 13/25-(12/25)t, where |t|<=2/5.
Expand at a=18/25 and put e=1/625-(12/25)t. The cubic square-root majorant
P=a+e/(2a)-e^2/(8a^3)+e^3/(16a^5) is valid throughout this interval, including
negative e. Its squared error is an explicit nonnegative polynomial and P>=1/2.
The bounds -21/50<=P'<=0 and P''>=-1/4 follow from |e|<=1/5. This is a
single whole-interval argument, not a numerical partition or root oracle.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail

def rootBase : ℝ := 18/25
def rootRate : ℝ := 12/25
def rootOffset (t : ℝ) : ℝ := 1/625-rootRate*t

def rootPolynomial (t : ℝ) : ℝ :=
  rootBase+rootOffset t/(2*rootBase)-(rootOffset t)^2/(8*rootBase^3)+
    (rootOffset t)^3/(16*rootBase^5)

def rootFirst (t : ℝ) : ℝ :=
  -rootRate/(2*rootBase)+rootRate*rootOffset t/(4*rootBase^3)-
    3*rootRate*(rootOffset t)^2/(16*rootBase^5)

def rootSecond (t : ℝ) : ℝ :=
  -rootRate^2/(4*rootBase^3)+6*rootRate^2*rootOffset t/(16*rootBase^5)

lemma root_offset_bounds {t : ℝ} (ht : -(2/5) ≤ t ∧ t ≤ 2/5) :
    -(1/5) ≤ rootOffset t ∧ rootOffset t ≤ 1/5 := by
  dsimp [rootOffset,rootRate]
  constructor <;> linarith [ht.1,ht.2]

lemma root_polynomial_lower {t : ℝ} (ht : -(2/5) ≤ t ∧ t ≤ 2/5) :
    1/2 ≤ rootPolynomial t := by
  have he := root_offset_bounds ht
  have hsq := mul_nonneg (show 0 ≤ 1/5-rootOffset t by linarith [he.2])
    (show 0 ≤ 1/5+rootOffset t by linarith [he.1])
  have hquad : 0 ≤ (rootOffset t)^2-(1/5)*rootOffset t+1/25 := by
    nlinarith [sq_nonneg (rootOffset t-1/10)]
  have hcube := mul_nonneg (show 0 ≤ rootOffset t+1/5 by linarith [he.1]) hquad
  dsimp [rootPolynomial,rootBase]
  nlinarith only [he.1,hsq,hcube]

lemma root_square_error (t : ℝ) :
    (rootPolynomial t)^2-(13/25-rootRate*t)=
      (rootOffset t)^4*((rootOffset t-2*rootBase^2)^2+16*rootBase^4)/(256*rootBase^10) := by
  dsimp [rootPolynomial,rootOffset,rootBase,rootRate]
  ring

/-- The upper bound is proved by its squared error, not assumed from a Taylor series. -/
theorem root_upper {t : ℝ} (ht : -(2/5) ≤ t ∧ t ≤ 2/5) :
    Real.sqrt (13/25-rootRate*t) ≤ rootPolynomial t := by
  have hr : 0 ≤ 13/25-rootRate*t := by dsimp [rootRate]; linarith [ht.2]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (13/25-rootRate*t)
  have hP := root_polynomial_lower ht
  have he := root_square_error t
  have hp : 0 ≤ (rootOffset t)^4*((rootOffset t-2*rootBase^2)^2+16*rootBase^4)/
      (256*rootBase^10) := by dsimp [rootBase]; positivity
  nlinarith only [hs,hn,hP,he,hp]

lemma root_hasDeriv (t : ℝ) : HasDerivAt rootPolynomial (rootFirst t) t := by
  have he : HasDerivAt rootOffset (-rootRate) t := by
    convert ((hasDerivAt_id t).const_mul (-rootRate)).const_add (1/625) using 1 <;>
      dsimp [rootOffset] <;> ring
  convert (((he.div_const (2*rootBase)).const_add rootBase).sub
    ((he.pow 2).div_const (8*rootBase^3))).add
    ((he.pow 3).div_const (16*rootBase^5)) using 1 <;>
    dsimp [rootPolynomial,rootFirst,rootBase,rootRate] <;> ring

lemma root_first_hasDeriv (t : ℝ) : HasDerivAt rootFirst (rootSecond t) t := by
  have he : HasDerivAt rootOffset (-rootRate) t := by
    convert ((hasDerivAt_id t).const_mul (-rootRate)).const_add (1/625) using 1 <;>
      dsimp [rootOffset] <;> ring
  convert (((he.const_mul rootRate).div_const (4*rootBase^3)).const_add
    (-rootRate/(2*rootBase))).sub
    (((he.pow 2).const_mul (3*rootRate)).div_const (16*rootBase^5)) using 1 <;>
    dsimp [rootFirst,rootSecond,rootBase,rootRate] <;> ring

lemma root_derivative_bounds {t : ℝ} (ht : -(2/5) ≤ t ∧ t ≤ 2/5) :
    -(21/50) ≤ rootFirst t ∧ rootFirst t ≤ 0 ∧ -(1/4) ≤ rootSecond t := by
  have he := root_offset_bounds ht
  have hsq := mul_nonneg (show 0 ≤ 1/5-rootOffset t by linarith [he.2])
    (show 0 ≤ 1/5+rootOffset t by linarith [he.1])
  have hn := sq_nonneg (rootOffset t)
  dsimp [rootFirst,rootSecond,rootBase,rootRate]
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [he.1,he.2,hsq,hn]

lemma root_antitone : AntitoneOn rootPolynomial (Set.Icc (-(2/5)) (2/5)) := by
  have hm : MonotoneOn (fun t => -rootPolynomial t) (Set.Icc (-(2/5)) (2/5)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [rootPolynomial,rootOffset]; fun_prop)
      (fun t _ => (root_hasDeriv t).neg)
    intro t ht
    exact neg_nonneg.mpr (root_derivative_bounds ⟨ht.1.le,ht.2.le⟩).2.1
  intro x hx y hy hxy
  have h := hm hx hy hxy
  linarith

end SquaresInCircles.Six.Analytic.SouthOuterTail
