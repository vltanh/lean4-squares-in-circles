module

public import SquaresInCircles.Common.Analysis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Eight squares: short arctangent estimates

The cubic lower bound and the tangent addition formula suffice for the two
core-square estimates. Subtracting an angle from `π/4` reduces the arguments
`3/4` and `6/7` to `1/7` and `1/13`; no long Taylor expansions are needed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic

/-- The cubic lower bound follows from the nonnegative derivative
`x⁴/(1+x²)` of the difference. -/
lemma arctan_lower_cubic {x : ℝ} (hx : 0 ≤ x) : x-x^3/3 ≤ Real.arctan x := by
  have hd (t : ℝ) : HasDerivAt (fun z => Real.arctan z-z+z^3/3)
      (1/(1+t^2)-1+t^2) t := by
    convert ((Real.hasDerivAt_arctan t).sub (hasDerivAt_id' t)).add
      (((hasDerivAt_id' t).pow 3).div_const 3) using 1
    simp
  have h := nonneg_of_deriv_nonneg (fun t => Real.arctan t-t+t^3/3)
    (fun t => (hd t).differentiableAt) (by simp) (fun t _ => by
      rw [(hd t).deriv]
      have he : 1/(1+t^2)-1+t^2 = t^4/(1+t^2) := by
        field_simp
        ring
      rw [he]
      positivity) hx
  linarith

/-- The tangent addition formula reduces angles near `π/4` to a small argument. -/
lemma arctan_complement {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x+Real.arctan ((1-x)/(1+x))=Real.pi/4 := by
  have hd : 0 < 1+x := by linarith
  have hp : x*((1-x)/(1+x)) < 1 := by
    rw [← mul_div_assoc,div_lt_iff₀ hd]
    nlinarith [sq_nonneg x]
  rw [Real.arctan_add hp]
  have he : (x+(1-x)/(1+x))/(1-x*((1-x)/(1+x)))=1 := by
    apply (div_eq_one_iff_eq (sub_pos.mpr hp).ne').mpr
    field_simp
    ring
  rw [he,Real.arctan_one]

end SquaresInCircles.Eight.Arithmetic
