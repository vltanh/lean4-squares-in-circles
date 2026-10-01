import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# The second derivative of a square root

Where `f > 0`, with derivative `d` and second derivative `dd`, the derivative
`-r d/(2√f)` of `-r√f` has the derivative `r(d² - 2f dd)/(4f√f)`; the quotient
rule reduces to a rational identity in `√f`. A function with an explicit
nonpositive second derivative on a closed interval is concave there.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

private lemma negative_sqrt_quotient_identity {z L d dd r : ℝ}
    (hL : 0<L) (hs : L^2=z) :
    r*(d^2-2*z*dd)/(4*z*L) =
      ((-r*dd)*(2*L)-(-r*d)*(2*(d/(2*L))))/(2*L)^2 := by
  subst z
  field_simp [ne_of_gt hL]
  ring

lemma hasDerivAt_negative_sqrt {f d : ℝ → ℝ} {r x dd : ℝ}
    (hf : HasDerivAt f (d x) x) (hd : HasDerivAt d dd x) (hx : 0<f x) :
    HasDerivAt (fun y => -r*d y/(2*Real.sqrt (f y)))
      (r*((d x)^2-2*f x*dd)/(4*f x*Real.sqrt (f x))) x := by
  have hroot := hf.sqrt (ne_of_gt hx)
  have hpos : 0<Real.sqrt (f x) := Real.sqrt_pos.mpr hx
  have hden : 2*Real.sqrt (f x)≠0 := ne_of_gt (by positivity)
  have hquot := HasDerivAt.div (hd.const_mul (-r)) (hroot.const_mul 2) hden
  convert hquot using 1
  all_goals first
    | rfl
    | exact negative_sqrt_quotient_identity hpos (Real.sq_sqrt hx.le)

/-- A function with a nonpositive second derivative on a closed interval is
concave there. -/
lemma concaveOn_of_explicit_second {l u : ℝ} {f d dd : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc l u, HasDerivAt f (d x) x)
    (hd : ∀ x ∈ Set.Icc l u, HasDerivAt d (dd x) x)
    (hdd : ∀ x ∈ Set.Icc l u, dd x≤0) :
    ConcaveOn ℝ (Set.Icc l u) f :=
  concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hdd x (interior_subset hx))

end SquaresInCircles.Six.Analytic
