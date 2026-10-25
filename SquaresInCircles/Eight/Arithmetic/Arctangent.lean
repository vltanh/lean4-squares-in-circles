module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: polynomial bounds for the arctangent

For `x ≥ 0` the alternating Taylor polynomials of the arctangent through the degrees 51 and 49
bound it from below and from above: `atanLower x ≤ arctan x ≤ atanUpper x`. Both differences
vanish at `0` and have nonnegative derivative, since `1 / (1 + x²)` exceeds the derivative of
`atanLower` by `x⁵² / (1 + x²)` and falls short of the derivative of `atanUpper` by
`x⁵⁰ / (1 + x²)`. `CorePairGeometry.lean` evaluates them at `6/7` and `3/4`.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic

/-- The alternating Taylor polynomial of the arctangent through degree 51. -/
def atanLower (x : ℝ) : ℝ := x - x^3/3 + x^5/5 - x^7/7 + x^9/9 - x^11/11 + x^13/13 - x^15/15 + x^17/17 - x^19/19 + x^21/21 - x^23/23 + x^25/25 - x^27/27 + x^29/29 - x^31/31 + x^33/33 - x^35/35 + x^37/37 - x^39/39 + x^41/41 - x^43/43 + x^45/45 - x^47/47 + x^49/49 - x^51/51
/-- The alternating Taylor polynomial of the arctangent through degree 49. -/
def atanUpper (x : ℝ) : ℝ := x - x^3/3 + x^5/5 - x^7/7 + x^9/9 - x^11/11 + x^13/13 - x^15/15 + x^17/17 - x^19/19 + x^21/21 - x^23/23 + x^25/25 - x^27/27 + x^29/29 - x^31/31 + x^33/33 - x^35/35 + x^37/37 - x^39/39 + x^41/41 - x^43/43 + x^45/45 - x^47/47 + x^49/49

theorem atanLower_le {x : ℝ} (hx : 0≤x) : atanLower x≤Real.arctan x := by
  have hh := nonneg_of_deriv_nonneg (fun t => Real.arctan t-atanLower t)
    (by unfold atanLower; exact Real.differentiable_arctan.sub (by fun_prop))
    (by norm_num [atanLower])
    (fun x hx0 => by
      have hd : (0:ℝ)<1+x^2 := by positivity
      have hid : 1/(1+x^2)-(1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48 - x^50)=x^52/(1+x^2) := by
        field_simp [ne_of_gt hd]
        ring
      have hp : deriv (fun t => atanLower t) x = 1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48 - x^50 := by
        unfold atanLower
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (Real.differentiableAt_arctan x) (by unfold atanLower; fun_prop),
        Real.deriv_arctan,hp,hid]
      exact div_nonneg (pow_nonneg hx0 52) hd.le) hx
  linarith

theorem arctan_le_atanUpper {x : ℝ} (hx : 0≤x) : Real.arctan x≤atanUpper x := by
  have hh := nonneg_of_deriv_nonneg (fun t => atanUpper t-Real.arctan t)
    (by unfold atanUpper; exact Differentiable.sub (by fun_prop) Real.differentiable_arctan)
    (by norm_num [atanUpper])
    (fun x hx0 => by
      have hd : (0:ℝ)<1+x^2 := by positivity
      have hid : (1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48)-1/(1+x^2)=x^50/(1+x^2) := by
        field_simp [ne_of_gt hd]
        ring
      have hp : deriv (fun t => atanUpper t) x = 1 - x^2 + x^4 - x^6 + x^8 - x^10 + x^12 - x^14 + x^16 - x^18 + x^20 - x^22 + x^24 - x^26 + x^28 - x^30 + x^32 - x^34 + x^36 - x^38 + x^40 - x^42 + x^44 - x^46 + x^48 := by
        unfold atanUpper
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (by unfold atanUpper; fun_prop) (Real.differentiableAt_arctan x),
        Real.deriv_arctan,hp,hid]
      exact div_nonneg (pow_nonneg hx0 50) hd.le) hx
  linarith

end SquaresInCircles.Eight.Arithmetic
