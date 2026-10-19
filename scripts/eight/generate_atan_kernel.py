#!/usr/bin/env python3
"""Write SquaresInCircles/Eight/Arithmetic/Arctangent.lean.

The module defines the alternating Taylor polynomials of the arctangent through the degrees
51 (`atanLower`) and 49 (`atanUpper`) and proves `atanLower x ≤ arctan x ≤ atanUpper x` for
`x ≥ 0`. This script only spells out the long polynomials and their derivatives:

    python3 -I scripts/eight/generate_atan_kernel.py
"""
from pathlib import Path

root = Path(__file__).resolve().parents[2]


def poly(n):
    """x - x^3/3 + x^5/5 - ... ± x^(2n+1)/(2n+1)"""
    s = 'x'
    for j in range(1, n + 1):
        s += (' - ' if j % 2 else ' + ') + f'x^{2*j+1}/{2*j+1}'
    return s


def deriv(n):
    """1 - x^2 + x^4 - ... ± x^(2n), the derivative of poly(n)"""
    s = '1'
    for j in range(1, n + 1):
        s += (' - ' if j % 2 else ' + ') + f'x^{2*j}'
    return s


text = '''module

public import SquaresInCircles.Common.Analysis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

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
def atanLower (x : ℝ) : ℝ := LOWER
/-- The alternating Taylor polynomial of the arctangent through degree 49. -/
def atanUpper (x : ℝ) : ℝ := UPPER

theorem atanLower_le {x : ℝ} (hx : 0≤x) : atanLower x≤Real.arctan x := by
  have hh := nonneg_of_deriv_nonneg (fun t => Real.arctan t-atanLower t)
    (by unfold atanLower; exact Real.differentiable_arctan.sub (by fun_prop))
    (by norm_num [atanLower])
    (fun x hx0 => by
      have hd : (0:ℝ)<1+x^2 := by positivity
      have hid : 1/(1+x^2)-(DERIVLOWER)=x^52/(1+x^2) := by
        field_simp [ne_of_gt hd]
        ring
      have hp : deriv (fun t => atanLower t) x = DERIVLOWER := by
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
      have hid : (DERIVUPPER)-1/(1+x^2)=x^50/(1+x^2) := by
        field_simp [ne_of_gt hd]
        ring
      have hp : deriv (fun t => atanUpper t) x = DERIVUPPER := by
        unfold atanUpper
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (by unfold atanUpper; fun_prop) (Real.differentiableAt_arctan x),
        Real.deriv_arctan,hp,hid]
      exact div_nonneg (pow_nonneg hx0 50) hd.le) hx
  linarith

end SquaresInCircles.Eight.Arithmetic
'''
text = (text.replace('DERIVLOWER', deriv(25)).replace('DERIVUPPER', deriv(24))
        .replace('LOWER', poly(25)).replace('UPPER', poly(24)))
(root / 'SquaresInCircles/Eight/Arithmetic/Arctangent.lean').write_text(text)
