module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial

/-!
# Eight squares: one whole-angle polynomial for the early positive mixed contact

`lowerPoly` is a rational lower polynomial for the quadratic reference envelope of the early
positive mixed contact, built from Taylor polynomials of sine and cosine and the coefficient
cages `C ≥ -.204013`, `A ≥ -.638364`, `B ≥ 1.347384`, `D ≤ -.159078`, `E ≥ -.153197`.

On the whole interval `[.87,1.3]` the polynomial exceeds `.00099` (`lower`): its Bernstein
coefficients there are positive, the smallest being its value at the right endpoint.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SecondWord.PositiveEarlyPolynomial
open Polynomial WholeIntervalPolynomial

def S13 : ℚ[X] :=
  X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+
    C (1/362880)*X^9-C (1/39916800)*X^11+C (1/6227020800)*X^13

def C12 : ℚ[X] :=
  1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+
    C (1/40320)*X^8-C (1/3628800)*X^10+C (1/479001600)*X^12

def C14 : ℚ[X] := C12-C (1/87178291200)*X^14

/-- The rational Taylor lower expression, with the required .89765
already subtracted. -/
def lowerPoly : ℚ[X] :=
  X-C (204013/1000000)-C (638364/1000000)*S13+
    C (1347384/1000000)*C14-
    C (159078/1000000)*(C12.comp (C 2*X))-
    C (153197/1000000)*(S13.comp (C 2*X))-C (17953/20000)

/-- The early angle interval has a strict polynomial reserve above `.00099`: on `[.87, 1.3]` the
polynomial `lowerPoly - 99/100000` has positive Bernstein coefficients of degree `14` (the last is
its value at the right endpoint), a positive combination that `linarith` finds. -/
theorem lower {x : ℝ} (hx : x∈Set.Icc (87/100:ℝ) (13/10)) :
    (99/100000:ℝ)<aeval x lowerPoly := by
  have h0 : 0≤x-87/100 := sub_nonneg.2 hx.1
  have h1 : 0≤13/10-x := sub_nonneg.2 hx.2
  have hb (i j : ℕ) : 0≤(x-87/100)^i*(13/10-x)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [lowerPoly,S13,C14,C12,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    aeval_comp,eq_ratCast]
  push_cast
  linarith [hb 14 0,hb 13 1,hb 12 2,hb 11 3,hb 10 4,hb 9 5,hb 8 6,hb 7 7,hb 6 8,hb 5 9,hb 4 10,
    hb 3 11,hb 2 12,hb 1 13,hb 0 14]

end SquaresInCircles.Eight.SecondWord.PositiveEarlyPolynomial

