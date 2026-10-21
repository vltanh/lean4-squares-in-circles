module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# One whole-angle polynomial for the early positive mixed contact

This is the rational lower polynomial for the quadratic reference
envelope in HAND_WRONG_0011011_MIXED_COMPONENTS_WITHOUT_TABLES, §6.1.
The coefficient cages used in its construction are
C ≥ -.204013, A ≥ -.638364, B ≥ 1.347384,
D ≤ -.159078, E ≥ -.153197.

The exact endpoint quotient is positive on the complete interval
[.87,1.3]. Thus the polynomial is bounded below by its right endpoint.
This module proves the polynomial statement only. The fixed-radical
coefficient cages, trigonometric transfer, and original B-coordinate
reduction are separate obligations and are not assumed by an actual
geometric theorem here.

Uncompiled source draft. All coefficient calculations are exact
rational identities and kernel arithmetic; no sampled angle data.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveEarlyPolynomial
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

/-- Explicit synthetic division at the right endpoint. Its coefficient
formula is determined by lowerPoly, rather than supplied as data. -/
def endpointQuotient : ℚ[X] :=
  -∑ n∈Finset.range 14,C (lowerPoly.coeff (n+1))*
    ∑ i∈Finset.range (n+1),C ((13/10:ℚ)^(n-i))*X^i

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem factor_identity :
    (C (13/10)-X)*endpointQuotient=
      lowerPoly-C (lowerPoly.eval (13/10)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem expansion_identity :
    centered (87/100) (13/10) endpointQuotient=
      expansion 13 (centered (87/100) (13/10) endpointQuotient) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserve :
    (1/25:ℚ)<lowerOn 13 (87/100) (13/10) endpointQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem endpoint_reserve :
    (99/100000:ℚ)<lowerPoly.eval (13/10) := by decide

theorem quotient_positive {x : ℝ} (hx : x∈Set.Icc (87/100:ℝ) (13/10)) :
    (1/25:ℝ)<aeval x endpointQuotient :=
  positive_on_interval (by norm_num) expansion_identity coefficient_reserve hx

/-- The complete early angle interval has a strict polynomial reserve
above .00099. No derivative premise or angle subdivision is used. -/
theorem lower {x : ℝ} (hx : x∈Set.Icc (87/100:ℝ) (13/10)) :
    (99/100000:ℝ)<aeval x lowerPoly := by
  have hq := quotient_positive hx
  have hp := mul_nonneg (show 0≤(13/10:ℝ)-x by linarith [hx.2])
    (show 0≤aeval x endpointQuotient by linarith)
  have he := congrArg (fun p : ℚ[X] => aeval x p) factor_identity
  simp only [map_mul,map_sub,aeval_C,aeval_X] at he
  have hend : (99/100000:ℝ)<(lowerPoly.eval (13/10):ℝ) := by
    exact_mod_cast endpoint_reserve
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveEarlyPolynomial

