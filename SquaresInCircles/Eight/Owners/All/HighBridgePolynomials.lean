module

public import SquaresInCircles.Eight.Owners.All.HighZeroPolynomial
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: four polynomials of the outer bridge

The endpoint polynomials `lowLow` and `lowNonlow`, built from `endpointPoly`, have degree eight;
the two circle envelopes `midLow` and `midNonlow` have degree twelve. Each is positive on
`[0, 7/10]` (`lowLow_positive`, `lowNonlow_positive`, `midLow_positive`, `midNonlow_positive`),
where its Bernstein coefficients are positive.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge.DualPolynomial

open Polynomial PowerTailBounds DirectedPowerBounds

def S7 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7
def C8 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+C (1/40320)*X^8
def C10 : ℚ[X] := C8-C (1/3628800)*X^10
def capQ : ℚ := 710/113-6*(8833/10000)
def piLow : ℚ := 314159/100000
def eta : ℚ := 957/1000
def radiusUpper : ℚ := 494697/250000
def a1Upper : ℚ := 3246869/2500000
def b1Lower : ℚ := 811717/2500000
def Am (mu : ℚ) : ℚ := -103/100+(11/10)*(8898/15625)+(11/10+mu)*(1489593/1000000)
def Bm (mu : ℚ) : ℚ := -(11/10)*(195443/500000)+(11/10+mu)*(1580219/1000000)
def endpointPoly (mu lambda K g bonus : ℚ) : ℚ[X] :=
  C ((1+mu)*piLow/2-mu*(capQ-bonus)+K+g+lambda/2-mu*(9/100))-
    C (1+mu)*X+C (lambda*(1/2-a1Upper)+mu*(9/100))*C8+
    C (lambda*(1/2+b1Lower)+mu*(9/100))*S7
def normSqPoly (mu lambda : ℚ) : ℚ[X] :=
  C (Am mu^2+Bm mu^2+lambda^2)+C (2*lambda)*(C (Am mu)*C8-C (Bm mu)*S7)
def distancePoly (mu lambda K g bonus : ℚ) : ℚ[X] :=
  C ((1+mu)*piLow/2-mu*(capQ-bonus)+K+g+lambda/2-mu*(9/100)-eta)-
    C (1+mu)*X+C (lambda+mu*(9/100))*C10+C (mu*(9/100))*S7
def pLow : ℚ[X] := C (1463/200)-C (129/100)*X-C (18/25)*X^2
def pNonlow : ℚ[X] := C (3241/200)-C (2643/1000)*X-C (731/500)*X^2
def lowLow : ℚ[X] := endpointPoly (17/10) (59/25) (2113/2500) (-4029/2500) 0-
  C eta-C (1/625)
def lowNonlow : ℚ[X] := endpointPoly 5 (93/20) (-1673/10000) (-1357/1000) (93/10000)-C eta
def midLow : ℚ[X] := C 2*pLow*
    distancePoly (17/10) (59/25) (109221/10000) (-4029/2500) (93/10000)-
  C radiusUpper*(pLow^2+normSqPoly (17/10) (59/25))
def midNonlow : ℚ[X] := C 2*pNonlow*
    distancePoly 5 (93/20) (115297/5000) (-1357/1000) (43/2500)-
  C radiusUpper*(pNonlow^2+normSqPoly 5 (93/20))

@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem C8_eval (z : ℝ) : aeval z C8=Arithmetic.cos8 z := by
  simp [C8,Arithmetic.cos8]
  ring
@[simp] theorem C10_eval (z : ℝ) : aeval z C10=Arithmetic.cos10 z := by
  simp [C10,Arithmetic.cos10,Arithmetic.cos8]
  ring
@[simp] theorem pLow_eval (z : ℝ) : aeval z pLow=1463/200-(129/100)*z-(18/25)*z^2 := by
  simp [pLow]
@[simp] theorem pNonlow_eval (z : ℝ) : aeval z pNonlow=3241/200-(2643/1000)*z-(731/500)*z^2 := by
  simp [pNonlow]

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-(7/20:ℝ)|≤7/20 := by
  apply abs_le.mpr
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

/-- Each of the four polynomials has positive Bernstein coefficients of its degree on `[0, 7/10]`:
it is a positive combination of the products `z^i (7/10 - z)^(n-i)`, which `linarith` finds. -/
theorem lowLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowLow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [lowLow,endpointPoly,capQ,piLow,eta,a1Upper,b1Lower,S7,C8,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 8 0,hb 7 1,hb 6 2,hb 5 3,hb 4 4,hb 3 5,hb 2 6,hb 1 7,hb 0 8]

theorem midLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midLow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [midLow,distancePoly,normSqPoly,pLow,Am,Bm,capQ,piLow,eta,radiusUpper,C10,S7,C8,
    map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 12 0,hb 11 1,hb 10 2,hb 9 3,hb 8 4,hb 7 5,hb 6 6,hb 5 7,hb 4 8,hb 3 9,hb 2 10,
    hb 1 11,hb 0 12]

theorem lowNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowNonlow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [lowNonlow,endpointPoly,capQ,piLow,eta,a1Upper,b1Lower,S7,C8,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 8 0,hb 7 1,hb 6 2,hb 5 3,hb 4 4,hb 3 5,hb 2 6,hb 1 7,hb 0 8]

theorem midNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midNonlow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [midNonlow,distancePoly,normSqPoly,pNonlow,Am,Bm,capQ,piLow,eta,radiusUpper,C10,S7,C8,
    map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 12 0,hb 11 1,hb 10 2,hb 9 3,hb 8 4,hb 7 5,hb 6 6,hb 5 7,hb 4 8,hb 3 9,hb 2 10,
    hb 1 11,hb 0 12]

theorem pLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z pLow := by
  rw [pLow_eval]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at *
  nlinarith

theorem pNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z pNonlow := by
  rw [pNonlow_eval]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at *
  nlinarith

end SquaresInCircles.Eight.GlobalAllHigh.Bridge.DualPolynomial
