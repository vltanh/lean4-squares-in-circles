module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeMinimumData

/-!
# Eight squares: whole-height polynomial signs for the negative-core minimum

The degree-eight denominator difference and the two stationary numerators, of degree six, have
positive Bernstein coefficients on [1.68,1.915] (the second numerator on [1.68,1.74]). Each input
is the displayed symbolic polynomial. No target subdivision, sampled
values, or supplied coefficient table is used.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

def q : ℚ := 9789/2500
def t : ℚ[X] := Polynomial.C (q+1)-Polynomial.C 2*X
def w : ℚ[X] := Polynomial.C q-X^2
def b : ℚ[X] := Polynomial.C 2*X^2-Polynomial.C (4*q)*X+Polynomial.C (q*(q+1))
def bd : ℚ[X] := Polynomial.C 4*X-Polynomial.C (4*q)
def a : ℚ[X] := b*X^2*t-w*(bd*X*t-b*(Polynomial.C 3*t-Polynomial.C 4*X))
def d : ℚ[X] := X^5*t^3-a
def c (h : ℚ) : ℚ[X] :=
  let s := Polynomial.C (h^2)*t-1
  Polynomial.C (3*h^2*q)*X*t^2*s-Polynomial.C (h^4)*w*X^2*t^2-Polynomial.C (4*h^2)*w*X^2*t*s+
    Polynomial.C (3*q)*t^2*s^2-Polynomial.C (6*q)*X*t*s^2+Polynomial.C 8*w*X^2*s^2
def cg : ℚ[X] := c (98439/100000)
lemma d_evaluation (u : ℝ) : aeval u d=D0 u := by
  simp [d,a,b,bd,t,w,q,D0,A0,baseE,baseEd,Q0]

lemma c_evaluation (h : ℚ) (u : ℝ) : aeval u (c h)=Ch (h:ℝ) u := by
  simp [c,t,w,q,Ch,Q0]

/-- `d` has positive Bernstein coefficients of degree `8` on `[42/25, 383/200]`. -/
theorem D0_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<D0 u := by
  have h0 : 0≤u-42/25 := sub_nonneg.2 hu.1
  have h1 : 0≤383/200-u := sub_nonneg.2 hu.2
  have hb (i j : ℕ) : 0≤(u-42/25)^i*(383/200-u)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  rw [← d_evaluation]
  simp only [d,a,b,bd,t,w,q,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 8 0,hb 7 1,hb 6 2,hb 5 3,hb 4 4,hb 3 5,hb 2 6,hb 1 7,hb 0 8]

/-- `cg` has positive Bernstein coefficients of degree `6` on `[42/25, 383/200]`. -/
theorem Ch_first_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<Ch g u := by
  have h0 : 0≤u-42/25 := sub_nonneg.2 hu.1
  have h1 : 0≤383/200-u := sub_nonneg.2 hu.2
  have hb (i j : ℕ) : 0≤(u-42/25)^i*(383/200-u)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  have hc : aeval u cg=Ch g u := by
    simpa [cg,g,EdgeThreeAligned.gn] using c_evaluation (98439/100000) u
  rw [← hc]
  simp only [cg,c,t,w,q,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 6 0,hb 5 1,hb 4 2,hb 3 3,hb 2 4,hb 1 5,hb 0 6]

/-- `c (39/40)` has positive Bernstein coefficients of degree `6` on `[42/25, 87/50]`. -/
theorem Ch_second_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (87/50)) : 0<Ch (39/40) u := by
  have h0 : 0≤u-42/25 := sub_nonneg.2 hu.1
  have h1 : 0≤87/50-u := sub_nonneg.2 hu.2
  have hb (i j : ℕ) : 0≤(u-42/25)^i*(87/50-u)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  have hc := c_evaluation (39/40) u
  norm_num at hc
  rw [← hc]
  simp only [c,t,w,q,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 6 0,hb 5 1,hb 4 2,hb 3 3,hb 2 4,hb 1 5,hb 0 6]

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
