module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3Polynomial

/-!
# Eight squares: the polynomials of the saturated-prefix monotonicity

For each saturated placement, the numerator of the derivative, with the prefix circle kept, is
the polynomial `H last`, of degree `13` or `14` in the prefix total. Each is positive on the whole
prefix interval `[0, 7/10]`, where its Bernstein coefficients of degree `14` are positive
(`positive`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3.SaturatedPolynomial

open Polynomial PowerTailBounds FrameCircleArc

def a (last : Bool) : ℚ := if last then 269343/250000 else 49/50
def other (last : Bool) : ℚ := if last then 49/50 else 269343/250000
def rho (last : Bool) : ℚ := if last then 574543/500000 else 616589/500000
def U : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def tangent (last : Bool) : ℚ[X] :=
  C ((3/5)/rho last)+C ((2/5)*(other last)^2/(rho last)^3)*X
def P (last : Bool) : ℚ[X] :=
  if last then C (3083/2500)-C (833/2500)*X-C (3167/10000)*X^2
  else C (11491/10000)-C (1541/5000)*X-C (2931/10000)*X^2
def numerator (last : Bool) : ℚ[X] :=
  C (a last)*PrefixPolynomial.c*TailPolynomial.C6+
    C ((2/5)*a last)*TailPolynomial.S7-C (2/5)*PrefixPolynomial.c
def energy (last : Bool) : ℚ[X] :=
  C ((a last)^2)+PrefixPolynomial.c^2-
    C (2*a last)*PrefixPolynomial.c*TailPolynomial.S7
def denominator (last : Bool) : ℚ[X] := energy last+(P last)^2
def affinePart (last : Bool) : ℚ[X] :=
  (if last then C (-3/5)+C (2/5)*TailPolynomial.C6-PrefixPolynomial.c*U
    else C (-1/5)-C (49/50)*U)-C ((1979/1000)*(2/5))*tangent last
def H (last : Bool) : ℚ[X] := affinePart last*denominator last+
  C (2*(989/500))*numerator last*P last

/-- `H last` has positive Bernstein coefficients of degree `14` on `[0, 7/10]`: it is a positive
combination of the products `p^i (7/10 - p)^(14-i)`, which `linarith` finds. -/
theorem positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p (H last) := by
  have h0 := hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤p^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  cases last <;>
    simp only [H,affinePart,denominator,energy,numerator,P,tangent,U,a,other,rho,
      PrefixPolynomial.c,TailPolynomial.S7,TailPolynomial.C6,Bool.false_eq_true,↓reduceIte,
      map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast] <;>
    push_cast <;>
    linarith [hb 14 0,hb 13 1,hb 12 2,hb 11 3,hb 10 4,hb 9 5,hb 8 6,hb 7 7,hb 6 8,hb 5 9,
      hb 4 10,hb 3 11,hb 2 12,hb 1 13,hb 0 14]

theorem a_bounds (last : Bool) : (49/50:ℝ)≤(a last:ℝ) ∧ 0<(a last:ℝ) := by
  cases last <;> norm_num [a]

theorem rho_reserve (last : Bool) :
    (0:ℝ)<(rho last:ℝ) ∧ (rho last:ℝ)^2<(other last:ℝ)^2+9/25 := by
  cases last <;> norm_num [rho,other]

theorem envelope_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p (P last) := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  dsimp [frameCap] at hp h2
  cases last <;> norm_num [P] <;> nlinarith [hp.1,hp.2]

theorem sine_polynomial_nonnegative {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0≤aeval p TailPolynomial.S7 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  have h6 := pow_le_pow_left₀ hp.1 hp.2 6
  have h4 := pow_nonneg hp.1 4
  have hfactor : 0≤1-p^2/6+p^4/120-p^6/5040 := by
    dsimp [frameCap] at h2 h6
    nlinarith only [h2,h6,h4]
  have hm := mul_nonneg hp.1 hfactor
  rw [TailPolynomial.S7_eval]
  dsimp [Arithmetic.sin7]
  nlinarith only [hm]

theorem cosine_polynomial_lower {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p TailPolynomial.C6 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  have h6 := pow_le_pow_left₀ hp.1 hp.2 6
  have h4 := pow_nonneg hp.1 4
  rw [TailPolynomial.C6_eval]
  dsimp [frameCap] at h2 h6
  nlinarith only [h2,h6,h4]

theorem numerator_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<aeval p (numerator last) := by
  have ha := a_bounds last
  have hc := weight_pos hp
  have hfirst := mul_lt_mul_of_pos_left (cosine_polynomial_lower hp)
    (mul_pos ha.2 hc)
  have hs := mul_nonneg (show 0≤(2/5:ℝ)*(a last:ℝ) from mul_nonneg (by norm_num) ha.2.le)
    (sine_polynomial_nonnegative hp)
  have hgap : 0<(3/4)*(a last:ℝ)-2/5 := by linarith [ha.1]
  have hpositive := mul_pos hc hgap
  simp only [numerator,map_sub,map_add,map_mul,aeval_C,eq_ratCast,PrefixPolynomial.c_eval]
  push_cast
  nlinarith only [hfirst,hs,hpositive]

end SquaresInCircles.Eight.GlobalBT.CoreDE3.SaturatedPolynomial
