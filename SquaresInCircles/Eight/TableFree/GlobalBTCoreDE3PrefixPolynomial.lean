module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Polynomial

/-!
# Exact polynomials for saturated-prefix monotonicity

The two retained-circle derivative numerators use one rational
certificate each, on the entire prefix interval.  These are the
explicit HB/HW expressions, not sampled derivative evaluations.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3.SaturatedPolynomial

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
def centered (last : Bool) : ℚ[X] := shift (7/20) (H last)
def degree (last : Bool) : ℕ := if last then 14 else 13

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_identity (last : Bool) : centered last=C ((centered last).coeff 0)+
    tail (centered last) 1 (degree last) := by cases last <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_reserve (last : Bool) :
    0<(centered last).coeff 0-norm (centered last) 1 (degree last) (7/20) := by
  cases last <;> decide

theorem positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p (H last) := by
  have hl := DirectedPowerBounds.constant_lower (centered_identity last)
    (TailPolynomial.centered_domain hp)
  have hpos : 0<((centered last).coeff 0:ℝ)-
      (norm (centered last) 1 (degree last) (7/20):ℝ) := by
    exact_mod_cast centered_reserve last
  have he : aeval (p-7/20) (centered last)=aeval p (H last) := by
    simp [centered,shift_eval]
  rw [he] at hl
  linarith

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
  have hs := mul_nonneg (show 0≤(2/5:ℝ)*(a last:ℝ) by positivity)
    (sine_polynomial_nonnegative hp)
  have hgap : 0<(3/4)*(a last:ℝ)-2/5 := by linarith [ha.1]
  have hpositive := mul_pos hc hgap
  simp only [numerator,map_sub,map_add,map_mul,aeval_C,PrefixPolynomial.c_eval]
  push_cast
  nlinarith only [hfirst,hs,hpositive]

theorem tangent_nonnegative (last : Bool) {p : ℝ} (hp : 0≤p) :
    0≤aeval p (tangent last) := by
  cases last <;> norm_num [tangent,rho,other] <;> linarith

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3.SaturatedPolynomial
