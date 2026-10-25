module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.Negative.TEntry
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Owners.TD0Span

/-!
# Eight squares: the negative-TD charge dominates the middle norm

The trigonometric charge `J z = (13/12) sin z - (2/5)(1 - cos z)` dominates the middle norm
`V TD0Span.lambda z` on `[0, 3/10]`, strictly at nonzero angle (`charge_lower`, `charge_strict`).
A comparison of positive squares reduces this to one rational polynomial on `[0, 3/10]`, a positive
combination of products of `z` and `3/10 - z` (`polynomial_positive`). The bounds on the
coordinates of T come from BT2, TD2 and the avoidance of the core (`actual_negative_cuts`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.NegativeTDSpanCharge
open Polynomial SpanNormBounds TD0Span

def J (z : ℝ) : ℝ := (13/12)*Real.sin z-(2/5)*(1-Real.cos z)

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def S7 : ℚ[X] := S5-C (1/5040)*X^7
def lowerA : ℚ[X] := C (13/12)*S7+C (3/5)*(C (1/2)*X^2-C (1/24)*X^4)
def upperA : ℚ[X] := C (13/12)*S5+C (3/10)*X^2
def numerator : ℚ[X] :=
  C (2*(1978787/1000000)*(596343/500000))*lowerA-
    C (2*(9789/2500)*(13/20))*S5-upperA^2

/-- `numerator` vanishes at `0`, and `numerator / z` has positive Bernstein coefficients of
degree nine on `[0, 3/10]`: `numerator` is a positive combination of `z` and the products
`z^(i+1) (3/10 - z)^(9-i)`, which `linarith` finds. -/
theorem polynomial_positive {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    0<aeval z numerator := by
  have h0 := hz.1.le
  have h1 : 0≤3/10-z := sub_nonneg.2 hz.2
  simp only [numerator,lowerA,upperA,S7,S5,map_sub,map_add,map_mul,map_pow,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hz.1,mul_nonneg h0 (pow_nonneg h1 9),mul_nonneg (pow_nonneg h0 2) (pow_nonneg h1 8),
    mul_nonneg (pow_nonneg h0 3) (pow_nonneg h1 7),mul_nonneg (pow_nonneg h0 4) (pow_nonneg h1 6),
    mul_nonneg (pow_nonneg h0 5) (pow_nonneg h1 5),mul_nonneg (pow_nonneg h0 6) (pow_nonneg h1 4),
    mul_nonneg (pow_nonneg h0 7) (pow_nonneg h1 3),mul_nonneg (pow_nonneg h0 8) (pow_nonneg h1 2),
    mul_nonneg (pow_nonneg h0 9) h1,pow_nonneg h0 10]

theorem lowerA_nonneg {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    0≤aeval z lowerA := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz6 := pow_le_pow_left₀ hz.1 hz.2 6
  have hp : 0≤(13/12)*(1-z^2/6+z^4/120-z^6/5040)+
      (3/5)*z*(1/2-z^2/24) := by
    have hm := mul_nonneg hz.1 (show 0≤1/2-z^2/24 by nlinarith)
    nlinarith [pow_nonneg hz.1 4]
  have he : aeval z lowerA=z*((13/12)*(1-z^2/6+z^4/120-z^6/5040)+
      (3/5)*z*(1/2-z^2/24)) := by simp [lowerA,S7,S5]; ring
  rw [he]
  exact mul_nonneg hz.1 hp

/-- At every angle `0 < z ≤ 3/10` the trigonometric charge strictly exceeds the middle norm. -/
theorem charge_strict {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    V TD0Span.lambda z<J z := by
  obtain ⟨a,ha⟩ : ∃ a : ℝ,a=(13/12)*Real.sin z+(3/5)*(1-Real.cos z) := ⟨_,rfl⟩
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,by simp only [frameCap]; linarith [hz.2]⟩
  have hsi := (transport_trig hzi).2.2.1
  have hcos1 := Real.cos_le_one z
  have ha0 : 0≤a := by rw [ha]; nlinarith
  have hlow : aeval z lowerA≤a := by
    have hs := sin_lower_seven hz.1.le
    have hc := cos_upper_four hz.1.le
    have he : aeval z lowerA=(13/12)*(z-z^3/6+z^5/120-z^7/5040)+
        (3/5)*(z^2/2-z^4/24) := by simp [lowerA,S7,S5]; ring
    rw [he,ha]
    linarith
  have hupp : a≤aeval z upperA := by
    have hs := sin_upper_five hz.1.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
    have he : aeval z upperA=(13/12)*(z-z^3/6+z^5/120)+(3/10)*z^2 := by
      simp [upperA,S5]; ring
    rw [he,ha]
    linarith
  have halow0 := lowerA_nonneg ⟨hz.1.le,hz.2⟩
  have hs5 : Real.sin z≤aeval z S5 := by
    have he : aeval z S5=z-z^3/6+z^5/120 := by simp [S5]; ring
    rw [he]
    exact sin_upper_five hz.1.le
  have hN0 := fixed_norm_bounds.1
  have hR0 : 0<R := by linarith [radius_bounds.1]
  have hcoeff : (2*(1978787/1000000)*(596343/500000):ℝ)≤
      2*R*N TD0Span.lambda 0 := by
    have hmul := mul_le_mul radius_bounds.1.le hN0.le (by norm_num) hR0.le
    simp only [TD0Span.lambda]
    linarith
  have hmain := mul_le_mul hcoeff hlow halow0 (by positivity : 0≤2*R*N TD0Span.lambda 0)
  have hsin := mul_le_mul_of_nonneg_left hs5
    (show 0≤2*qCap*TD0Span.lambda by norm_num [qCap,TD0Span.lambda])
  have hasq := pow_le_pow_left₀ ha0 hupp 2
  have hp := polynomial_positive hz
  have hpos : 0<2*R*N TD0Span.lambda 0*a-
      2*qCap*TD0Span.lambda*Real.sin z-a^2 := by
    simp only [numerator,map_sub,map_mul,map_pow,aeval_C,eq_ratCast] at hp
    push_cast at hp
    simp only [qCap,TD0Span.lambda] at hsin ⊢
    linarith
  have hzabs : |-z|≤frameCap := by rw [abs_neg,abs_of_pos hz.1]; exact hzi.2
  have hNsq := N_sq (show (0:ℝ)<TD0Span.lambda by norm_num [TD0Span.lambda]) hzabs
  have hN0sq := N_sq (show (0:ℝ)<TD0Span.lambda by norm_num [TD0Span.lambda])
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hn2 : (R*N TD0Span.lambda (-z))^2=
      qCap*(1+TD0Span.lambda^2-2*TD0Span.lambda*Real.sin z) := by
    rw [mul_pow,hR2,hNsq,Real.sin_neg]
    ring
  have hn02 : (R*N TD0Span.lambda 0)^2=qCap*(1+TD0Span.lambda^2) := by
    rw [mul_pow,hR2,hN0sq,Real.sin_zero]
    ring
  have hnonneg : 0≤R*N TD0Span.lambda (-z) := mul_nonneg hR0.le (Real.sqrt_nonneg _)
  have hgain : R*N TD0Span.lambda 0-a<R*N TD0Span.lambda (-z) := by
    by_contra! hbad
    have hsquare := pow_le_pow_left₀ hnonneg hbad 2
    have hexp : (R*N TD0Span.lambda 0-a)^2=
        (R*N TD0Span.lambda 0)^2-2*R*N TD0Span.lambda 0*a+a^2 := by ring
    linarith
  have hV : V TD0Span.lambda z=(Real.cos z-1)-
      (R*N TD0Span.lambda (-z)-R*N TD0Span.lambda 0) := by
    simp only [SpanNormBounds.V,OrdinaryAngleConcavity.V,SpanNormBounds.N]
    ring
  rw [hV,J]
  linarith

theorem charge_lower {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    V TD0Span.lambda z≤J z := by
  rcases eq_or_lt_of_le hz.1 with hz0 | hz0
  · simp [← hz0,J,SpanNormBounds.V,OrdinaryAngleConcavity.V]
  · exact (charge_strict ⟨hz0,hz.2⟩).le

/-- BT2 and TD2 give `1/10 < T.y < 83/200`, `7/12 ≤ T.a` and `z < 3/10`; T need not lie on the
boundary. -/
theorem actual_negative_cuts {q z v : ℝ} {B T D : SignedPoint}
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hTc : T.AvoidsCore) (hDc0 : D.AvoidsCore) (hq : q≤qCap)
    (hyD : D.y≤0) (hz : z∈Ioc 0 frameCap)
    (hBT : quarterFeasible B T v 2) (hTD : zeroFeasible T D (-z) 2) :
    1/10<T.y ∧ T.y<83/200 ∧ 7/12≤T.a ∧ z<3/10 := by
  obtain ⟨hy,hyu,hsum,hyD'⟩ := NegativeTEntry.negative_TD_signs
    hBs hTs hDs hBc hDc hDc0 hq hyD hz hBT hTD
  have hDu := (SignedPoint.coordinate_bounds hDs hDc0 hDc hq).2.2
  rw [abs_of_nonpos hyD] at hDu
  have hyl : 1/10<T.y := by linarith
  have haHalf := SignedPoint.primary_gt_half hTs hTc
  have hcore := hTc
  simp only [SignedPoint.AvoidsCore,SignedPoint.coreDistance,abs_of_pos hy,
    max_eq_left (by linarith : 0≤T.a-1/2),max_eq_right (by linarith : T.y-1/2≤0)] at hcore
  have ha : 7/12≤T.a := by nlinarith
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hzi
  have h1 := mul_le_mul_of_nonneg_right ha hs0
  have h2 := mul_lt_mul_of_pos_right hyu (show 0<Real.cos z by linarith)
  have hh : edgeWidth (-z)≤T.a*Real.sin (-z)+T.y*Real.cos (-z)-D.y := hTD
  rw [edgeWidth_negative_formula hzi,Real.sin_neg,Real.cos_neg] at hh
  have hmargin : (17/200)*Real.cos z+(13/12)*Real.sin z<2/5 := by linarith
  have hshort : z<3/10 := by
    by_contra! hbad
    have hm := NegativeTEntry.TD_short_harmonic_mono.monotoneOn
      (⟨by norm_num,by norm_num [frameCap]⟩ : (3/10:ℝ)∈Icc 0 frameCap) hzi hbad
    have hc3 := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
    have hs3 := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
    norm_num at hc3 hs3 hm
    linarith
  exact ⟨hyl,hyu,ha,hshort⟩

end SquaresInCircles.Eight.NegativeTDSpanCharge
