module

public import SquaresInCircles.Eight.TableFree.TD0Span
public import SquaresInCircles.Eight.TableFree.PowerTailBounds
public import SquaresInCircles.Eight.TableFree.NegativeTEntry

/-!
# The actual negative-TD charge dominates the middle norm

Uncompiled source. A positive-square comparison replaces the third-
derivative calculation by one factored rational polynomial on [0,.3].
Its exact coefficient identities and positive reserves are specified for
kernel reduction, which has not been executed. The original T coordinate
bounds are derived from BT2, TD2 and true-core avoidance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.NegativeTDSpanCharge
open Polynomial SpanNormBounds TD0Span

def J (z : ℝ) : ℝ := (13/12)*Real.sin z-(2/5)*(1-Real.cos z)

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def S7 : ℚ[X] := S5-C (1/5040)*X^7
def lowerA : ℚ[X] := C (13/12)*S7+C (3/5)*(C (1/2)*X^2-C (1/24)*X^4)
def upperA : ℚ[X] := C (13/12)*S5+C (3/10)*X^2
def numerator : ℚ[X] :=
  C (2*(1978787/1000000)*(596343/500000))*lowerA-
    C (2*(9789/2500)*(13/20))*S5-upperA^2
def quotient : ℚ[X] := ∑ i : Fin 10,C (numerator.coeff (i.val+1))*X^i.val

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem polynomial_identities :
    X*quotient=numerator ∧
      quotient=C (quotient.coeff 0)+C (quotient.coeff 1)*X+
        PowerTailBounds.tail quotient 2 8 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserves :
    (1/50:ℚ)<quotient.coeff 0 ∧
      0<quotient.coeff 1-PowerTailBounds.norm quotient 2 8 (3/10) := by decide

theorem polynomial_positive {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    0<aeval z numerator := by
  have hlo := PowerTailBounds.linear_lower polynomial_identities.2
    (show (0:ℚ)≤3/10 by norm_num)
    (show |z|≤(3/10:ℝ) by rw [abs_of_pos hz.1]; exact hz.2)
  rw [abs_of_pos hz.1] at hlo
  have hzero : (1/50:ℝ)<(quotient.coeff 0:ℝ) := by exact_mod_cast coefficient_reserves.1
  have hlinear : 0<(quotient.coeff 1:ℝ)-(PowerTailBounds.norm quotient 2 8 (3/10):ℝ) := by
    exact_mod_cast coefficient_reserves.2
  have hq : 0<aeval z quotient := by nlinarith
  have he := congrArg (fun p : ℚ[X] => aeval z p) polynomial_identities.1
  simp only [map_mul,aeval_X] at he
  rw [← he]
  exact mul_pos hz.1 hq

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

/-- A strictly positive original trigonometric charge at every nonzero
angle in the single complete short interval. -/
theorem charge_strict {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) :
    V TD0Span.lambda z<J z := by
  let a : ℝ := (13/12)*Real.sin z+(3/5)*(1-Real.cos z)
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,by norm_num [frameCap] at *; linarith [hz.2]⟩
  have hsi := (transport_trig hzi).2.2.1
  have hcos1 := Real.cos_le_one z
  have ha0 : 0≤a := by dsimp [a]; positivity
  have hlow : aeval z lowerA≤a := by
    have hs := sin_lower_seven hz.1.le
    have hc := cos_upper_four hz.1.le
    simp [lowerA,S7,S5]
    dsimp [a]
    nlinarith
  have hupp : a≤aeval z upperA := by
    have hs := sin_upper_five hz.1.le
    have hc := Real.one_sub_sq_div_two_le_cos z
    simp [upperA,S5]
    dsimp [a]
    nlinarith
  have halow0 := lowerA_nonneg ⟨hz.1.le,hz.2⟩
  have hs5 : Real.sin z≤aeval z S5 := by
    simpa [S5] using sin_upper_five hz.1.le
  have hN0 := fixed_norm_bounds.1
  have hR0 : 0<R := by linarith [radius_bounds.1]
  have hN00 : 0<N TD0Span.lambda 0 := by dsimp [TD0Span.lambda]; linarith
  have hcoeff : (2*(1978787/1000000)*(596343/500000):ℝ)≤
      2*R*N TD0Span.lambda 0 := by
    have hmul := mul_le_mul radius_bounds.1.le hN0.le (by norm_num) hR0.le
    dsimp [TD0Span.lambda]
    nlinarith
  have hmain := mul_le_mul hcoeff hlow halow0 (by positivity : 0≤2*R*N TD0Span.lambda 0)
  have hsin := mul_le_mul_of_nonneg_left hs5
    (show 0≤2*qCap*TD0Span.lambda by norm_num [qCap,TD0Span.lambda])
  have hasq := pow_le_pow_left₀ ha0 hupp 2
  have hp := polynomial_positive hz
  have hpos : 0<2*R*N TD0Span.lambda 0*a-
      2*qCap*TD0Span.lambda*Real.sin z-a^2 := by
    simp only [numerator,map_sub,map_mul,map_pow,aeval_C] at hp
    norm_num at hp
    dsimp [qCap,TD0Span.lambda] at hsin ⊢
    nlinarith
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
    nlinarith
  dsimp [J,SpanNormBounds.V,OrdinaryAngleConcavity.V,SpanNormBounds.N,a] at *
  nlinarith

theorem charge_lower {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    V TD0Span.lambda z≤J z := by
  rcases eq_or_lt_of_le hz.1 with hz0 | hz0
  · simp [← hz0,J,SpanNormBounds.V,OrdinaryAngleConcavity.V]
  · exact (charge_strict ⟨hz0,hz.2⟩).le

/-- The short interval and true-core primary bound follow from actual
BT2/TD2. The point need not lie on a radial boundary. -/
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
    max_eq_left (by linarith : 0≤T.a-1/2),max_eq_right (by linarith : T.y-1/2≤0),
    zero_pow,add_zero] at hcore
  have ha : 7/12≤T.a := by nlinarith
  have hzi : z∈Icc 0 frameCap := ⟨hz.1.le,hz.2⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hzi
  have h1 := mul_le_mul_of_nonneg_right ha hs0
  have h2 := mul_lt_mul_of_pos_right hyu (show 0<Real.cos z by linarith)
  have hh := hTD
  rw [zeroFeasible,edgeWidth_negative_formula hzi] at hh
  simp only [zeroProjection,Matrix.cons_val_two,Real.sin_neg,Real.cos_neg] at hh
  have hmargin : (17/200)*Real.cos z+(13/12)*Real.sin z<2/5 := by nlinarith
  have hshort : z<3/10 := by
    by_contra! hbad
    have hm := NegativeTEntry.TD_short_harmonic_mono.monotoneOn
      (by norm_num [frameCap]) hzi hbad
    have hc3 := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
    have hs3 := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
    norm_num at hc3 hs3
    linarith
  exact ⟨hyl,hyu,ha,hshort⟩

end SquaresInCircles.Eight.TableFree.NegativeTDSpanCharge
