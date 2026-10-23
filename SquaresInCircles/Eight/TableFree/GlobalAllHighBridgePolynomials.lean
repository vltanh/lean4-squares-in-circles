module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeDualSupport

/-!
# Four fixed whole-interval outer-bridge polynomials

The endpoint-source polynomials have degree eight.  The two circle
envelopes have degree twelve.  Each is certified on the full interval
[0,.7] by one translated coefficient bound or one retained quadratic;
there is no subdivision of an angle or of a state arc.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge.DualPolynomial

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
def lowShift : ℚ[X] := shift (11/20) lowLow
def lowQuotient : ℚ[X] := lowShift.divX.divX
def midNonlowSlope : ℚ[X] := shift (7/20) (-midNonlow.derivative)

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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_factor : lowShift=C (lowShift.coeff 0)+C (lowShift.coeff 1)*X+X^2*lowQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_quotient_identity : CenteredMonomialBounds.translated (-1/5) lowQuotient=
    CenteredMonomialBounds.series 6 (CenteredMonomialBounds.translated (-1/5) lowQuotient) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_quotient_reserve : (3/25:ℚ)<
    CenteredMonomialBounds.lowerOn 6 (-1/5) (7/20) lowQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_discriminant : (lowShift.coeff 1)^2<4*(3/25)*(lowShift.coeff 0) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem midLow_identity : midLow=C (midLow.coeff 0)+C (midLow.coeff 1)*X+
    C (midLow.coeff 2)*X^2+tail midLow 3 10 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem midLow_reserves : (0:ℚ)<midLow.coeff 0 ∧ 0≤midLow.coeff 1 ∧
    0≤midLow.coeff 2-negativeNorm midLow 3 10 (7/10) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lowNonlow_slope_identity : CenteredMonomialBounds.translated (7/20) (-lowNonlow.derivative)=
    CenteredMonomialBounds.series 7
      (CenteredMonomialBounds.translated (7/20) (-lowNonlow.derivative)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lowNonlow_slope_reserve : (1/4:ℚ)<
    CenteredMonomialBounds.lowerOn 7 (7/20) (7/20) (-lowNonlow.derivative) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem midNonlow_slope_identity : midNonlowSlope=C (midNonlowSlope.coeff 0)+
    tail midNonlowSlope 1 11 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem midNonlow_slope_reserve : (2:ℚ)<midNonlowSlope.coeff 0-
    PowerTailBounds.norm midNonlowSlope 1 11 (7/20) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem last_reserves : (0:ℚ)<lowNonlow.eval (7/10) ∧ (0:ℚ)<midNonlow.eval (7/10) := by decide

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-(7/20:ℝ)|≤7/20 := by
  apply abs_le.mpr
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

theorem lowLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowLow := by
  have hdom : |(z-11/20)-((-1/5:ℚ):ℝ)|≤((7/20:ℚ):ℝ) := by
    norm_num
    convert centered_domain hz using 1 <;> congr 1 <;> ring
  have hl := CenteredMonomialBounds.interval_lower low_quotient_identity
    (by norm_num : (0:ℚ)≤7/20) hdom
  have hr : (3/25:ℝ)<(CenteredMonomialBounds.lowerOn 6 (-1/5) (7/20) lowQuotient:ℝ) := by
    exact_mod_cast low_quotient_reserve
  have hq : (3/25:ℝ)≤aeval (z-11/20) lowQuotient := by linarith
  have hdisc : (lowShift.coeff 1:ℝ)^2<4*(3/25)*(lowShift.coeff 0:ℝ) := by
    exact_mod_cast low_discriminant
  have hp := positive_quadratic (z := z-11/20) (by norm_num : (0:ℝ)<3/25) hdisc
  have hm := mul_le_mul_of_nonneg_left hq (sq_nonneg (z-11/20))
  have hi := congrArg (fun p : ℚ[X] => aeval (z-11/20) p) low_factor
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at hi
  have he : aeval (z-11/20) lowShift=aeval z lowLow := by
    simp [lowShift,shift_eval]
  rw [he] at hi
  nlinarith only [hp,hm,hi]

theorem midLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midLow := by
  have hl := quadratic_lower midLow_identity (show z∈Icc 0 ((7/10:ℚ):ℝ) from hz)
  have hr0 : (0:ℝ)<(midLow.coeff 0:ℝ) := by exact_mod_cast midLow_reserves.1
  have hr1 : (0:ℝ)≤(midLow.coeff 1:ℝ) := by exact_mod_cast midLow_reserves.2.1
  have hr2 : (0:ℝ)≤(midLow.coeff 2:ℝ)-(negativeNorm midLow 3 10 (7/10):ℝ) := by
    exact_mod_cast midLow_reserves.2.2
  nlinarith only [hl,hr0,mul_nonneg hr1 hz.1,mul_nonneg hr2 (sq_nonneg z)]

theorem lowNonlow_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z lowNonlow.derivative<0 := by
  have hl := CenteredMonomialBounds.interval_lower lowNonlow_slope_identity
    (by norm_num : (0:ℚ)≤7/20) (centered_domain hz)
  have hr : (1/4:ℝ)<
      (CenteredMonomialBounds.lowerOn 7 (7/20) (7/20) (-lowNonlow.derivative):ℝ) := by
    exact_mod_cast lowNonlow_slope_reserve
  simp only [map_neg] at hl
  linarith

theorem midNonlow_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z midNonlow.derivative<0 := by
  have hl := constant_lower midNonlow_slope_identity (centered_domain hz)
  have hr : (2:ℝ)<(midNonlowSlope.coeff 0:ℝ)-
      (PowerTailBounds.norm midNonlowSlope 1 11 (7/20):ℝ) := by
    exact_mod_cast midNonlow_slope_reserve
  have he : aeval (z-7/20) midNonlowSlope= -aeval z midNonlow.derivative := by
    simp [midNonlowSlope,shift_eval]
  rw [he] at hl
  linarith

theorem lowNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowNonlow := by
  have hm : AntitoneOn (fun z : ℝ => aeval z lowNonlow) (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt lowNonlow z).continuousAt.continuousWithinAt
    · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt lowNonlow z
    · exact fun z hz => (lowNonlow_derivative_negative (Ioo_subset_Icc_self hz)).le
  have he : 0<aeval (frameCap:ℝ) lowNonlow := by
    rw [show frameCap=((7/10:ℚ):ℝ) by norm_num [frameCap],ZeroPolynomial.rational_aeval]
    exact_mod_cast last_reserves.1
  exact he.trans_le (hm hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2)

theorem midNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midNonlow := by
  have hm : AntitoneOn (fun z : ℝ => aeval z midNonlow) (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt midNonlow z).continuousAt.continuousWithinAt
    · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt midNonlow z
    · exact fun z hz => (midNonlow_derivative_negative (Ioo_subset_Icc_self hz)).le
  have he : 0<aeval (frameCap:ℝ) midNonlow := by
    rw [show frameCap=((7/10:ℚ):ℝ) by norm_num [frameCap],ZeroPolynomial.rational_aeval]
    exact_mod_cast last_reserves.2
  exact he.trans_le (hm hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2)

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

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge.DualPolynomial
