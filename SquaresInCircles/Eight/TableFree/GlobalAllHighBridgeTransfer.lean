module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgePolynomials

/-!
# Transfer of the four bridge polynomials to their exact trigonometric duals

All Taylor signs are fixed on the whole interval.  The positive
quadratic norm envelope uses only a square completion and the original
circle norm.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open Polynomial FrameCircleArc FrameLowArc FrameMidArc GlobalOuterAnchor

def endpointScalar (mu lambda K g bonus z : ℝ) : ℝ :=
  (1+mu)*(Real.pi/2-z)-mu*(cap-bonus)+K+g+lambda*width (-z)+
    mu*(9/50)*frameCost z-lambda*a1*Real.cos z+lambda*b1*Real.sin z
def circleBase (mu lambda K g bonus z : ℝ) : ℝ :=
  (1+mu)*(Real.pi/2-z)-mu*(cap-bonus)+K+g+lambda/2-mu*(9/100)+
    (lambda+mu*(9/100))*Real.cos z+mu*(9/100)*Real.sin z
def circleScalar (mu lambda K g bonus z : ℝ) : ℝ :=
  circleBase mu lambda K g bonus z-R*sourceNorm mu lambda z

theorem S7_le_sin {z : ℝ} (hz : 0≤z) : Arithmetic.sin7 z≤Real.sin z := by
  simpa only [Arithmetic.sin7] using sin_lower_seven hz

@[simp] theorem Am_cast (mu : ℚ) : (DualPolynomial.Am mu:ℝ)=midDualA (mu:ℝ) := by
  norm_num [DualPolynomial.Am,midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p] <;> ring
@[simp] theorem Bm_cast (mu : ℚ) : (DualPolynomial.Bm mu:ℝ)=midDualB (mu:ℝ) := by
  norm_num [DualPolynomial.Bm,midDualB,rho,FrameHighArc.v,FrameMidArc.q] <;> ring

theorem endpoint_polynomial_lower (mu lambda K g bonus : ℚ)
    (hmu : (0:ℝ)≤(mu:ℝ)) (hl : (0:ℝ)≤(lambda:ℝ))
    (hcos : (lambda:ℝ)*(1/2-(DualPolynomial.a1Upper:ℝ))+(mu:ℝ)*(9/100)≤0)
    (hsin : 0≤(lambda:ℝ)*(1/2+(DualPolynomial.b1Lower:ℝ))+(mu:ℝ)*(9/100))
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z (DualPolynomial.endpointPoly mu lambda K g bonus)≤
      endpointScalar (mu:ℝ) (lambda:ℝ) (K:ℝ) (g:ℝ) (bonus:ℝ) z := by
  have tr := transport_trig hz
  have hpi := mul_le_mul_of_nonneg_left
    (show (DualPolynomial.piLow:ℝ)≤Real.pi by
      norm_num [DualPolynomial.piLow]; exact Arithmetic.pi_hand_enclosure.1.le)
    (show 0≤(1+(mu:ℝ))/2 by linarith)
  have ha : a1≤(DualPolynomial.a1Upper:ℝ) := by
    norm_num [DualPolynomial.a1Upper]
    linarith [a1_precise.2]
  have hb : (DualPolynomial.b1Lower:ℝ)≤b1 := by
    norm_num [DualPolynomial.b1Lower]
    exact b1_precise.1.le
  have hpa := mul_nonneg (mul_nonneg hl (show 0≤Real.cos z by linarith [tr.1]))
    (sub_nonneg.mpr ha)
  have hpb := mul_nonneg (mul_nonneg hl tr.2.2.1) (sub_nonneg.mpr hb)
  have hc := mul_le_mul_of_nonpos_left (Arithmetic.cos_le_cos8 hz.1) hcos
  have hs := mul_le_mul_of_nonneg_left (S7_le_sin hz.1) hsin
  simp only [DualPolynomial.endpointPoly,map_add,map_sub,map_mul,aeval_C,aeval_X,
    DualPolynomial.C8_eval,DualPolynomial.S7_eval]
  push_cast
  dsimp [endpointScalar]
  rw [width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
  dsimp [frameCost,DualPolynomial.capQ,cap]
  nlinarith only [hpi,hpa,hpb,hc,hs]

theorem low_low_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)+1/625<endpointScalar (17/10) (59/25) (2113/2500) (-4029/2500) 0 z := by
  have hh := endpoint_polynomial_lower (17/10) (59/25) (2113/2500) (-4029/2500) 0
    (by norm_num) (by norm_num)
    (by norm_num [DualPolynomial.a1Upper]) (by norm_num [DualPolynomial.b1Lower]) hz
  have hp := DualPolynomial.lowLow_positive hz
  simp only [DualPolynomial.lowLow,map_sub,aeval_C] at hp
  norm_num [DualPolynomial.eta] at hp hh ⊢
  linarith

theorem low_nonlow_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)<endpointScalar 5 (93/20) (-1673/10000) (-1357/1000) (93/10000) z := by
  have hh := endpoint_polynomial_lower 5 (93/20) (-1673/10000) (-1357/1000) (93/10000)
    (by norm_num) (by norm_num)
    (by norm_num [DualPolynomial.a1Upper]) (by norm_num [DualPolynomial.b1Lower]) hz
  have hp := DualPolynomial.lowNonlow_positive hz
  simp only [DualPolynomial.lowNonlow,map_sub,aeval_C] at hp
  norm_num [DualPolynomial.eta] at hp hh ⊢
  linarith

theorem norm_polynomial_upper (mu lambda : ℚ)
    (hl : (0:ℝ)≤(lambda:ℝ)) (ha : 0≤midDualA (mu:ℝ)) (hb : 0≤midDualB (mu:ℝ))
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (sourceNorm (mu:ℝ) (lambda:ℝ) z)^2≤aeval z (DualPolynomial.normSqPoly mu lambda) := by
  have hc := mul_le_mul_of_nonneg_left (Arithmetic.cos_le_cos8 hz.1) ha
  have hs := mul_le_mul_of_nonneg_left (S7_le_sin hz.1) hb
  have hh := mul_le_mul_of_nonneg_left (show midDualA (mu:ℝ)*Real.cos z-
      midDualB (mu:ℝ)*Real.sin z≤midDualA (mu:ℝ)*Arithmetic.cos8 z-
        midDualB (mu:ℝ)*Arithmetic.sin7 z by linarith)
    (show 0≤2*(lambda:ℝ) by linarith)
  rw [sourceNorm_sq]
  simp only [DualPolynomial.normSqPoly,map_add,map_sub,map_mul,aeval_C,
    DualPolynomial.C8_eval,DualPolynomial.S7_eval]
  push_cast
  simp only [Am_cast,Bm_cast]
  nlinarith only [hh]

theorem distance_polynomial_lower (mu lambda K g bonus : ℚ)
    (hmu : (0:ℝ)≤(mu:ℝ)) (hl : (0:ℝ)≤(lambda:ℝ))
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z (DualPolynomial.distancePoly mu lambda K g bonus)≤
      circleBase (mu:ℝ) (lambda:ℝ) (K:ℝ) (g:ℝ) (bonus:ℝ) z-957/1000 := by
  have hp := mul_le_mul_of_nonneg_left
    (show (DualPolynomial.piLow:ℝ)≤Real.pi by
      norm_num [DualPolynomial.piLow]; exact Arithmetic.pi_hand_enclosure.1.le)
    (show 0≤(1+(mu:ℝ))/2 by linarith)
  have hc := mul_le_mul_of_nonneg_left (Arithmetic.cos10_le_cos hz.1)
    (show 0≤(lambda:ℝ)+(mu:ℝ)*(9/100) by positivity)
  have hs := mul_le_mul_of_nonneg_left (S7_le_sin hz.1)
    (show 0≤(mu:ℝ)*(9/100) by positivity)
  simp only [DualPolynomial.distancePoly,map_add,map_sub,map_mul,aeval_C,aeval_X,
    DualPolynomial.C10_eval,DualPolynomial.S7_eval]
  push_cast
  dsimp [circleBase,DualPolynomial.piLow,DualPolynomial.capQ,DualPolynomial.eta,cap] at *
  nlinarith only [hp,hc,hs]

theorem quadratic_norm_envelope {p D N S r upper : ℝ}
    (hp : 0<p) (hN : 0≤N) (hu : 0≤upper) (hr : r≤upper)
    (hS : N^2≤S) (hP : 0<2*p*D-upper*(p^2+S)) : r*N<D := by
  have h1 := mul_nonneg hu (sq_nonneg (p-N))
  have h2 := mul_nonneg hu (sub_nonneg.mpr hS)
  have hscaled : 0<2*p*(D-upper*N) := by nlinarith only [h1,h2,hP]
  have hD : upper*N<D := by
    have hh := (mul_pos_iff_of_pos_left (show 0<2*p by linarith)).1 hscaled
    linarith
  exact (mul_le_mul_of_nonneg_right hr hN).trans_lt hD

theorem middle_low_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)<circleScalar (17/10) (59/25) (109221/10000) (-4029/2500) (93/10000) z := by
  have hp := DualPolynomial.midLow_positive hz
  simp only [DualPolynomial.midLow,map_sub,map_mul,map_pow,aeval_C] at hp
  norm_num at hp
  have hS := norm_polynomial_upper (17/10) (59/25) (by norm_num)
    (by norm_num [midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p])
    (by norm_num [midDualB,rho,FrameHighArc.v,FrameMidArc.q]) hz
  have hR : R≤(DualPolynomial.radiusUpper:ℝ) := by
    simpa [DualPolynomial.radiusUpper,FrameHighArc.radiusUpper] using FrameHighArc.radius_bound.le
  have hN := quadratic_norm_envelope (DualPolynomial.pLow_positive hz)
    (sourceNorm_nonnegative (17/10) (59/25) z)
    (by norm_num [DualPolynomial.radiusUpper]) hR hS hp
  have hd := distance_polynomial_lower (17/10) (59/25) (109221/10000)
    (-4029/2500) (93/10000) (by norm_num) (by norm_num) hz
  norm_num at hd hN
  dsimp [circleScalar]
  linarith

theorem middle_nonlow_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (957/1000:ℝ)<circleScalar 5 (93/20) (115297/5000) (-1357/1000) (43/2500) z := by
  have hp := DualPolynomial.midNonlow_positive hz
  simp only [DualPolynomial.midNonlow,map_sub,map_mul,map_pow,aeval_C] at hp
  norm_num at hp
  have hS := norm_polynomial_upper 5 (93/20) (by norm_num)
    (by norm_num [midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p])
    (by norm_num [midDualB,rho,FrameHighArc.v,FrameMidArc.q]) hz
  have hR : R≤(DualPolynomial.radiusUpper:ℝ) := by
    simpa [DualPolynomial.radiusUpper,FrameHighArc.radiusUpper] using FrameHighArc.radius_bound.le
  have hN := quadratic_norm_envelope (DualPolynomial.pNonlow_positive hz)
    (sourceNorm_nonnegative 5 (93/20) z)
    (by norm_num [DualPolynomial.radiusUpper]) hR hS hp
  have hd := distance_polynomial_lower 5 (93/20) (115297/5000)
    (-1357/1000) (43/2500) (by norm_num) (by norm_num) hz
  norm_num at hd hN
  dsimp [circleScalar]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
