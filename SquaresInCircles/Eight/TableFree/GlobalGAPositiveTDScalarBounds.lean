module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDPolynomialData

/-!
# Exact transfer from TD2 polynomials to actual force norms

Uncompiled source.  A positive auxiliary mass bounds a norm directly
from its squared-norm upper bound.  This avoids any premise about the
auxiliary mass approximating a root.  Taylor bounds and the three fixed
radical upper bounds are proved on the complete frame interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus

theorem radius_le_Rbar : R≤(Rbar:ℝ) := by
  have hs := radius_sq
  have hp := Real.sqrt_nonneg qCap
  norm_num [qCap,Rbar] at hs ⊢
  nlinarith

theorem diagonal_le_cbar : GlobalGA.Secondary.diagonal≤(cbar:ℝ) := by
  have hs := diagonal_circle
  have hp := diagonal_bounds.1
  norm_num [qCap,cbar] at hs ⊢
  nlinarith

theorem sigma_le_sigmabar : sigma≤(sigmabar:ℝ) := by
  have hn : 0≤Real.sqrt (1+eta^2) := Real.sqrt_nonneg _
  have hs : (R*Real.sqrt (1+eta^2))^2=qCap*(1+eta^2) := by
    rw [mul_pow,radius_sq,Real.sq_sqrt (by positivity)]
  have hp : 0≤R*Real.sqrt (1+eta^2) := mul_nonneg (Real.sqrt_nonneg qCap) hn
  dsimp [sigma,fullSupport]
  norm_num [eta,qCap,sigmabar] at hs ⊢
  nlinarith

theorem three_norm_transfer {A P0 P1 P2 r0 r1 r2 a n0 n1 n2 : ℝ}
    (hr0 : 0<r0) (hr1 : 0<r1) (hr2 : 0<r2)
    (hn0 : 0≤n0) (hn1 : 0≤n1) (hn2 : 0≤n2)
    (h0 : n0^2≤P0) (h1 : n1^2≤P1) (h2 : n2^2≤P2)
    (hA : A≤a)
    (hP : 0<2*A*r0*r1*r2-(Rbar:ℝ)*
      ((P0+r0^2)*r1*r2+(P1+r1^2)*r0*r2+(P2+r2^2)*r0*r1)) :
    0<a-R*(n0+n1+n2) := by
  have hRbar : (0:ℝ)≤(Rbar:ℝ) := by norm_num [Rbar]
  have h0' := mul_le_mul_of_nonneg_left
    (show 2*r0*n0≤P0+r0^2 by nlinarith [sq_nonneg (n0-r0)])
    (mul_nonneg hRbar (mul_nonneg hr1.le hr2.le))
  have h1' := mul_le_mul_of_nonneg_left
    (show 2*r1*n1≤P1+r1^2 by nlinarith [sq_nonneg (n1-r1)])
    (mul_nonneg hRbar (mul_nonneg hr0.le hr2.le))
  have h2' := mul_le_mul_of_nonneg_left
    (show 2*r2*n2≤P2+r2^2 by nlinarith [sq_nonneg (n2-r2)])
    (mul_nonneg hRbar (mul_nonneg hr0.le hr1.le))
  have hden : 0<2*r0*r1*r2 := by positivity
  have hA' := mul_le_mul_of_nonneg_left hA hden.le
  have hR' := mul_le_mul_of_nonneg_right radius_le_Rbar
    (mul_nonneg hden.le (show 0≤n0+n1+n2 by positivity))
  have hpos : 0<(2*r0*r1*r2)*(a-R*(n0+n1+n2)) := by
    nlinarith only [hP,h0',h1',h2',hA',hR']
  exact (mul_pos_iff_of_pos_left hden).mp hpos

theorem four_norm_transfer {A P0 P1 P2 P3 r0 r1 r2 r3 a n0 n1 n2 n3 : ℝ}
    (hr0 : 0<r0) (hr1 : 0<r1) (hr2 : 0<r2) (hr3 : 0<r3)
    (hn0 : 0≤n0) (hn1 : 0≤n1) (hn2 : 0≤n2) (hn3 : 0≤n3)
    (h0 : n0^2≤P0) (h1 : n1^2≤P1) (h2 : n2^2≤P2) (h3 : n3^2≤P3)
    (hA : A≤a)
    (hP : 0<2*A*r0*r1*r2*r3-(Rbar:ℝ)*
      ((P0+r0^2)*r1*r2*r3+(P1+r1^2)*r0*r2*r3+
        (P2+r2^2)*r0*r1*r3+(P3+r3^2)*r0*r1*r2)) :
    0<a-R*(n0+n1+n2+n3) := by
  have hRbar : (0:ℝ)≤(Rbar:ℝ) := by norm_num [Rbar]
  have h0' := mul_le_mul_of_nonneg_left
    (show 2*r0*n0≤P0+r0^2 by nlinarith [sq_nonneg (n0-r0)])
    (show 0≤(Rbar:ℝ)*r1*r2*r3 by positivity)
  have h1' := mul_le_mul_of_nonneg_left
    (show 2*r1*n1≤P1+r1^2 by nlinarith [sq_nonneg (n1-r1)])
    (show 0≤(Rbar:ℝ)*r0*r2*r3 by positivity)
  have h2' := mul_le_mul_of_nonneg_left
    (show 2*r2*n2≤P2+r2^2 by nlinarith [sq_nonneg (n2-r2)])
    (show 0≤(Rbar:ℝ)*r0*r1*r3 by positivity)
  have h3' := mul_le_mul_of_nonneg_left
    (show 2*r3*n3≤P3+r3^2 by nlinarith [sq_nonneg (n3-r3)])
    (show 0≤(Rbar:ℝ)*r0*r1*r2 by positivity)
  have hden : 0<2*r0*r1*r2*r3 := by positivity
  have hA' := mul_le_mul_of_nonneg_left hA hden.le
  have hR' := mul_le_mul_of_nonneg_right radius_le_Rbar
    (mul_nonneg hden.le (show 0≤n0+n1+n2+n3 by positivity))
  have hpos : 0<(2*r0*r1*r2*r3)*(a-R*(n0+n1+n2+n3)) := by
    nlinarith only [hP,h0',h1',h2',h3',hA',hR']
  exact (mul_pos_iff_of_pos_left hden).mp hpos

theorem num3_transfer {z a n0 n1 n2 : ℝ} {A P0 P1 P2 r0 r1 r2 : ℚ[X]}
    (hr0 : 0<aeval z r0) (hr1 : 0<aeval z r1) (hr2 : 0<aeval z r2)
    (hn0 : 0≤n0) (hn1 : 0≤n1) (hn2 : 0≤n2)
    (h0 : n0^2≤aeval z P0) (h1 : n1^2≤aeval z P1) (h2 : n2^2≤aeval z P2)
    (hA : aeval z A≤a) (hP : 0<aeval z (num3 A P0 P1 P2 r0 r1 r2)) :
    0<a-R*(n0+n1+n2) := by
  apply three_norm_transfer hr0 hr1 hr2 hn0 hn1 hn2 h0 h1 h2 hA
  simpa only [num3,map_sub,map_add,map_mul,map_pow,aeval_C,eq_ratCast,Rat.cast_ofNat] using hP

theorem num4_transfer {z a n0 n1 n2 n3 : ℝ}
    {A P0 P1 P2 P3 r0 r1 r2 r3 : ℚ[X]}
    (hr0 : 0<aeval z r0) (hr1 : 0<aeval z r1)
    (hr2 : 0<aeval z r2) (hr3 : 0<aeval z r3)
    (hn0 : 0≤n0) (hn1 : 0≤n1) (hn2 : 0≤n2) (hn3 : 0≤n3)
    (h0 : n0^2≤aeval z P0) (h1 : n1^2≤aeval z P1)
    (h2 : n2^2≤aeval z P2) (h3 : n3^2≤aeval z P3)
    (hA : aeval z A≤a) (hP : 0<aeval z (num4 A P0 P1 P2 P3 r0 r1 r2 r3)) :
    0<a-R*(n0+n1+n2+n3) := by
  apply four_norm_transfer hr0 hr1 hr2 hr3 hn0 hn1 hn2 hn3 h0 h1 h2 h3 hA
  simpa only [num4,map_sub,map_add,map_mul,map_pow,aeval_C,eq_ratCast,Rat.cast_ofNat] using hP

theorem taylor_lower_signs {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤aeval z S11 ∧ (1/2:ℝ)≤aeval z C10 := by
  have hz1 : z≤1 := by dsimp [frameCap] at hz; linarith [hz.2]
  have hz2 : z^2≤1 := by nlinarith [sq_nonneg z,mul_nonneg hz.1 (sub_nonneg.mpr hz1)]
  have hs1 := mul_nonneg hz.1 (show 0≤1-z^2/6 by nlinarith)
  have hs5 := mul_nonneg (pow_nonneg hz.1 5) (show 0≤1/120-z^2/5040 by nlinarith)
  have hs9 := mul_nonneg (pow_nonneg hz.1 9)
    (show 0≤1/362880-z^2/39916800 by nlinarith)
  have hc4 := mul_nonneg (pow_nonneg hz.1 4) (show 0≤1/24-z^2/720 by nlinarith)
  have hc8 := mul_nonneg (pow_nonneg hz.1 8)
    (show 0≤1/40320-z^2/3628800 by nlinarith)
  simp only [S11_eval,C10_eval]
  dsimp [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]
  constructor <;> nlinarith

theorem taylor_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤aeval z S11 ∧ aeval z S11≤Real.sin z ∧ Real.sin z≤aeval z S9 ∧
      (1/2:ℝ)≤aeval z C10 ∧ aeval z C10≤Real.cos z ∧ Real.cos z≤aeval z C12 := by
  exact ⟨(taylor_lower_signs hz).1,by simpa using HighOrderTaylor.S11_le_sin hz.1,
    by simpa using Arithmetic.sin_le_sin9 hz.1,(taylor_lower_signs hz).2,
    by simpa using Arithmetic.cos10_le_cos hz.1,
    by simpa using HighOrderTaylor.cos_le_C12 hz.1⟩

theorem tilted_polynomial_bounds {z : ℝ} {c : ℚ[X]}
    (hz : z∈Icc 0 frameCap) (hc : 0<aeval z c) :
    0<aeval z (mMinus c) ∧ aeval z (mMinus c)≤tilted (aeval z c) z ∧
      tilted (aeval z c) z≤aeval z (mPlus c) := by
  have ht := taylor_bounds hz
  have heta : (0:ℝ)≤eta := by norm_num [eta]
  have hslo := mul_le_mul_of_nonneg_left ht.2.1 heta
  have hshi := mul_le_mul_of_nonneg_left ht.2.2.1 heta
  have hlo := mul_le_mul_of_nonneg_left
    (show aeval z C10+eta*aeval z S11≤Real.cos z+eta*Real.sin z by
      linarith [ht.2.2.2.2.1]) hc.le
  have hhi := mul_le_mul_of_nonneg_left
    (show Real.cos z+eta*Real.sin z≤aeval z C12+eta*aeval z S9 by
      linarith [ht.2.2.2.2.2]) hc.le
  have hpos : 0<aeval z c*(aeval z C10+eta*aeval z S11) := by
    apply mul_pos hc
    have hh := mul_nonneg heta ht.1
    linarith [ht.2.2.2.1]
  have he : ((etaQ:ℚ):ℝ)=eta := by norm_num [etaQ,eta]
  have hm : aeval z (mMinus c)=aeval z c*(aeval z C10+eta*aeval z S11) := by
    simp only [mMinus,map_mul,map_add,aeval_C,eq_ratCast,he]
  have hp : aeval z (mPlus c)=aeval z c*(aeval z C12+eta*aeval z S9) := by
    simp only [mPlus,map_mul,map_add,aeval_C,eq_ratCast,he]
  rw [hm,hp]
  exact ⟨hpos,hlo,hhi⟩

theorem sigma_sine_upper {z c : ℝ} (hz : z∈Icc 0 frameCap) (hc : 0≤c) :
    c*sigma*Real.sin z≤c*(sigmabar:ℝ)*aeval z S9 := by
  have hs : 0≤Real.sin z := (transport_trig hz).2.2.1
  have h1 := mul_le_mul_of_nonneg_right sigma_le_sigmabar hs
  have h2 := mul_le_mul_of_nonneg_left (taylor_bounds hz).2.2.1
    (show (0:ℝ)≤(sigmabar:ℝ) by norm_num [sigmabar])
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hc
  nlinarith only [h3]

theorem pairNorm_nonneg (p q z : ℝ) : 0≤pairNorm p q z := Real.sqrt_nonneg _

theorem zero_norm_sq (p q : ℝ) : (pairNorm p q 0)^2=p^2+q^2 := by
  rw [pairNorm_zero,Real.sq_sqrt (by positivity)]

theorem negative_norm_sq_le {p q z s : ℝ}
    (hp : 0<p) (hq : 0<q) (hz : z∈Icc 0 frameCap) (hs : s≤Real.sin z) :
    (pairNorm p q (-z))^2≤p^2+q^2-2*p*q*s := by
  have hh := pairNorm_sq hp hq
    (show |-z|≤frameCap by simpa only [abs_neg,abs_of_nonneg hz.1] using hz.2)
  have hm := mul_le_mul_of_nonneg_left hs (show 0≤2*p*q by positivity)
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hh
  nlinarith only [hh,hm]

theorem clippedSupport_le_fullSupport (f g : ℝ) :
    clippedSupport f g≤fullSupport f g := by
  by_cases hfg : f≤g
  · have hh := raw_full_support (a:=GlobalGA.Secondary.diagonal) (b:=GlobalGA.Secondary.diagonal) (f:=f) (g:=g)
      (show (GlobalGA.Secondary.diagonal+1/2)^2+(GlobalGA.Secondary.diagonal+1/2)^2≤qCap by nlinarith [diagonal_circle])
    simp only [clippedSupport,if_pos hfg,diagonalSupport]
    nlinarith only [hh]
  · simp [clippedSupport,hfg]

def lowNonradical (k l c z : ℝ) : ℝ :=
  2*k+3*l+(3/2)*tilted c z+5/2+c*edgeWidth z-
    (1+c)*GlobalGA.Secondary.diagonal-c*sigma*Real.sin z

theorem low_baseline_identity {k l c z : ℝ} (hc : 1≤c) :
    baseline k l c z=lowNonradical k l c z-
      R*(pairNorm k 1 0+pairNorm k l 0+pairNorm l (tilted c z) 0) := by
  simp only [baseline,fullSupport_pair]
  simp only [clippedSupport,if_pos hc,diagonalSupport]
  dsimp [lowNonradical]
  ring

theorem low_H_identity {k l c z t : ℝ} (hc : 1≤c) :
    baseline k l c z+V R k 1 t=lowNonradical k l c z+Real.cos t-1-
      R*(pairNorm k 1 (-t)+pairNorm k l 0+pairNorm l (tilted c z) 0) := by
  rw [low_baseline_identity hc]
  dsimp [V]
  ring

theorem low_G_identity {k l c z t : ℝ} (hc : 1≤c) :
    baseline k l c z+V R k l t=lowNonradical k l c z+l*(Real.cos t-1)-
      R*(pairNorm k 1 0+pairNorm k l (-t)+pairNorm l (tilted c z) 0) := by
  rw [low_baseline_identity hc]
  dsimp [V]
  ring

def upperNonradical (k c z : ℝ) : ℝ :=
  2*k+5+Real.cos z+(3/2)*tilted c z+c/2+c*edgeWidth z-c*sigma*Real.sin z

theorem upper_H_lower (k c z : ℝ) :
    upperNonradical k c z-
      R*(pairNorm k 1 0+pairNorm (tilted c z) 1 0+pairNorm k 1 (-z)+pairNorm c 1 0)≤
      baseline k 1 c z+V R k 1 z := by
  have hD := clippedSupport_le_fullSupport 1 c
  simp only [baseline,fullSupport_pair]
  rw [fullSupport_pair c 1] at hD
  rw [pairNorm_symm 1 (tilted c z) 0]
  dsimp [V,upperNonradical]
  nlinarith only [hD]

theorem upper_B_lower (k c z : ℝ) :
    upperNonradical k c z-
      R*(pairNorm k 1 0+pairNorm k 1 0+pairNorm (tilted c z) 1 (-z)+pairNorm c 1 0)≤
      baseline k 1 c z+V R (tilted c z) 1 z := by
  have hD := clippedSupport_le_fullSupport 1 c
  simp only [baseline,fullSupport_pair]
  rw [fullSupport_pair c 1] at hD
  rw [pairNorm_symm 1 (tilted c z) 0]
  dsimp [V,upperNonradical]
  nlinarith only [hD]

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
