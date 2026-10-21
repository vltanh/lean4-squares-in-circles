module

public import SquaresInCircles.Eight.TableFree.HalfRatioNormGain
public import SquaresInCircles.Eight.TableFree.SingleAngleConcavity

/-!
# A balanced negative pair dominates the sole-E A charge

Uncompiled source. At a fixed product, the decrease of the pair norm is
largest at equal coefficients. Rationalization proves this comparison
on the whole angle interval. A coarse Taylor inequality then suffices
for the actual A coefficient range; no angle partition is involved.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.BalancedNegativeGain
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open SoleNormGain SingleAngleConcavity

theorem pair_decrease_nonneg {a b v : ℝ} (ha : 0<a) (hb : 0<b)
    (hv : v∈Icc 0 frameCap) : 0≤pairNorm a b 0-pairNorm a b (-v) := by
  have h0 := pairNorm_sq ha hb (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hv' := pairNorm_sq ha hb (show |-v|≤frameCap by
    rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2)
  have hpos := pairNorm_pos ha hb (show |-v|≤frameCap by
    rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2)
  have hzero := pairNorm_pos ha hb (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hsin := (transport_trig hv).2.2.1
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at h0 hv'
  have hh := mul_nonneg (mul_nonneg ha.le hb.le) hsin
  nlinarith

theorem fixed_product {R a b v : ℝ} (hR : 0≤R) (ha : 0<a) (hb : 0<b)
    (hv : v∈Icc 0 frameCap) :
    normGain R a b v≤Real.sqrt (a*b)*normGain R 1 1 v := by
  let w := Real.sqrt (a*b)
  let A := pairNorm a b 0
  let B := pairNorm a b (-v)
  let C := pairNorm 1 1 0
  let D := pairNorm 1 1 (-v)
  have hw : 0<w := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hw2 : w^2=a*b := Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have h0 : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hv' : |-v|≤frameCap := by rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2
  have hA := pairNorm_pos ha hb h0
  have hB := pairNorm_pos ha hb hv'
  have hC := pairNorm_pos (p:=1) (q:=1) (by norm_num) (by norm_num) h0
  have hD := pairNorm_pos (p:=1) (q:=1) (by norm_num) (by norm_num) hv'
  have hA2 := pairNorm_sq ha hb h0
  have hB2 := pairNorm_sq ha hb hv'
  have hC2 := pairNorm_sq (p:=1) (q:=1) (by norm_num) (by norm_num) h0
  have hD2 := pairNorm_sq (p:=1) (q:=1) (by norm_num) (by norm_num) hv'
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at hA2 hB2 hC2 hD2
  have hAC : w*C≤A := by
    have hp := mul_pos hw hC
    have he : (w*C)^2=w^2*C^2 := by ring
    dsimp [A,C] at *
    nlinarith [sq_nonneg (a-b)]
  have hBD : w*D≤B := by
    have hp := mul_pos hw hD
    have he : (w*D)^2=w^2*D^2 := by ring
    have hwprod := congrArg (fun x : ℝ => x*(2-2*Real.sin v)) hw2
    dsimp [B,D] at *
    nlinarith [sq_nonneg (a-b)]
  have hsum : w*(C+D)≤A+B := by linarith
  have hdiff : 0≤C-D := pair_decrease_nonneg (by norm_num) (by norm_num) hv
  have hid : (A-B)*(A+B)=w^2*(C-D)*(C+D) := by
    have hp := congrArg (fun x : ℝ => x*(2*Real.sin v)) hw2
    dsimp [A,B,C,D] at *
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsum (mul_nonneg hw.le hdiff)
  have hcancel : (A-B)*(A+B)≤(w*(C-D))*(A+B) := by
    nlinarith only [hprod,hid]
  have hcomp : A-B≤w*(C-D) := (mul_le_mul_iff_right₀ (by linarith : 0<A+B)).1 hcancel
  have hm := mul_le_mul_of_nonneg_left hcomp hR
  dsimp [normGain,w,A,B,C,D] at *
  nlinarith only [hm]

theorem unit_gain_cosine {R v : ℝ} (hR : 3/2≤R)
    (hv : v∈Icc 0 frameCap) :
    (11/5)*(1-Real.cos v)≤normGain R 1 1 v := by
  have h0 : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hv' : |-v|≤frameCap := by rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2
  have hA := pairNorm_pos (p:=1) (q:=1) (by norm_num) (by norm_num) h0
  have hB := pairNorm_pos (p:=1) (q:=1) (by norm_num) (by norm_num) hv'
  have hA2 := pairNorm_sq (p:=1) (q:=1) (by norm_num) (by norm_num) h0
  have hB2 := pairNorm_sq (p:=1) (q:=1) (by norm_num) (by norm_num) hv'
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at hA2 hB2
  have hsmall : pairNorm 1 1 0≤3/2 := by nlinarith
  have hdiff := pair_decrease_nonneg (by norm_num : (0:ℝ)<1) (by norm_num) hv
  have hgain : Real.sin v≤normGain R 1 1 v := by
    have hp := mul_le_mul_of_nonneg_right (hsmall.trans hR) hdiff
    have hs := sq_nonneg (pairNorm 1 1 0-pairNorm 1 1 (-v))
    dsimp [normGain]
    nlinarith
  have hv7 : v≤7/10 := hv.2
  have hv2 : v^2≤(7/10)*v := by nlinarith [hv.1,hv7]
  have hv3 : v^3≤(49/100)*v := by
    have hh := mul_le_mul_of_nonneg_right hv2 hv.1
    nlinarith
  have hsin := Real.sin_ge_sub_cube hv.1
  have hcos := Real.one_sub_sq_div_two_le_cos v
  have htrig : (11/5)*(1-Real.cos v)≤Real.sin v := by nlinarith
  exact htrig.trans hgain

theorem unit_nonneg {R v : ℝ} (hR : 3/2≤R)
    (hv : v∈Icc 0 frameCap) : 0≤Vnu R 1 1 1 v := by
  have hh := unit_gain_cosine hR hv
  have hc := Real.cos_le_one v
  dsimp [Vnu,normGain] at *
  linarith

theorem dominates_A {R k l p v : ℝ} (hR : 3/2≤R)
    (hk : 0<k) (hl : 0<l) (hsum : k+l≤2) (hlinear : 11*k+l≤12)
    (hp : 1≤p) (hv : v∈Icc 0 frameCap) :
    Vnu R l k l v≤p*Vnu R 1 1 1 v := by
  let w := Real.sqrt (k*l)
  have hw : 0≤w := Real.sqrt_nonneg _
  have hw2 : w^2=k*l := Real.sq_sqrt (mul_nonneg hk.le hl.le)
  have ham : 2*w≤k+l := by nlinarith [sq_nonneg (k-l)]
  have hw1 : w≤1 := by linarith
  have hcoefficient : 1-l≤(11/5)*(1-w) := by linarith
  have hcos : 0≤1-Real.cos v := sub_nonneg.mpr (Real.cos_le_one v)
  have hco := mul_le_mul_of_nonneg_right hcoefficient hcos
  have hunit := unit_gain_cosine hR hv
  have hscaled := mul_le_mul_of_nonneg_left hunit (sub_nonneg.mpr hw1)
  have hfixed := fixed_product (by linarith : 0≤R) hl hk hv
  have hroot : Real.sqrt (l*k)=w := by dsimp [w]; rw [mul_comm]
  rw [hroot] at hfixed
  have hunitnonneg := unit_nonneg hR hv
  have hpunit := mul_le_mul_of_nonneg_right hp hunitnonneg
  dsimp [Vnu,normGain] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.BalancedNegativeGain
