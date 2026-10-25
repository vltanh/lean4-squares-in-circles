module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTSupport
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTScalarModel
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTOrdinaryData
public import SquaresInCircles.Eight.Owners.Sole.NegativeTDSupport
public import SquaresInCircles.Eight.Owners.Sole.OrdinaryData
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope

/-!
# Eight squares: complete low-family ordinary envelope for original E contact

All original positive/negative ordinary allocations
are covered by continuous concentration. The H block retains its EH0
angle, D may be relaxed to a two-angle block, and A retains its actual
one-angle coefficient. The fixed-ratio gap pays the whole positive
budget with a strict reserve, leaving the actual B pure charge.
-/

section
/-!
## Low exceptional-family pure-charge comparisons

A keeps its actual negative coefficient l. Its
cosine gain pays the change from k to c. H and D are compared with the
fixed pair (.86265,1); B has an explicit initial-slope upper bound and
a circle-norm bound at the frame cap. These are whole-domain analytic
comparisons, including equality when the total angle is zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalELowCharges
open ExceptionalECoefficients SoleNormGain PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem low_order {t : ℝ} (ht : t∈domain .low) :
    0<k .low t ∧ ell .low t≤k .low t ∧ ell .low t≤c .low t ∧
    (117/200)*c .low t≤ell .low t ∧ c .low t≤2*ell .low t := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have hcor := (low_correlations ht).1
  have hp : 0≤t*c .low t := mul_nonneg ht.1 (by linarith)
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith

theorem A_ge_B {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤Vnu R (ell .low t) (k .low t) (ell .low t) t := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have ho := low_order ht
  have hs : t∈Icc 0 (1/5:ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hg := coefficient_short hR ho.1 hkc ho.2.2.2.1 hlk hs
  have hcos := SoleLowAComparison.cosine_loss_lower hs
  have hcos0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  have hcl' : (1/4:ℝ)≤c .low t-ell .low t := by linarith
  have hck : c .low t-k .low t≤t/5 := by
    have hh := (low_correlations ht).2.2.2
    linarith [ht.1]
  have hm := mul_le_mul_of_nonneg_right hcl' hcos0
  have hm' := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤1/4)
  have hkg := mul_le_mul_of_nonneg_left hck (mul_nonneg (by norm_num : (0:ℝ)≤11/20) ht.1)
  dsimp only [V,Vnu,normGain] at hg hm hm' hkg ⊢
  linarith [sq_nonneg t]

theorem A_ge_B_at_cap {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) frameCap≤
      Vnu R (ell .low t) (k .low t) (ell .low t) frameCap := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have ho := low_order ht
  have hg := coefficient_cap hR ho.1 hkc ho.2.2.2.1 hlk
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
  have hm := mul_le_mul_of_nonneg_right (show (1/4:ℝ)≤c .low t-ell .low t by linarith)
    (show 0≤1-Real.cos frameCap by linarith)
  have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤1/4)
  have hck : c .low t-k .low t≤9/250 := by
    have hh := (low_correlations ht).2.2.2
    linarith [ht.1,ht.2]
  dsimp [V,Vnu,normGain] at *
  linarith

theorem B_zero_slope {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vd R (ell .low t) (c .low t) 0≤23/20 := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have hc : 0<c .low t := (low_order ht).1.trans_le hkc
  have hl : 0<ell .low t := by linarith
  have hr0 : 0≤ell .low t/c .low t := div_nonneg hl.le hc.le
  have hr1 : ell .low t/c .low t≤7/10 := (div_le_iff₀ hc).2 (by
    have hh := (low_correlations ht).2.1
    nlinarith)
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono hr0 hr1 (by norm_num) hz
  have hN := root_pos (7/10) hz
  have hN2 := root_sq (7/10) hz
  have hNlo : (61/50:ℝ)≤root (7/10) 0 := by nlinarith
  have hnum : c .low t*R*(7/10)≤(501/500)*2*(7/10) := by
    have hm := mul_le_mul hc1.le hR.2 hR.1 (by norm_num : (0:ℝ)≤501/500)
    nlinarith
  have hbound : c .low t*R*(7/10)/root (7/10) 0≤23/20 := by
    apply (div_le_iff₀ hN).2
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hc.le hR.1)
  rw [Vd_normalized hc]
  simp only [Real.sin_zero,Real.cos_zero,neg_zero,zero_add,mul_one]
  calc
    c .low t*(R*(ell .low t/c .low t)/root (ell .low t/c .low t) 0)
        ≤c .low t*R*(7/10)/root (7/10) 0 := by simpa only [mul_div_assoc,mul_assoc] using hm
    _≤23/20 := hbound

theorem B_short {R t : ℝ} (hR : 0≤R) (hQU : R^2≤qCap) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤(23/20)*t := by
  have ho := low_order ht
  have hl : 0<ell .low t := by linarith [(low_bounds ht).2.2.2.2.1]
  have hc := ho.1.trans_le (low_bounds ht).2.2.1
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU hl ho.2.2.1 ho.2.2.2.2
  have hd := derivative_reserve
    (f := fun x => -V R (ell .low t) (c .low t) x)
    (df := fun x => -Vd R (ell .low t) (c .low t) x)
    (k := -Vd R (ell .low t) (c .low t) 0)
    (fun x hx => (V_hasDerivAt hl hc hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt hl hc (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le))
    hz (angle ht) ht.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  have hm := mul_le_mul_of_nonneg_right (B_zero_slope ⟨hR,hR2⟩ ht) ht.1
  linarith

theorem B_cap {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) frameCap<18/25 := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have ho := low_order ht
  have hc : 0<c .low t := ho.1.trans_le hkc
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hsmall := normGain_smaller_mono hR.1 hc hh
    ⟨by linarith [ho.2.2.2.2],ho.2.2.1⟩
    (show (673/1000:ℝ)∈Icc (c .low t/2) (c .low t) by constructor <;> linarith) hl1.le
  have hlarge := normGain_larger_mono hR.1 (by norm_num : (0:ℝ)<673/1000)
    (show (673/1000:ℝ)≤c .low t by linarith) hc1.le hh
    (show Real.sin frameCap*(501/500)≤(673/1000:ℝ) by linarith [(transport_trig hh).2.2.2.1])
  have hX2 : (pairNorm (673/1000) (501/500) 0)^2=(673/1000:ℝ)^2+(501/500)^2 := by
    simp only [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hY2 := SoleLowGap.negative_norm_square (by norm_num : (0:ℝ)<673/1000)
    (by norm_num : (0:ℝ)<501/500) hh
  have hX0 : 0≤pairNorm (673/1000) (501/500) 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm (673/1000) (501/500) (-frameCap) := Real.sqrt_nonneg _
  have hX : pairNorm (673/1000) (501/500) 0≤151/125 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) (by rw [hX2]; norm_num)
  have hY : (383/500:ℝ)≤pairNorm (673/1000) (501/500) (-frameCap) := by
    apply le_of_pow_le_pow_left₀ two_ne_zero hY0
    rw [hY2]
    have hs := (transport_trig hh).2.2.2.1
    norm_num at hs ⊢
    linarith
  have hdiff : pairNorm (673/1000) (501/500) 0-
      pairNorm (673/1000) (501/500) (-frameCap)≤221/500 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hR.1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
  have hpen := mul_le_mul (hk0.trans hkc) hclo (by norm_num : (0:ℝ)≤117/500) hc.le
  dsimp [normGain,V] at *
  linarith [hR.2]

theorem wide_dominates {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : SoleLowChargeBounds.base≤p) (hpq : p≤q) (hq : q∈Icc 1 (21/20:ℝ))
    (hnu : nu≤21/20) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤Vnu R p q nu t ∧
      V R (ell .low t) (c .low t) frameCap≤Vnu R p q nu frameCap := by
  have hq' : q∈Icc 1 (28/25:ℝ) := ⟨hq.1,by linarith [hq.2]⟩
  have hn' : nu≤28/25 := by linarith
  have ht' : t∈SoleECoefficients.domain .low := ⟨ht.1,by linarith [ht.2]⟩
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  constructor
  · have hw := SoleLowChargeBounds.wide_short hR hQL hp hpq hq' hn' ht'
    have hB := B_short hR hQU ht
    nlinarith [ht.1]
  · linarith [SoleLowChargeBounds.wide_cap hR hQL hp hpq hq' hn',B_cap ⟨hR,hR2⟩ ht]

end SquaresInCircles.Eight.ExceptionalELowCharges
end
end
end

section
/-!
## A small-total ordinary-angle gap with a fixed coefficient ratio

The whole interval [0,.18] is reduced by derivative
monotonicity to its right endpoint. That endpoint uses positive-sided
circle squaring and the displayed Taylor bounds. Ratio monotonicity
then transfers the gap to every original coefficient pair. No interval
subdivision or sampled scalar input is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalSmallGap
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open OrdinaryNegativeEnvelope VaryingBFunctions VaryingBComparison SoleLowGap

def ratio : ℝ := 117/200
def scale : ℝ := 17253/20000

theorem short_right_slope {R : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) :
    7/10<Vd R ratio 1 (9/50) := by
  have hs : (9/50:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos ratio (sin_mem hs)
  have hN2 := root_sq ratio (sin_mem hs)
  have hsn := (transport_trig hs).2.2.1
  have hNu : root ratio (Real.sin (9/50))≤6/5 := by dsimp [ratio] at *; nlinarith
  have hsu := Real.sin_le (show (0:ℝ)≤9/50 by norm_num)
  have hco := SoleBalancedCoefficients.cosine_quadratic (show (0:ℝ)≤9/50 by norm_num)
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hCpos : 0<Real.cos (9/50:ℝ) := by linarith
  have hnum := mul_lt_mul_of_pos_right hrad hCpos
  have hcross : (7/10+Real.sin (9/50))*root ratio (Real.sin (9/50))<
      R*ratio*Real.cos (9/50) := by
    have hm := mul_le_mul hNu (show 7/10+Real.sin (9/50)≤22/25 by linarith)
      (by linarith : 0≤7/10+Real.sin (9/50)) (by norm_num : (0:ℝ)≤6/5)
    dsimp [ratio] at *
    nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
  simpa only [div_one,one_mul] using (show 7/10< -Real.sin (9/50)+
    R*ratio*Real.cos (9/50)/root ratio (Real.sin (9/50)) by linarith)

theorem right_gap {R : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) :
    (7/10)*(frameCap-9/50)<V R ratio 1 frameCap-V R ratio 1 (9/50) := by
  have hs : (9/50:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hX0 : 0≤pairNorm ratio 1 (-(9/50)) := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm ratio 1 (-frameCap) := Real.sqrt_nonneg _
  have hX2 := negative_norm_square (by norm_num [ratio] : 0<ratio) (by norm_num : (0:ℝ)<1) hs
  have hY2 := negative_norm_square (by norm_num [ratio] : 0<ratio) (by norm_num : (0:ℝ)<1) hh
  have hsu := sin_upper_five (show (0:ℝ)≤9/50 by norm_num)
  have hX : (10643/10000:ℝ)<pairNorm ratio 1 (-(9/50)) := by
    have h2 : (10643/10000:ℝ)^2<(pairNorm ratio 1 (-(9/50)))^2 := by
      rw [hX2]
      norm_num [ratio] at hsu ⊢
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hX0 h2
  have hY : pairNorm ratio 1 (-frameCap)<959/1250 := by
    have h2 : (pairNorm ratio 1 (-frameCap))^2<(959/1250:ℝ)^2 := by
      rw [hY2]
      norm_num [ratio]
      linarith [cap_sin_lower]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h2
  have hgap : (2971/10000:ℝ)<pairNorm ratio 1 (-(9/50))-pairNorm ratio 1 (-frameCap) := by
    linarith
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmul := mul_lt_mul hrad hgap.le (by norm_num : (0:ℝ)<2971/10000) hR
  have hcosh := (transport_trig hh).1
  have hcost := cos_upper_four (show (0:ℝ)≤9/50 by norm_num)
  norm_num at hcost
  have hlhs : (7/10:ℝ)*(frameCap-9/50)=91/250 := by norm_num [frameCap]
  rw [hlhs]
  dsimp only [V]
  linarith

theorem fixed_gap {R t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈Icc 0 (9/50:ℝ)) :
    (7/10)*(frameCap-t)<V R ratio 1 frameCap-V R ratio 1 t := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap] at *; linarith [ht.2]⟩
  have hr : (9/50:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU (by norm_num [ratio] : 0<ratio)
    (by norm_num [ratio] : ratio≤1) (by norm_num [ratio] : (1:ℝ)≤2*ratio)
  have hlow (s : ℝ) (hs : s∈Icc 0 (9/50:ℝ)) : 7/10≤Vd R ratio 1 s :=
    (short_right_slope hR hQL).le.trans
      (hanti ⟨hs.1,hs.2.trans hr.2⟩ hr hs.2)
  have hd := derivative_reserve
    (f := V R ratio 1) (df := Vd R ratio 1) (k := 7/10)
    (fun s hs => (V_hasDerivAt (by norm_num [ratio]) (by norm_num)
      ⟨hs.1,hs.2.trans hr.2⟩).continuousAt.continuousWithinAt)
    (fun s hs => V_hasDerivAt (by norm_num [ratio]) (by norm_num)
      ⟨hs.1.le,hs.2.le.trans hr.2⟩)
    (fun s hs => hlow s (Ioo_subset_Icc_self hs)) ht (by norm_num) ht.2
  have he := right_gap hR hQL
  linarith

theorem derivative_ratio {R p q s : ℝ} (hR : 0≤R) (hq : 0<q)
    (hpq : p≤q) (hratio : ratio*q≤p) (hs : s∈Icc 0 frameCap) :
    q*Vd R ratio 1 s≤Vd R p q s := by
  have hrlo : ratio≤p/q := (le_div_iff₀ hq).2 hratio
  have hrhi : p/q≤1 := (div_le_one hq).2 hpq
  have hf := normalized_fraction_mono (by norm_num [ratio] : 0≤ratio) hrlo hrhi (sin_mem hs)
  have hc : 0≤Real.cos s := by linarith [(transport_trig hs).1]
  have hm := mul_le_mul_of_nonneg_left hf (mul_nonneg hR hc)
  have hm' := mul_le_mul_of_nonneg_left hm hq.le
  rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
  simp only [div_one,one_mul]
  have e1 : R*ratio*Real.cos s/root ratio (Real.sin s)=
      R*Real.cos s*(ratio/root ratio (Real.sin s)) := by ring
  have e2 : R*(p/q)*Real.cos s/root (p/q) (Real.sin s)=
      R*Real.cos s*(p/q/root (p/q) (Real.sin s)) := by ring
  rw [e1,e2]
  linarith

theorem scaled_gap {R p q t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hq : scale≤q) (hpq : p≤q) (hratio : ratio*q≤p) (ht : t∈Icc 0 (9/50:ℝ)) :
    scale*(7/10)*(frameCap-t)<V R p q frameCap-V R p q t := by
  have hq0 : 0<q := by dsimp [scale] at hq; linarith
  have hp : 0<p := by dsimp [ratio] at hratio; nlinarith
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd := derivative_reserve
    (f := fun s => V R p q s-q*V R ratio 1 s)
    (df := fun s => Vd R p q s-q*Vd R ratio 1 s) (k := 0)
    (fun s hs => ((V_hasDerivAt hp hq0 hs).sub
      ((V_hasDerivAt (by norm_num [ratio]) (by norm_num) hs).const_mul q)).continuousAt.continuousWithinAt)
    (fun s hs => (V_hasDerivAt hp hq0 (Ioo_subset_Icc_self hs)).sub
      ((V_hasDerivAt (by norm_num [ratio]) (by norm_num) (Ioo_subset_Icc_self hs)).const_mul q))
    (fun s hs => sub_nonneg.mpr (derivative_ratio hR hq0 hpq hratio (Ioo_subset_Icc_self hs)))
    ht' hh ht'.2
  have hbase := mul_lt_mul_of_pos_left (fixed_gap hR hQL hQU ht) hq0
  have hlen : 0≤(7/10)*(frameCap-t) := by dsimp [frameCap]; nlinarith [ht.2]
  have hm := mul_le_mul_of_nonneg_right hq hlen
  nlinarith

end SquaresInCircles.Eight.ExceptionalSmallGap
end
end
end

section
/-!
## Ordinary-angle growth of the positive-T contact families

The growth bounds are the chord of fixed ratio on the low family (`low_growth`), the balanced and
one-angle slopes on the middle family (`balanced_growth`, `middle_A_growth`), and the quartic of
ratio `0.71` on the high family (`high_growth`). The actual negative coefficient is kept until its
scalar comparison, and every transfer of derivatives uses the radius `R` of the cycle.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTGrowth
open Polynomial

def lowerRadius : ℚ := 19787/10000

open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryAngleConcentration OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem radius_le {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) :
    (lowerRadius:ℝ)≤R := by
  have h := SoleAngleGrowth.radius_lower hR hQ
  have e : ((lowerRadius:ℚ):ℝ)=19787/10000 := by norm_num [lowerRadius]
  linarith

theorem ratio_square {r : ℝ} (hr : r∈Icc (71/100:ℝ) 1) :
    (13/250:ℝ)<(lowerRadius:ℝ)^2*r^2*(478/625)^2-
      (r+6443/10000)^2*(1+r^2-2*r*(3221/5000)) := by
  have h1 : 0≤r-71/100 := sub_nonneg.2 hr.1
  have h2 : 0≤1-r := sub_nonneg.2 hr.2
  rw [show (lowerRadius:ℝ)=19787/10000 by norm_num [lowerRadius]]
  linarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h1) h2,
    mul_nonneg (mul_nonneg (mul_nonneg h1 h1) h2) (by linarith : (0:ℝ)≤r)]

theorem normalized_high_slope {R r : ℝ}
    (hR : 0≤R) (hQ : qLow≤R^2) (hr : r∈Icc (71/100:ℝ) 1) :
    r< -Real.sin frameCap+R*r*Real.cos frameCap/root r (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := transport_trig hh
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0<r := by linarith [hr.1]
  have hS : Real.sin frameCap≤6443/10000 := hs.2.2.2.1.le
  have hC : (478/625:ℝ)≤Real.cos frameCap := by linarith [hs.1]
  have hD : (root r (Real.sin frameCap))^2≤
      1+r^2-2*r*(3221/5000) := by
    nlinarith [mul_le_mul_of_nonneg_left cap_sin_lower.le hr0.le]
  have hDmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (r+6443/10000))
  have hpoly := ratio_square hr
  have hcross0 : (r+6443/10000)*root r (Real.sin frameCap)<
      (lowerRadius:ℝ)*r*(478/625) := by
    have hp : 0≤(lowerRadius:ℝ)*r*(478/625) := by
      exact mul_nonneg (mul_nonneg (by norm_num [lowerRadius]) hr0.le) (by norm_num)
    nlinarith
  have hleft := mul_le_mul_of_nonneg_right
    (by linarith : r+Real.sin frameCap≤r+6443/10000) hN.le
  have hright := mul_le_mul
    (mul_le_mul_of_nonneg_right (radius_le hR hQ) hr0.le) hC
    (by norm_num : (0:ℝ)≤478/625) (mul_nonneg hR hr0.le)
  have hcross : (r+Real.sin frameCap)*root r (Real.sin frameCap)<
      R*r*Real.cos frameCap := hleft.trans_lt (hcross0.trans_le hright)
  linarith [(lt_div_iff₀ hN).2 hcross]

theorem Vd_gt_smaller {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (71/100)*q≤p)
    (ht : t∈Icc 0 frameCap) : p<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (71/100:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 hratio,(div_le_one hq).2 hpq⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hbase := mul_lt_mul_of_pos_left (normalized_high_slope hR hQL hr) hq
  have hcancel : q*(p/q)=p := by field_simp [hq.ne']
  rw [hcancel,← Vd_normalized hq] at hbase
  exact hbase.trans_le ((Vd_antitone hR hQU hp hpq (by linarith)) ht hh ht.2)

theorem VnuDeriv_antitone {R p q nu : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) :
    AntitoneOn (VnuDeriv R p q nu) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro x hx
    exact (VnuDeriv_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt
  · intro x hx
    exact VnuDeriv_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx)
  · intro x hx
    linarith [Vnu_second_lt hR hQU hp hpq hqp hnu (Ioo_subset_Icc_self hx)]

theorem VnuDeriv_ge_Vd {R p q nu t : ℝ} (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) : Vd R p q t≤VnuDeriv R p q nu t := by
  have h := mul_le_mul_of_nonneg_right hnu (transport_trig ht).2.2.1
  dsimp [Vd,mixedNDerivative,VnuDeriv]
  simp only [zero_sub]
  linarith

theorem high_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (71/100)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    p*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hu htu
  exact (Vd_gt_smaller hR hQL hQU hp hpq hratio (Ioo_subset_Icc_self hx)).le.trans
    (VnuDeriv_ge_Vd hnu (Ioo_subset_Icc_self hx))

theorem low_growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (117/200)*q≤p)
    (hq : 431/500≤q) (hnu : nu≤q) (ht : t∈Icc 0 (9/50:ℝ)) :
    (431/500)*(7/10)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have hq0 := hp.trans_le hpq
  have hbase := ExceptionalSmallGap.fixed_gap hR hQL hQU ht
  have hlen : 0≤frameCap-t := by dsimp [frameCap]; linarith [ht.2]
  have hpositive : 0≤V R (117/200) 1 frameCap-V R (117/200) 1 t := by
    dsimp [ExceptionalSmallGap.ratio] at hbase
    simp only [frameCap] at hbase hlen ⊢
    linarith
  have hscale := mul_le_mul_of_nonneg_right hq hpositive
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have htransfer := derivative_reserve
    (f:=fun s => Vnu R p q nu s-q*V R (117/200) 1 s)
    (df:=fun s => VnuDeriv R p q nu s-q*Vd R (117/200) 1 s) (k:=0)
    (fun s hs => ((Vnu_hasDerivAt hp hq0 hs).sub
      ((V_hasDerivAt (by norm_num) (by norm_num) hs).const_mul q)).continuousAt.continuousWithinAt)
    (fun s hs => (Vnu_hasDerivAt hp hq0 (Ioo_subset_Icc_self hs)).sub
      ((V_hasDerivAt (by norm_num) (by norm_num) (Ioo_subset_Icc_self hs)).const_mul q))
    (fun s hs => sub_nonneg.mpr
      ((ExceptionalSmallGap.derivative_ratio hR hq0 hpq hratio (Ioo_subset_Icc_self hs)).trans
        (VnuDeriv_ge_Vd hnu (Ioo_subset_Icc_self hs))))
    ht' (by norm_num [frameCap]) ht'.2
  dsimp [ExceptionalSmallGap.ratio] at hbase
  nlinarith

def balancedPolynomial : ℚ[X] :=
  C (lowerRadius^2*(2/3)^2)*(1-X^2)-
    (X+C (337/500))^2*(C (1+(2/3)^2)-C (4/3)*X)
private theorem r54_balanced_explicit : balancedPolynomial=
    C (81295223/75000000)+C (-754543/562500)*X+C (-312125369/225000000)*X^2+C (4/3)*X^3 := by
  apply Polynomial.funext
  intro r
  simp only [balancedPolynomial,lowerRadius,eval_sub,eval_mul,eval_C,eval_pow,eval_add,eval_X,
    eval_one]
  ring
private theorem r54_balanced_coeff (j : ℕ) : balancedPolynomial.coeff j=
    if j=0 then 81295223/75000000 else if j=1 then -754543/562500 else
      if j=2 then -312125369/225000000 else if j=3 then 4/3 else 0 := by
  rw [r54_balanced_explicit]
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X]
  rcases j with _ | _ | _ | _ | j <;> simp
theorem balanced_identity : balancedPolynomial=
    WholeIntervalBernstein.expansion 3 (6443/10000) balancedPolynomial := by
  apply Polynomial.funext
  intro r
  simp only [WholeIntervalBernstein.expansion,WholeIntervalBernstein.coefficient,
    WholeIntervalBernstein.basis,r54_balanced_coeff,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.val_zero,Fin.val_succ,zero_add,Finset.sum_range_succ,Finset.sum_range_zero,add_zero]
  rw [r54_balanced_explicit]
  simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X,eval_sub]
  norm_num [Nat.choose]
  ring
theorem balanced_partition :
    (∑i : Fin 4,WholeIntervalBernstein.basis 3 (6443/10000) i)=1 := by
  apply Polynomial.funext
  intro r
  simp only [WholeIntervalBernstein.basis,Fin.sum_univ_four,eval_add,eval_mul,eval_C,eval_pow,
    eval_X,eval_sub,eval_one,Fin.val_zero,Fin.val_one,Fin.val_two,Fin.isValue]
  norm_num [Nat.choose]
  ring
theorem balanced_reserve (i : Fin 4) :
    (1/100000:ℚ)≤WholeIntervalBernstein.coefficient 3 (6443/10000) balancedPolynomial i := by
  fin_cases i <;>
    simp only [WholeIntervalBernstein.coefficient,r54_balanced_coeff,Finset.sum_range_succ,
      Finset.sum_range_zero] <;>
    norm_num [Nat.choose]

theorem balanced_normalized {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (337/500:ℝ)< -Real.sin s+(lowerRadius:ℝ)*(2/3)*Real.cos s/
      root (2/3) (Real.sin s) := by
  have hsin : Real.sin s∈Icc (0:ℝ) (6443/10000) :=
    ⟨(transport_trig hs).2.2.1,(transport_trig hs).2.2.2.1.le⟩
  have hpoly := WholeIntervalBernstein.lower_on_interval (by norm_num)
    balanced_identity balanced_partition balanced_reserve (x := Real.sin s) (by simpa using hsin)
  have hN := root_pos (2/3) (sin_mem hs)
  have hN2 := root_sq (2/3) (sin_mem hs)
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcross : (337/500+Real.sin s)*root (2/3) (Real.sin s)<
      (lowerRadius:ℝ)*(2/3)*Real.cos s := by
    norm_num [balancedPolynomial,lowerRadius] at hpoly
    have hright : 0<(lowerRadius:ℝ)*(2/3)*Real.cos s := by
      exact mul_pos (by norm_num [lowerRadius]) hcos
    have hB2 : ((337/500+Real.sin s)*root (2/3) (Real.sin s))^2=
        (Real.sin s+337/500)^2*(13/9-4/3*Real.sin s) := by
      rw [mul_pow,hN2]
      ring
    have hA2 : ((lowerRadius:ℝ)*(2/3)*Real.cos s)^2=
        391525369/225000000*(1-Real.sin s^2) := by
      rw [mul_pow,Real.cos_sq']
      norm_num [lowerRadius]
    nlinarith [hA2,hB2,hpoly,hright]
  linarith [(lt_div_iff₀ hN).2 hcross]

theorem balanced_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (337/500)*q*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  have hq := hp.trans_le hpq
  have hbase := derivative_reserve
    (f:=V (lowerRadius:ℝ) (2/3) 1) (df:=Vd (lowerRadius:ℝ) (2/3) 1)
    (k:=337/500)
    (fun x hx => (V_hasDerivAt (by norm_num) (by norm_num) hx).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt (by norm_num) (by norm_num) (Ioo_subset_Icc_self hx))
    (fun x hx => by
      rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
      simpa only [div_one,one_mul] using (balanced_normalized (Ioo_subset_Icc_self hx)).le)
    ht hu htu
  have hscale := mul_le_mul_of_nonneg_left hbase hq.le
  have htransfer := SolePositiveTGrowth.normalized_growth (radius_le hR hQL) hp hpq
    (by norm_num : (0:ℝ)<2/3) hratio hnu ht hu htu
  have e : ((SolePositiveTGrowth.lowerRadius:ℚ):ℝ)=(lowerRadius:ℝ) := by
    norm_num [SolePositiveTGrowth.lowerRadius,lowerRadius]
  rw [e] at htransfer
  nlinarith

theorem middle_A_endpoint {R p q : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 159/250≤p) (hq : 0<q) (hr : p/q∈Icc (31/50:ℝ) (203/250)) :
    (4/5:ℝ)<VnuDeriv R p q p frameCap := by
  let r : ℝ := p/q
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0≤r := by dsimp [r]; linarith [hr.1]
  have hproduct := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hsin := mul_le_mul_of_nonneg_left cap_sin_lower.le hr0
  have hNupper : root r (Real.sin frameCap)≤393/500 := by
    have hsq : (root r (Real.sin frameCap))^2≤(393/500)^2 := by
      dsimp only [r] at hN2 hsin hr0 ⊢
      nlinarith [hproduct,hr.2]
    nlinarith [hN]
  have hc : (478/625:ℝ)≤Real.cos frameCap := by linarith [(transport_trig hh).1]
  have hs := (transport_trig hh).2.2.2.1.le
  have hnum : (lowerRadius:ℝ)*(478/625)≤R*Real.cos frameCap :=
    mul_le_mul (radius_le hR hQL) hc (by norm_num) hR
  let k : ℝ := (lowerRadius:ℝ)*(478/625)/(393/500)
  have hk0 : 0≤k := by norm_num [k,lowerRadius]
  have hprod := mul_le_mul_of_nonneg_left hNupper hk0
  have hfraction : k≤R*Real.cos frameCap/root r (Real.sin frameCap) := by
    apply (le_div_iff₀ hN).2
    dsimp [k] at hprod ⊢
    nlinarith
  have hbracket : k-6443/10000≤
      -Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap) := by linarith
  have hpositive : 0≤k-6443/10000 := by norm_num [k,lowerRadius]
  have hmul := mul_le_mul hp hbracket hpositive (by linarith : 0≤p)
  have hreserve : (4/5:ℝ)<(159/250)*(k-6443/10000) := by norm_num [k,lowerRadius]
  have he : VnuDeriv R p q p frameCap=
      p*(-Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap)) := by
    dsimp [VnuDeriv,normD1,pairProduct,r]
    rw [Real.cos_neg,negativeNorm_normalized hq]
    field_simp [hq.ne']
  rw [he]
  exact hreserve.trans_le hmul

theorem middle_A_growth {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 159/250≤p) (hpq : p≤q) (hr : p/q∈Icc (31/50:ℝ) (203/250))
    (ht : t∈Icc 0 frameCap) :
    (4/5)*(frameCap-t)≤Vnu R p q p frameCap-Vnu R p q p t := by
  have hp0 : 0<p := by linarith
  have hq := hp0.trans_le hpq
  have hqp : q≤2*p := by
    have hh := (le_div_iff₀ hq).1 hr.1
    nlinarith
  have hanti := VnuDeriv_antitone hR hQU hp0 hpq hqp (le_refl p)
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp0 hq hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp0 hq (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hh ht.2
  exact (middle_A_endpoint hR hQL hp hq hr).le.trans
    (hanti (Ioo_subset_Icc_self hx) hh hx.2.le)

theorem low_same_block {R p q t : ℝ} (hq : 0≤q)
    (hr : (117/200+1/5*t)*q≤p) (ht : t∈Icc 0 (9/50:ℝ)) :
    V R p q t≤OrdinaryAngleConcentration.M R p q t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  apply SolePositiveTSameBlock.from_bracket hq hr ht'
  apply SolePositiveTSameBlock.half_angle_bracket ht' (by linarith [ht.2])
  have hm := mul_le_mul_of_nonneg_right hc.le
    (show 0≤frameCap-t by linarith [ht'.2])
  dsimp [frameCap] at *
  nlinarith [sq_nonneg t,ht.1,ht.2]

end SquaresInCircles.Eight.ExceptionalPositiveTGrowth
end
end
end

section
/-!
## The complete outside-strip ordinary envelope at arbitrary EH contact

The full original signed domain is concentrated
before any scalar coefficient is enlarged. H and TD B are the only
possible mixed blocks. Their same-block alternatives and every
separated alternative dominate their respective pure charge at t.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTEnvelope
open ExceptionalPositiveTScalarModel ExceptionalPositiveTCoefficients
open ExceptionalPositiveTOrdinaryData ExceptionalPositiveTGrowth
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

theorem growth_pays (s : ScalarCase) {R t z : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    (109/200)*(cap s.family:ℝ)*(frameCap-t)≤
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) frameCap-
        pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [pure_eq,pure_eq]
  have hp := small_pos s ht hz i
  have hpq := small_le_large s t z i
  have hq := hp.trans_le hpq
  have hnu := (nu_between s t z i).2
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤ small s t z i at hr
  have hlo := larger_lower s ht hz i
  change (largeFloor s.family:ℝ)≤large s t z i at hlo
  have hsmall := smaller_lower s ht hz i
  change (smallFloor s.family i:ℝ)≤ small s t z i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  cases hf : s.family
  · have hratio : (117/200)*large s t z i≤ small s t z i := by
      simp [ratio,hf] at hr
      split_ifs at hr <;> nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (9/50:ℝ) := by
      simp [domain,hf,left,right] at ht
      exact ⟨ht'.1,by linarith [ht.2]⟩
    have hg := low_growth hR hQL hQU hp hpq hratio
      (by simpa [largeFloor,hf] using hlo) hnu htg
    have hc : (109/200)*(cap s.family:ℝ)≤(431/500)*(7/10) := by norm_num [cap,hf]
    rw [hf] at hc
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (117/200)*large s t z i≤ small s t z i := by
      simp [ratio,hf] at hr
      split_ifs at hr <;> nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (9/50:ℝ) := by
      simp [domain,hf,left,right] at ht
      exact ⟨ht'.1,ht.2⟩
    have hg := low_growth hR hQL hQU hp hpq hratio
      (by simpa [largeFloor,hf] using hlo) hnu htg
    have hc : (109/200)*(cap s.family:ℝ)≤(431/500)*(7/10) := by norm_num [cap,hf]
    rw [hf] at hc
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := middle_A_data s hf ht hz
      have hd := middle_A s hf ht hz
      have hg := middle_A_growth hR hQL hQU hd.1
        (by rw [← hs,← hl]; exact hpq) hrA ht'
      rw [hs,hl,hn]
      have hc : (109/200)*(cap s.family:ℝ)≤4/5 := by norm_num [cap,hf]
      rw [hf] at hc
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (2/3)*large s t z 2≤ small s t z 2 := by simpa [ratio,hf] using hr
        have hg := balanced_growth hR hQL hp hpq hratio hnu ht' hh ht'.2
        have hfloor : (911/1000:ℝ)≤large s t z 2 := by simpa [largeFloor,hf] using hlo
        have hc : (109/200)*(cap s.family:ℝ)≤(337/500)*large s t z 2 := by
          norm_num [cap,hf]
          nlinarith
        rw [hf] at hc
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (71/100)*large s t z i≤ small s t z i := by
          simpa [ratio,hf,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hfloor : (911/1000:ℝ)≤ small s t z i := by
          simpa [smallFloor,hf,hi] using hsmall
        have hc : (109/200)*(cap s.family:ℝ)≤ small s t z i := by norm_num [cap,hf]; linarith
        rw [hf] at hc
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (71/100)*large s t z i≤ small s t z i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hfloor : (731/1000:ℝ)≤ small s t z i := by simpa [smallFloor,hf] using hsmall
    have hc : (109/200)*(cap s.family:ℝ)≤ small s t z i := by norm_num [cap,hf]; linarith
    rw [hf] at hc
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg

theorem same_block (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : single s i=false) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t≤
      M R (small s t z i) (large s t z i) t := by
  simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte]
  have hp := small_pos s ht hz i
  have hq := hp.trans_le (small_le_large s t z i)
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤ small s t z i at hr
  have hindices : i=0 ∨ i=2 := by
    fin_cases i <;> simp_all [single,ExceptionalPositiveTBlocks.single]
  have ht' := angle ht
  rcases hindices with rfl | rfl
  · apply M_ge_V hp.le hq.le _ (angle ht)
    cases hf : s.family <;> simp [ratio,hf] at hr <;> nlinarith
  · cases hf : s.family
    · apply low_same_block hq.le (by simpa [ratio,hf] using hr)
      simp [domain,hf,left,right] at ht
      exact ⟨ht'.1,by linarith [ht.2]⟩
    · apply low_same_block hq.le (by simpa [ratio,hf] using hr)
      simp [domain,hf,left,right] at ht
      exact ⟨by linarith [ht.1],ht.2⟩
    · apply M_ge_V hp.le hq.le _ (angle ht)
      simp [ratio,hf] at hr
      linarith
    · apply M_ge_V hp.le hq.le _ (angle ht)
      simp [ratio,hf] at hr
      nlinarith

theorem original_increment {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R t z L : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (ha : ∀ i,|Candidate.delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤Candidate.delta C.theta Candidate.G) (hD : 0≤Candidate.delta C.theta Candidate.D)
    (hT : 0≤ExceptionalPositiveTStress.primary C s.td)
    (htotal : Candidate.delta C.theta Candidate.G+Candidate.delta C.theta Candidate.D+ExceptionalPositiveTStress.primary C s.td=t)
    (hpure : ∀ i,L≤pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t) :
    L≤ExceptionalPositiveTBlocks.increment C ab s.td (weights s t z) R := by
  have hhalf (i : Fin 4) : large s t z i≤2*small s t z i := half_ratio s ht hz i
  apply ExceptionalPositiveTBlocks.original_lower s.td (weights s t z) hab hR hQU
    (small_pos s ht hz) hhalf ha hvar hG hD hT htotal hpure
  · intro i hi
    exact (hpure i).trans (same_block s ht hz i hi)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [(angle ht).2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (small_pos s ht hz i)
      (small_le_large s t z i) (hhalf i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [(angle ht).1]⟩)
    have hV := growth_pays s hR hQL hQU ht hz j
    have hcap := pair_upper s ht hz i
    change large s t z i≤(cap s.family:ℝ) at hcap
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤109/200)) hlen
    have hj := hpure j
    show L≤U R (small s t z i) (large s t z i) (frameCap-t)+
      SingleAngleConcavity.pure (single s j) R (small s t z j) (large s t z j) (actualNu s t z j)
        frameCap
    simp only [frameCap] at hU hV hpay hlen ⊢
    linarith

end SquaresInCircles.Eight.ExceptionalPositiveTEnvelope
end
end
end

section
/-!
## Actual positive-T exceptional-contact exclusion outside the sharp strip

Both complete fixed-z faces use the same original
coordinates and the same arbitrary EH contact. Their strict scalar
reserve and the concave G/E split contradict the original seven weak
witnesses at the actual common ceiling. No radial assumption is used.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTOutside
open Candidate ExceptionalPositiveTScalarModel ExceptionalPositiveTOrdinaryData
open ExceptionalContactStress PositiveAngularEnvelope

theorem baseline_eq (s : ScalarCase) (R t z : ℝ) :
    baseline s R t z=ExceptionalPositiveTStress.baseline s.td R
      (k s.family t z) (ell s.family t z) (c s.family t z) (eta s.family t)
      z (x s t z) (ExceptionalPositiveTScalarModel.e s t z) := by
  simp [baseline,ExceptionalPositiveTStress.baseline,SoleEStress.zeroNorms,
    first,second,n,m,p,ExceptionalPositiveTStress.bWeight,ExceptionalPositiveTStress.tWeight,
    Fin.sum_univ_succ,add_assoc]

theorem increment_eq (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (R t z : ℝ) :
    ExceptionalPositiveTBlocks.increment C ab s.td (weights s t z) R=
      ExceptionalPositiveTStress.increment C ab s.td R
        (k s.family t z) (ell s.family t z) (c s.family t z) (eta s.family t)
        z (x s t z) (ExceptionalPositiveTScalarModel.e s t z) := rfl

theorem endpoint_positive {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {q t z : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hsource : ExceptionalPositiveTStress.primary C s.td=z)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hT : 0≤ExceptionalPositiveTStress.primary C s.td)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C s.td=t)
    (hcontact : Contact C) :
    0<ExceptionalPositiveTStress.value C ab s.td (Real.sqrt q)
      (k s.family t z) (ell s.family t z) (c s.family t z) (eta s.family t)
      t z (x s t z) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR2 := Real.sq_sqrt hq0
  have hR := Real.sqrt_nonneg q
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRL : qLow≤(Real.sqrt q)^2 := by simpa only [hR2] using hQL
  have hRU : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hpure (i : Fin 4) : 77/1000000-baseline s (Real.sqrt q) t z≤
      SingleAngleConcavity.pure (single s i) (Real.sqrt q) (small s t z i) (large s t z i)
        (actualNu s t z i) t := by
    have hs := ExceptionalPositiveTScalar.actual_radius_positive (charged s t z i) hQU ht hz
    have hl := pure_scalar_lower s (R:=Real.sqrt q) ht hz i
    linarith
  have hi := ExceptionalPositiveTEnvelope.original_increment s hab hR hRL hRU ht hz
    ha hvar hG hD hT htotal hpure
  have hx : x s t z∈Icc 0 (t-z) := by
    cases h : s.atG <;> simp [x,h] <;> linarith [hz.2]
  have he : t-z-x s t z=ExceptionalPositiveTScalarModel.e s t z := by
    cases h : s.atG <;> simp [x,ExceptionalPositiveTScalarModel.e,h]
  have hl := ExceptionalPositiveTSupport.value_lower s.td hab hR
    (coefficient_positive ht hz).2.2.2 (angle ht) hz hx hsource hC.sorted hc hn ha hcontact
    (k:=k s.family t z) (l:=ell s.family t z) (c:=c s.family t z)
  rw [he,← baseline_eq,← increment_eq] at hl
  linarith

def choose (t : ℝ) : Family :=
  if t≤1/10 then .lowZero else if t≤9/50 then .lowAfter else if t≤7/20 then .middle else .high
theorem choose_mem {t : ℝ} (ht : t∈Icc 0 frameCap) (houtside : t≤1/10 ∨ 4/25≤t) :
    t∈domain (choose t) := by
  have h2 : t≤7/10 := ht.2
  dsimp [choose]
  split_ifs <;> norm_num [domain,left,right] <;> constructor <;>
    rcases houtside with h | h <;> linarith [ht.1,h2]

theorem original_false {C : SignedCycle} {ab : Fin 4} (td : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hT : 0≤ExceptionalPositiveTStress.primary C td) (hEy : 0≤(C.point E).y)
    (hcontact : Contact C)
    (houtside : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td≤1/10 ∨
      4/25≤delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab
      (ExceptionalPositiveTStress.btOwner td) (ExceptionalPositiveTStress.tdOwner td) 3 0 i)) : False := by
  let z := ExceptionalPositiveTStress.primary C td
  let t := delta C.theta G+delta C.theta D+z
  let f := choose t
  have htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t := rfl
  have htcap := (ExceptionalPositiveTBlocks.original_budgets hab td
    ⟨0,0,0,0,0,0⟩ hvar hG hD hT htotal).1
  have ht : t∈domain f := choose_mem htcap houtside
  have hz : z∈Icc 0 t := ⟨hT,by dsimp [t]; linarith⟩
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by dsimp [t]; linarith⟩
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hweights := coefficient_positive ht hz
  have hsplit := split_bounds ht hz
  have hconc := ExceptionalPositiveTStress.concave ab td hR hRsq hsplit.1 hsplit.2 htcap hz
    hC.sorted hcCap ha hEy (l:=ell f t z) (c:=c f t z)
  have h0 : 0<ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (k f t z) (ell f t z) (c f t z) (eta f t) t z 0 := by
    have hh := endpoint_positive (C:=C) (ab:=ab) ⟨f,td,false,0,false⟩ hab hQL hQU ht hz rfl
      hC hn hvar hG hD hT htotal hcontact
    simpa only [x,Bool.false_eq_true,ite_false] using hh
  have h1 : 0<ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (k f t z) (ell f t z) (c f t z) (eta f t) t z (t-z) := by
    have hh := endpoint_positive (C:=C) (ab:=ab) ⟨f,td,true,0,false⟩ hab hQL hQU ht hz rfl
      hC hn hvar hG hD hT htotal hcontact
    simpa only [x,ite_true] using hh
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (t-z) from ⟨le_rfl,by linarith [hz.2]⟩)
    (show t-z∈Icc 0 (t-z) from ⟨by linarith [hz.2],le_rfl⟩) hx
  have hpos := (lt_min h0 h1).trans_le hmin
  have hnec := ExceptionalPositiveTStress.necessary td hab hR hweights.1.le
    hweights.2.1.le hweights.2.2.1.le hweights.2.2.2 htcap hz rfl hG hD
    (by simpa only [z] using htotal) hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.ExceptionalPositiveTOutside
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalELowEnvelope
open Candidate ExceptionalECoefficients ExceptionalContactStress ExceptionalContactBlocks
open ExceptionalELowCharges PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration SingleAngleConcavity

theorem AB_data {t x e : ℝ} (ht : t∈domain .low) :
    small (k .low t) (ell .low t) (c .low t) (eta .low t) x e 1=ell .low t ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e 1=k .low t ∧
    small (k .low t) (ell .low t) (c .low t) (eta .low t) x e 2=ell .low t ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e 2=c .low t := by
  have ho := low_order ht
  simp [small,large,ExceptionalContactBlocks.alpha,ExceptionalContactBlocks.beta,min_eq_left ho.2.1,max_eq_right ho.2.1,
    min_eq_left ho.2.2.1,max_eq_right ho.2.2.1]

theorem wide_data {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) {i : Fin 4} (hi : i=0 ∨ i=3) :
    SoleLowChargeBounds.base≤ small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i∈Icc 1 (21/20:ℝ) := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  obtain ⟨hx0,hx1⟩ := low_tilt ht hx
  obtain ⟨he0',he1'⟩ := low_tilt ht he
  have hkpos := (low_order ht).1
  have hn0 := mul_le_mul_of_nonneg_left hx0 hkpos.le
  have hn1 := mul_lt_mul_of_pos_left hx1 hkpos
  have hn : k .low t*tilt (eta .low t) x≤21/20 := by nlinarith
  rcases hi with rfl | rfl
  · change SoleLowChargeBounds.base≤ min (tilt (eta .low t) e) (k .low t*tilt (eta .low t) x) ∧
      max (tilt (eta .low t) e) (k .low t*tilt (eta .low t) x)∈Icc 1 (21/20:ℝ)
    exact ⟨le_min (by dsimp [SoleLowChargeBounds.base]; linarith)
      (by dsimp [SoleLowChargeBounds.base]; nlinarith),
      he0'.trans (le_max_left _ _),max_le he1'.le hn⟩
  · change SoleLowChargeBounds.base≤ min 1 (c .low t) ∧ max 1 (c .low t)∈Icc 1 (21/20:ℝ)
    exact ⟨le_min (by norm_num [SoleLowChargeBounds.base])
      (by dsimp [SoleLowChargeBounds.base]; linarith),
      le_max_left _ _,max_le (by norm_num) (by linarith)⟩

theorem coefficient_conditions {t x e : ℝ} (ht : t∈domain .low)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    0<small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i≤
      2*small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i ∧
    large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i≤21/20 := by
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have ho := low_order ht
  have hp := small_pos (l := ell .low t) ho.1 (by linarith) (ho.1.trans_le hkc) (tilt_pos ht hx) (tilt_pos ht he) i
  refine ⟨hp,?_⟩
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hh := wide_data ht hx he (Or.inl rfl)
    dsimp [SoleLowChargeBounds.base] at hh
    constructor <;> linarith [hh.1,hh.2.2]
  · obtain ⟨ha,hA,_,_⟩ := AB_data (x := x) (e := e) ht
    rw [ha,hA]
    constructor <;> linarith
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) ht
    rw [hb,hB]
    exact ⟨ho.2.2.2.2,by linarith⟩
  · have hh := wide_data ht hx he (Or.inr rfl)
    dsimp [SoleLowChargeBounds.base] at hh
    constructor <;> linarith [hh.1,hh.2.2]

theorem pure_dominates {R t x e : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R (ell .low t) (c .low t) t≤
      pure (single i) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) t ∧
    V R (ell .low t) (c .low t) frameCap≤
      pure (single i) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hw := wide_data ht hx he (Or.inl rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large _ _ _ _ _ _ 0) hw.2 hw.2.2 ht
    exact hh
  · obtain ⟨ha,hA,_,_⟩ := AB_data (x := x) (e := e) ht
    rw [ha,hA]
    exact ⟨A_ge_B ⟨hR,hR2⟩ ht,A_ge_B_at_cap ⟨hR,hR2⟩ ht⟩
  · obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) ht
    rw [hb,hB]
    exact ⟨le_rfl,le_rfl⟩
  · have hw := wide_data ht hx he (Or.inr rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large _ _ _ _ _ _ 3) hw.2 hw.2.2 ht
    exact hh

theorem same_block_dominates {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (i : Fin 4) (hi : single i=false) :
    V R (ell .low t) (c .low t) t≤
      M R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) t := by
  by_cases hB : i=2
  · subst i
    obtain ⟨_,_,hb,hB⟩ := AB_data (x := x) (e := e) ht
    rw [hb,hB]
    have hc : 0≤c .low t := (low_order ht).1.le.trans (low_bounds ht).2.2.1
    have hratio : PositiveStressCoefficients.ratio t*c .low t≤ell .low t := by
      have hh := (low_correlations ht).1
      dsimp [PositiveStressCoefficients.ratio]
      nlinarith [mul_nonneg ht.1 hc]
    have hh := CorrelatedSameBlock.negative_surplus (R := R) hc hratio (angle ht)
      (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
    have hid : mixedBlock R (ell .low t) (c .low t) (frameCap-t) frameCap=
        M R (ell .low t) (c .low t) t := by
      simpa only [show t+(frameCap-t)=frameCap by ring] using mixedBlock_saturated R (ell .low t) (c .low t) t
    simpa only [sub_zero,hid] using hh
  · have hiw : i=0 ∨ i=3 := by fin_cases i <;> simp_all [single]
    have hw := wide_data ht hx he hiw
    have hp := (coefficient_conditions ht hx he i).1
    have hpq := small_le_large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i
    have hratio : large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i≤
        (3/2)*small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i := by
      dsimp [SoleLowChargeBounds.base] at hw
      linarith [hw.1,hw.2.2]
    have hM := M_ge_V (R := R) hp.le (hp.trans_le hpq).le hratio (angle ht)
    have hV := (pure_dominates hR hQL hQU ht hx he i).1
    simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte] at hV
    exact hV.trans hM

theorem separated_dominates {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i j : Fin 4) :
    V R (ell .low t) (c .low t) t<
      U R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) (frameCap-t)+
      pure (single j) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e j)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e j)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e j) frameCap := by
  have hi := coefficient_conditions ht hx he i
  have hlen : 0≤frameCap-t := by dsimp [frameCap]; linarith [ht.2]
  have hU := OrdinaryPositiveEnvelope.U_lower hR hQU hi.1 (small_le_large _ _ _ _ _ _ i) hi.2.1
    (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
  have hUscale := mul_le_mul_of_nonneg_right hi.2.2 hlen
  have hcap := (pure_dominates hR hQL hQU ht hx he j).2
  have ho := low_order ht
  have hc : ExceptionalSmallGap.scale≤c .low t := by
    dsimp [ExceptionalSmallGap.scale]
    exact (low_bounds ht).1.trans (low_bounds ht).2.2.1
  have hgap := ExceptionalSmallGap.scaled_gap hR hQL hQU hc ho.2.2.1 ho.2.2.2.1 ht
  dsimp only [ExceptionalSmallGap.scale] at hgap
  generalize frameCap=F at hU hUscale hcap hgap hlen ⊢
  linarith [hU,hUscale,hcap,hgap,hlen]

theorem ordinary_lower {R t x e : ℝ} (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single i=true → P i=0 ∨ N i=0) :
    V R (ell .low t) (c .low t) t≤
      ∑i,F (single i) R (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e i)
        (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e i) (P i) (N i) := by
  apply SingleAngleConcentration.lower_from_endpoints single R
    (small (k .low t) (ell .low t) (c .low t) (eta .low t) x e)
    (large (k .low t) (ell .low t) (c .low t) (eta .low t) x e)
    (nu (k .low t) (ell .low t) (c .low t) (eta .low t) x e) P N hR hQU
    (fun i => (coefficient_conditions ht hx he i).1) (small_le_large _ _ _ _ _ _)
    (fun i => (coefficient_conditions ht hx he i).2.1) (fun i => (nu_between _ _ _ _ _ _ i).1)
    hP hN (angle ht) hbudget hbalance hsingle
  · intro i; exact (pure_dominates hR hQL hQU ht hx he i).1
  · intro i hi; exact same_block_dominates hR hQL hQU ht hx he i hi
  · intro i j _; exact (separated_dominates hR hQL hQU ht hx he i j).le

theorem original_increment {C : SignedCycle} {ab : Fin 4} {R t x e : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t) :
    V R (ell .low t) (c .low t) t≤ExceptionalContactSupport.increment C ab R
      (k .low t) (ell .low t) (c .low t) (eta .low t) x e := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab (k .low t) (ell .low t) (c .low t) (eta .low t) t x e
    hvar hG hD htotal
  have hlow := ordinary_lower
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).P)
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).N)
    hR hQL hQU ht hx he
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).P_nonneg)
    (fun i => (blocks C ab (k .low t) (ell .low t) (c .low t) (eta .low t) x e i).N_nonneg)
    hP hN (single_parts C ab _ _ _ _ _ _)
  exact hlow.trans (sum_minorant hab ht0 (fun i => (coefficient_conditions ht hx he i).1.le) ha hP hN)

end SquaresInCircles.Eight.ExceptionalELowEnvelope
end
end
end
