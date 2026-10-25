module

public import SquaresInCircles.Eight.TableFree.ExceptionalSmallGap

/-!
# Low exceptional-family pure-charge comparisons

Uncompiled source. A keeps its actual negative coefficient l. Its
cosine gain pays the change from k to c. H and D are compared with the
fixed pair (.86265,1); B has an explicit initial-slope upper bound and
a circle-norm bound at the frame cap. These are whole-domain analytic
comparisons, including equality when the total angle is zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ExceptionalELowCharges
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

end SquaresInCircles.Eight.TableFree.ExceptionalELowCharges
