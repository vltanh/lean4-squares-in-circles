module

public import SquaresInCircles.Eight.TableFree.SoleLowGap

/-!
# The low-family H, D and B charges

Uncompiled source. H and D are compared along a rectangle of actual
positive force coefficients with the fixed pair (17253/20000,1).
The larger negative coefficient 28/25 allows the sole-DE endpoint too.
All estimates cover whole angle intervals and the original radius band.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleLowChargeBounds
open SoleECoefficients SoleNormGain SoleLowGap PositiveAngularEnvelope
open PairNormCalculus OrdinaryAngleConcavity OrdinaryNegativeSlope
open SingleAngleConcavity OrdinaryCurvatureBounds VaryingBFunctions VaryingBComparison

def base : ℝ := 17253/20000

theorem base_gain_le {R p q s : ℝ} (hR : 0≤R)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hs : s∈Icc 0 frameCap) : normGain R base 1 s≤normGain R p q s := by
  have hb : 0<base := by norm_num [base]
  have hq0 : 0<q := by linarith [hq.1]
  have hsin := (transport_trig hs).2.2.2.1
  have hsin0 := (transport_trig hs).2.2.1
  have hr : Real.sin s*q≤base := by
    have hm := mul_le_mul hsin.le hq.2 hq0.le (by norm_num : (0:ℝ)≤6443/10000)
    norm_num [base] at *
    linarith
  have hlarge := normGain_larger_mono hR hb (by norm_num [base]) hq.1 hs hr
  have hsmall := normGain_smaller_mono hR hq0 hs
    (show base∈Icc (q/2) q by
      constructor <;> dsimp [base] at * <;> linarith [hq.1,hq.2])
    (show p∈Icc (q/2) q from ⟨by dsimp [base] at hp; linarith [hq.2],hpq⟩) hp
  exact hlarge.trans hsmall

theorem base_gain_linear {R s : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hs : s∈Icc 0 frameCap) : (323/250)*Real.sin s≤normGain R base 1 s := by
  let X := pairNorm base 1 0
  let Y := pairNorm base 1 (-s)
  have hX0 : 0<X := by dsimp [X]; exact Real.sqrt_pos.mpr (by norm_num [pairNorm,base])
  have hY0 : 0≤Y := Real.sqrt_nonneg _
  have hX2 : X^2=base^2+1 := by
    dsimp [X,pairNorm]
    simpa using Real.sq_sqrt (show 0≤base^2+1 by positivity)
  have hY2 : Y^2=base^2+1-2*base*Real.sin s := by
    simpa [Y] using negative_norm_square (by norm_num [base]) (by norm_num) hs
  have hsin := (transport_trig hs).2.2.1
  have hXY : Y≤X := by dsimp [base] at *; nlinarith
  have hXhi : X≤132067/100000 := by dsimp [base] at hX2; nlinarith
  have hdiff : 0≤X-Y := sub_nonneg.mpr hXY
  have hprod := mul_le_mul_of_nonneg_left
    (show X+Y≤2*(132067/100000 : ℝ) by linarith) hdiff
  have hid : (X-Y)*(X+Y)=2*base*Real.sin s := by nlinarith
  rw [hid] at hprod
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmR := mul_le_mul_of_nonneg_right hrad.le hdiff
  have hcoef : (323/250 : ℝ)*(132067/100000)≤(19787/10000)*base := by norm_num [base]
  have hmcoef := mul_le_mul_of_nonneg_right hcoef hsin
  have hmprod := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤19787/10000)
  have hmrad := mul_le_mul_of_nonneg_left hmR (by norm_num : (0:ℝ)≤132067/100000)
  change (323/250)*Real.sin s≤R*(X-Y)
  nlinarith

theorem short_trig {t : ℝ} (ht : t∈Icc 0 (1/5 : ℝ)) :
    (149/150)*t≤Real.sin t ∧ 1-Real.cos t≤t/10 := by
  have ht2 : t^2≤1/25 := by nlinarith [ht.1,ht.2]
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht.1
  have hs := Real.sin_ge_sub_cube ht.1
  have hc := nonneg_of_deriv_nonneg (fun x => Real.cos x-1+x^2/2)
    (by fun_prop) (by norm_num)
    (fun x hx => by
      simp (disch := fun_prop)
      linarith [Real.sin_le hx]) ht.1
  have hquad := mul_le_mul_of_nonneg_left ht.2 ht.1
  constructor <;> nlinarith

theorem wide_short {R p q nu t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hnu : nu≤28/25) (ht : t∈domain .low) :
    (117/100)*t≤Vnu R p q nu t := by
  have hg := (base_gain_linear hR hQL (angle ht)).trans
    (base_gain_le hR hp hpq hq (angle ht))
  have hc0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  have hnu' := mul_le_mul_of_nonneg_right hnu hc0
  obtain ⟨hs,hc⟩ := short_trig ht
  dsimp [normGain,Vnu] at *
  nlinarith [ht.1]

theorem wide_cap {R p q nu : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hnu : nu≤28/25) : (31/40 : ℝ)<Vnu R p q nu frameCap := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hg := base_gain_le hR hp hpq hq hh
  have hX2 : (pairNorm base 1 0)^2=base^2+1 := by
    simp only [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hY2 := negative_norm_square (by norm_num [base] : 0<base)
    (by norm_num : (0:ℝ)<1) hh
  have hX0 : 0≤pairNorm base 1 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm base 1 (-frameCap) := Real.sqrt_nonneg _
  have hX : (66033/50000 : ℝ)<pairNorm base 1 0 := by
    dsimp [base] at hX2
    nlinarith
  have hY : pairNorm base 1 (-frameCap)<79543/100000 := by
    have hs := cap_sin_lower
    dsimp [base] at hY2
    nlinarith
  have hdiff : (52523/100000 : ℝ)<pairNorm base 1 0-pairNorm base 1 (-frameCap) := by
    linarith
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmul := mul_lt_mul hrad hdiff (by norm_num : (0:ℝ)≤52523/100000)
    (by linarith : 0<R)
  have hc := (transport_trig hh).1
  have hnu' := mul_le_mul_of_nonneg_right hnu
    (show 0≤1-Real.cos frameCap by linarith [Real.cos_le_one frameCap])
  dsimp [normGain,Vnu] at *
  nlinarith

theorem B_zero_slope {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vd R (ell .low t) (c .low t) 0≤233/200 := by
  have hp := positive ht
  have hb := low_bounds ht
  have hc : 0<c .low t := hp.2.2.1
  have hr0 : 0≤ell .low t/c .low t := div_nonneg hp.2.1.le hc.le
  have hr1 : ell .low t/c .low t≤669/1000 :=
    (div_le_iff₀ hc).2 (by simpa [mul_comm] using (low_correlations ht).2.1.le)
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono hr0 hr1 (by norm_num) hz
  have hN := root_pos (669/1000) hz
  have hN2 := root_sq (669/1000) hz
  have hNlo : (1203/1000 : ℝ)≤root (669/1000) 0 := by nlinarith
  have hnum : c .low t*R*(669/1000)≤(209/200)*2*(669/1000) := by
    have hm := mul_le_mul hb.2.2.2.1.le hR.2 hR.1 (by norm_num : (0:ℝ)≤209/200)
    nlinarith
  have hbound : c .low t*R*(669/1000)/root (669/1000) 0≤233/200 := by
    apply (div_le_iff₀ hN).2
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hc.le hR.1)
  rw [Vd_normalized hc]
  simp only [Real.sin_zero,Real.cos_zero,neg_zero,zero_add,mul_one]
  calc
    c .low t*(R*(ell .low t/c .low t)/root (ell .low t/c .low t) 0)
        ≤c .low t*R*(669/1000)/root (669/1000) 0 := by
          simpa only [mul_div_assoc,mul_assoc] using hm
    _≤233/200 := hbound

theorem B_short {R t : ℝ} (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤(233/200)*t := by
  have hp := positive ht
  have hb := low_bounds ht
  have hpq : ell .low t≤c .low t := hb.2.2.2.2.2.2.1.le.trans hb.2.2.1
  have hqp := hb.2.2.2.2.2.2.2.1
  have hR2 : R≤2 := by norm_num [qCap] at hQ; nlinarith
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQ hp.2.1 hpq hqp
  have hd := derivative_reserve
    (f := fun x => -V R (ell .low t) (c .low t) x)
    (df := fun x => -Vd R (ell .low t) (c .low t) x)
    (k := -Vd R (ell .low t) (c .low t) 0)
    (fun x hx => (V_hasDerivAt hp.2.1 hp.2.2.1 hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt hp.2.1 hp.2.2.1 (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le))
    hz (angle ht) ht.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  have hm := mul_le_mul_of_nonneg_right (B_zero_slope ⟨hR,hR2⟩ ht) ht.1
  linarith

theorem B_cap {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) frameCap<18/25 := by
  have hp := positive ht
  rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hsmall := normGain_smaller_mono hR.1 hp.2.2.1 hh
    (show ell .low t∈Icc (c .low t/2) (c .low t) from ⟨by linarith,hlk.le.trans hkc⟩)
    (show (349/500 : ℝ)∈Icc (c .low t/2) (c .low t) by constructor <;> linarith)
    hl1.le
  have hlarge := normGain_larger_mono hR.1 (by norm_num : (0:ℝ)<349/500)
    (show (349/500 : ℝ)≤c .low t by linarith) hc1.le hh
    (show Real.sin frameCap*(209/200)≤(349/500 : ℝ) by
      linarith [(transport_trig hh).2.2.2.1])
  have hX2 : (pairNorm (349/500) (209/200) 0)^2=(349/500 : ℝ)^2+(209/200)^2 := by
    simp only [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hY2 := negative_norm_square (by norm_num : (0:ℝ)<349/500)
    (by norm_num : (0:ℝ)<209/200) hh
  have hX0 : 0≤pairNorm (349/500) (209/200) 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm (349/500) (209/200) (-frameCap) := Real.sqrt_nonneg _
  have hX : pairNorm (349/500) (209/200) 0≤1257/1000 := by nlinarith
  have hY : (799/1000 : ℝ)≤pairNorm (349/500) (209/200) (-frameCap) := by
    nlinarith [(transport_trig hh).2.2.2.1]
  have hdiff : pairNorm (349/500) (209/200) 0-
      pairNorm (349/500) (209/200) (-frameCap)≤229/500 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hR.1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo : (117/500 : ℝ)≤1-Real.cos frameCap := by
    norm_num [frameCap] at hcos
    linarith
  have hpen := mul_le_mul (hk0.trans hkc) hclo
    (by norm_num : (0:ℝ)≤117/500) hp.2.2.1.le
  dsimp [normGain,V] at *
  nlinarith [hR.2]

theorem wide_dominates {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (28/25 : ℝ))
    (hnu : nu≤28/25) (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤Vnu R p q nu t ∧
    V R (ell .low t) (c .low t) frameCap≤Vnu R p q nu frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  constructor
  · have hwide := wide_short hR hQL hp hpq hq hnu ht
    have hB := B_short hR hQU ht
    nlinarith [ht.1]
  · linarith [wide_cap hR hQL hp hpq hq hnu,B_cap ⟨hR,hR2⟩ ht]

end SquaresInCircles.Eight.TableFree.SoleLowChargeBounds
