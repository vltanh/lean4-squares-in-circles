module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Critical.EWeightBounds
public import SquaresInCircles.Eight.Owners.SecantNormCurvature
public import SquaresInCircles.Eight.Owners.Sole.NegativeTDSupport
public import SquaresInCircles.Eight.Owners.Sole.NormGain
public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope

/-!
# Eight squares: the critical positive-T envelope on the original ordinary domain

Every pure and far charge dominates the same TD B charge.
The H and TD B mixed alternatives retain their actual two angles.
The original P,N budgets are used before concentration.
-/

section
/-!
## The canonical B chord on the positive-T critical strip

The fixed ratio is .61, the scale
is .8402, and the chord has slope .75 on the whole interval [0,.16].
The endpoint comparison uses positive radical squaring; monotonicity
of the exact derivative extends it to every smaller left endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTGap
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open OrdinaryNegativeEnvelope VaryingBFunctions VaryingBComparison SoleLowGap

def ratio : ℝ := 61/100
def scale : ℝ := 4201/5000

theorem short_right_slope {R : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) :
    3/4<Vd R ratio 1 (4/25) := by
  have hs : (4/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos ratio (sin_mem hs)
  have hN2 := root_sq ratio (sin_mem hs)
  have hsn := (transport_trig hs).2.2.1
  have hNu : root ratio (Real.sin (4/25))≤6/5 := by dsimp [ratio] at *; nlinarith
  have hsu := Real.sin_le (show (0:ℝ)≤4/25 by norm_num)
  have hco := SoleBalancedCoefficients.cosine_quadratic (show (0:ℝ)≤4/25 by norm_num)
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hCpos : 0<Real.cos (4/25:ℝ) := by linarith
  have hnum := mul_lt_mul_of_pos_right hrad hCpos
  have hcross : (3/4+Real.sin (4/25))*root ratio (Real.sin (4/25))<
      R*ratio*Real.cos (4/25) := by
    have hm := mul_le_mul hNu (show 3/4+Real.sin (4/25)≤91/100 by linarith)
      (by linarith : 0≤3/4+Real.sin (4/25)) (by norm_num : (0:ℝ)≤6/5)
    dsimp [ratio] at *
    nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
  simpa only [div_one,one_mul] using (show 3/4< -Real.sin (4/25)+
    R*ratio*Real.cos (4/25)/root ratio (Real.sin (4/25)) by linarith)

theorem right_gap {R : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) :
    (3/4)*(frameCap-4/25)<V R ratio 1 frameCap-V R ratio 1 (4/25) := by
  have hs : (4/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hX0 : 0≤pairNorm ratio 1 (-(4/25)) := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm ratio 1 (-frameCap) := Real.sqrt_nonneg _
  have hX2 := negative_norm_square (by norm_num [ratio] : 0<ratio) (by norm_num : (0:ℝ)<1) hs
  have hY2 := negative_norm_square (by norm_num [ratio] : 0<ratio) (by norm_num : (0:ℝ)<1) hh
  have hsu := sin_upper_five (show (0:ℝ)≤4/25 by norm_num)
  have hr : ratio=61/100 := rfl
  have hX : (2713/2500:ℝ)<pairNorm ratio 1 (-(4/25)) := by
    have h0 := hX0
    rw [hr] at hX2 h0 ⊢
    norm_num at hsu
    nlinarith
  have hY : pairNorm ratio 1 (-frameCap)<76563/100000 := by
    have h0 := hY0
    rw [hr] at hY2 h0 ⊢
    nlinarith [cap_sin_lower]
  have hgap : (31957/100000:ℝ)<pairNorm ratio 1 (-(4/25))-pairNorm ratio 1 (-frameCap) := by
    linarith
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmul := mul_lt_mul'' hrad hgap (by norm_num) (by norm_num)
  have hcosh := (transport_trig hh).1
  have hcost := cos_upper_four (show (0:ℝ)≤4/25 by norm_num)
  norm_num at hcost
  dsimp [V,frameCap]
  nlinarith

theorem fixed_gap {R t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈Icc 0 (4/25:ℝ)) :
    (3/4)*(frameCap-t)<V R ratio 1 frameCap-V R ratio 1 t := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap] at *; linarith [ht.2]⟩
  have hr : (4/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU (by norm_num [ratio] : 0<ratio)
    (by norm_num [ratio] : ratio≤1) (by norm_num [ratio] : (1:ℝ)≤2*ratio)
  have hlow (s : ℝ) (hs : s∈Icc 0 (4/25:ℝ)) : 3/4≤Vd R ratio 1 s :=
    (short_right_slope hR hQL).le.trans
      (hanti ⟨hs.1,hs.2.trans hr.2⟩ hr hs.2)
  have hd := derivative_reserve
    (f := V R ratio 1) (df := Vd R ratio 1) (k := 3/4)
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
  have e1 : R*ratio*Real.cos s/root ratio (Real.sin s)=R*Real.cos s*(ratio/root ratio (Real.sin s)) := by
    ring
  have e2 : R*(p/q)*Real.cos s/root (p/q) (Real.sin s)=
      R*Real.cos s*(p/q/root (p/q) (Real.sin s)) := by ring
  rw [e1,e2]
  linarith [hm']

theorem scaled_gap {R p q t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hq : scale≤q) (hpq : p≤q) (hratio : ratio*q≤p) (ht : t∈Icc 0 (4/25:ℝ)) :
    scale*(3/4)*(frameCap-t)<V R p q frameCap-V R p q t := by
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
  have hlen : 0≤(3/4)*(frameCap-t) := by dsimp [frameCap]; nlinarith [ht.2]
  have hm := mul_le_mul_of_nonneg_right hq hlen
  nlinarith

end SquaresInCircles.Eight.CriticalPositiveTGap
end
end
end

section
/-!
## The critical coefficient-loss estimates

The
factored cubic proves the uniform .4 bound for the normalized gain
integrand at every actual sine argument. Integration in the angle and
then in the coefficient gives the BT-to-TD comparison on the full
coefficient segment. The short A estimate is its stated .5 consequence.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTNormGain
open SoleNormGain PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison

theorem integrand_upper {r s : ℝ} (hr : r∈Icc (61/100:ℝ) (71/100))
    (hs : s∈Icc 0 frameCap) : integrand r s≤1/5 := by
  have hN := root_pos r hs
  have hN2 := root_sq r hs
  have hr0 : 0≤r := by linarith [hr.1]
  by_cases hsr : r ≤ s
  · have hnum : r^2*(r-s)≤0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (by linarith)
    have hdiv : integrand r s≤0 := div_nonpos_of_nonpos_of_nonneg hnum (pow_pos hN 3).le
    linarith
  · have hx : 0≤r-s := by linarith [lt_of_not_ge hsr]
    have hr2 : r^2≤(71/100:ℝ)^2 := pow_le_pow_left₀ hr0 hr.2 2
    have ha : 0≤1-r^2 := by nlinarith
    have hfactor : 0≤(1-r^2-r*(r-s))^2*(1-r^2+8*r*(r-s)) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [mul_nonneg hr0 hx])
    have hremain : 0≤r^2*(r-s)^2*(27*(1-r^2)-25*r^2) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg (r-s))) (by nlinarith)
    have hid : (1+r^2-2*r*s)^3-(5*r^2*(r-s))^2=
        (1-r^2-r*(r-s))^2*(1-r^2+8*r*(r-s))+
        r^2*(r-s)^2*(27*(1-r^2)-25*r^2) := by ring
    have hsquare : (5*r^2*(r-s))^2≤((root r s)^3)^2 := by
      have he : ((root r s)^3)^2=((root r s)^2)^3 := by ring
      rw [he,hN2]
      nlinarith only [hid,hfactor,hremain]
    have hcross : 5*r^2*(r-s)≤(root r s)^3 := by
      nlinarith [mul_nonneg (by positivity : 0≤5*r^2) hx,pow_nonneg hN.le 3]
    dsimp [integrand]
    apply (div_le_iff₀ (pow_pos hN 3)).2
    linarith

theorem scaled_integrand_upper {R r s : ℝ} (hR : R∈Icc 0 2)
    (hr : r∈Icc (61/100:ℝ) (71/100)) (hs : s∈Icc 0 frameCap) :
    R*integrand r s≤2/5 := by
  have hh := mul_le_mul_of_nonneg_left (integrand_upper hr hs) hR.1
  nlinarith [hR.2]

theorem scaled_gain {R r s : ℝ} (hR : R∈Icc 0 2)
    (hr : r∈Icc (61/100:ℝ) (71/100)) (hs : s∈Icc 0 frameCap) :
    R*gain r (Real.sin s)≤(2/5)*s := by
  have hsin := sin_mem hs
  have hh := derivative_reserve
    (f:=fun v => -R*gain r v) (df:=fun v => -R*integrand r v) (k:= -(2/5:ℝ))
    (fun v hv => ((gain_hasDerivAt_u r hv).const_mul (-R)).continuousAt.continuousWithinAt)
    (fun v hv => (gain_hasDerivAt_u r (Ioo_subset_Icc_self hv)).const_mul (-R))
    (fun v hv => by linarith [scaled_integrand_upper hR hr (Ioo_subset_Icc_self hv)])
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hsin hsin.1
  have hz : gain r 0=0 := by simp [gain,root,OrdinaryCurvatureBounds.shape]
  rw [hz] at hh
  nlinarith [Real.sin_le hs.1]

theorem coefficient_loss {R p a b s : ℝ} (hR : R∈Icc 0 2)
    (ha : 0<a) (hab : a≤b) (hplo : (61/100)*b≤p) (hphi : p≤(71/100)*a)
    (hs : s∈Icc 0 frameCap) :
    normGain R p b s-normGain R p a s≤(2/5)*s*(b-a) := by
  have hp : 0<p := by nlinarith
  have hx (x : ℝ) (hxx : x∈Icc a b) : 0<x ∧ p/x∈Icc (61/100:ℝ) (71/100) := by
    have hxp : 0<x := ha.trans_le hxx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_iff₀ hxp).2 ?_⟩⟩ <;>
      nlinarith [hxx.1,hxx.2]
  have hh := derivative_reserve
    (f:=fun x => -normGain R p x s)
    (df:=fun x => -(R*gain (p/x) (Real.sin s))) (k:= -(2/5)*s)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x hxx).1 hs).neg.continuousAt.continuousWithinAt)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs).neg)
    (fun x hxx => by linarith [scaled_gain hR (hx x (Ioo_subset_Icc_self hxx)).2 hs])
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩) hab
  linarith

theorem coefficient_short {R p a b s : ℝ} (hR : R∈Icc 0 2)
    (ha : 0<a) (hab : a≤b) (hplo : (61/100)*b≤p) (hphi : p≤(27/40)*a)
    (hs : s∈Icc 0 (4/25:ℝ)) :
    normGain R p b s-normGain R p a s≤(1/2)*s*(b-a) := by
  have hh := coefficient_loss hR ha hab hplo (show p≤(71/100)*a by nlinarith)
    (show s∈Icc 0 frameCap from ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩)
  have hprod := mul_nonneg hs.1 (sub_nonneg.mpr hab)
  nlinarith

end SquaresInCircles.Eight.CriticalPositiveTNormGain
end
end
end

section
/-!
## Pure and far negative charges for the adapted critical dual

H and D use the balanced
rectangle with lower coefficient .8402 and negative coefficient at
most 1.04. A keeps its actual smaller negative coefficient. The BT B
charge is compared to the same TD charge using its correlated change
Delta=m-c; no ordinary angle or actual owner is changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTPureCharges
open Candidate CriticalPositiveTCoefficients SoleNormGain SoleLowGap
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity OrdinaryNegativeSlope
open OrdinaryNegativeEnvelope SingleAngleConcavity VaryingBFunctions VaryingBComparison

def base : ℝ := 4201/5000

theorem radius_upper {R : ℝ} (hR : 0≤R) (hQ : R^2≤qCap) : R≤1979/1000 := by
  norm_num [qCap] at hQ
  nlinarith

theorem base_gain_le {R p q s : ℝ} (hR : 0≤R)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (26/25:ℝ))
    (hs : s∈Icc 0 frameCap) : normGain R base 1 s≤normGain R p q s := by
  have hb : 0<base := by norm_num [base]
  have hq0 : 0<q := by linarith [hq.1]
  have hr : Real.sin s*q≤base := by
    have hm := mul_le_mul (transport_trig hs).2.2.2.1.le hq.2 hq0.le
      (by norm_num : (0:ℝ)≤6443/10000)
    norm_num [base] at *
    linarith
  have hlarge := normGain_larger_mono hR hb (by norm_num [base]) hq.1 hs hr
  have hsmall := normGain_smaller_mono hR hq0 hs
    (show base∈Icc (q/2) q by constructor <;> dsimp [base] at * <;> linarith [hq.1,hq.2])
    (show p∈Icc (q/2) q from ⟨by dsimp [base] at hp; linarith [hq.2],hpq⟩) hp
  exact hlarge.trans hsmall

theorem base_gain_linear {R s : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hs : s∈Icc 0 frameCap) : (1591/1250)*Real.sin s≤normGain R base 1 s := by
  let X := pairNorm base 1 0
  let Y := pairNorm base 1 (-s)
  have hX0 : 0<X := by dsimp [X]; exact Real.sqrt_pos.mpr (by norm_num [pairNorm,base])
  have hY0 : 0≤Y := Real.sqrt_nonneg _
  have hX2 : X^2=base^2+1 := by
    dsimp [X,pairNorm]
    simpa using Real.sq_sqrt (show 0≤base^2+1 by positivity)
  have hY2 : Y^2=base^2+1-2*base*Real.sin s := by
    simpa [Y] using negative_norm_square (p:=base) (q:=1) (by norm_num [base]) (by norm_num) hs
  have hsin := (transport_trig hs).2.2.1
  have hXY : Y≤X := by dsimp [base] at *; nlinarith
  have hXhi : X≤261223/200000 := by dsimp [base] at hX2; nlinarith
  have hdiff : 0≤X-Y := sub_nonneg.mpr hXY
  have hprod := mul_le_mul_of_nonneg_left
    (show X+Y≤2*(261223/200000:ℝ) by linarith) hdiff
  have hid : (X-Y)*(X+Y)=2*base*Real.sin s := by nlinarith
  rw [hid] at hprod
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmR := mul_le_mul_of_nonneg_right hrad.le hdiff
  have hcoef : (1591/1250:ℝ)*(261223/200000)≤(19787/10000)*base := by norm_num [base]
  have hmcoef := mul_le_mul_of_nonneg_right hcoef hsin
  have hmprod := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤19787/10000)
  have hmrad := mul_le_mul_of_nonneg_left hmR (by norm_num : (0:ℝ)≤261223/200000)
  change (1591/1250)*Real.sin s≤R*(X-Y)
  nlinarith

theorem wide_short {R p q nu t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (26/25:ℝ))
    (hnu : nu≤26/25) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    (148/125)*t<Vnu R p q nu t := by
  have ht' : t∈Icc 0 frameCap := ⟨by linarith [ht.1],by dsimp [frameCap]; linarith [ht.2]⟩
  have hg := (base_gain_linear hR hQL ht').trans (base_gain_le hR hp hpq hq ht')
  have hc0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  have hn := mul_le_mul_of_nonneg_right hnu hc0
  have ht2 : t^2≤(4/25:ℝ)^2 := pow_le_pow_left₀ ht'.1 ht.2 2
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht'.1
  have hs := Real.sin_ge_sub_cube ht'.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have htq := mul_le_mul_of_nonneg_left ht.2 ht'.1
  dsimp [normGain,Vnu] at *
  nlinarith [ht.1]

theorem wide_cap {R p q nu : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (26/25:ℝ))
    (hnu : nu≤26/25) : (777/1000:ℝ)<Vnu R p q nu frameCap := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hg := base_gain_le hR hp hpq hq hh
  have hX2 : (pairNorm base 1 0)^2=base^2+1 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity)]; ring
  have hY2 := negative_norm_square (by norm_num [base] : 0<base) (by norm_num : (0:ℝ)<1) hh
  have hX0 : 0≤pairNorm base 1 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm base 1 (-frameCap) := Real.sqrt_nonneg _
  have hb : base=4201/5000 := rfl
  have hX : (130611/100000:ℝ)<pairNorm base 1 0 := by
    have h0 := hX0
    rw [hb] at hX2 h0 ⊢; nlinarith
  have hY : pairNorm base 1 (-frameCap)<197393/250000 := by
    have h0 := hY0
    rw [hb] at hY2 h0 ⊢
    nlinarith [cap_sin_lower]
  have hdiff : (258269/500000:ℝ)<pairNorm base 1 0-pairNorm base 1 (-frameCap) := by linarith
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hmul := mul_lt_mul'' hrad hdiff (by norm_num) (by norm_num)
  have hc := (transport_trig hh).1
  have hn := mul_le_mul_of_nonneg_right hnu
    (show 0≤1-Real.cos frameCap by linarith [Real.cos_le_one frameCap])
  dsimp [normGain,Vnu] at *
  nlinarith

theorem B_zero_slope {R t z k l c m eta : ℝ} (hR : 0≤R) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) : Vd R l m 0≤551/500 := by
  have hm : 0< m := by linarith [h.c_lower,h.c_le_m]
  let N := Real.sqrt (l^2+m^2)
  have hN : 0<N := Real.sqrt_pos.mpr (by positivity)
  have hN2 : N^2=l^2+m^2 := Real.sq_sqrt (by positivity)
  have hl2 : l^2≤(67/100:ℝ)^2 := pow_le_pow_left₀ h.ell_pos.le h.ell_upper.le 2
  have hm2 : m^2≤1 := by nlinarith [h.m_upper,sq_nonneg (m-1)]
  have hprod1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤(67/100)^2) (sq_nonneg l))
    (sub_nonneg.mpr hm2)
  have hprod2 := mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hl2)
  have hfrac : (1+(67/100:ℝ)^2)*(l*m)^2≤(67/100)^2*(l^2+m^2) := by nlinarith
  have hRmax := radius_upper hR hQU
  have hR2 : R^2≤(1979/1000:ℝ)^2 := pow_le_pow_left₀ hR hRmax 2
  have hRprod := mul_le_mul_of_nonneg_right hR2 (sq_nonneg (l*m))
  have hratio := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℝ)≤(1979/1000)^2)
  have hcoef : (1979/1000:ℝ)^2*(67/100)^2≤(551/500)^2*(1+(67/100)^2) := by norm_num
  have hcoefmul := mul_le_mul_of_nonneg_right hcoef (show 0≤l^2+m^2 by positivity)
  have hcross : R*l*m≤(551/500)*N := by nlinarith
  have he : Vd R l m 0=R*l*m/N := by
    simp [Vd,mixedNDerivative,normD1,pairProduct,pairNorm,N]
    ring
  rw [he]
  exact (div_le_iff₀ hN).2 hcross

theorem B_short {R t z k l c m eta : ℝ} (hR : 0≤R) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) : V R l m t≤(551/500)*t := by
  have hm : 0< m := by linarith [h.c_lower,h.c_le_m]
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ho := h.order
  have hanti := Vd_antitone hR hQU h.ell_pos h.ell_m_upper.le ho.2.2.2.2.2.2
  have hd := derivative_reserve (f:=fun x => -V R l m x) (df:=fun x => -Vd R l m x)
    (k:= -Vd R l m 0)
    (fun x hx => (V_hasDerivAt h.ell_pos hm hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt h.ell_pos hm (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le)) hz h.angle h.angle.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  have hh := mul_le_mul_of_nonneg_right (B_zero_slope hR hQU h) h.angle.1
  linarith

theorem B_cap {R t z k l c m eta : ℝ} (hR : 0≤R) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) : V R l m frameCap<671/1000 := by
  have hm : 0< m := by linarith [h.c_lower,h.c_le_m]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hsmall := normGain_smaller_mono hR hm hh
    (show l∈Icc (m/2) m by constructor <;> linarith [h.ell_m_lower,h.ell_m_upper])
    (show (67/100:ℝ)∈Icc (m/2) m by constructor <;> linarith [h.m_upper,h.c_lower,h.c_le_m])
    h.ell_upper.le
  have hlarge := normGain_larger_mono hR (by norm_num : (0:ℝ)<67/100)
    (show (67/100:ℝ)≤ m by linarith [h.c_lower,h.c_le_m]) h.m_upper.le hh
    (by linarith [(transport_trig hh).2.2.2.1] : Real.sin frameCap*1≤(67/100:ℝ))
  have hX2 : (pairNorm (67/100) 1 0)^2=(67/100:ℝ)^2+1 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity)]; ring
  have hY2 := negative_norm_square (by norm_num : (0:ℝ)<67/100) (by norm_num : (0:ℝ)<1) hh
  have hX0 : 0≤pairNorm (67/100) 1 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm (67/100) 1 (-frameCap) := Real.sqrt_nonneg _
  have hX : pairNorm (67/100) 1 0≤120371/100000 := by nlinarith
  have hY : (1913/2500:ℝ)≤pairNorm (67/100) 1 (-frameCap) := by
    nlinarith [(transport_trig hh).2.2.2.1]
  have hdiff : pairNorm (67/100) 1 0-pairNorm (67/100) 1 (-frameCap)≤43851/100000 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hR
  have hRmax := radius_upper hR hQU
  have hcos := cos_upper_four (show 0≤frameCap by norm_num [frameCap])
  have hloss : (23499/100000:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
  have hpen := mul_le_mul (show (4201/5000:ℝ)≤ m by linarith [h.c_lower,h.c_le_m])
    hloss (by norm_num) hm.le
  dsimp [normGain,V] at *
  nlinarith

theorem A_ge_B {R t z k l c m eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t z k l c m eta) : V R l m t≤Vnu R l k l t := by
  have ho := h.order
  have hcos0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  by_cases hmk : m≤k
  · have hg := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos h.ell_m_upper.le hmk
      ho.2.2.2.2.1 h.angle
    have hp := mul_nonneg (show 0≤ m-l by linarith [h.ell_m_upper]) hcos0
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hkm : k≤ m := (lt_of_not_ge hmk).le
    have hg := CriticalPositiveTNormGain.coefficient_short hR ho.1 hkm h.ell_m_lower.le
      h.ell_k.le ⟨h.angle.1,h.angle_upper⟩
    have hc := SoleLowAComparison.cosine_loss_lower
      (show t∈Icc 0 (1/5:ℝ) from ⟨h.angle.1,by linarith [h.angle_upper]⟩)
    have hgap := mul_le_mul_of_nonneg_right h.gap.le hcos0
    have hdiff := mul_le_mul_of_nonneg_left h.difference.le (show 0≤(1/2)*t by linarith [h.angle.1])
    have hquad := mul_nonneg h.angle.1 (show 0≤t-1/10 by linarith [h.angle_lower])
    dsimp [V,Vnu,normGain] at *
    nlinarith

theorem A_ge_B_at_cap {R t z k l c m eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t z k l c m eta) : V R l m frameCap≤Vnu R l k l frameCap := by
  have ho := h.order
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hcos0 : 0≤1-Real.cos frameCap := by linarith [Real.cos_le_one frameCap]
  by_cases hmk : m≤k
  · have hg := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos h.ell_m_upper.le hmk
      ho.2.2.2.2.1 hh
    have hp := mul_nonneg (show 0≤ m-l by linarith [h.ell_m_upper]) hcos0
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hm : 0< m := by linarith [h.c_lower,h.c_le_m]
    have hg := SoleNormGain.coefficient_cap hR ho.1 (lt_of_not_ge hmk).le
      (show (117/200)*m≤l by nlinarith [h.ell_m_lower])
      (show l≤(18/25)*k by nlinarith [h.ell_k])
    have hc := cos_upper_four (show 0≤frameCap by norm_num [frameCap])
    have hloss : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hc; linarith
    have hgap := mul_le_mul_of_nonneg_right h.gap.le hcos0
    dsimp [V,Vnu,normGain] at *
    linarith [h.difference]

theorem BT_ge_B {R t z k l c m eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t z k l c m eta) : V R l m t≤Vnu R l c l t := by
  have hc : 0<c := by linarith [h.c_lower]
  have hg := CriticalPositiveTNormGain.coefficient_loss hR hc h.c_le_m
    h.ell_m_lower.le h.ell_c_upper.le h.angle
  let a := 1-Real.cos t
  let Δ := m-c
  have ha : 0≤a := by dsimp [a]; linarith [Real.cos_le_one t]
  have hΔ : 0≤Δ := sub_nonneg.mpr h.c_le_m
  have hcos := SoleLowAComparison.cosine_loss_lower
    (show t∈Icc 0 (1/5:ℝ) from ⟨h.angle.1,by linarith [h.angle_upper]⟩)
  have hquad := Real.one_sub_sq_div_two_le_cos (x := t)
  have htq := mul_le_mul_of_nonneg_left h.angle_upper h.angle.1
  have hnegative : a-(2/5)*t≤0 := by dsimp [a]; nlinarith
  have hgap := mul_le_mul_of_nonneg_right h.refined_gap.le ha
  have hdelta := mul_le_mul_of_nonpos_right h.delta_upper hnegative
  have htz := mul_le_mul_of_nonneg_left h.z_le h.angle.1
  have hza := mul_nonneg h.z_nonneg ha
  dsimp [V,Vnu,normGain,a,Δ] at *
  nlinarith [sq_nonneg t]

theorem BT_ge_B_at_cap {R t z k l c m eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t z k l c m eta) : V R l m frameCap≤Vnu R l c l frameCap := by
  have hc : 0<c := by linarith [h.c_lower]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hg := CriticalPositiveTNormGain.coefficient_loss hR hc h.c_le_m
    h.ell_m_lower.le h.ell_c_upper.le hh
  have hcos := cos_upper_four (show 0≤frameCap by norm_num [frameCap])
  have hclo : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
  have hgap := mul_le_mul_of_nonneg_right h.gap.le
    (show 0≤1-Real.cos frameCap by linarith)
  have hdelta : m-c≤31/625 := by linarith [h.delta_upper,h.z_le,h.angle_upper]
  dsimp [V,Vnu,normGain,frameCap] at *
  linarith

theorem wide_dominates {R p q nu t z k l c m eta : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : base≤p) (hpq : p≤q) (hq : q∈Icc 1 (26/25:ℝ))
    (hnu : nu≤26/25) (h : Bounds t z k l c m eta) :
    V R l m t≤Vnu R p q nu t ∧ V R l m frameCap≤Vnu R p q nu frameCap := by
  constructor
  · have hw := wide_short hR hQL hp hpq hq hnu ⟨h.angle_lower,h.angle_upper⟩
    have hB := B_short hR hQU h
    nlinarith [h.angle.1]
  · linarith [wide_cap hR hQL hp hpq hq hnu,B_cap hR hQU h]

end SquaresInCircles.Eight.CriticalPositiveTPureCharges
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CriticalPositiveTEnvelope
open CriticalPositiveTCoefficients CriticalPositiveTPureCharges
open ExceptionalPositiveTBlocks ExceptionalContactStress
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

theorem H_data {t z k l c m eta x e : ℝ} (td : Bool)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    37/40<small (weights td k l c m eta x e) 0 ∧
      large (weights td k l c m eta x e) 0∈Icc 1 (26/25:ℝ) := by
  have hf := h.tilt hx
  have hg := h.tilt he
  have hk : 0≤k := by linarith [h.k_lower]
  have hn0 := mul_le_mul_of_nonneg_left hf.1 hk
  have hn1 : k*tilt eta x<199/200*(26/25) :=
    mul_lt_mul h.k_upper hf.2.le (by linarith [hf.1]) (by norm_num)
  change 37/40< min (tilt eta e) (k*tilt eta x) ∧
    max (tilt eta e) (k*tilt eta x)∈Icc 1 (26/25:ℝ)
  refine ⟨lt_min (by linarith) (by linarith [h.k_lower]),?_,?_⟩
  · exact hg.1.trans (le_max_left _ _)
  · exact max_le hg.2.le (by linarith)

theorem ordinary_data {t z k l c m eta x e : ℝ} (td : Bool)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,0<small (weights td k l c m eta x e) i) ∧
    (∀ i,large (weights td k l c m eta x e) i≤2*small (weights td k l c m eta x e) i) ∧
    (∀ i,large (weights td k l c m eta x e) i≤26/25) := by
  have hH := H_data td h hx he
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hm : 0< m := hc.trans_le h.c_le_m
  have hc1 : c≤1 := h.c_le_m.trans h.m_upper.le
  have hm1 : m≤1 := h.m_upper.le
  have hk1 : k≤1 := by linarith [h.k_upper]
  obtain ⟨b,hbd⟩ : ∃ b,b=(if td then m else c) := ⟨_,rfl⟩
  obtain ⟨d,hdd⟩ : ∃ d,d=(if td then c else m) := ⟨_,rfl⟩
  have hb : l≤b ∧ b≤1 ∧ b≤2*l := by
    cases td <;> simp only [Bool.false_eq_true,↓reduceIte] at hbd <;> subst hbd <;>
      exact ⟨by linarith [ho.2.2.1,ho.2.2.2.1],by linarith,by linarith [ho.2.2.2.2.2.1,ho.2.2.2.2.2.2]⟩
  have hd : 4201/5000<d ∧ d≤1 := by
    cases td <;> simp only [Bool.false_eq_true,↓reduceIte] at hdd <;> subst hdd <;>
      exact ⟨by linarith [h.c_lower,h.c_le_m],by linarith⟩
  have e1s : small (weights td k l c m eta x e) 1=l :=
    (show min k l=l from min_eq_right ho.2.1)
  have e1l : large (weights td k l c m eta x e) 1=k :=
    (show max k l=k from max_eq_left ho.2.1)
  have e2s : small (weights td k l c m eta x e) 2=l := by
    show min l (if td then m else c)=l
    rw [← hbd]; exact min_eq_left hb.1
  have e2l : large (weights td k l c m eta x e) 2=b := by
    show max l (if td then m else c)=b
    rw [← hbd]; exact max_eq_right hb.1
  have e3s : small (weights td k l c m eta x e) 3=d := by
    show min 1 (if td then c else m)=d
    rw [← hdd]; exact min_eq_right hd.2
  have e3l : large (weights td k l c m eta x e) 3=1 := by
    show max 1 (if td then c else m)=1
    rw [← hdd]; exact max_eq_left hd.2
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_⟩ <;> fin_cases i
  · show 0<small (weights td k l c m eta x e) 0
    linarith [hH.1]
  · show 0<small (weights td k l c m eta x e) 1
    rw [e1s]; exact h.ell_pos
  · show 0<small (weights td k l c m eta x e) 2
    rw [e2s]; exact h.ell_pos
  · show 0<small (weights td k l c m eta x e) 3
    rw [e3s]; linarith [hd.1]
  · show large (weights td k l c m eta x e) 0≤2*small (weights td k l c m eta x e) 0
    linarith [hH.1,hH.2.2]
  · show large (weights td k l c m eta x e) 1≤2*small (weights td k l c m eta x e) 1
    rw [e1s,e1l]; exact ho.2.2.2.2.1
  · show large (weights td k l c m eta x e) 2≤2*small (weights td k l c m eta x e) 2
    rw [e2s,e2l]; exact hb.2.2
  · show large (weights td k l c m eta x e) 3≤2*small (weights td k l c m eta x e) 3
    rw [e3s,e3l]; linarith [hd.1]
  · exact hH.2.2
  · show large (weights td k l c m eta x e) 1≤26/25
    rw [e1l]; linarith
  · show large (weights td k l c m eta x e) 2≤26/25
    rw [e2l]; linarith [hb.2.1]
  · show large (weights td k l c m eta x e) 3≤26/25
    rw [e3l]; norm_num

theorem pure_dominates {R t z k l c m eta x e : ℝ} (td : Bool)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R l m t≤pure (single td i) R (small (weights td k l c m eta x e) i)
      (large (weights td k l c m eta x e) i) (negative (weights td k l c m eta x e) td i) t ∧
    V R l m frameCap≤pure (single td i) R (small (weights td k l c m eta x e) i)
      (large (weights td k l c m eta x e) i) (negative (weights td k l c m eta x e) td i) frameCap := by
  rw [pure_eq,pure_eq]
  have hR2 : R∈Icc 0 2 := ⟨hR,by linarith [radius_upper hR hQU]⟩
  have ho := h.order
  have hc1 : c≤1 := h.c_le_m.trans h.m_upper.le
  have hm1 : m≤1 := h.m_upper.le
  fin_cases i
  · have hh := H_data td h hx he
    apply wide_dominates hR hQL hQU
      (by dsimp [base]; linarith [hh.1]) (small_le_large _ _) hh.2
    · simpa [negative,large,first,second,weights] using hh.2.2
    · exact h
  · simpa [small,large,first,second,negative,weights,min_eq_right ho.2.1,
      max_eq_left ho.2.1] using ⟨A_ge_B hR2 h,A_ge_B_at_cap hR2 h⟩
  · cases td
    · simpa [small,large,first,second,negative,weights,min_eq_left ho.2.2.1,
        max_eq_right ho.2.2.1] using ⟨BT_ge_B hR2 h,BT_ge_B_at_cap hR2 h⟩
    · simp [small,large,first,second,negative,weights,min_eq_left ho.2.2.2.1,
        max_eq_right ho.2.2.2.1,Vnu,V]
  · cases td
    · have hw := wide_dominates hR hQL hQU
        (show base≤ m by dsimp [base]; linarith [h.c_lower,h.c_le_m]) hm1
        (show (1:ℝ)∈Icc 1 (26/25:ℝ) by norm_num)
        (show m≤26/25 by linarith [h.m_upper]) h
      simpa [small,large,first,second,negative,weights,min_eq_right hm1,max_eq_left hm1] using hw
    · have hw := wide_dominates hR hQL hQU
        (show base≤c by dsimp [base]; linarith [h.c_lower]) hc1
        (show (1:ℝ)∈Icc 1 (26/25:ℝ) by norm_num)
        (show c≤26/25 by linarith) h
      simpa [small,large,first,second,negative,weights,min_eq_right hc1,max_eq_left hc1] using hw

theorem same_block {R t z k l c m eta x e : ℝ} (td : Bool)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (i : Fin 4) (hi : single td i=false) :
    pure (single td i) R (small (weights td k l c m eta x e) i)
      (large (weights td k l c m eta x e) i) (negative (weights td k l c m eta x e) td i) t≤
      M R (small (weights td k l c m eta x e) i)
        (large (weights td k l c m eta x e) i) t := by
  simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte]
  have hp := (ordinary_data td h hx he).1 i
  have hq := hp.trans_le (small_le_large _ _)
  have hindices : i=0 ∨ i=2 := by fin_cases i <;> cases td <;> simp_all [single]
  rcases hindices with rfl | rfl
  · have hh := H_data td h hx he
    apply M_ge_V hp.le hq.le ?_ h.angle
    linarith [hh.1,hh.2.2]
  · have htd : td=true := by cases td <;> simp_all [single]
    subst td
    have ho := h.order
    have e1 : small (weights true k l c m eta x e) 2=l := min_eq_left ho.2.2.2.1
    have e2 : large (weights true k l c m eta x e) 2=m := max_eq_right ho.2.2.2.1
    rw [e1,e2]
    apply SolePositiveTSameBlock.from_bracket (show 0≤ m by linarith [h.c_lower,h.c_le_m])
      h.ell_m_lower.le h.angle
    have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
    have hc := (transport_trig hh).1
    have hs := (transport_trig hh).2.2.2.1
    apply SolePositiveTSameBlock.half_angle_bracket h.angle (by linarith)
    have hlen : (27/50:ℝ)≤frameCap-t := by norm_num [frameCap]; linarith [h.angle_upper]
    have hm := mul_le_mul (show (387/2500:ℝ)≤Real.cos frameCap-61/100 by linarith)
      hlen (by norm_num) (by linarith)
    linarith

theorem original_increment {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {R t z k l c m eta x e : ℝ} (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (ha : ∀ i,|Candidate.delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤Candidate.delta C.theta Candidate.G) (hD : 0≤Candidate.delta C.theta Candidate.D)
    (hT : 0≤ExceptionalPositiveTStress.primary C td)
    (htotal : Candidate.delta C.theta Candidate.G+Candidate.delta C.theta Candidate.D+ExceptionalPositiveTStress.primary C td=t) :
    V R l m t≤ increment C ab td (weights td k l c m eta x e) R := by
  have hw := ordinary_data td h hx he
  apply original_lower td (weights td k l c m eta x e) hab hR hQU hw.1 hw.2.1
    ha hvar hG hD hT htotal
  · intro i
    exact (pure_dominates td hR hQL hQU h hx he i).1
  · intro i hi
    exact (pure_dominates td hR hQL hQU h hx he i).1.trans (same_block td h hx he i hi)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [h.angle.2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (hw.1 i) (small_le_large _ _) (hw.2.1 i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [h.angle.1]⟩)
    have hV := (pure_dominates td hR hQL hQU h hx he j).2
    have hgap := CriticalPositiveTGap.scaled_gap hR hQL hQU
      (show CriticalPositiveTGap.scale≤ m by
        dsimp [CriticalPositiveTGap.scale]; linarith [h.c_lower,h.c_le_m])
      h.ell_m_upper.le h.ell_m_lower.le ⟨h.angle.1,h.angle_upper⟩
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hw.2.2 i) (by norm_num : (0:ℝ)≤109/200)) hlen
    have hreserve := mul_nonneg (show (0:ℝ)≤(4201/5000)*(3/4)-(109/200)*(26/25) by norm_num) hlen
    dsimp [CriticalPositiveTGap.scale] at hgap
    linarith

end SquaresInCircles.Eight.CriticalPositiveTEnvelope
end
end
end
