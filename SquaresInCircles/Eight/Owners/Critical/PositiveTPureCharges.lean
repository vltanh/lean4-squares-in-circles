module

public import SquaresInCircles.Eight.Owners.Critical.PositiveTCoefficients
public import SquaresInCircles.Eight.Owners.Critical.PositiveTNormGain
public import SquaresInCircles.Eight.Owners.HalfRatioNormGain

/-!
# Eight squares: pure and far negative charges for the adapted critical dual

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
