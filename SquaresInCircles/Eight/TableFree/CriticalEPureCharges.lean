module

public import SquaresInCircles.Eight.TableFree.CriticalECoefficients
public import SquaresInCircles.Eight.TableFree.HalfRatioNormGain
public import SquaresInCircles.Eight.TableFree.ExceptionalELowCharges

/-!
# Pure ordinary charges for the exact critical family

Uncompiled source. The comparisons use the actual coefficient bounds
of the supporting chain. Both orders of k and c are included. The
one-angle A coefficient stays l, while H and D admit the stronger
two-angle relaxation needed for an arbitrary original EH0 angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalEPureCharges
open CriticalECoefficients SoleNormGain PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem A_ge_B {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : V R l c t≤Vnu R l k l t := by
  have ho := h.order
  have hcos0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  by_cases hck : c≤k
  · have hg := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos ho.2.2.1 hck
      ho.2.2.2.2.2.1 h.angle
    have hp := mul_nonneg (show 0≤c-l by linarith [ho.2.2.1]) hcos0
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hkc : k≤c := le_of_lt (lt_of_not_ge hck)
    have hs : t∈Icc 0 (1/5:ℝ) := ⟨h.angle.1,by linarith [h.angle_upper]⟩
    have hg := coefficient_short hR ho.1 hkc ho.2.2.2.1
      (show l≤(18/25)*k by linarith [h.ell_k]) hs
    have hcos := SoleLowAComparison.cosine_loss_lower hs
    have hck' : c-k≤t/5 := by linarith [h.difference,h.angle_lower]
    have hm := mul_le_mul_of_nonneg_right ho.2.2.2.2.2.2 hcos0
    have hm' := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤1/4)
    have hkg := mul_le_mul_of_nonneg_left hck' (show 0≤(11/20)*t by positivity)
    dsimp [V,Vnu,normGain] at *
    nlinarith [sq_nonneg t]

theorem A_ge_B_at_cap {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : V R l c frameCap≤Vnu R l k l frameCap := by
  have ho := h.order
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hcos0 : 0≤1-Real.cos frameCap := by linarith [Real.cos_le_one frameCap]
  by_cases hck : c≤k
  · have hg := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos ho.2.2.1 hck
      ho.2.2.2.2.2.1 hh
    have hp := mul_nonneg (show 0≤c-l by linarith [ho.2.2.1]) hcos0
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hkc : k≤c := le_of_lt (lt_of_not_ge hck)
    have hg := coefficient_cap hR ho.1 hkc ho.2.2.2.1
      (show l≤(18/25)*k by linarith [h.ell_k])
    have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
    have hc : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
    have hm := mul_le_mul_of_nonneg_right ho.2.2.2.2.2.2 hcos0
    have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤1/4)
    dsimp [V,Vnu,normGain] at *
    linarith [h.difference]

theorem B_zero_slope {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : Vd R l c 0≤23/20 := by
  have hc : 0<c := by linarith [h.c_lower]
  have hr0 : 0≤l/c := div_nonneg h.ell_pos.le hc.le
  have hr1 : l/c≤7/10 := (div_le_iff₀ hc).2 (by linarith [h.ell_c_upper])
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono hr0 hr1 (by norm_num) hz
  have hN := root_pos (7/10) hz
  have hN2 := root_sq (7/10) hz
  have hNlo : (61/50:ℝ)≤root (7/10) 0 := by nlinarith
  have hnum : c*R*(7/10)≤(501/500)*2*(7/10) := by
    have hm := mul_le_mul (show c≤501/500 by linarith [h.c_upper]) hR.2 hR.1
      (by norm_num : (0:ℝ)≤501/500)
    nlinarith
  have hbound : c*R*(7/10)/root (7/10) 0≤23/20 := by
    apply (div_le_iff₀ hN).2
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hc.le hR.1)
  rw [Vd_normalized hc]
  simp only [Real.sin_zero,Real.cos_zero,neg_zero,zero_add,mul_one]
  calc
    c*(R*(l/c)/root (l/c) 0)≤c*R*(7/10)/root (7/10) 0 := by
      simpa only [mul_div_assoc,mul_assoc] using hm
    _≤23/20 := hbound

theorem B_short {R t k l c eta : ℝ} (hR : 0≤R) (hQU : R^2≤Candidate.qCap)
    (h : Bounds t k l c eta) : V R l c t≤(23/20)*t := by
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hR2 : R≤2 := by norm_num [Candidate.qCap] at hQU; nlinarith
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU h.ell_pos ho.2.2.1 ho.2.2.2.2.1
  have hd := derivative_reserve (f := fun x => -V R l c x)
    (df := fun x => -Vd R l c x) (k := -Vd R l c 0)
    (fun x hx => (V_hasDerivAt h.ell_pos hc hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt h.ell_pos hc (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le))
    hz h.angle h.angle.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  have hm := mul_le_mul_of_nonneg_right (B_zero_slope ⟨hR,hR2⟩ h) h.angle.1
  linarith

theorem B_cap {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : V R l c frameCap<18/25 := by
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hsmall := normGain_smaller_mono hR.1 hc hh
    ⟨by linarith [ho.2.2.2.2.1],ho.2.2.1⟩
    (show (673/1000:ℝ)∈Icc (c/2) c by constructor <;> linarith [h.c_lower,h.c_upper])
    (show l≤673/1000 by linarith [h.ell_upper])
  have hlarge := normGain_larger_mono hR.1 (by norm_num : (0:ℝ)<673/1000)
    (show (673/1000:ℝ)≤c by linarith [h.c_lower])
    (show c≤501/500 by linarith [h.c_upper]) hh
    (show Real.sin frameCap*(501/500)≤(673/1000:ℝ) by linarith [(transport_trig hh).2.2.2.1])
  have hX2 : (pairNorm (673/1000) (501/500) 0)^2=(673/1000:ℝ)^2+(501/500)^2 := by
    simp only [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hY2 := SoleLowGap.negative_norm_square (by norm_num : (0:ℝ)<673/1000)
    (by norm_num : (0:ℝ)<501/500) hh
  have hX0 : 0≤pairNorm (673/1000) (501/500) 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm (673/1000) (501/500) (-frameCap) := Real.sqrt_nonneg _
  have hX : pairNorm (673/1000) (501/500) 0≤151/125 := by nlinarith
  have hY : (383/500:ℝ)≤pairNorm (673/1000) (501/500) (-frameCap) := by
    nlinarith [(transport_trig hh).2.2.2.1]
  have hdiff : pairNorm (673/1000) (501/500) 0-
      pairNorm (673/1000) (501/500) (-frameCap)≤221/500 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hR.1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
  have hpen := mul_le_mul (show (17253/20000:ℝ)≤c by linarith [h.c_lower])
    hclo (by norm_num : (0:ℝ)≤117/500) hc.le
  dsimp [normGain,V] at *
  nlinarith [hR.2]

theorem wide_dominates {R p q nu t k l c eta : ℝ}
    (hR : 0≤R) (hQL : Candidate.qLow≤R^2) (hQU : R^2≤Candidate.qCap)
    (hp : SoleLowChargeBounds.base≤p) (hpq : p≤q) (hq : q∈Icc 1 (21/20:ℝ))
    (hnu : nu≤21/20) (h : Bounds t k l c eta) :
    V R l c t≤Vnu R p q nu t ∧ V R l c frameCap≤Vnu R p q nu frameCap := by
  have hq' : q∈Icc 1 (28/25:ℝ) := ⟨hq.1,by linarith [hq.2]⟩
  have hn' : nu≤28/25 := by linarith
  have ht' : t∈SoleECoefficients.domain .low := ⟨h.angle.1,by linarith [h.angle_upper]⟩
  have hR2 : R≤2 := by norm_num [Candidate.qCap] at hQU; nlinarith
  constructor
  · have hw := SoleLowChargeBounds.wide_short hR hQL hp hpq hq' hn' ht'
    have hB := B_short hR hQU h
    nlinarith [h.angle.1]
  · linarith [SoleLowChargeBounds.wide_cap hR hQL hp hpq hq' hn',B_cap ⟨hR,hR2⟩ h]

end SquaresInCircles.Eight.TableFree.CriticalEPureCharges
