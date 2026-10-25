module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Sole.BalancedCoefficients

/-!
# Eight squares: A small-total ordinary-angle gap with a fixed coefficient ratio

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
