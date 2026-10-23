module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEnvelopeGeometry

/-!
# Whole-interval secants for the BT3 low family

Uncompiled Section 8 of
`HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md`.
The H endpoint is concave in its coefficient, with its derivative
bounded at K and its value bounded at k0. The B derivative is bounded
at the far angular endpoint on its complete coefficient interval.
All radical estimates use the displayed positive-square reserves.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LowSecants
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope OrdinaryCurvatureBounds
open TwoPositive.Coefficient

abbrev k0 : ℝ := 2933/5000
abbrev m0 : ℝ := 10163/10000

def J (k : ℝ) : ℝ := V R k 1 frameCap
def JD (k : ℝ) : ℝ := R*(normD 1 0 k-normD 1 (-frameCap) k)
def JDD (k : ℝ) : ℝ := R*(normDD 1 0 k-normDD 1 (-frameCap) k)

theorem J_derivative {k : ℝ} (hk : 0<k) : HasDerivAt J (JD k) k := by
  have h0 := norm_derivative (l:=1) (s:=0) (by norm_num) hk (by norm_num [frameCap])
  have hh := norm_derivative (l:=1) (s:=-frameCap) (by norm_num) hk (by norm_num [frameCap])
  convert (hasDerivAt_const k (Real.cos frameCap-1)).sub ((hh.sub h0).const_mul R) using 1
  · funext x
    dsimp [J,V]
    rw [pairNorm_symm x 1]
    rw [pairNorm_symm x 1]
    ring
  · dsimp [JD]
    ring

theorem JD_derivative {k : ℝ} (hk : 0<k) : HasDerivAt JD (JDD k) k := by
  exact ((norm_second (l:=1) (s:=0) (by norm_num) hk (by norm_num [frameCap])).sub
    (norm_second (l:=1) (s:=-frameCap) (by norm_num) hk (by norm_num [frameCap]))).const_mul R

theorem cap_norm_sq {k : ℝ} (hk : 0<k) :
    (pairNorm 1 k (-frameCap))^2=1+k^2-2*k*Real.sin frameCap := by
  simpa using NonnegativeTotals.Analytic.norm_negative_square
    (by norm_num : (0:ℝ)<1) hk (show frameCap∈Icc 0 frameCap by norm_num [frameCap])

/-- The quadratic upper bound is convex and below .768 squared at
both original coefficient endpoints; its maximum is the left endpoint. -/
theorem H_cap_norm_upper {k : ℝ} (hk : k∈Icc k0 K) :
    pairNorm 1 k (-frameCap)<96/125 := by
  have hk0 : 0<k := by dsimp [k0] at hk; linarith [hk.1]
  have hsq := cap_norm_sq hk0
  have hchord := mul_nonneg (sub_nonneg.mpr hk.1) (sub_nonneg.mpr hk.2)
  have hs := mul_le_mul_of_nonneg_left cap_sin_lower.le hk0.le
  have hn : 0≤pairNorm 1 k (-frameCap) := Real.sqrt_nonneg _
  dsimp [k0,K] at *
  nlinarith only [hsq,hchord,hs,hk.1,hk.2,hn]

theorem JDD_negative {k : ℝ} (hk : k∈Icc k0 K) : JDD k<0 := by
  have hk0 : 0<k := by dsimp [k0] at hk; linarith [hk.1]
  have hN0 : 1≤pairNorm 1 k 0 := by
    have hsq := NonnegativeTotals.Analytic.norm_zero_square 1 k
    have hn : 0≤pairNorm 1 k 0 := Real.sqrt_nonneg _
    nlinarith [sq_nonneg k]
  have hN : 0<pairNorm 1 k (-frameCap) := pairNorm_pos (by norm_num) hk0 (by norm_num [frameCap])
  have hNhi := H_cap_norm_upper hk
  have hcube0 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hN0 3
  have hcube := pow_le_pow_left₀ hN.le hNhi.le 3
  have hcos := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
  have hfirst : normDD 1 0 k≤1 := by
    simp only [normDD,one_pow,Real.cos_zero,mul_one,one_mul]
    exact (div_le_one (pow_pos (by linarith : 0<pairNorm 1 k 0) 3)).mpr (by simpa using hcube0)
  have hsecond : 1<normDD 1 (-frameCap) k := by
    simp only [normDD,one_pow,one_mul,Real.cos_neg]
    apply (lt_div_iff₀ (pow_pos hN 3)).mpr
    norm_num at hcube
    nlinarith only [hcube,hcos]
  have hR : 0<R := by linarith [radius_bounds.1]
  exact mul_neg_of_pos_of_neg hR (sub_neg.mpr (hfirst.trans_lt hsecond))

theorem JD_antitone : AntitoneOn JD (Icc k0 K) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun k hk => (JD_derivative (by dsimp [k0] at hk; linarith [hk.1])).continuousAt.continuousWithinAt)
    (fun k hk => JD_derivative (by dsimp [k0] at hk; linarith [hk.1]))
  intro k hk
  exact (JDD_negative (Ioo_subset_Icc_self hk)).le

theorem JD_at_K : (1:ℝ)<JD K := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN0 := pairNorm_pos (p:=1) (q:=K) (t:=0) (by norm_num) (by norm_num [K]) (by norm_num [frameCap])
  have hN := pairNorm_pos (p:=1) (q:=K) (t:=-frameCap) (by norm_num) (by norm_num [K]) (by norm_num [frameCap])
  have hN02 := NonnegativeTotals.Analytic.norm_zero_square 1 K
  have hN2 := cap_norm_sq (by norm_num [K] : (0:ℝ)<K)
  have hsin := (transport_trig hh).2.2.2.1
  have hN0hi : pairNorm 1 K 0<301/250 := by norm_num [K] at hN02; nlinarith
  have hNlo : (191/250:ℝ)<pairNorm 1 K (-frameCap) := by
    norm_num [K] at hN2
    nlinarith
  have hnum : K-Real.sin frameCap<(1/40:ℝ) := by dsimp [K]; linarith [cap_sin_lower]
  have hfirst : K/(301/250)<normD 1 0 K := by
    simp only [normD,Real.sin_zero,mul_zero,add_zero]
    apply (div_lt_div_iff₀ (by norm_num : (0:ℝ)<301/250) hN0).mpr
    have hprod := mul_lt_mul_of_pos_left hN0hi (by norm_num : (0:ℝ)<K)
    nlinarith only [hprod]
  have hsecond : normD 1 (-frameCap) K<(1/40)/(191/250) := by
    simp only [normD,Real.sin_neg,one_mul]
    apply (div_lt_div_iff₀ hN (by norm_num : (0:ℝ)<191/250)).mpr
    nlinarith only [hnum,hNlo]
  have hdiff : K/(301/250)-(1/40)/(191/250)<normD 1 0 K-normD 1 (-frameCap) K := by linarith
  have hR : 0<R := by linarith [radius_bounds.1]
  have hprod := mul_lt_mul_of_pos_left hdiff hR
  have hrad := mul_lt_mul_of_pos_right
    (show (989/500:ℝ)<R by linarith [sqrt_cap_lower])
    (show (0:ℝ)<K/(301/250)-(1/40)/(191/250) by norm_num [K])
  dsimp [JD,K] at *
  norm_num at hprod hrad ⊢
  linarith

theorem J_at_k0 : (541/1000:ℝ)<J k0 := by
  have hN0 := pairNorm_pos (p:=1) (q:=k0) (t:=0) (by norm_num) (by norm_num [k0]) (by norm_num [frameCap])
  have hN := pairNorm_pos (p:=1) (q:=k0) (t:=-frameCap) (by norm_num) (by norm_num [k0]) (by norm_num [frameCap])
  have hN02 := NonnegativeTotals.Analytic.norm_zero_square 1 k0
  have hN2 := cap_norm_sq (by norm_num [k0] : (0:ℝ)<k0)
  have hs7 := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hN0lo : (1159353/1000000:ℝ)<pairNorm 1 k0 0 := by
    norm_num [k0] at hN02
    nlinarith
  have hNhi : pairNorm 1 k0 (-frameCap)<76701/100000 := by
    norm_num [frameCap] at hs7
    norm_num [k0] at hN2
    nlinarith
  have hgap : (392343/1000000:ℝ)<pairNorm 1 k0 0-pairNorm 1 k0 (-frameCap) := by linarith
  have hprod := mul_lt_mul_of_pos_left hgap (show 0<R by linarith [radius_bounds.1])
  have hrad := mul_lt_mul_of_pos_right sqrt_cap_lower (by norm_num : (0:ℝ)<392343/1000000)
  have hcos := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
  rw [J,V,pairNorm_symm k0 1,pairNorm_symm k0 1]
  nlinarith only [hprod,hrad,hcos]

theorem J_linear_lower {k : ℝ} (hk : k∈Icc k0 K) :
    (541/1000:ℝ)+(k-k0)<J k := by
  have hder (z : ℝ) (hz : z∈Icc k0 K) : 1≤JD z := by
    have hh := JD_antitone hz (show K∈Icc k0 K by norm_num [k0,K]) hz.2
    linarith [JD_at_K]
  have hh := derivative_reserve
    (fun z hz => (J_derivative (by dsimp [k0] at hz; linarith [hz.1])).continuousAt.continuousWithinAt)
    (fun z hz => J_derivative (by dsimp [k0] at hz; linarith [hz.1]))
    (fun z hz => hder z (Ioo_subset_Icc_self hz))
    (show k0∈Icc k0 K by norm_num [k0,K]) hk hk.1
  linarith [J_at_k0]

theorem H_small_upper {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    V R (lowK t) 1 t≤(1101/1000)*t := by
  have hk := (Analytic.low_ranges ht).1
  have htf := PositiveTD.Certificate.low_frame_domain ht
  have hh := PositiveTD.V_first_coefficient (by norm_num : (0:ℝ)<1)
    (by linarith [hk.1]) hk.2 (by norm_num [K]) htf
  exact hh.trans (vstar_linear_upper htf)

theorem H_secant {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    V R (lowK t) 1 t+(3/4)*(frameCap-t)<V R (lowK t) 1 frameCap := by
  have hh := J_linear_lower (Analytic.low_ranges ht).1
  have hu := H_small_upper ht
  dsimp [J,lowK,k0,frameCap] at *
  linarith [ht.1]

theorem B_small {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    V R (lowK t) 1 t≤V R 1 (lowM t) t := by
  have hr := Analytic.low_ranges ht
  have hfirst : V R (lowK t) 1 t≤V R 1 1 t :=
    PositiveTD.V_first_coefficient (by norm_num) (by linarith [hr.1.1])
      (by dsimp [K] at hr; linarith [hr.1.2]) (by norm_num)
      (PositiveTD.Certificate.low_frame_domain ht)
  exact hfirst.trans (PositiveTD.V_short_second_coefficient (by norm_num) (by norm_num)
    (by linarith [hr.2.1]) (by dsimp [Cmax] at hr; linarith [hr.2.2]) ht)

theorem B_cap_norm_upper {m : ℝ} (hm : m∈Icc m0 Cmax) :
    pairNorm 1 m (-frameCap)<463/500 := by
  have hm0 : 0<m := by dsimp [m0] at hm; linarith [hm.1]
  have hsq := cap_norm_sq hm0
  have hchord := mul_nonneg (sub_nonneg.mpr hm.1) (sub_nonneg.mpr hm.2)
  have hs := mul_le_mul_of_nonneg_left cap_sin_lower.le hm0.le
  have hn : 0≤pairNorm 1 m (-frameCap) := Real.sqrt_nonneg _
  dsimp [m0,Cmax] at *
  nlinarith only [hsq,hchord,hs,hm.1,hm.2,hn]

theorem B_slope_at_cap {m : ℝ} (hm : m∈Icc m0 Cmax) :
    (1:ℝ)<Vd R 1 m frameCap := by
  have hm0 : 0<m := by dsimp [m0] at hm; linarith [hm.1]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=1) (q:=m) (t:=-frameCap) (by norm_num) hm0 (by norm_num [frameCap])
  have hnorm := B_cap_norm_upper hm
  have hcos := (transport_trig hh).1
  have hsin := (transport_trig hh).2.2.2.1
  have hc0 : 0<Real.cos frameCap := by linarith
  have hnum1 := mul_lt_mul_of_pos_right
    (show (989/500:ℝ)<R by linarith [sqrt_cap_lower]) hc0
  have hnum2 := mul_lt_mul_of_pos_left hcos (by norm_num : (0:ℝ)<989/500)
  have hfrac : ((989/500:ℝ)*(478/625))/(463/500)<R*Real.cos frameCap/pairNorm 1 m (-frameCap) := by
    apply (lt_div_iff₀ hn).mpr
    have hp := mul_lt_mul_of_pos_left hnorm
      (by norm_num : (0:ℝ)<((989/500:ℝ)*(478/625))/(463/500))
    nlinarith only [hp,hnum1,hnum2]
  have hbracket : -(129/200:ℝ)+((989/500)*(478/625))/(463/500)<
      -Real.sin frameCap+R*Real.cos frameCap/pairNorm 1 m (-frameCap) := by linarith
  have hprod := mul_lt_mul_of_pos_left hbracket hm0
  have hbase := mul_le_mul_of_nonneg_right hm.1
    (by norm_num : (0:ℝ)≤-(129/200:ℝ)+((989/500)*(478/625))/(463/500))
  have hid : Vd R 1 m frameCap=
      m*(-Real.sin frameCap+R*Real.cos frameCap/pairNorm 1 m (-frameCap)) := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [hid]
  dsimp [m0] at hbase
  norm_num at hprod hbase ⊢
  linarith

theorem B_slope {m s : ℝ} (hm : m∈Icc m0 Cmax) (hs : s∈Icc 0 frameCap) :
    (1:ℝ)<Vd R 1 m s := by
  have hm1 : 1≤m := by dsimp [m0] at hm; linarith [hm.1]
  have hm2 : m≤2*(1:ℝ) := by dsimp [Cmax] at hm; linarith [hm.2]
  have ha := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) hm1 hm2
  exact (B_slope_at_cap hm).trans_le
    (ha hs (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs.2)

theorem B_secant {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    V R (lowK t) 1 t+(3/4)*(frameCap-t)<V R 1 (lowM t) frameCap := by
  have hm := (Analytic.low_ranges ht).2
  have hm0 : 0<lowM t := by linarith [hm.1]
  have htf := PositiveTD.Certificate.low_frame_domain ht
  have hg := derivative_reserve
    (fun s hs => (V_hasDerivAt (by norm_num : (0:ℝ)<1) hm0 hs).continuousAt.continuousWithinAt)
    (fun s hs => V_hasDerivAt (by norm_num : (0:ℝ)<1) hm0 (Ioo_subset_Icc_self hs))
    (fun s hs => (B_slope hm (Ioo_subset_Icc_self hs)).le)
    htf (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) htf.2
  have hp := B_small ht
  dsimp [frameCap] at *
  linarith [ht.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LowSecants
