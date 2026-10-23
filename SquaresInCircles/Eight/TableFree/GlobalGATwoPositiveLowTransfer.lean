module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveAEnvelope
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveLowPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowTransfer

/-!
# The four low scalar inequalities at the all-A endpoint

Uncompiled translation of Section 4 of the complete two-positive scalar
proof.  The actual A support charge is retained, the D support is its
sorted diagonal branch, and each of the four displayed numerators is
transferred to the corresponding original force norms.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD
open PositiveTD.Certificate

def lowANonradical (k l c a : ℝ) : ℝ :=
  2*k+3*l+(5/2)*c+5/2-(1+c)*diagonal+l*ASupport.charge a

theorem low_A_H_identity {k l c a v : ℝ} (hc : 1≤c) :
    baseline k l c 0+l*ASupport.charge a+V R k 1 v=
      lowANonradical k l c a+Real.cos v-1-
        R*(pairNorm k 1 (-v)+pairNorm k l 0+pairNorm l c 0) := by
  have he := PositiveTD.Certificate.low_H_identity (k:=k) (l:=l) (c:=c) (z:=0) (t:=v) hc
  simp only [tilted,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] at he
  have hw : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
  dsimp [lowNonradical] at he
  simp only [tilted,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,hw] at he
  dsimp [lowANonradical]
  linarith only [he]

theorem low_A_G_identity {k l c a v : ℝ} (hc : 1≤c) :
    baseline k l c 0+l*ASupport.charge a+V R k l v=
      lowANonradical k l c a+l*(Real.cos v-1)-
        R*(pairNorm k 1 0+pairNorm k l (-v)+pairNorm l c 0) := by
  have he := PositiveTD.Certificate.low_G_identity (k:=k) (l:=l) (c:=c) (z:=0) (t:=v) hc
  have hw : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
  dsimp [lowNonradical] at he
  simp only [tilted,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,hw] at he
  dsimp [lowANonradical]
  linarith only [he]

theorem low_A_nonradical_lower {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    aeval a lowA≤lowANonradical (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) a ∧
    aeval a lowAstar≤lowANonradical (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) a-
      (109/200)*Explicit.lowC a*(frameCap-a) := by
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges ha
  have hD := mul_le_mul_of_nonneg_left diagonal_le_cbar
    (show 0≤1+Explicit.lowC a by linarith)
  have hJ := mul_le_mul_of_nonneg_left (ASupport.low_polynomial_charge ha)
    (show 0≤Explicit.lowL a by linarith)
  constructor
  · norm_num only [lowA,map_add,map_sub,map_mul,map_one,aeval_C,lowK_eval,lowL_eval,lowC_eval]
    dsimp [lowANonradical]
    nlinarith only [hD,hJ]
  · norm_num only [lowAstar,lowA,map_add,map_sub,map_mul,map_one,aeval_C,aeval_X,
      lowK_eval,lowL_eval,lowC_eval,h]
    dsimp [lowANonradical,frameCap]
    nlinarith only [hD,hJ]

theorem low_A_norm_bounds {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    (pairNorm (Explicit.lowK a) 1 (-a))^2≤aeval a lowPH ∧
    (pairNorm (Explicit.lowK a) (Explicit.lowL a) 0)^2≤aeval a lowPG ∧
    (pairNorm (Explicit.lowL a) (Explicit.lowC a) 0)^2≤aeval a lowPB ∧
    (pairNorm (Explicit.lowK a) 1 (-frameCap))^2≤aeval a lowPHh ∧
    (pairNorm (Explicit.lowK a) 1 0)^2≤aeval a lowPH0 ∧
    (pairNorm (Explicit.lowK a) (Explicit.lowL a) (-frameCap))^2≤aeval a lowPGh := by
  have hh := PositiveTD.Certificate.low_norm_bounds ha
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [lowPH,PositiveTD.Certificate.lowPH] using hh.1
  · simpa only [lowPG,PositiveTD.Certificate.lowPG] using hh.2.1
  · rw [zero_norm_sq]
    simp [lowPB,add_comm]
  · simpa only [lowPHh,PositiveTD.Certificate.lowPHh] using hh.2.2.2.1
  · simpa only [lowPH0,PositiveTD.Certificate.lowPH0] using hh.2.2.2.2.1
  · simpa only [lowPGh,PositiveTD.Certificate.lowPGh] using hh.2.2.2.2.2

theorem low_A_mixed_charge {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    aeval a lowMixedCharge≤Explicit.lowK a*(phi (frameCap-a)-1)+
      Explicit.lowL a*(Real.cos frameCap-Real.cos a) := by
  simpa only [lowMixedCharge,PositiveTD.Certificate.lowJ] using
    PositiveTD.Certificate.low_J_lower ha

theorem low_A_PM_num3 :
    lowPM=num3 (lowA+C10-1+lowMixedCharge) lowPH lowPG lowPB lowRH lowRG lowRB := by
  dsimp [lowPM,lowP,lowDen,num3]
  ring

theorem low_A_H_positive {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) 0+
      Explicit.lowL a*ASupport.charge a+V R (Explicit.lowK a) 1 a := by
  have hr := low_masses_positive ha
  have hn := low_A_norm_bounds ha
  have ht := taylor_bounds (low_frame_domain ha)
  have hA : aeval a (lowA+C10-1)≤
      lowANonradical (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) a+
        Real.cos a-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [(low_A_nonradical_lower ha).1,ht.2.2.2.2.1]
  have hp := num3_transfer hr.1 hr.2.1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.1 hA (lowP_positive ha)
  have hh := Explicit.low_ranges ha
  rw [low_A_H_identity (by linarith [hh.2.2.1,hh.2.2.2.1])]
  exact hp

theorem low_A_M_positive {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) 0+
      Explicit.lowL a*ASupport.charge a+V R (Explicit.lowK a) 1 a+
      Explicit.lowK a*(phi (frameCap-a)-1)+
        Explicit.lowL a*(Real.cos frameCap-Real.cos a) := by
  have hr := low_masses_positive ha
  have hn := low_A_norm_bounds ha
  have ht := taylor_bounds (low_frame_domain ha)
  have hA : aeval a (lowA+C10-1+lowMixedCharge)≤
      lowANonradical (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) a+
        Real.cos a-1+Explicit.lowK a*(phi (frameCap-a)-1)+
          Explicit.lowL a*(Real.cos frameCap-Real.cos a) := by
    simp only [map_add,map_sub,map_one]
    linarith [(low_A_nonradical_lower ha).1,ht.2.2.2.2.1,low_A_mixed_charge ha]
  have hP : 0<aeval a (num3 (lowA+C10-1+lowMixedCharge)
      lowPH lowPG lowPB lowRH lowRG lowRB) := by
    rw [← low_A_PM_num3]
    exact lowPM_positive ha
  have hp := num3_transfer hr.1 hr.2.1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.1 hA hP
  have hh := Explicit.low_ranges ha
  rw [low_A_H_identity (by linarith [hh.2.2.1,hh.2.2.2.1])]
  linarith only [hp]

theorem low_A_SH_positive {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) 0+
      Explicit.lowL a*ASupport.charge a-(109/200)*Explicit.lowC a*(frameCap-a)+
        V R (Explicit.lowK a) 1 frameCap := by
  have hr := low_masses_positive ha
  have hn := low_A_norm_bounds ha
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hA : aeval a (lowAstar+C (ch-1))≤
      lowANonradical (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) a-
        (109/200)*Explicit.lowC a*(frameCap-a)+Real.cos frameCap-1 := by
    norm_num only [map_add,aeval_C,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [(low_A_nonradical_lower ha).2,ht.2.2.2.2.1]
  have hp := num3_transfer (show 0<aeval a (C (77/100):ℚ[X]) by norm_num)
    hr.2.1 hr.2.2 (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.1 hn.2.1 hn.2.2.1 hA (lowPSH_positive ha)
  have hh := Explicit.low_ranges ha
  have he := low_A_H_identity (k:=Explicit.lowK a) (l:=Explicit.lowL a)
    (c:=Explicit.lowC a) (a:=a) (v:=frameCap)
    (by linarith [hh.2.2.1,hh.2.2.2.1])
  linarith only [hp,he]

theorem low_A_SG_positive {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) 0+
      Explicit.lowL a*ASupport.charge a-(109/200)*Explicit.lowC a*(frameCap-a)+
        V R (Explicit.lowK a) (Explicit.lowL a) frameCap := by
  have hr := low_masses_positive ha
  have hn := low_A_norm_bounds ha
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges ha
  have hr0 : 0<aeval a (C (41/50)+C (143/250)*PositiveTD.Certificate.lowK) := by
    norm_num only [map_add,map_mul,aeval_C,lowK_eval]
    linarith
  have hr1 : 0<aeval a (C (153/200)*PositiveTD.Certificate.lowL) := by
    norm_num only [map_mul,aeval_C,lowL_eval]
    linarith
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [ht.2.2.2.2.1]
  have hL := mul_le_mul_of_nonneg_left hcos (by linarith : 0≤Explicit.lowL a)
  have hA : aeval a (lowAstar+PositiveTD.Certificate.lowL*C (ch-1))≤
      lowANonradical (Explicit.lowK a) (Explicit.lowL a) (Explicit.lowC a) a-
        (109/200)*Explicit.lowC a*(frameCap-a)+Explicit.lowL a*(Real.cos frameCap-1) := by
    norm_num only [map_add,map_mul,aeval_C,Rat.cast_sub,Rat.cast_one,lowL_eval]
    linarith [(low_A_nonradical_lower ha).2]
  have hp := num3_transfer hr0 hr1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.2.2.2.2 hn.2.2.1 hA (lowPSG_positive ha)
  have he := low_A_G_identity (k:=Explicit.lowK a) (l:=Explicit.lowL a)
    (c:=Explicit.lowC a) (a:=a) (v:=frameCap) (by linarith : 1≤Explicit.lowC a)
  linarith only [hp,he]

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
