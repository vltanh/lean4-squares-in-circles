module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2ScalarIdentities

/-!
# The five actual low negative-DE scalar endpoints

Uncompiled transfer of (51)--(57).  The mixed endpoint retains the
original G same-block correction, the separated endpoints retain the
largest tilted B coefficient, and the equal-angle endpoint uses the
actual diagonal D support with its secant cancelled by cosine.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 C4 ch Ch sh h cbar num3
  taylor_bounds pairNorm_nonneg num3_transfer ch_cast Ch_cast sh_cast)

private theorem r74_low {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    θ∈Icc ((left .low:ℚ):ℝ) ((right .low:ℚ):ℝ) := by
  simpa [left,right,PositiveTD.Certificate.L] using hθ

theorem low_mixed_charge {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ ZG≤Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
      Explicit.l .low θ*(Real.cos frameCap-Real.cos θ) := by
  obtain ⟨hk,hl,_,_⟩ := split_positive .low .atT (r74_low hθ)
  have hθ' := family_frame_domain .low (r74_low hθ)
  have ht := taylor_bounds hθ'
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have htcap := taylor_bounds hcap
  have hs : 0≤Real.sin θ := (transport_trig hθ').2.2.1
  have hsum : (ch:ℝ)+(sh:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
    rw [ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.1]
  have hsum0 : 0≤Real.cos frameCap+Real.sin frameCap := by
    linarith [(transport_trig hcap).1,(transport_trig hcap).2.2.1]
  have hprod := mul_le_mul hsum ht.2.2.2.2.1
    (show 0≤aeval θ C10 by linarith [ht.2.2.2.1]) hsum0
  have hdiff : Real.cos frameCap-Real.sin frameCap≤(Ch:ℝ)-(sh:ℝ) := by
    rw [Ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.2]
  have hdiff0 : 0≤(Ch:ℝ)-(sh:ℝ) := by
    linarith [(transport_trig hcap).2.2.2.2]
  have hprod' := mul_le_mul hdiff ht.2.2.1 hs hdiff0
  have hphi : PositiveAngularEnvelope.phi (frameCap-θ)=
      (Real.cos frameCap+Real.sin frameCap)*Real.cos θ-
        (Real.cos frameCap-Real.sin frameCap)*Real.sin θ := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  have hphiLower : ((ch:ℝ)+(sh:ℝ))*aeval θ C10-
      ((Ch:ℝ)-(sh:ℝ))*aeval θ S9≤PositiveAngularEnvelope.phi (frameCap-θ) := by
    rw [hphi]
    linarith
  have hK := mul_le_mul_of_nonneg_left (sub_le_sub_right hphiLower 1) hk.le
  have hcos : (ch:ℝ)-aeval θ C12≤Real.cos frameCap-Real.cos θ := by
    rw [ch_cast]
    linarith [htcap.2.2.2.2.1,ht.2.2.2.2.2]
  have hL := mul_le_mul_of_nonneg_left hcos hl.le
  simp only [ZG,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,eq_ratCast]
  linarith only [hK,hL]

theorem mixed_num3 (e : Split) : NM e=num3 (lowB e+C10-1+ZG)
    (PHminus .low) (PG .low) (PB .low e) (RHminus .low) (RG .low) (RB .low e) := by
  dsimp [NM,NH,lowDen,num3]
  ring

theorem low_H_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0+V R (Explicit.k .low θ) 1 θ := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have ht := taylor_bounds (family_frame_domain .low (r74_low hθ))
  have hA : aeval θ (lowB e+C10-1)≤lowNonradical e θ+Real.cos θ-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [low_nonradical_lower e hθ,ht.2.2.2.2.1]
  have hp := num3_transfer
    (show 0<aeval θ (RHminus .low) from low_auxiliary_positive e 3 hθ)
    (show 0<aeval θ (RG .low) from low_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.1 hn.2.2.1 hA
    (by simpa [NH] using (low_numerators_positive e hθ).1)
  rw [low_H_identity e hθ θ]
  exact hp

theorem low_M_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0+V R (Explicit.k .low θ) 1 θ+
      Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
      Explicit.l .low θ*(Real.cos frameCap-Real.cos θ) := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have ht := taylor_bounds (family_frame_domain .low (r74_low hθ))
  have hA : aeval θ (lowB e+C10-1+ZG)≤lowNonradical e θ+Real.cos θ-1+
      (Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
        Explicit.l .low θ*(Real.cos frameCap-Real.cos θ)) := by
    simp only [map_add,map_sub,map_one]
    linarith [low_nonradical_lower e hθ,ht.2.2.2.2.1,low_mixed_charge hθ]
  have hP : 0<aeval θ (num3 (lowB e+C10-1+ZG) (PHminus .low) (PG .low)
      (PB .low e) (RHminus .low) (RG .low) (RB .low e)) := by
    rw [←mixed_num3]
    exact (low_numerators_positive e hθ).2.1
  have hp := num3_transfer
    (show 0<aeval θ (RHminus .low) from low_auxiliary_positive e 3 hθ)
    (show 0<aeval θ (RG .low) from low_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.1 hn.2.2.1 hA hP
  rw [low_H_identity e hθ θ]
  linarith only [hp]

theorem low_separated_nonradical (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (lowB e-C (109/200)*mHi .low e*(C PositiveTD.Certificate.h-X))≤
      lowNonradical e θ-(109/200)*Explicit.splitM .low e θ*(frameCap-θ) := by
  have ht := (tilted_bounds .low e (r74_low hθ)).2.2
  have hp := mul_le_mul_of_nonneg_right ht
    (sub_nonneg.mpr (family_frame_domain .low (r74_low hθ)).2)
  have hh : ((PositiveTD.Certificate.h:ℚ):ℝ)=frameCap := by
    norm_num [PositiveTD.Certificate.h,frameCap]
  have hl := low_nonradical_lower e hθ
  simp only [map_sub,map_mul,aeval_C,aeval_X,eq_ratCast,hh]
  push_cast
  generalize frameCap = F at hp ⊢
  linarith

theorem low_SH_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+
      V R (Explicit.k .low θ) 1 frameCap := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have hcap := cap_norm_bounds hθ
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hA : aeval θ (lowB e-C (109/200)*mHi .low e*(C PositiveTD.Certificate.h-X)+C (ch-1))≤
      lowNonradical e θ-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+Real.cos frameCap-1 := by
    simp only [map_add,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [low_separated_nonradical e hθ,ht.2.2.2.2.1]
  have hp := num3_transfer
    (show 0<aeval θ (RHcap) from low_auxiliary_positive e 4 hθ)
    (show 0<aeval θ (RG .low) from low_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hcap.1 hn.2.1 hn.2.2.1 hA (low_numerators_positive e hθ).2.2.1
  have he := low_H_identity e hθ frameCap
  linarith only [hp,he]

theorem low_SG_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+
      V R (Explicit.k .low θ) (Explicit.l .low θ) frameCap := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have hcap := cap_norm_bounds hθ
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hl := (split_positive .low e (r74_low hθ)).2.1
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 hl.le
  have hA : aeval θ (lowB e-C (109/200)*mHi .low e*(C PositiveTD.Certificate.h-X)+l .low*C (ch-1))≤
      lowNonradical e θ-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+
        Explicit.l .low θ*(Real.cos frameCap-1) := by
    simp only [map_add,map_mul,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,l_eval,ch_cast]
    linarith [low_separated_nonradical e hθ]
  have hp := num3_transfer
    (show 0<aeval θ (RH .low) from low_auxiliary_positive e 0 hθ)
    (show 0<aeval θ (RGcap) from low_auxiliary_positive e 5 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hcap.2 hn.2.2.1 hA (low_numerators_positive e hθ).2.2.2.1
  have he := low_G_identity e hθ frameCap
  linarith only [hp,he]

theorem low_equal_nonradical (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (C10*(lowB e+C dbar)+C K*S11-C dbar)≤
      Real.cos θ*(lowNonradical e θ+(GlobalGA.Secondary.diagonal-1/2))+Explicit.K*Real.sin θ-(GlobalGA.Secondary.diagonal-1/2) := by
  have ht := taylor_bounds (family_frame_domain .low (r74_low hθ))
  have hB : 0<aeval θ (lowB e+C dbar) := by
    simpa only [↓reduceIte] using multiplied_baseline_positive .low e (r74_low hθ)
  have h₁ := mul_le_mul_of_nonneg_right ht.2.2.2.2.1 hB.le
  have hc : 0≤Real.cos θ := by linarith [(transport_trig (family_frame_domain .low (r74_low hθ))).1]
  have h₂ := mul_le_mul_of_nonneg_left (low_nonradical_lower e hθ) hc
  have h₃ := mul_nonneg (sub_nonneg.mpr PositiveTD.Certificate.diagonal_le_cbar)
    (sub_nonneg.mpr (Real.cos_le_one θ))
  have hK : ((K:ℚ):ℝ)=Explicit.K := by norm_num [K,Explicit.K]
  have hhalf : ((1/2:ℚ):ℝ)=1/2 := by norm_num
  simp only [map_sub,map_add,map_mul,aeval_C,eq_ratCast,hhalf,hK] at h₁ ⊢
  have hK0 : 0≤Explicit.K := by norm_num [Explicit.K]
  have h₄ := mul_le_mul_of_nonneg_left ht.2.1 hK0
  generalize ((cbar:ℚ):ℝ) = cb at h₁ h₃ ⊢
  linarith only [h₁,h₂,h₃,h₄]

theorem low_Z_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ θ := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have hθ' := family_frame_domain .low (r74_low hθ)
  have hc : 0<Real.cos θ := by linarith [(transport_trig hθ').1]
  have hp := num3_transfer
    (show 0<aeval θ (C4*RH .low) from low_auxiliary_positive e 6 hθ)
    (show 0<aeval θ (C4*RG .low) from low_auxiliary_positive e 7 hθ)
    (show 0<aeval θ (C4*RB .low e) from low_auxiliary_positive e 8 hθ)
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (scaled_norm_bound hθ' hn.1) (scaled_norm_bound hθ' hn.2.1)
    (scaled_norm_bound hθ' hn.2.2.1) (low_equal_nonradical e hθ)
    (by simpa only [NZ,↓reduceIte] using (low_numerators_positive e hθ).2.2.2.2)
  rw [←low_equal_identity e hθ] at hp
  exact (mul_pos_iff_of_pos_left hc).mp hp

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
