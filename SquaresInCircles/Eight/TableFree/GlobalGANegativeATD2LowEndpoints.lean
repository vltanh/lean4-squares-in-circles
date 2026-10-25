module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2ScalarTransfer
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowTransfer

/-!
# The low mixed and separated negative-A / TD2 endpoints

Uncompiled transcription of equations (46)--(54) in the complete scalar
companion. The separated estimates keep the hand proof's larger
coefficient m + .4 z, which controls the original secant weight.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h ch Ch sh
  ch_cast Ch_cast sh_cast)

private theorem r41_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc ((left .low:ℚ):ℝ) ((right .low:ℚ):ℝ) := by
  norm_num [left,right,split]
  exact hz

theorem cap_norm_bounds {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    (pairNorm (Explicit.k .low z) 1 (-frameCap))^2≤aeval z PHcap ∧
    (pairNorm (Explicit.k .low z) (Explicit.l .low z) (-frameCap))^2≤aeval z PGcap := by
  have hzf := r41_low_dom hz
  obtain ⟨hk,hl,_,_⟩ := family_positive .low hzf
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hs := (PositiveTD.Certificate.taylor_bounds hcap).2.1
  have hH := PositiveTD.Certificate.negative_norm_sq_le (q:=1) hk (by norm_num) hcap hs
  have hG := PositiveTD.Certificate.negative_norm_sq_le hk hl hcap hs
  constructor
  · norm_num only [PHcap,PH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
      k_eval,eq_ratCast,Rat.cast_mul,sh_cast]
    linarith only [hH]
  · norm_num only [PGcap,PG,map_add,map_sub,map_mul,map_pow,aeval_C,
      k_eval,l_eval,eq_ratCast,Rat.cast_mul,sh_cast]
    linarith only [hG]

theorem phi_lower {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z phiLo≤PositiveAngularEnvelope.phi (frameCap-z) := by
  have ht := PositiveTD.Certificate.taylor_bounds hz
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have htcap := PositiveTD.Certificate.taylor_bounds hcap
  have hs : 0≤Real.sin z := (transport_trig hz).2.2.1
  have hsum : (ch:ℝ)+(sh:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
    rw [ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.1]
  have hsum0 : 0≤Real.cos frameCap+Real.sin frameCap := by
    linarith [(transport_trig hcap).1,(transport_trig hcap).2.2.1]
  have hp := mul_le_mul hsum ht.2.2.2.2.1
    (show 0≤aeval z C10 by linarith [ht.2.2.2.1]) hsum0
  have hdiff : Real.cos frameCap-Real.sin frameCap≤(Ch:ℝ)-(sh:ℝ) := by
    rw [Ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.2]
  have hdiff0 : 0≤(Ch:ℝ)-(sh:ℝ) := by
    linarith [(transport_trig hcap).2.2.2.2]
  have hp' := mul_le_mul hdiff ht.2.2.1 hs hdiff0
  have he : PositiveAngularEnvelope.phi (frameCap-z)=
      (Real.cos frameCap+Real.sin frameCap)*Real.cos z-
        (Real.cos frameCap-Real.sin frameCap)*Real.sin z := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  simp only [phiLo,map_sub,map_mul,aeval_C,eq_ratCast,Rat.cast_add]
  rw [he]
  linarith only [hp,hp']

theorem low_M_elementary {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    aeval z (elementary .low+k .low*(phiLo-1)+l .low*C (ch-1))≤
      nonradical .low z+Explicit.k .low z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
        Explicit.l .low z*(Real.cos frameCap-1) := by
  have hzf := r41_low_dom hz
  obtain ⟨hk,hl,_,_⟩ := family_positive .low hzf
  have hphi := mul_le_mul_of_nonneg_left
    (sub_le_sub_right (phi_lower (family_frame_domain .low hzf)) 1) hk.le
  have hcap := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [hcap.2.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_left hcos hl.le
  simp only [map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,eq_ratCast]
  linarith [elementary_lower .low hzf]

theorem low_M_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z := by
  have hzf := r41_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  obtain ⟨hrH,_,hrB,_,_,hrG,_⟩ := ordinary_masses_positive .low hzf
  have hp := PositiveTD.Certificate.num3_transfer hrH hrB hrG
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.1 hn.2.2.2.2.2.1 (low_M_elementary hz)
    (show 0<aeval z (PositiveTD.Certificate.num3 _ _ _ _ _ _ _) from
      (low_numerators_positive hz).2.2.1)
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  simp only [normSum,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at he
  unfold mixedG
  linarith only [hp,he,hl]

theorem low_separated_elementary {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    aeval z lowStar≤nonradical .low z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z) := by
  have hzf := r41_low_dom hz
  have hm := (tilted_bounds .low hzf).2.2
  have hgap : 0≤frameCap-z := by dsimp [frameCap]; linarith [hz.2]
  have hp : (Explicit.m .low z+(2/5)*z)*(frameCap-z)≤
      (aeval z (mHi .low)+(2/5)*z)*(frameCap-z) :=
    mul_le_mul_of_nonneg_right (by linarith) hgap
  simp only [lowStar,map_sub,map_mul,map_add,aeval_C,aeval_X,eq_ratCast]
  norm_num only [PositiveTD.Certificate.h]
  dsimp [frameCap] at hp ⊢
  linarith [elementary_lower .low hzf]

theorem low_SH_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        V R (Explicit.k .low z) 1 frameCap := by
  have hzf := r41_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  have hncap := cap_norm_bounds hz
  obtain ⟨_,hrG,hrB,_,_,_,_⟩ := ordinary_masses_positive .low hzf
  have hcap := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hA : aeval z (lowStar+C (ch-1))≤nonradical .low z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+Real.cos frameCap-1 := by
    simp only [map_add,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [low_separated_elementary hz,hcap.2.2.2.2.1]
  have hp := PositiveTD.Certificate.num3_transfer hrG hrB
    (show 0<aeval z (C (77/100):ℚ[X]) by simp only [aeval_C,eq_ratCast]; norm_num)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.1 hncap.1 hA
    (show 0<aeval z (PositiveTD.Certificate.num3 _ _ _ _ _ _ _) from
      (low_numerators_positive hz).2.2.2.1)
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  simp only [normSum,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at he
  unfold V
  linarith only [hp,he,hl]

theorem low_SG_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        V R (Explicit.k .low z) (Explicit.l .low z) frameCap := by
  have hzf := r41_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  have hncap := cap_norm_bounds hz
  obtain ⟨hrH,_,hrB,_,_,_,_⟩ := ordinary_masses_positive .low hzf
  have hlpos := (family_positive .low hzf).2.1
  have hcap := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [hcap.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hcos hlpos.le
  have hA : aeval z (lowStar+l .low*C (ch-1))≤nonradical .low z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        Explicit.l .low z*(Real.cos frameCap-1) := by
    simp only [map_add,map_mul,aeval_C,l_eval,eq_ratCast,Rat.cast_sub,Rat.cast_one]
    linarith [low_separated_elementary hz]
  have hrG : 0<aeval z (C (77/100)*l .low) := by
    simp only [map_mul,aeval_C,l_eval,eq_ratCast]
    have := hlpos
    positivity
  have hp := PositiveTD.Certificate.num3_transfer hrH hrB hrG
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.1 hncap.2 hA
    (show 0<aeval z (PositiveTD.Certificate.num3 _ _ _ _ _ _ _) from
      (low_numerators_positive hz).2.2.2.2)
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  simp only [normSum,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at he
  unfold V
  linarith only [hp,he,hl]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
