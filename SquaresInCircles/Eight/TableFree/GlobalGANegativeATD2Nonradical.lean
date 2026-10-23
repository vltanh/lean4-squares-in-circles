module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2ScalarData

/-!
# Elementary-term bounds for the fourteen negative-A endpoints

Uncompiled transcription of equations (37)--(38), (43), and (46)--(49)
of the scalar companion. In particular the positive factor in the
equal-angle cosine multiplication is proved from the weight ranges.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h)

theorem elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) : aeval z (elementary f)≤nonradical f z := by
  have hz' := family_frame_domain f hz
  have hc := (family_positive f hz).2.2.1
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  have hm := (tilted_bounds f hz).2.1
  have hs := PositiveTD.Certificate.sigma_sine_upper hz' hc.le
  have hw0 := mul_le_mul_of_nonneg_left
    (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
  have hw : Explicit.c f z*aeval z widthLo≤Explicit.c f z*edgeWidth z := by
    rw [edgeWidth_positive_formula hz']
    norm_num [widthLo]
    nlinarith only [hw0]
  have hD := mul_le_mul_of_nonneg_left PositiveTD.Certificate.diagonal_le_cbar
    (show 0≤1+Explicit.c f z by linarith)
  cases f <;>
    norm_num only [elementary,nonradical,↓reduceIte,map_add,map_sub,map_mul,map_neg,
      map_one,aeval_C,k_eval,l_eval,c_eval] at ⊢ <;>
    nlinarith only [hm,hs,hw,hD]

theorem sine_upper_polynomial_le {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z S9≤z := by
  have hz1 : z≤1 := by dsimp [frameCap] at hz; linarith [hz.2]
  have hz2 := pow_le_pow_left₀ hz.1 hz1 2
  have h3 := mul_nonneg (pow_nonneg hz.1 3)
    (show 0≤1/6-z^2/120 by nlinarith)
  have h7 := mul_nonneg (pow_nonneg hz.1 7)
    (show 0≤1/5040-z^2/362880 by nlinarith)
  norm_num [S9,S5]
  nlinarith

theorem elementary_minus_l_positive (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    (5:ℝ)<aeval z (elementary f)-Explicit.l f z := by
  have hz' := family_frame_domain f hz
  have hc := (family_positive f hz).2.2.1
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  have hs9 := sine_upper_polynomial_le hz'
  have hs90 : 0≤aeval z S9 := le_trans (transport_trig hz').2.2.1 ht.2.2.1
  have hfactor : (1/2:ℝ)≤aeval z C10+(etaQ:ℝ)*aeval z S11 := by
    norm_num [etaQ]
    nlinarith [ht.1,ht.2.2.2.1]
  have hm0 := mul_le_mul_of_nonneg_left hfactor hc.le
  have hm : Explicit.c f z/2≤aeval z (mLo f) := by
    norm_num only [mLo,PositiveTD.Certificate.mMinus,map_mul,map_add,aeval_C,c_eval]
    nlinarith only [hm0]
  have hw0 : (3/4:ℝ)≤aeval z widthLo := by
    norm_num [widthLo]
    linarith [ht.1,ht.2.2.2.1]
  have hw := mul_le_mul_of_nonneg_left hw0 hc.le
  cases f
  · obtain ⟨hk,_,hl,_,hclo,hchi⟩ := low_ranges hz
    have hs9hi : aeval z S9≤(1/5:ℝ) := by
      norm_num [left,right,split] at hz
      linarith [hz.2]
    have hp := mul_le_mul hchi hs9hi hs90 (by norm_num : (0:ℝ)≤19/10)
    have hs := mul_le_mul_of_nonneg_right hp
      (by norm_num [sigmabar] : (0:ℝ)≤(sigmabar:ℝ))
    have hd := mul_le_mul_of_nonneg_left
      (by norm_num [cbar] : (cbar:ℝ)≤9/10)
      (show 0≤1+Explicit.c .low z by linarith)
    norm_num only [elementary,↓reduceIte,map_add,map_sub,map_mul,map_neg,map_one,
      aeval_C,k_eval,l_eval,c_eval] at ⊢
    norm_num [sigmabar] at hs
    nlinarith only [hk,hl,hclo,hm,hw,hs,hd]
  · obtain ⟨hk,_,hl,_,hclo,hchi,_,_⟩ := high_ranges hz
    have hs9hi : aeval z S9≤(7/10:ℝ) := by
      dsimp [frameCap] at hz'
      linarith [hz'.2]
    have hp := mul_le_mul hchi hs9hi hs90 (by norm_num : (0:ℝ)≤1)
    have hs := mul_le_mul_of_nonneg_right hp
      (by norm_num [sigmabar] : (0:ℝ)≤(sigmabar:ℝ))
    norm_num only [elementary,↓reduceIte,map_add,map_sub,map_mul,map_neg,map_one,
      aeval_C,k_eval,l_eval,c_eval] at ⊢
    norm_num [sigmabar] at hs
    nlinarith only [hk,hl,hclo,hm,hw,hs]

theorem equal_elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    aeval z (AZ f)≤Real.cos z*(nonradical f z-Explicit.l f z)+
      Explicit.l f z+(13/12)*Explicit.l f z*Real.sin z := by
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain f hz)
  have hI := elementary_lower f hz
  have hI0 : 0≤aeval z (elementary f)-Explicit.l f z := by
    linarith [elementary_minus_l_positive f hz]
  have hc0 : 0≤Real.cos z := by linarith [(transport_trig (family_frame_domain f hz)).1]
  have hp := mul_le_mul ht.2.2.2.2.1
    (sub_le_sub_right hI (Explicit.l f z)) hI0 hc0
  have hs := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤(13/12)*Explicit.l f z by have hh := (family_positive f hz).2.1; positivity)
  norm_num only [AZ,map_add,map_sub,map_mul,aeval_C,l_eval]
  nlinarith only [hp,hs]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
