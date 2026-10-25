module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CutData

/-!
# Squared-norm bounds at the original negative-A angle cuts

Uncompiled transcription of equations (59)--(63). The lower sine
polynomial may be negative at the left endpoint. The rotated-norm proof
first compares it with the actual nonnegative sine, before decreasing
either the cosine-square multiplier or the tilted coefficient.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (h)

private theorem r41_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc ((left .high:ℚ):ℝ) ((right .high:ℚ):ℝ) := by
  norm_num [left,right,split,PositiveTD.Certificate.h]
  exact hz

theorem cut_cosine_squares (e : Cut) :
    (gammaLo e:ℝ)^2≤(Real.cos (cutAngle e:ℝ))^2 ∧
      (Real.cos (cutAngle e:ℝ))^2≤(gammaHi e:ℝ)^2 := by
  obtain ⟨hg0,hglo,hghi,_,_,_⟩ := cut_trig_bounds e
  have hc0 : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  exact ⟨pow_le_pow_left₀ hg0 hglo 2,pow_le_pow_left₀ hc0 hghi 2⟩

theorem cut_base_norm_bounds (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) :
    (scaledNorms .high (cutAtG e) (cutAngle e:ℝ) z i)^2≤aeval z (cutP0 e i) := by
  have hz' := r41_high_dom (cut_high_domain e hz)
  have hn := ordinary_norm_bounds .high hz'
  have hcos := (cut_cosine_squares e).2
  have hc : 0<Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  fin_cases i
  · have hp := mul_le_mul hcos hn.1 (sq_nonneg _) (sq_nonneg _)
    by_cases hG : cutAtG e=true <;>
      simpa [cutP0,hG,scaledNorms,norms,mul_pow] using hp
  · by_cases hG : cutAtG e=true
    · have hp := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.k .high z))
      have hb : (Real.cos (cutAngle e:ℝ)*pairNorm (Explicit.k .high z)
          (secant (Explicit.l .high z) (cutAngle e:ℝ)) 0)^2≤
          (Explicit.l .high z)^2+(gammaHi e:ℝ)^2*(Explicit.k .high z)^2 := by
        rw [scaled_secant_norm_sq hc]
        linarith
      simpa [cutP0,hG,scaledNorms,norms,lambdaG] using hb
    · have hp := mul_le_mul hcos hn.2.1 (sq_nonneg _) (sq_nonneg _)
      simpa [cutP0,hG,scaledNorms,norms,lambdaG,mul_pow] using hp
  · by_cases hG : cutAtG e=true
    · have hp := mul_le_mul hcos hn.2.2.1 (sq_nonneg _) (sq_nonneg _)
      simpa [cutP0,hG,scaledNorms,norms,lambdaB,mul_pow,Explicit.m] using hp
    · have hm := (tilted_bounds .high hz').2.2
      have hm0 := (family_positive .high hz').2.2.2
      have hm2 : (Explicit.m .high z)^2≤(aeval z (mHi .high))^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hm)
          (show 0≤aeval z (mHi .high)+Explicit.m .high z by linarith)]
      have hp := mul_le_mul hcos hm2 (sq_nonneg _) (sq_nonneg _)
      have hb : (Real.cos (cutAngle e:ℝ)*pairNorm
          (secant (Explicit.l .high z) (cutAngle e:ℝ)) (Explicit.m .high z) 0)^2≤
          (Explicit.l .high z)^2+(gammaHi e:ℝ)^2*(aeval z (mHi .high))^2 := by
        rw [secant_scaled_norm_sq hc]
        linarith
      simpa [cutP0,hG,scaledNorms,norms,lambdaB,Explicit.m] using hb
  · have hp := mul_le_mul hcos hn.2.2.2.1 (sq_nonneg _) (sq_nonneg _)
    by_cases hG : cutAtG e=true <;>
      simpa [cutP0,hG,scaledNorms,norms,mul_pow] using hp

/-- This is the sign-sensitive multiplication behind all three rotated
norm replacements, including a slightly negative polynomial sine. -/
theorem scaled_negative_norm_bound {s t p q P v sine lo hi : ℝ}
    (hp : 0<p) (hq : 0<q) (ht : t∈Icc 0 frameCap)
    (hlo : lo^2≤(Real.cos s)^2) (hhi : (Real.cos s)^2≤hi^2)
    (hP : p^2+q^2≤P) (hv0 : 0≤v) (hv : v≤p*q)
    (hsine : sine≤Real.sin t) :
    (Real.cos s*pairNorm p q (-t))^2≤hi^2*P-2*lo^2*v*sine := by
  have hsin0 : 0≤Real.sin t := (transport_trig ht).2.2.1
  have hbase := mul_le_mul hhi hP (by positivity : 0≤p^2+q^2) (sq_nonneg hi)
  have h₁ := mul_le_mul_of_nonneg_left hsine
    (mul_nonneg (sq_nonneg lo) hv0)
  have h₂ := mul_le_mul_of_nonneg_left hv
    (mul_nonneg (sq_nonneg lo) hsin0)
  have h₃ := mul_le_mul_of_nonneg_right hlo
    (show 0≤p*q*Real.sin t by positivity)
  have hn := PositiveTD.Certificate.negative_norm_sq_le hp hq ht (le_refl (Real.sin t))
  have hscaled := mul_le_mul_of_nonneg_left hn (sq_nonneg (Real.cos s))
  rw [mul_pow]
  nlinarith only [hbase,h₁,h₂,h₃,hscaled]

theorem cut_rotated_H_bound (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    (Real.cos (cutAngle e:ℝ)*pairNorm (Explicit.k .high z) 1
      (-(z-(cutAngle e:ℝ))))^2≤
      aeval z (C (gammaHi e)^2*PH .high-
        C (2*gammaLo e^2)*k .high*thetaSinLo e) := by
  have hk := (family_positive .high (r41_high_dom (cut_high_domain e hz))).1
  have hP : (Explicit.k .high z)^2+1^2≤aeval z (PH .high) := by simp [PH,add_comm]
  have hh := scaled_negative_norm_bound hk (by norm_num : (0:ℝ)<1)
    (cut_theta_domain e hz) (cut_cosine_squares e).1 (cut_cosine_squares e).2
    hP hk.le (by simp : Explicit.k .high z≤Explicit.k .high z*1)
    (theta_trig_lower e hz).2
  simp only [map_sub,map_mul,map_pow,aeval_C,eq_ratCast,k_eval,Rat.cast_ofNat]
  linarith only [hh]

theorem cut_rotated_G_bound (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    (Real.cos (cutAngle e:ℝ)*pairNorm (Explicit.k .high z) (Explicit.l .high z)
      (-(z-(cutAngle e:ℝ))))^2≤
      aeval z (C (gammaHi e)^2*PG .high-
        C (2*gammaLo e^2)*k .high*l .high*thetaSinLo e) := by
  obtain ⟨hk,hl,_,_⟩ := family_positive .high (r41_high_dom (cut_high_domain e hz))
  have hP : (Explicit.k .high z)^2+(Explicit.l .high z)^2≤aeval z (PG .high) := by simp [PG]
  have hh := scaled_negative_norm_bound hk hl
    (cut_theta_domain e hz) (cut_cosine_squares e).1 (cut_cosine_squares e).2
    hP (mul_nonneg hk.le hl.le) (le_refl (Explicit.k .high z*Explicit.l .high z))
    (theta_trig_lower e hz).2
  simp only [map_sub,map_mul,map_pow,aeval_C,eq_ratCast,k_eval,l_eval,Rat.cast_ofNat]
  linarith only [hh]

theorem cut_rotated_B_bound (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    (Real.cos (cutAngle e:ℝ)*pairNorm (Explicit.l .high z) (Explicit.m .high z)
      (-(z-(cutAngle e:ℝ))))^2≤
      aeval z (C (gammaHi e)^2*PB .high-
        C (2*gammaLo e^2)*l .high*mLo .high*thetaSinLo e) := by
  have hz' := r41_high_dom (cut_high_domain e hz)
  obtain ⟨_,hl,_,hm⟩ := family_positive .high hz'
  have hP := (ordinary_norm_bounds .high hz').2.2.1
  rw [PositiveTD.Certificate.zero_norm_sq] at hP
  obtain ⟨hmLo0,hmLo,_⟩ := tilted_bounds .high hz'
  have hv := mul_le_mul_of_nonneg_left hmLo hl.le
  have hh := scaled_negative_norm_bound hl hm
    (cut_theta_domain e hz) (cut_cosine_squares e).1 (cut_cosine_squares e).2
    hP (mul_nonneg hl.le hmLo0.le) hv (theta_trig_lower e hz).2
  simp only [map_sub,map_mul,map_pow,aeval_C,eq_ratCast,l_eval,Rat.cast_ofNat]
  linarith only [hh]

theorem cut_norm_bounds (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) :
    (cutNorms e z i)^2≤aeval z (cutP e i) := by
  by_cases hi : i=cutRole e
  · subst i
    cases e
    · simpa [cutNorms,cutP,cutRole,cutPCoefficient,cutQCoefficient] using
        cut_rotated_H_bound .gaH hz
    · simpa [cutNorms,cutP,cutRole,cutPCoefficient,cutQCoefficient] using
        cut_rotated_B_bound .gaB hz
    · simpa [cutNorms,cutP,cutRole,cutPCoefficient,cutQCoefficient] using
        cut_rotated_G_bound .abG hz
    · simpa [cutNorms,cutP,cutRole,cutPCoefficient,cutQCoefficient] using
        cut_rotated_H_bound .abH hz
  · simpa [cutNorms,cutP,hi] using cut_base_norm_bounds e hz i

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
