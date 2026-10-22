module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Nonradical

/-!
# Actual squared-norm bounds for the negative-A scalar endpoints

Uncompiled transcription of equations (39), (44), and (45) in the
complete scalar companion. Equal-angle norms retain the actual positive
cosine factor, including its exact cancellation of the secant weight.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h)

theorem ordinary_norm_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    (pairNorm (Explicit.k f z) 1 0)^2≤aeval z (PH f) ∧
    (pairNorm (Explicit.k f z) (Explicit.l f z) 0)^2≤aeval z (PG f) ∧
    (pairNorm (Explicit.l f z) (Explicit.m f z) 0)^2≤aeval z (PB f) ∧
    (pairNorm (Explicit.c f z) 1 0)^2≤aeval z (PD f) ∧
    (pairNorm (Explicit.k f z) 1 (-z))^2≤aeval z (PHminus f) ∧
    (pairNorm (Explicit.k f z) (Explicit.l f z) (-z))^2≤aeval z (PGminus f) ∧
    (pairNorm (Explicit.l f z) (Explicit.m f z) (-z))^2≤aeval z (PBminus f) := by
  obtain ⟨hk,hl,hc,hm⟩ := family_positive f hz
  have hz' := family_frame_domain f hz
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  obtain ⟨hmLo0,hmLo,hmHi⟩ := tilted_bounds f hz
  have hm2 : (Explicit.m f z)^2≤(aeval z (mHi f))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmHi)
      (show 0≤aeval z (mHi f)+Explicit.m f z by linarith)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [PositiveTD.Certificate.zero_norm_sq]
    simp [PH,add_comm]
  · rw [PositiveTD.Certificate.zero_norm_sq]
    simp [PG]
  · rw [PositiveTD.Certificate.zero_norm_sq]
    simp only [PB,map_add,map_pow,l_eval]
    linarith
  · rw [PositiveTD.Certificate.zero_norm_sq]
    simp [PD,add_comm]
  · have hh := PositiveTD.Certificate.negative_norm_sq_le
      (q:=1) hk (by norm_num) hz' ht.2.1
    norm_num only [PHminus,PH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,k_eval]
    nlinarith only [hh]
  · have hh := PositiveTD.Certificate.negative_norm_sq_le hk hl hz' ht.2.1
    norm_num only [PGminus,PG,map_add,map_sub,map_mul,map_pow,aeval_C,k_eval,l_eval]
    nlinarith only [hh]
  · have hh := PositiveTD.Certificate.negative_norm_sq_le hl hm hz' ht.2.1
    have hp := mul_le_mul_of_nonneg_left hmLo
      (show 0≤2*Explicit.l f z*aeval z S11 by positivity)
    norm_num only [PBminus,PB,map_add,map_sub,map_mul,map_pow,aeval_C,l_eval]
    nlinarith only [hh,hp,hm2]

theorem cosine_square_upper {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (Real.cos z)^2≤(aeval z C12)^2 := by
  have ht := PositiveTD.Certificate.taylor_bounds hz
  have hc : 0≤Real.cos z := by linarith [(transport_trig hz).1]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.2.2.2.2)
    (show 0≤aeval z C12+Real.cos z by linarith [ht.2.2.2.2.2])]

theorem scaled_secant_norm_sq {a l s : ℝ} (hc : 0<Real.cos s) :
    (Real.cos s*pairNorm a (secant l s) 0)^2=(Real.cos s)^2*a^2+l^2 := by
  rw [mul_pow,PositiveTD.Certificate.zero_norm_sq]
  dsimp [secant]
  field_simp [hc.ne']
  ring

theorem secant_scaled_norm_sq {a l s : ℝ} (hc : 0<Real.cos s) :
    (Real.cos s*pairNorm (secant l s) a 0)^2=l^2+(Real.cos s)^2*a^2 := by
  rw [pairNorm_symm (secant l s) a 0,scaled_secant_norm_sq hc]
  ring

theorem equal_GA_norm_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) (i : Fin 4) :
    (scaledNorms f true z z i)^2≤aeval z (equalGAP f i) := by
  have hn := ordinary_norm_bounds f hz
  have hcos := cosine_square_upper (family_frame_domain f hz)
  have hc : 0<Real.cos z := by linarith [(transport_trig (family_frame_domain f hz)).1]
  fin_cases i
  · have hp := mul_le_mul hcos hn.1 (sq_nonneg _) (sq_nonneg _)
    simpa [scaledNorms,norms,equalGAP,mul_pow] using hp
  · have hp := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.k f z))
    simp only [scaledNorms,norms,lambdaG,↓reduceIte,Matrix.cons_val_succ,
      Matrix.cons_val_zero,scaled_secant_norm_sq hc]
    norm_num only [equalGAP,Matrix.cons_val_succ,Matrix.cons_val_zero,
      map_add,map_mul,map_pow,k_eval,l_eval]
    nlinarith only [hp]
  · have hp := mul_le_mul hcos hn.2.2.1 (sq_nonneg _) (sq_nonneg _)
    simpa [scaledNorms,norms,lambdaB,equalGAP,mul_pow,Explicit.m] using hp
  · have hp := mul_le_mul hcos hn.2.2.2.1 (sq_nonneg _) (sq_nonneg _)
    simpa [scaledNorms,norms,equalGAP,mul_pow] using hp

theorem equal_AB_norm_bounds {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    (scaledNorms .high false z z i)^2≤aeval z (equalABP i) := by
  have hn := ordinary_norm_bounds .high hz
  have hcos := cosine_square_upper (family_frame_domain .high hz)
  have hc : 0<Real.cos z := by linarith [(transport_trig (family_frame_domain .high hz)).1]
  fin_cases i
  · have hp := mul_le_mul hcos hn.1 (sq_nonneg _) (sq_nonneg _)
    simpa [scaledNorms,norms,equalABP,mul_pow] using hp
  · have hp := mul_le_mul hcos hn.2.1 (sq_nonneg _) (sq_nonneg _)
    simpa [scaledNorms,norms,lambdaG,equalABP,mul_pow] using hp
  · have hm := (tilted_bounds .high hz).2.2
    have hm0 := (family_positive .high hz).2.2.2
    have hm2 : (Explicit.m .high z)^2≤(aeval z (mHi .high))^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm)
        (show 0≤aeval z (mHi .high)+Explicit.m .high z by linarith)]
    have hp := mul_le_mul hcos hm2 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,lambdaB,↓reduceIte,Matrix.cons_val_succ,
      Matrix.cons_val_zero,secant_scaled_norm_sq hc]
    norm_num only [equalABP,Matrix.cons_val_succ,Matrix.cons_val_zero,
      map_add,map_mul,map_pow,l_eval]
    dsimp [Explicit.m] at hp
    nlinarith only [hp]
  · have hp := mul_le_mul hcos hn.2.2.2.1 (sq_nonneg _) (sq_nonneg _)
    simpa [scaledNorms,norms,equalABP,mul_pow] using hp

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
