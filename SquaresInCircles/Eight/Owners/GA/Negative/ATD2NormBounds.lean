module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2ScalarData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Tilted

/-!
# Eight squares: actual squared-norm bounds for the negative-A scalar endpoints

Equal-angle norms retain the actual positive
cosine factor, including its exact cancellation of the secant weight.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
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
    simp only [PHminus,PH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,eq_ratCast,k_eval]
    push_cast
    linarith only [hh]
  · have hh := PositiveTD.Certificate.negative_norm_sq_le hk hl hz' ht.2.1
    simp only [PGminus,PG,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,k_eval,l_eval]
    push_cast
    linarith only [hh]
  · have hh := PositiveTD.Certificate.negative_norm_sq_le hl hm hz' ht.2.1
    have hp := mul_le_mul_of_nonneg_left hmLo
      (mul_nonneg (by linarith : (0:ℝ)≤2*Explicit.l f z) ht.1)
    simp only [PBminus,PB,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,l_eval]
    push_cast
    linarith only [hh,hp,hm2]

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
  field_simp

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
  have h0 : (scaledNorms f true z z 0)^2≤aeval z (equalGAP f 0) := by
    have hp := mul_le_mul hcos hn.1 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,equalGAP,Matrix.cons_val_zero,map_mul,map_pow,mul_pow]
    exact hp
  have h1 : (scaledNorms f true z z 1)^2≤aeval z (equalGAP f 1) := by
    have hp := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Explicit.k f z))
    simp only [scaledNorms,norms,lambdaG,↓reduceIte,Matrix.cons_val_one,Matrix.cons_val_zero,
      scaled_secant_norm_sq hc]
    simp only [equalGAP,Matrix.cons_val_one,Matrix.cons_val_zero,
      map_add,map_mul,map_pow,k_eval,l_eval]
    linarith only [hp]
  have h2 : (scaledNorms f true z z 2)^2≤aeval z (equalGAP f 2) := by
    have hp := mul_le_mul hcos hn.2.2.1 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,lambdaB,↓reduceIte,equalGAP,Matrix.cons_val_two,
      Matrix.tail_cons,Matrix.head_cons,map_mul,map_pow,mul_pow]
    exact hp
  have h3 : (scaledNorms f true z z 3)^2≤aeval z (equalGAP f 3) := by
    have hp := mul_le_mul hcos hn.2.2.2.1 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,equalGAP,Matrix.cons_val_three,
      Matrix.tail_cons,Matrix.head_cons,map_mul,map_pow,mul_pow]
    exact hp
  fin_cases i
  exacts [h0,h1,h2,h3]

theorem equal_AB_norm_bounds {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    (scaledNorms .high false z z i)^2≤aeval z (equalABP i) := by
  have hzh : z∈Icc (left .high:ℝ) (right .high:ℝ) := by
    norm_num [left,right,split,PositiveTD.Certificate.h]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hn := ordinary_norm_bounds .high hzh
  have hcos := cosine_square_upper (family_frame_domain .high hzh)
  have hc : 0<Real.cos z := by linarith [(transport_trig (family_frame_domain .high hzh)).1]
  have h0 : (scaledNorms .high false z z 0)^2≤aeval z (equalABP 0) := by
    have hp := mul_le_mul hcos hn.1 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,equalABP,Matrix.cons_val_zero,map_mul,map_pow,mul_pow]
    exact hp
  have h1 : (scaledNorms .high false z z 1)^2≤aeval z (equalABP 1) := by
    have hp := mul_le_mul hcos hn.2.1 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,lambdaG,Bool.false_eq_true,↓reduceIte,equalABP,
      Matrix.cons_val_one,Matrix.cons_val_zero,map_mul,map_pow,mul_pow]
    exact hp
  have h2 : (scaledNorms .high false z z 2)^2≤aeval z (equalABP 2) := by
    have hm := (tilted_bounds .high hzh).2.2
    have hm0 := (family_positive .high hzh).2.2.2
    have hm2 : (Explicit.m .high z)^2≤(aeval z (mHi .high))^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm)
        (show 0≤aeval z (mHi .high)+Explicit.m .high z by linarith)]
    have hp := mul_le_mul hcos hm2 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,lambdaB,Bool.false_eq_true,↓reduceIte,
      Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,secant_scaled_norm_sq hc]
    simp only [equalABP,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,
      map_add,map_mul,map_pow,l_eval]
    dsimp [Explicit.m] at hp
    linarith only [hp]
  have h3 : (scaledNorms .high false z z 3)^2≤aeval z (equalABP 3) := by
    have hp := mul_le_mul hcos hn.2.2.2.1 (sq_nonneg _) (sq_nonneg _)
    simp only [scaledNorms,norms,equalABP,Matrix.cons_val_three,
      Matrix.tail_cons,Matrix.head_cons,map_mul,map_pow,mul_pow]
    exact hp
  fin_cases i
  exacts [h0,h1,h2,h3]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
