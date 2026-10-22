module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2AEnvelope
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowTransfer
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveHighTransfer

/-!
# Actual nonradical and force-norm bounds at the A/TD split endpoints

Uncompiled transcription of the norm comparisons in Sections 7--8.
The equal-angle endpoints retain the actual positive cosine multiplier,
and the DE secant remains in the D force until that multiplication.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 ch Ch sh h cbar sigmabar
  taylor_bounds zero_norm_sq negative_norm_sq_le pairNorm_nonneg)

theorem family_frame_domain (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) : θ∈Icc 0 frameCap := by
  apply Explicit.family_frame_domain f
  cases f <;> simpa only [left,right,Explicit.left,Explicit.right,Explicit.L,
    PositiveTD.Certificate.L,h,frameCap] using hθ

theorem split_angles (e : Split) {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    Explicit.splitA e θ∈Icc 0 θ ∧ Explicit.splitT e θ∈Icc 0 θ ∧
      Explicit.splitA e θ+Explicit.splitT e θ=θ := by
  cases e <;> simp only [Explicit.splitA,Explicit.splitT,zero_add,add_zero]
  · exact ⟨⟨le_rfl,hθ.1⟩,⟨hθ.1,le_rfl⟩,rfl⟩
  · exact ⟨⟨hθ.1,le_rfl⟩,⟨le_rfl,hθ.1⟩,rfl⟩

theorem split_positive (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    0<Explicit.k f θ ∧ 0<Explicit.l f θ ∧ 0<Explicit.c f θ ∧ 0<Explicit.splitM f e θ := by
  apply Explicit.family_positive f _ (split_angles e (family_frame_domain f hθ)).2.1
  cases f <;> simpa only [left,right,Explicit.left,Explicit.right,Explicit.L,
    PositiveTD.Certificate.L,h,frameCap] using hθ

theorem tilted_bounds (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval θ (mLo f e) ∧ aeval θ (mLo f e)≤Explicit.splitM f e θ ∧
      Explicit.splitM f e θ≤aeval θ (mHi f e) := by
  have hc := (split_positive f e hθ).2.2.1
  cases e
  · have ht := PositiveTD.Certificate.tilted_polynomial_bounds (c:=c f)
      (family_frame_domain f hθ) (by simpa using hc)
    simpa [mLo,mHi,Explicit.splitM,Explicit.splitT,Explicit.m,Explicit.eta,
      PositiveTD.tilted,PositiveTD.eta,PositiveTD.Certificate.mMinus,
      PositiveTD.Certificate.mPlus] using ht
  · simpa [mLo,mHi,Explicit.splitM,Explicit.splitT,Explicit.m] using
      (show 0<Explicit.c f θ ∧ Explicit.c f θ≤Explicit.c f θ ∧
        Explicit.c f θ≤Explicit.c f θ from ⟨hc,le_rfl,le_rfl⟩)

def lowNonradical (e : Split) (θ : ℝ) : ℝ :=
  2*Explicit.k .low θ+3*Explicit.l .low θ+(3/2)*Explicit.splitM .low e θ+5/2+
    Explicit.c .low θ*edgeWidth (Explicit.splitT e θ)-
    Explicit.c .low θ*Explicit.sigma*Real.sin (Explicit.splitT e θ)+
    Explicit.l .low θ*TwoPositive.ASupport.charge (Explicit.splitA e θ)-
    (1+Explicit.c .low θ)*diagonal
def highNonradical (e : Split) (θ : ℝ) : ℝ :=
  2*Explicit.k .high θ+3*Explicit.l .high θ+(3/2)*Explicit.splitM .high e θ+
    Explicit.c .high θ/2+3+Explicit.c .high θ*edgeWidth (Explicit.splitT e θ)-
    Explicit.c .high θ*Explicit.sigma*Real.sin (Explicit.splitT e θ)+
    Explicit.l .high θ*TwoPositive.ASupport.charge (Explicit.splitA e θ)

theorem low_nonradical_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (lowB e)≤lowNonradical e θ := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive .low e hθ
  have ht := taylor_bounds (family_frame_domain .low hθ)
  have htilt := (tilted_bounds .low e hθ).2.1
  have hD := mul_le_mul_of_nonneg_left PositiveTD.Certificate.diagonal_le_cbar
    (show 0≤1+Explicit.c .low θ by linarith)
  cases e
  · have hs := PositiveTD.Certificate.sigma_sine_upper (family_frame_domain .low hθ) hc.le
    have hW0 := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
    have hW : Explicit.c .low θ/2*(1+aeval θ C10+aeval θ S11)≤
        Explicit.c .low θ*edgeWidth θ := by
      rw [edgeWidth_positive_formula (family_frame_domain .low hθ)]
      nlinarith only [hW0]
    have hj : TwoPositive.ASupport.charge 0=0 := by
      rw [TwoPositive.ASupport.charge_low (by norm_num)]
      norm_num [TwoPositive.ASupport.axialCharge]
    norm_num only [lowB,lowE,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval]
    simp only [lowNonradical,Explicit.splitA,Explicit.splitT,hj,mul_zero,add_zero]
    nlinarith only [htilt,hD,hs,hW]
  · have hJ := mul_le_mul_of_nonneg_left (AEnvelope.low_polynomial_charge hθ) hl.le
    have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    norm_num only [lowB,lowE,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval]
    simp only [lowNonradical,Explicit.splitA,Explicit.splitT,Explicit.splitM,Explicit.m,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,hW]
    nlinarith only [hD,hJ]

theorem high_nonradical_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval θ (highB e)≤highNonradical e θ := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive .high e hθ
  have ht := taylor_bounds (family_frame_domain .high hθ)
  have htilt := (tilted_bounds .high e hθ).2.1
  cases e
  · have hs := PositiveTD.Certificate.sigma_sine_upper (family_frame_domain .high hθ) hc.le
    have hW0 := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
    have hW : Explicit.c .high θ/2*(1+aeval θ C10+aeval θ S11)≤
        Explicit.c .high θ*edgeWidth θ := by
      rw [edgeWidth_positive_formula (family_frame_domain .high hθ)]
      nlinarith only [hW0]
    have hj : TwoPositive.ASupport.charge 0=0 := by
      rw [TwoPositive.ASupport.charge_low (by norm_num)]
      norm_num [TwoPositive.ASupport.axialCharge]
    norm_num only [highB,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval]
    simp only [highNonradical,Explicit.splitA,Explicit.splitT,hj,mul_zero,add_zero]
    nlinarith only [htilt,hs,hW]
  · have hJ := mul_le_mul_of_nonneg_left (AEnvelope.high_polynomial_charge hθ) hl.le
    have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    norm_num only [highB,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,c_eval]
    simp only [highNonradical,Explicit.splitA,Explicit.splitT,Explicit.splitM,Explicit.m,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,hW]
    nlinarith only [hJ]

theorem ordinary_norm_bounds (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (left f:ℝ) (right f:ℝ)) :
    (pairNorm (Explicit.k f θ) 1 0)^2≤aeval θ (PH f) ∧
    (pairNorm (Explicit.k f θ) (Explicit.l f θ) 0)^2≤aeval θ (PG f) ∧
    (pairNorm (Explicit.l f θ) (Explicit.splitM f e θ) 0)^2≤aeval θ (PB f e) ∧
    (pairNorm 1 (Explicit.c f θ) 0)^2≤aeval θ (PD f) ∧
    (pairNorm (Explicit.k f θ) 1 (-θ))^2≤aeval θ (PHminus f) ∧
    (pairNorm (Explicit.k f θ) (Explicit.l f θ) (-θ))^2≤aeval θ (PGminus f) ∧
    (pairNorm (Explicit.l f θ) (Explicit.splitM f e θ) (-θ))^2≤aeval θ (PBminus f e) := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive f e hθ
  have hθ' := family_frame_domain f hθ
  have ht := taylor_bounds hθ'
  obtain ⟨hmLo0,hmLo,hmHi⟩ := tilted_bounds f e hθ
  have hm2 : (Explicit.splitM f e θ)^2≤(aeval θ (mHi f e))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmHi)
      (show 0≤aeval θ (mHi f e)+Explicit.splitM f e θ by linarith)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [zero_norm_sq]; simp [PH,add_comm]
  · rw [zero_norm_sq]; simp [PG]
  · rw [zero_norm_sq]; simp only [PB,map_add,map_pow,l_eval]; linarith
  · rw [zero_norm_sq]; simp [PD]
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hθ' ht.2.1
    norm_num only [PHminus,PH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,k_eval]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hk hl hθ' ht.2.1
    norm_num only [PGminus,PG,map_add,map_sub,map_mul,map_pow,aeval_C,k_eval,l_eval]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hl hm hθ' ht.2.1
    have hp := mul_le_mul_of_nonneg_left hmLo
      (show 0≤2*Explicit.l f θ*aeval θ S11 by positivity)
    norm_num only [PBminus,PB,map_add,map_sub,map_mul,map_pow,aeval_C,l_eval]
    nlinarith only [hh,hp,hm2]

theorem cap_norm_bounds {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (pairNorm (Explicit.k .low θ) 1 (-frameCap))^2≤aeval θ PHcap ∧
    (pairNorm (Explicit.k .low θ) (Explicit.l .low θ) (-frameCap))^2≤aeval θ PGcap := by
  obtain ⟨hk,hl,_,_⟩ := split_positive .low .atT hθ
  have hc : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hs := (taylor_bounds hc).2.1
  constructor
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hc hs
    norm_num only [PHcap,PH,map_sub,map_add,map_mul,map_pow,map_one,aeval_C,
      k_eval,Rat.cast_mul,PositiveTD.Certificate.sh_cast]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hk hl hc hs
    norm_num only [PGcap,PG,map_sub,map_add,map_mul,map_pow,aeval_C,
      k_eval,l_eval,Rat.cast_mul,PositiveTD.Certificate.sh_cast]
    nlinarith only [hh]

theorem cosine_square_upper {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    (Real.cos θ)^2≤(aeval θ C12)^2 := by
  have ht := taylor_bounds hθ
  have hc : 0≤Real.cos θ := by linarith [(transport_trig hθ).1]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.2.2.2.2)
    (show 0≤aeval θ C12+Real.cos θ by linarith [ht.2.2.2.2.2])]

theorem scaled_norm_bound {θ n : ℝ} {P : ℚ[X]} (hθ : θ∈Icc 0 frameCap)
    (hn : n^2≤aeval θ P) : (Real.cos θ*n)^2≤aeval θ (C12^2*P) := by
  have hh := mul_le_mul (cosine_square_upper hθ) hn (sq_nonneg n) (sq_nonneg _)
  simpa only [mul_pow,map_mul,map_pow] using hh

theorem scaled_secant_norm_bound {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (Real.cos θ*pairNorm (Explicit.secant θ) (Explicit.c .high θ) 0)^2≤
      aeval θ (1+(c .high)^2*C12^2) := by
  have hc : 0<Real.cos θ := by linarith [(transport_trig (family_frame_domain .high hθ)).1]
  have he : (Real.cos θ*pairNorm (Explicit.secant θ) (Explicit.c .high θ) 0)^2=
      1+(Explicit.c .high θ)^2*(Real.cos θ)^2 := by
    rw [mul_pow,zero_norm_sq]
    dsimp [Explicit.secant]
    field_simp [hc.ne']
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (cosine_square_upper (family_frame_domain .high hθ))
    (sq_nonneg (Explicit.c .high θ))
  simpa only [map_add,map_one,map_mul,map_pow,c_eval] using add_le_add_left hh 1

theorem qStar_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    max (Explicit.l .high θ) (Explicit.splitM .high e θ)≤aeval θ qStar := by
  have hl : Explicit.l .high θ≤aeval θ qStar := by
    simp only [qStar,map_add,map_mul,map_sub,aeval_C,aeval_X,l_eval]
    norm_num [h]
    linarith [hθ.2]
  apply max_le hl
  cases e
  · have hc := (split_positive .high .atT hθ).2.2.1
    have hθ' := family_frame_domain .high hθ
    have hs := sin_upper_five hθ'.1
    have hcos := cos_upper_four hθ'.1
    have happrox : Explicit.splitM .high .atT θ≤aeval θ (mu .high .atT) := by
      have hh := mul_le_mul_of_nonneg_left
        (show Real.cos θ+Explicit.eta*Real.sin θ≤
          (1-θ^2/2+θ^4/24)+Explicit.eta*(θ-θ^3/6+θ^5/120) by
            dsimp [Explicit.eta]
            linarith) hc.le
      simpa [mu,Explicit.splitM,Explicit.splitT,Explicit.m,C4,S5,
        PositiveTD.Certificate.etaQ,Explicit.eta] using hh
    have hcert := quadratic_positive .highQStar hθ
    norm_num [quadraticReserveValue,quadraticPolynomial] at hcert
    exact happrox.trans (by linarith)
  · have hcert := qStar_A_positive hθ
    simp only [map_sub,c_eval] at hcert
    simpa [Explicit.splitM,Explicit.splitT,Explicit.m] using (le_of_lt (sub_pos.mp hcert))

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
