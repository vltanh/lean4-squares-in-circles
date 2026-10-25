module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CutData
public import SquaresInCircles.Eight.Owners.SecantNormCurvature

/-!
# Eight squares: the low AB angular baseline slope

The positive-square comparison
is the displayed concave cubic in the sine square. The final cubic
uses the prescribed shift by `.2` and its exact completed-square reserve.
-/

section
/-!
## Actual squared-norm bounds for the negative-A scalar endpoints

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
end
end
end

section
/-!
## Squared-norm bounds at the angle cuts of a negative A

The lower sine polynomial may be negative at the left endpoint. The bound of the rotated norms
first compares it with the sine itself, which is nonnegative, before decreasing either the
cosine-square multiplier or the tilted coefficient (`cut_norm_bounds`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
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

/-- The sign-sensitive multiplication behind the bounds of the three rotated norms, including a
slightly negative polynomial sine. -/
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

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## The exact secant baseline and its angular derivative

The analytic extension agrees with the original baseline throughout the
nonnegative frame interval. Its only varying norm is the affected G or
B pair; the other terms are constant in s.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SecantBaseline
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open SecantNormCurvature

def affected (atG : Bool) (k c z : ℝ) : ℝ := if atG then k else PositiveTD.tilted c z
def basicRatio (atG : Bool) (k l c z : ℝ) : ℝ := affected atG k c z/l
def angularBaseline (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c 0 z+FlatTStress.secantCharge R l (affected atG k c z) s
def denominator (r s : ℝ) : ℝ := Real.sqrt (1+r^2*Real.cos s^2)
def angleSlope (l r s : ℝ) : ℝ :=
  l*(13/12+Real.sin s-R*Real.sin s/denominator r s)/Real.cos s^2

theorem baseline_eq_extension (atG : Bool) (k l c z : ℝ) {s : ℝ}
    (hs : s∈Icc 0 frameCap) :
    baseline atG k l c s z=angularBaseline atG k l c s z := by
  have hw := secant_width_identity (l:=l) hs
  dsimp only [NegativeAPositiveTD.secant] at hw
  have hid : l*(1/Real.cos s-1+(13/12)*Real.tan s)=
      l/Real.cos s-l+(13/12)*l*Real.tan s := by ring
  cases atG
  · simp only [angularBaseline,baseline,affected,lambdaG,lambdaB,Bool.false_eq_true,↓reduceIte,
      NegativeAPositiveTD.secant,Real.cos_zero,div_one,Real.tan_zero,edgeWidth_zero,
      mul_zero,add_zero,fullSupport_pair,FlatTStress.secantCharge]
    rw [pairNorm_symm (PositiveTD.tilted c z) (l/Real.cos s),
      pairNorm_symm (PositiveTD.tilted c z) l,hid]
    linarith only [hw]
  · simp only [angularBaseline,baseline,affected,lambdaG,lambdaB,↓reduceIte,
      NegativeAPositiveTD.secant,Real.cos_zero,div_one,Real.tan_zero,edgeWidth_zero,
      mul_zero,add_zero,fullSupport_pair,FlatTStress.secantCharge]
    rw [hid]
    linarith only [hw]

theorem denominator_pos (r s : ℝ) : 0<denominator r s :=
  Real.sqrt_pos.mpr (by positivity)

theorem denominator_sq (r s : ℝ) : (denominator r s)^2=1+r^2*Real.cos s^2 :=
  Real.sq_sqrt (by positivity)

theorem support_norm_identity {r s : ℝ} (hc : 0<Real.cos s) :
    supportNorm r s=denominator r s/Real.cos s := by
  have hN := norm_pos (a:=r) hc
  have hN2 := norm_sq r s
  have hD := denominator_pos r s
  have hD2 := denominator_sq r s
  have he : (supportNorm r s*Real.cos s)^2=(denominator r s)^2 := by
    rw [mul_pow,hN2,hD2]
    dsimp [SecantNormCurvature.secant]
    field_simp [hc.ne']
    ring
  have he' : supportNorm r s*Real.cos s=denominator r s := by
    nlinarith [mul_pos hN hc]
  exact (eq_div_iff hc.ne').2 he'

theorem angleSlope_eq {l r s : ℝ} (hc : 0<Real.cos s) :
    l*gainFirst R r s=angleSlope l r s := by
  dsimp [gainFirst,normFirst,first,SecantNormCurvature.secant,angleSlope]
  rw [support_norm_identity hc]
  field_simp [hc.ne',(denominator_pos r s).ne']
  ring

theorem angularBaseline_hasDerivAt (atG : Bool) {k l c s z : ℝ}
    (hl : 0<l) (hc : 0<Real.cos s) :
    HasDerivAt (fun s => angularBaseline atG k l c s z)
      (angleSlope l (basicRatio atG k l c z) s) s := by
  have hh := (charge_hasDerivAt (R:=R) (a:=affected atG k c z) hl hc).const_add
    (baseline atG k l c 0 z)
  simpa only [angularBaseline,basicRatio,angleSlope_eq hc] using hh

theorem coefficient_upper {r s r₀ c₀ D : ℝ}
    (hr₀ : 0≤r₀) (hc₀ : 0≤c₀) (hD : 0<D)
    (hr : r₀≤r) (hc : c₀≤Real.cos s)
    (hsquare : qCap<D^2*(1+r₀^2*c₀^2)) :
    R/denominator r s<D := by
  have hr0 := hr₀.trans hr
  have hc0 := hc₀.trans hc
  have hrc := mul_le_mul hr hc hc₀ hr0
  have hrc2 := pow_le_pow_left₀ (mul_nonneg hr₀ hc₀) hrc 2
  have hden : 1+r₀^2*c₀^2≤(denominator r s)^2 := by
    rw [denominator_sq]
    nlinarith only [hrc2]
  have hscaled := mul_le_mul_of_nonneg_left hden (sq_nonneg D)
  apply OrdinaryCurvatureBounds.quotient_lt_of_square (denominator_pos r s) hD
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  nlinarith

theorem slope_lower {l r s D y b : ℝ}
    (hl : 0<l) (hc : 0<Real.cos s) (hs : 0≤Real.sin s)
    (hsy : Real.sin s≤y) (hD : 1≤D) (hb : 0≤b)
    (hcoeff : R/denominator r s≤D) (hreserve : b<13/12-(D-1)*y) :
    b*l<angleSlope l r s := by
  have hmul := mul_le_mul_of_nonneg_right hcoeff hs
  have hsy' := mul_le_mul_of_nonneg_left hsy (sub_nonneg.mpr hD)
  have hnum : b<13/12+Real.sin s-R*Real.sin s/denominator r s := by
    have he : R*Real.sin s/denominator r s=(R/denominator r s)*Real.sin s := by ring
    rw [he]
    linarith
  have hcos2 : Real.cos s^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s)]
  have hbc := mul_le_mul_of_nonneg_left hcos2 hb
  have hbase := mul_lt_mul_of_pos_left hnum hl
  have hbase' := mul_le_mul_of_nonneg_left hbc hl.le
  unfold angleSlope
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith only [hbase,hbase']

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SecantBaseline
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowABSlope
open Candidate Secondary SecantBaseline

def squarePolynomial (t : ℝ) : ℝ := (7/5+(19/50)*t)^2*(2-t)-qCap
def squareFirst (t : ℝ) : ℝ := 21/125-(969/625)*t-(1083/2500)*t^2
def squareSecond (t : ℝ) : ℝ := -(969/625)-(1083/1250)*t

theorem square_hasDerivAt (t : ℝ) :
    HasDerivAt squarePolynomial (squareFirst t) t := by
  have h1 : HasDerivAt (fun t:ℝ => 7/5+(19/50)*t) (19/50) t := by
    simpa using ((hasDerivAt_id t).const_mul (19/50:ℝ)).const_add (7/5:ℝ)
  have h2 : HasDerivAt (fun t:ℝ => 2-t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (2:ℝ)
  exact (((h1.fun_pow 2).fun_mul h2).sub_const qCap).congr_deriv (by norm_num [squareFirst]; ring)

theorem squareFirst_hasDerivAt (t : ℝ) :
    HasDerivAt squareFirst (squareSecond t) t := by
  have h1 : HasDerivAt (fun t:ℝ => (1083/2500:ℝ)*t^2) ((1083/2500:ℝ)*(2*t)) t := by
    simpa using ((hasDerivAt_id t).fun_pow 2).const_mul (1083/2500:ℝ)
  have h0 : HasDerivAt (fun t:ℝ => 21/125-(969/625)*t) (-(969/625)) t := by
    simpa using ((hasDerivAt_id t).const_mul (969/625:ℝ)).const_sub (21/125:ℝ)
  exact (h0.fun_sub h1).congr_deriv (by simp only [squareSecond]; ring)

theorem square_positive {t : ℝ} (ht : t∈Icc 0 ((371/1000:ℝ)^2)) :
    0<squarePolynomial t := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) ((371/1000:ℝ)^2)) squarePolynomial := by
    apply concave_of_deriv2 (fun x _ => square_hasDerivAt x)
      (fun x _ => squareFirst_hasDerivAt x)
    intro x hx
    dsimp [squareSecond]
    nlinarith [hx.1]
  exact concave_gt_of_endpoints hc ht
    (by norm_num [squarePolynomial,qCap]) (by norm_num [squarePolynomial,qCap])

theorem cubic_positive {y : ℝ} (hy : y∈Icc 0 (371/1000:ℝ)) :
    0<(13/12:ℝ)-26/25-(2/5)*y+(26/25)*y^2-(19/50)*y^3 := by
  let v : ℝ := y-1/5
  have hv : v≤171/1000 := by dsimp [v]; linarith [hy.2]
  have htail := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)
  have hsq := sq_nonneg (v-740/37351)
  have hid : (13/12:ℝ)-26/25-(2/5)*y+(26/25)*y^2-(19/50)*y^3=
      71/37500-(37/1250)*v+(203/250)*v^2-(19/50)*v^3 := by dsimp [v]; ring
  have hcomplete : (71/37500:ℝ)-(37/1250)*v+(37351/50000)*v^2=
      (37351/50000)*(v-740/37351)^2+2241221/1400662500 := by ring
  rw [hid]
  nlinarith only [htail,hsq,hcomplete]

theorem sine_bound {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) :
    Real.sin s∈Icc 0 (371/1000:ℝ) := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := trig_bracket (l:=0) (u:=(19/50:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  exact ⟨(transport_trig hsf).2.2.1,by norm_num at hb; linarith [hb.2.1]⟩

theorem coefficient {r s : ℝ} (hr : 1≤r) (hs : s∈Icc 0 (19/50:ℝ)) :
    R/denominator r s<7/5+(19/50)*(Real.sin s)^2 := by
  have hy := sine_bound hs
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hp := square_positive ⟨sq_nonneg (Real.sin s),hy2⟩
  have hden := denominator_sq r s
  have hr2 : 1≤r^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (Real.cos s))
  have hd : 2-(Real.sin s)^2≤(denominator r s)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hD : 0<7/5+(19/50)*(Real.sin s)^2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hd (sq_nonneg (7/5+(19/50)*(Real.sin s)^2))
  apply OrdinaryCurvatureBounds.quotient_lt_of_square (denominator_pos r s) hD
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  dsimp [squarePolynomial] at hp
  rw [hR2]
  linarith only [hp,hscaled]

theorem lower {l r s : ℝ} (hl : 0<l) (hr : 1≤r)
    (hs : s∈Icc 0 (19/50:ℝ)) : (26/25)*l<angleSlope l r s := by
  have hy := sine_bound hs
  have hcoef := coefficient hr hs
  have hpoly := cubic_positive hy
  have hc : 0<Real.cos s := by linarith [Explicit.AB_cut_cosine hs]
  have hp := mul_le_mul_of_nonneg_right hcoef.le hy.1
  have hnum : (26/25)*(Real.cos s)^2<
      13/12+Real.sin s-R*Real.sin s/denominator r s := by
    have he : R*Real.sin s/denominator r s=(R/denominator r s)*Real.sin s := by ring
    rw [he]
    nlinarith [Real.sin_sq_add_cos_sq s]
  unfold angleSlope
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith only [mul_lt_mul_of_pos_left hnum hl]

theorem original {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) :
    (26/25)*Explicit.l .low z<angleSlope (Explicit.l .low z)
      (Explicit.m .low z/Explicit.l .low z) s := by
  have hz' : z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split]
    exact hz
  have hl := (Explicit.family_positive .low hz').2.1
  exact lower hl ((one_le_div hl).2 (Explicit.low_tilted hz).1.le) hs

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowABSlope
end
end
end
