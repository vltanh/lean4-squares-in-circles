module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighTransferData
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighDerivative

/-!
# The high-BT3 right derivative at the original total angle

Uncompiled Section 7.4 and Section 8.3. The two reciprocal-norm
numerators are transferred using the actual total-dependent D support.
The B derivative is compared with G only after the two positive
coefficients and the sorted-pair identity have been established.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighDerivative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope PairNormCalculus
open NegativeAPositiveTD (SecantBaseline SecantCoordinate)
open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds)

lemma H_G_endpoint (atH : Bool) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    secantGainDeriv qCap (Explicit.c .high θ θ) θ<
      Vd R (Explicit.k .high θ) (if atH then 1 else Explicit.l .high θ) 0 := by
  let x := HighTransfer.native θ
  let p := Explicit.k .high θ
  let q : ℝ := if atH then 1 else Explicit.l .high θ
  let c := Explicit.c .high θ θ
  have hx := HighShape.native_domain hθ
  have hf := Explicit.frame_domain .high hθ
  have hb := Explicit.high_bounds hθ
  have hp : 0<p := by linarith [hb.k_lower]
  have hq : 0<q := by cases atH <;> simp only [q] <;> linarith [hb.l_lower]
  have hn := pairNorm_pos hp hq (by norm_num [frameCap])
  have hnorm : (pairNorm p q 0)^2≤aeval x (Certificate.derivativeP atH) := by
    cases atH <;>
      simp [Certificate.derivativeP,Certificate.highK_eval,Certificate.highL_eval,
        HighShape.native_total,HighTransfer.native,x,p,q,
        NonnegativeTotals.Analytic.norm_zero_square,add_comm]
  have hmass := Certificate.derivative_masses_positive atH hx
  have hden := SecantBaseline.denominator_pos c θ
  have hden2 := SecantBaseline.denominator_sq c θ
  have ht := taylor_bounds hf
  have hcos := NegativeESecant.cos_pos hf
  have hC10 : 0≤aeval θ C10 := by linarith [ht.2.2.2.1]
  have hC10sq := pow_le_pow_left₀ hC10 ht.2.2.2.2.1 2
  have hC12sq := NegativeDEPositiveTD.Certificate.cosine_square_upper hf
  have hc0 : 0≤c := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,hb.m_lower]
  have hC := HighShape.coefficient_majorant hθ
  have hC2 := pow_le_pow_left₀ hc0 hC 2
  have hprod := mul_le_mul hC2 hC12sq (sq_nonneg (Real.cos θ))
    (sq_nonneg (aeval x Certificate.highC))
  have hD : (SecantBaseline.denominator c θ)^2≤aeval x Certificate.derivativeD := by
    rw [hden2]
    simpa [Certificate.derivativeD,aeval_comp,Certificate.theta_eval,
      HighShape.native_total,x,HighTransfer.native,c] using add_le_add_left hprod 1
  have hR : (Certificate.Rlo:ℝ)≤R := by
    have hs : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
    have hr : 0≤R := Real.sqrt_nonneg qCap
    norm_num [Certificate.Rlo,qCap] at hs ⊢
    nlinarith
  have hpoly : 0<
      2*(Certificate.Rlo:ℝ)*aeval x (Certificate.derivativeMass atH)*(p*q)*(aeval θ C10)^2*
        (aeval x Certificate.derivativeD+(aeval x Certificate.derivativeDMass)^2)+
      2*(Certificate.Rlo:ℝ)*aeval x Certificate.derivativeDMass*aeval θ S11*
        (aeval x (Certificate.derivativeP atH)+(aeval x (Certificate.derivativeMass atH))^2)-
      (13/12+aeval θ S9)*
        (aeval x (Certificate.derivativeP atH)+(aeval x (Certificate.derivativeMass atH))^2)*
        (aeval x Certificate.derivativeD+(aeval x Certificate.derivativeDMass)^2) := by
    have hh := Certificate.derivative_numerator_positive atH hx
    cases atH <;>
      simpa [Certificate.derivativeNumerator,Certificate.derivativeProduct,Certificate.K,
        Certificate.theta_eval,HighShape.native_total,x,HighTransfer.native,p,q,
        mul_assoc,mul_comm,mul_left_comm] using hh
  have htransfer := NegativeDEPositiveTD.HighDerivative.derivative_transfer hn hden
    hmass.1 hmass.2 hnorm hD (mul_nonneg hp.le hq.le)
    (sq_nonneg _) hC10sq ht.1 ht.2.1 ht.2.2.1
    (by norm_num [Certificate.Rlo] : (0:ℝ)≤(Certificate.Rlo:ℝ)) hR hpoly
  rw [NegativeDEPositiveTD.HighDerivative.zero_slope]
  change (13/12+Real.sin θ-R*Real.sin θ/SecantBaseline.denominator c θ)/Real.cos θ^2<
    R*(p*q)/pairNorm p q 0
  apply (div_lt_iff₀ (sq_pos_of_pos hcos)).2
  nlinarith only [htransfer]

theorem all_endpoint {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    secantGainDeriv qCap (Explicit.c .high θ θ) θ<
      Vd R (Explicit.p .high θ i) (Explicit.q .high θ i) 0 := by
  have hb := Explicit.high_bounds hθ
  fin_cases i
  · simpa [Explicit.p,Explicit.q] using H_G_endpoint true hθ
  · simpa [Explicit.p,Explicit.q] using H_G_endpoint false hθ
  · have hm := NegativeDEPositiveTD.HighDerivative.zero_slope_first_mono
      (show 0<Explicit.k .high θ by linarith [hb.k_lower])
      (show Explicit.k .high θ≤Explicit.m .high θ by linarith [hb.k_upper,hb.m_lower])
      (show 0<Explicit.l .high θ by linarith [hb.l_lower])
    have hh := H_G_endpoint false hθ
    simp only [Bool.false_eq_true,if_false] at hh
    have he : Vd R (min (Explicit.l .high θ) (Explicit.m .high θ))
        (max (Explicit.l .high θ) (Explicit.m .high θ)) 0=
        Vd R (Explicit.m .high θ) (Explicit.l .high θ) 0 := by
      rcases le_total (Explicit.l .high θ) (Explicit.m .high θ) with h|h
      · rw [min_eq_left h,max_eq_right h,NegativeDEPositiveTD.HighDerivative.zero_slope,
          NegativeDEPositiveTD.HighDerivative.zero_slope,pairNorm_symm]
        ring
      · rw [min_eq_right h,max_eq_left h]
    simpa only [Explicit.p,Explicit.q,Matrix.cons_val_succ,Matrix.cons_val_zero,he] using hh.trans_le hm

theorem first_right_negative {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    SecantCoordinate.pureFirst 1 (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ (Real.tan θ)<0 := by
  have hh := all_endpoint hθ i
  have hden : 0<1+Real.tan θ^2 := by positivity
  simp only [SecantCoordinate.pureFirst,one_mul,
    SecantCoordinate.arctan_tan (Explicit.frame_domain .high hθ),sub_self,
    NegativeDEPositiveTD.HighDerivative.baseFirst_tan (Explicit.frame_domain .high hθ)]
  exact sub_neg.mpr (div_lt_div_of_pos_right hh hden)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighDerivative
