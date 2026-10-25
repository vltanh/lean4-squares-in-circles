module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.CorrelatedSameBlock
public import SquaresInCircles.Eight.Owners.GA.Positive.ANegativeTDGain

/-!
# Eight squares: the two ordinary same-block comparisons

The two-angle norm cancels without changing the signed angle. The
negative-surplus comparison uses the stated sine condition; the
positive-surplus comparison uses the coefficient ratio at most 1.7.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SameBlock
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity CorrelatedSameBlock

theorem negative_difference (p q P N : ℝ) :
    mixedBlock R p q P N-V R p q (N-P)=
      (p-q*Real.cos N)*(Real.cos P-1)+(p-q*Real.sin N)*Real.sin P := by
  dsimp [mixedBlock,V,PositiveAngularEnvelope.phi]
  rw [show -(N-P)=P-N by ring,Real.cos_sub]
  ring

theorem positive_difference (p q P N : ℝ) :
    mixedBlock R p q P N-U R p q (P-N)=
      p*(PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N))-q*(1-Real.cos N) := by
  dsimp [mixedBlock,U]
  ring

theorem negative_surplus {p q P N : ℝ} (hp : 0≤p)
    (hP : P∈Icc 0 N) (hN : N∈Icc 0 frameCap)
    (hsine : q*Real.sin N≤p) :
    V R p q (N-P)≤ mixedBlock R p q P N := by
  have hP' : P∈Icc 0 frameCap := ⟨hP.1,hP.2.trans hN.2⟩
  have htP := transport_trig hP'
  have htN := transport_trig hN
  have hcosN : 0<Real.cos N := by linarith [htN.1]
  have hcosP : Real.cos P-1≤0 := by linarith [Real.cos_le_one P]
  have he := negative_difference p q P N
  by_cases hlarge : p≤q*Real.cos N
  · have hfirst := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hlarge) hcosP
    have hsecond := mul_nonneg (sub_nonneg.mpr hsine) htP.2.2.1
    linarith
  · have hsmall : 0≤p-q*Real.cos N := by linarith
    have harg : N-P∈Icc 0 frameCap :=
      ⟨by linarith [hP.2],by linarith [hN.2,hP.1]⟩
    have hcos := cos_anti harg hN (by linarith [hP.1])
    have hfactor := mul_nonneg hsmall (sub_nonneg.mpr hcos)
    have hpositive := mul_nonneg
      (mul_nonneg hp (sub_nonneg.mpr htN.2.2.2.2.le)) htP.2.2.1
    have hid :
        ((p-q*Real.cos N)*(Real.cos P-1)+(p-q*Real.sin N)*Real.sin P)*Real.cos N=
        (p-q*Real.cos N)*(Real.cos (N-P)-Real.cos N)+
          p*(Real.cos N-Real.sin N)*Real.sin P := by
      rw [Real.cos_sub]
      ring
    have hnum : 0≤ mixedBlock R p q P N-V R p q (N-P) := by
      apply nonneg_of_mul_nonneg_left (b:=Real.cos N) _ hcosN
      rw [he,hid]
      exact add_nonneg hfactor hpositive
    linarith

theorem phi_slope_at_cap : (3/25:ℝ)<Real.cos frameCap-Real.sin frameCap := by
  have hc := cos_lower_six (x:=frameCap) (by norm_num [frameCap])
  have hs := sin_upper_five (x:=frameCap) (by norm_num [frameCap])
  norm_num [frameCap] at hc hs ⊢
  linarith

theorem phi_cap_difference {N : ℝ} (hN : N∈Icc 0 frameCap) :
    0≤PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)-(17/10)*(1-Real.cos N) := by
  have hsin := (transport_trig hN).2.2.1
  have hcos := sub_nonneg.mpr (Real.cos_le_one N)
  have hhalf := PositiveANegativeTD.one_sub_cos_upper hN
  have hp := mul_le_mul_of_nonneg_right phi_cap_lower.le hcos
  have hd := mul_le_mul_of_nonneg_right phi_slope_at_cap.le hsin
  have hid : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)=
      PositiveAngularEnvelope.phi frameCap*(1-Real.cos N)+
        (Real.cos frameCap-Real.sin frameCap)*Real.sin N := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  rw [hid]
  nlinarith

theorem positive_surplus {p q P N : ℝ} (hp : 0≤p)
    (hratio : q≤(17/10)*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 P) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hN' : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hP.2⟩
  have hinc := phi_increment_anti hN'
    (show P-N∈Icc 0 (frameCap-N) by constructor <;> linarith [hN.2,hP.2])
    (show frameCap-N∈Icc 0 (frameCap-N) by
      exact ⟨by linarith [hN'.2],le_rfl⟩)
    (by linarith [hP.2])
  have hinc' : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
    convert hinc using 1 <;> congr 1 <;> ring
  have hpinc := mul_le_mul_of_nonneg_left hinc' hp
  have hbase := mul_nonneg hp (phi_cap_difference hN')
  have hqcos := mul_le_mul_of_nonneg_right hratio
    (sub_nonneg.mpr (Real.cos_le_one N))
  have he := positive_difference p q P N
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SameBlock
