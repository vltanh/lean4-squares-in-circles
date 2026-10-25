module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEnvelope
public import SquaresInCircles.Eight.TableFree.GlobalGAHybridConcentration

/-!
# Same-block saturation for the continuous low BT3 weight family

Uncompiled transcription of Section 7 of the sorted-D companion.
The H/G comparison keeps the exact correction E.  Its third derivative
is negative on the whole low interval; the two rational derivative
endpoint reserves then prove E increasing from a positive initial value.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LowEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration CorrelatedSameBlock

def correction (t : ℝ) : ℝ :=
  lowK t*(PositiveAngularEnvelope.phi (frameCap-t)-1)+Real.cos frameCap-Real.cos t
def correctionD (t : ℝ) : ℝ :=
  (1239/2500)*(PositiveAngularEnvelope.phi (frameCap-t)-1)-
    lowK t*(Real.cos (frameCap-t)-Real.sin (frameCap-t))+Real.sin t
def correctionDD (t : ℝ) : ℝ :=
  -(2478/2500)*(Real.cos (frameCap-t)-Real.sin (frameCap-t))-
    lowK t*PositiveAngularEnvelope.phi (frameCap-t)+Real.cos t
def correctionDDD (t : ℝ) : ℝ :=
  -Real.sin t-(3717/2500)*PositiveAngularEnvelope.phi (frameCap-t)+
    lowK t*(Real.cos (frameCap-t)-Real.sin (frameCap-t))

theorem lowK_hasDerivAt (t : ℝ) : HasDerivAt lowK (1239/2500) t := by
  have h : HasDerivAt (fun x : ℝ => 2933/5000+(1239/2500)*x) ((1239/2500)*1) t :=
    ((hasDerivAt_id' t).const_mul (1239/2500:ℝ)).const_add (2933/5000:ℝ)
  convert h using 1
  · funext x; simp only [lowK]
  · ring

private theorem r81_shift_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => frameCap-x) (-1) t := by
  exact (hasDerivAt_id' t).const_sub frameCap

private theorem r81_phi_shift (t : ℝ) :
    HasDerivAt (fun x : ℝ => PositiveAngularEnvelope.phi (frameCap-x))
      (-(Real.cos (frameCap-t)-Real.sin (frameCap-t))) t := by
  have h := (phi_hasDerivAt (frameCap-t)).comp t (r81_shift_hasDerivAt t)
  rw [show (Real.cos (frameCap-t)-Real.sin (frameCap-t))*(-1)=
    -(Real.cos (frameCap-t)-Real.sin (frameCap-t)) by ring] at h
  exact h

private theorem r81_diff_shift (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (frameCap-x)-Real.sin (frameCap-x))
      (PositiveAngularEnvelope.phi (frameCap-t)) t := by
  have h := (r81_shift_hasDerivAt t).cos.sub (r81_shift_hasDerivAt t).sin
  convert h using 1
  simp only [PositiveAngularEnvelope.phi]
  ring

theorem correction_hasDerivAt (t : ℝ) : HasDerivAt correction (correctionD t) t := by
  have h := (((lowK_hasDerivAt t).mul ((r81_phi_shift t).sub_const 1)).add_const
    (Real.cos frameCap)).sub (Real.hasDerivAt_cos t)
  convert h using 1
  · rfl
  · simp only [correctionD]; ring

theorem correctionD_hasDerivAt (t : ℝ) : HasDerivAt correctionD (correctionDD t) t := by
  have h := ((((r81_phi_shift t).sub_const 1).const_mul (1239/2500:ℝ)).sub
    ((lowK_hasDerivAt t).mul (r81_diff_shift t))).add (Real.hasDerivAt_sin t)
  convert h using 1
  · rfl
  · simp only [correctionDD]; ring

theorem correctionDD_hasDerivAt (t : ℝ) : HasDerivAt correctionDD (correctionDDD t) t := by
  have h := (((r81_diff_shift t).const_mul (-(2478/2500:ℝ))).sub
    ((lowK_hasDerivAt t).mul (r81_phi_shift t))).add (Real.hasDerivAt_cos t)
  convert h using 1
  · rfl
  · simp only [correctionDDD]; ring

theorem correction_third_negative {t : ℝ} (ht : t∈Icc 0 L) : correctionDDD t<0 := by
  have hb : frameCap-t∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap,L] at ht ⊢; linarith [ht.2],by linarith [ht.1]⟩
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap,L] at ht ⊢; linarith [ht.2]⟩
  have hs := (transport_trig ht').2.2.1
  have hsb := (transport_trig hb).2.2.1
  have hphi := one_le_phi hb
  have hk := (Analytic.low_ranges ht).1
  have hm := mul_le_mul_of_nonneg_left
    (show Real.cos (frameCap-t)-Real.sin (frameCap-t)≤1 by linarith [Real.cos_le_one (frameCap-t)])
    (show 0≤lowK t by linarith [hk.1])
  dsimp [correctionDDD,K] at *
  linarith [hk.1,hk.2]

theorem low_endpoint_trig :
    Real.cos frameCap-Real.sin frameCap<(1207/10000:ℝ) ∧
    (369/1000:ℝ)<PositiveAngularEnvelope.phi (8/15) -1 ∧
    Real.cos (8/15)-Real.sin (8/15)<(353/1000:ℝ) ∧
    (829/5000:ℝ)<Real.sin L := by
  have hh := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hb := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤8/15 by norm_num)
  have hl := sin_lower_seven (show (0:ℝ)≤L by norm_num [L])
  norm_num [Arithmetic.sin7,Arithmetic.sin9,Arithmetic.cos8,Arithmetic.cos10,frameCap,L] at hh hb hl
  dsimp [PositiveAngularEnvelope.phi]
  exact ⟨by linarith [hh.1,hh.2.2.2],by linarith [hb.1,hb.2.2.1],
    by linarith [hb.1,hb.2.2.2],by linarith⟩

theorem correction_initial : 0<correction 0 ∧ (11/100:ℝ)<correctionD 0 := by
  have hphi := phi_cap_lower
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
  have hd := low_endpoint_trig.1
  norm_num [correction,correctionD,lowK] at ⊢
  constructor <;> linarith

theorem correction_final_derivative : (11/100:ℝ)<correctionD L := by
  have hb := low_endpoint_trig
  have he : frameCap-L=(8/15:ℝ) := by norm_num [frameCap,L]
  rw [correctionD,he]
  norm_num [lowK,L]
  linarith [hb.2.1,hb.2.2.1,hb.2.2.2]

theorem correction_positive {t : ℝ} (ht : t∈Icc 0 L) : 0<correction t := by
  have hconc : ConcaveOn ℝ (Icc 0 L) correctionD := by
    apply concave_of_deriv2 (fun x _ => correctionD_hasDerivAt x)
      (fun x _ => correctionDD_hasDerivAt x)
    intro x hx
    exact (correction_third_negative hx).le
  have hderiv (x : ℝ) (hx : x∈Icc 0 L) : (11/100:ℝ)<correctionD x :=
    concave_gt_of_endpoints hconc hx correction_initial.2 correction_final_derivative
  have hres := derivative_reserve
    (f:=correction) (df:=correctionD) (k:=11/100)
    (fun x _ => (correction_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => correction_hasDerivAt x)
    (fun x hx => (hderiv x (Ioo_subset_Icc_self hx)).le)
    (show (0:ℝ)∈Icc 0 L by norm_num [L]) ht ht.1
  linarith [correction_initial.1,ht.1]

theorem H_same_block {t : ℝ} (ht : t∈Icc 0 L) :
    V R (lowK t) 1 t≤M R (lowK t) 1 t := by
  have hh := correction_positive ht
  dsimp [correction,M,V] at *
  linarith

theorem B_same_block {t : ℝ} (ht : t∈Icc 0 L) :
    V R 1 (lowM t) t≤M R 1 (lowM t) t := by
  have hm := (Analytic.low_ranges ht).2
  exact M_ge_V (by norm_num) (by linarith [hm.1])
    (by norm_num [Cmax] at hm ⊢; linarith [hm.2])
    ⟨ht.1,by norm_num [L,frameCap] at ht ⊢; linarith [ht.2]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LowEnvelope
