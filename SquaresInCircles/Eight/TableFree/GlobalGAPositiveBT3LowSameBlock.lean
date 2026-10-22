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
  lowK t*(phi (frameCap-t)-1)+Real.cos frameCap-Real.cos t
def correctionD (t : ℝ) : ℝ :=
  (1239/2500)*(phi (frameCap-t)-1)-
    lowK t*(Real.cos (frameCap-t)-Real.sin (frameCap-t))+Real.sin t
def correctionDD (t : ℝ) : ℝ :=
  -(2478/2500)*(Real.cos (frameCap-t)-Real.sin (frameCap-t))-
    lowK t*phi (frameCap-t)+Real.cos t
def correctionDDD (t : ℝ) : ℝ :=
  -Real.sin t-(3717/2500)*phi (frameCap-t)+
    lowK t*(Real.cos (frameCap-t)-Real.sin (frameCap-t))

theorem lowK_hasDerivAt (t : ℝ) : HasDerivAt lowK (1239/2500) t := by
  convert ((hasDerivAt_id t).const_mul (1239/2500)).const_add (2933/5000) using 1 <;>
    dsimp [lowK] <;> ring

theorem correction_hasDerivAt (t : ℝ) : HasDerivAt correction (correctionD t) t := by
  have hb := (hasDerivAt_id t).const_sub frameCap
  have hphi := (phi_hasDerivAt (frameCap-t)).comp t hb
  convert (((lowK_hasDerivAt t).mul (hphi.sub_const 1)).add_const
    (Real.cos frameCap)).sub (Real.hasDerivAt_cos t) using 1 <;>
    dsimp [correction,correctionD] <;> ring

theorem correctionD_hasDerivAt (t : ℝ) : HasDerivAt correctionD (correctionDD t) t := by
  have hb := (hasDerivAt_id t).const_sub frameCap
  have hp := (phi_hasDerivAt (frameCap-t)).comp t hb
  have hd := hb.cos.sub hb.sin
  convert (((hp.sub_const 1).const_mul (1239/2500)).sub
    ((lowK_hasDerivAt t).mul hd)).add (Real.hasDerivAt_sin t) using 1 <;>
    dsimp [correctionD,correctionDD,phi] <;> ring

theorem correctionDD_hasDerivAt (t : ℝ) : HasDerivAt correctionDD (correctionDDD t) t := by
  have hb := (hasDerivAt_id t).const_sub frameCap
  have hp := (phi_hasDerivAt (frameCap-t)).comp t hb
  have hd := hb.cos.sub hb.sin
  convert ((hd.const_mul (-(2478/2500))).sub
    ((lowK_hasDerivAt t).mul hp)).add (Real.hasDerivAt_cos t) using 1 <;>
    dsimp [correctionDD,correctionDDD,phi] <;> ring

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
  linarith

theorem low_endpoint_trig :
    Real.cos frameCap-Real.sin frameCap<(1207/10000:ℝ) ∧
    (369/1000:ℝ)<phi (8/15) -1 ∧
    Real.cos (8/15)-Real.sin (8/15)<(353/1000:ℝ) ∧
    (829/5000:ℝ)<Real.sin L := by
  have hh := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hb := Arithmetic.trig_taylor_bounds (show (0:ℝ)≤8/15 by norm_num)
  have hl := sin_lower_seven (show (0:ℝ)≤L by norm_num [L])
  norm_num [Arithmetic.sin7,Arithmetic.sin9,Arithmetic.cos8,Arithmetic.cos10,frameCap,L] at hh hb hl
  dsimp [phi]
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
  nlinarith [correction_initial.1]

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
