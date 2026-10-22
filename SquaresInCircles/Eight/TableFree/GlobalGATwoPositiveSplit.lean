module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveCoefficientBounds

/-!
# Concavity in the actual A/TD split

Uncompiled transcription of Sections 3--6 of
`HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md`.
The coefficients are fixed while the nonnegative total is split.  The
low coefficient function is shifted by `12/25`; its compensating term
is kept in the scalar remainder.  The high proof joins the two actual
A support branches with their common value and derivative.  Thus the
coefficient kink and the A support transition retain their closed ties.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Split
open Candidate Secondary PositiveTD PositiveAngularEnvelope
open SplitConcavityTools

def mD (c t a : ℝ) : ℝ := c*(Real.sin (t-a)-eta*Real.cos (t-a))

def smooth (c z : ℝ) : ℝ := c*(1+Real.cos z+Real.sin z)/2-c*sigma*Real.sin z

def smoothD (c t a : ℝ) : ℝ :=
  c*(Real.sin (t-a)-Real.cos (t-a))/2+c*sigma*Real.cos (t-a)

def smoothDD (c t a : ℝ) : ℝ :=
  c*(-Real.cos (t-a)/2+(sigma-1/2)*Real.sin (t-a))

def axialRest (r c l t a : ℝ) : ℝ :=
  smooth c (t-a)+l*ASupport.axialCharge a-r*tilted c (t-a)

def circleRest (r c l t a : ℝ) : ℝ :=
  smooth c (t-a)+l*ASupport.circleCharge a-r*tilted c (t-a)

def rest (c l t a : ℝ) : ℝ := smooth c (t-a)+l*ASupport.charge a

theorem split_domain {t a : ℝ} (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t) :
    a∈Icc 0 frameCap ∧ t-a∈Icc 0 frameCap := by
  exact ⟨⟨ha.1,ha.2.trans ht.2⟩,⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩⟩

theorem tilted_derivative (c t a : ℝ) :
    HasDerivAt (fun x => tilted c (t-x)) (mD c t a) a := by
  have hz := (hasDerivAt_id a).const_sub t
  convert (((Real.hasDerivAt_cos (t-a)).comp a hz).add
    (((Real.hasDerivAt_sin (t-a)).comp a hz).const_mul eta)).const_mul c using 1 <;>
    dsimp [tilted,mD] <;> ring

theorem tilted_second (c t a : ℝ) :
    HasDerivAt (mD c t) (-tilted c (t-a)) a := by
  have hz := (hasDerivAt_id a).const_sub t
  convert (((Real.hasDerivAt_sin (t-a)).comp a hz).sub
    (((Real.hasDerivAt_cos (t-a)).comp a hz).const_mul eta)).const_mul c using 1 <;>
    dsimp [tilted,mD] <;> ring

theorem tilted_concave {c t : ℝ} (hc : 0<c) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 t) (fun a => tilted c (t-a)) := by
  apply concave_of_deriv2 (fun a _ => tilted_derivative c t a)
    (fun a _ => tilted_second c t a)
  intro a ha
  exact neg_nonpos.mpr (tilted_pos hc (split_domain ht ha).2).le

theorem smooth_actual {c z : ℝ} (hz : z∈Icc 0 frameCap) :
    smooth c z=c*edgeWidth z-c*sigma*Real.sin z := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hz.1]; exact hz.2)
  simp only [smooth,edgeWidth,pairWidth,abs_of_pos hc,
    abs_of_nonneg (transport_trig hz).2.2.1]
  ring

theorem smooth_derivative (c t a : ℝ) :
    HasDerivAt (fun x => smooth c (t-x)) (smoothD c t a) a := by
  have hz := (hasDerivAt_id a).const_sub t
  have hcos := (Real.hasDerivAt_cos (t-a)).comp a hz
  have hsin := (Real.hasDerivAt_sin (t-a)).comp a hz
  convert ((((hcos.const_add 1).add hsin).const_mul c).div_const 2).sub
    (hsin.const_mul (c*sigma)) using 1 <;> dsimp [smooth,smoothD] <;> ring

theorem smooth_second (c t a : ℝ) :
    HasDerivAt (smoothD c t) (smoothDD c t a) a := by
  have hz := (hasDerivAt_id a).const_sub t
  have hcos := (Real.hasDerivAt_cos (t-a)).comp a hz
  have hsin := (Real.hasDerivAt_sin (t-a)).comp a hz
  convert (((hsin.sub hcos).const_mul c).div_const 2).add
    (hcos.const_mul (c*sigma)) using 1 <;> dsimp [smoothD,smoothDD] <;> ring

theorem axial_derivative (r c l t a : ℝ) :
    HasDerivAt (axialRest r c l t)
      (smoothD c t a+l*ASupport.axialD a-r*mD c t a) a := by
  convert ((smooth_derivative c t a).add
    ((ASupport.axial_derivative a).const_mul l)).sub
      ((tilted_derivative c t a).const_mul r) using 1 <;> rfl

theorem axial_second (r c l t a : ℝ) :
    HasDerivAt (fun x => smoothD c t x+l*ASupport.axialD x-r*mD c t x)
      (smoothDD c t a+l*ASupport.axialDD a+r*tilted c (t-a)) a := by
  convert ((smooth_second c t a).add
    ((ASupport.axial_second a).const_mul l)).sub
      ((tilted_second c t a).const_mul r) using 1 <;> ring

theorem circle_derivative (r c l t a : ℝ) :
    HasDerivAt (circleRest r c l t)
      (smoothD c t a+l*ASupport.circleD a-r*mD c t a) a := by
  convert ((smooth_derivative c t a).add
    ((ASupport.circle_derivative a).const_mul l)).sub
      ((tilted_derivative c t a).const_mul r) using 1 <;> rfl

theorem circle_second (r c l t a : ℝ) :
    HasDerivAt (fun x => smoothD c t x+l*ASupport.circleD x-r*mD c t x)
      (smoothDD c t a+l*ASupport.circleDD a+r*tilted c (t-a)) a := by
  convert ((smooth_second c t a).add
    ((ASupport.circle_second a).const_mul l)).sub
      ((tilted_second c t a).const_mul r) using 1 <;> ring

theorem sigma_bound : sigma≤177/125 := by
  have hh := PositiveTD.Certificate.sigma_le_sigmabar
  norm_num [PositiveTD.Certificate.sigmabar] at hh
  linarith

theorem low_trig {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    (71/72:ℝ)≤Real.cos a ∧ 0≤Real.sin a ∧ Real.sin a≤1/6 := by
  have ha2 : a^2≤(1/6:ℝ)^2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=a)
  exact ⟨by nlinarith,(transport_trig ⟨ha.1,by norm_num [frameCap]; linarith [ha.2]⟩).2.2.1,
    (Real.sin_le_self ha.1).trans ha.2⟩

theorem low_rest_curvature {c l t a : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) :
    smoothDD c t a+l*ASupport.axialDD a+(12/25)*tilted c (t-a)<-(9/100)*l := by
  have ha' : a∈Icc 0 (1/6:ℝ) := ⟨ha.1,ha.2.trans ht.2⟩
  have hz : t-a∈Icc 0 (1/6:ℝ) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have hta := low_trig ha'
  have htz := low_trig hz
  have hsig := mul_le_mul_of_nonneg_right
    (show sigma-1/2≤229/250 by linarith [sigma_bound]) htz.2.1
  have hax := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) hta.2.1
  have hzBound : -Real.cos (t-a)/2+(sigma-1/2)*Real.sin (t-a)≤
      -71/144+229/1500 := by linarith [htz.1,htz.2.2]
  have haBound : ASupport.axialDD a≤-71/144+61/400 := by
    dsimp [ASupport.axialDD]
    linarith [hta.1,hta.2.2]
  have hm : tilted c (t-a)≤c*(1+eta/6) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    have hh := Real.cos_le_one (t-a)
    dsimp [eta]
    linarith [htz.2.2]
  have hcz := mul_le_mul_of_nonneg_left hzBound hc.le
  have hla := mul_le_mul_of_nonneg_left haBound hl.le
  have hcm := mul_le_mul_of_nonneg_left hm (show (0:ℝ)≤12/25 by norm_num)
  have hratio := mul_le_mul_of_nonneg_right hcl
    (show (0:ℝ)≤(12/25)*(1+eta/6)-71/144+229/1500 by norm_num [eta])
  dsimp [smoothDD,eta] at *
  nlinarith only [hcz,hla,hcm,hratio,hl]

theorem low_rest_concave {c l t : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l) (ht : t∈Icc 0 (1/6:ℝ)) :
    ConcaveOn ℝ (Icc 0 t) (axialRest (12/25) c l t) := by
  apply concave_of_deriv2 (fun a _ => axial_derivative (12/25) c l t a)
    (fun a _ => axial_second (12/25) c l t a)
  intro a ha
  exact (low_rest_curvature hc hl hcl ht ha).le.trans (by linarith)

theorem low_tilted_lower {c t a : ℝ} (hc : 0<c)
    (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) : c/2≤tilted c (t-a) := by
  have hz : t-a∈Icc 0 (1/6:ℝ) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have htrig := low_trig hz
  have hf : (1/2:ℝ)≤Real.cos (t-a)+eta*Real.sin (t-a) := by
    have hh := mul_nonneg (show (0:ℝ)≤eta by norm_num [eta]) htrig.2.1
    linarith [htrig.1]
  have hh := mul_le_mul_of_nonneg_left hf hc.le
  simpa [tilted,div_eq_mul_inv,mul_comm] using hh

/-- Every low scalar in equation (24), with its actual coefficient
transition, is concave on the complete fixed-total split. -/
theorem low_scalar_concave {c l t s g e : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ)) (hs : |s|≤frameCap)
    (hg : 0≤g) (he : e≤0) (heLow : Real.cos frameCap-1≤e)
    (hePos : 0<s→e=0)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => Coefficient.H l s g e (tilted c (t-a))+rest c l t a) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hH := Coefficient.H_shifted_low (L:=c/2) (U:=(3/2)*l)
    hl (by positivity) le_rfl hs hg he heLow hePos
  have hcomp := compose hH.1 hH.2 (tilted_concave hc ht')
    (fun a ha => ⟨low_tilted_lower hc ht ha,hm a ha⟩)
  have hsum := hcomp.add (low_rest_concave hc hl hcl ht)
  have heq {a : ℝ} (ha : a∈Icc 0 t) :
      Coefficient.H l s g e (tilted c (t-a))+(12/25)*tilted c (t-a)+
        axialRest (12/25) c l t a=
      Coefficient.H l s g e (tilted c (t-a))+rest c l t a := by
    rw [rest,ASupport.charge_low (ha.2.trans ht.2)]
    dsimp [axialRest]
    ring
  refine ⟨hsum.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hsum.2 hx hy hr hv hrv
  simp only [Pi.add_apply] at hh
  rw [heq hx,heq hy,heq (hsum.1 hx hy hr hv hrv)] at hh
  exact hh

theorem high_rest_curvature {c l t a d : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    smoothDD c t a+l*d<-(1/50)*l := by
  have hc : 0<c := by linarith
  have hdom := split_domain ht ha
  have hsa := (transport_trig hdom.1).2.2.1
  have hsz := (transport_trig hdom.2).2.2.1
  have hca : (478/625:ℝ)<Real.cos a :=
    Coefficient.cap_cosine_lower.trans_le
      (Real.cos_le_cos_of_nonneg_of_le_pi hdom.1.1
        (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hdom.1.2)
  have hcz : (478/625:ℝ)<Real.cos (t-a) :=
    Coefficient.cap_cosine_lower.trans_le
      (Real.cos_le_cos_of_nonneg_of_le_pi hdom.2.1
        (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hdom.2.2)
  have hcosA := mul_le_mul_of_nonneg_left hca.le hl.le
  have hcosZ := mul_le_mul_of_nonneg_left hcz.le hc.le
  have hsig := mul_le_mul_of_nonneg_right
    (show sigma-1/2≤229/250 by linarith [sigma_bound]) hsz
  have hsigC := mul_le_mul_of_nonneg_left hsig hc.le
  have hczUpper := mul_le_mul_of_nonneg_right hcHigh hsz
  have hcharge := mul_le_mul_of_nonneg_left hd hl.le
  have hsin : Real.sin a+Real.sin (t-a)≤frameCap := by
    linarith [Real.sin_le_self ha.1,Real.sin_le_self hdom.2.1,ht.2]
  have hsinL := mul_le_mul_of_nonneg_left hsin hl.le
  have hsinAL := mul_nonneg hl.le hsa
  dsimp [smoothDD,frameCap] at *
  nlinarith only [hcLow,hcosA,hcosZ,hsigC,hczUpper,hcharge,hsinL,hsinAL,hl]

theorem high_axial_bound {a : ℝ} (ha : a∈Icc 0 frameCap) :
    ASupport.axialDD a≤-Real.cos a/2+(23/25)*Real.sin a := by
  have hh := ASupport.axial_curvature ha
  have hs := (transport_trig ha).2.2.1
  linarith

theorem high_rest_concave {c l t : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) : ConcaveOn ℝ (Icc 0 t) (rest c l t) := by
  have hax {L U : ℝ} (hL : 0≤L) (hU : U≤t) :
      ConcaveOn ℝ (Icc L U) (axialRest 0 c l t) := by
    apply concave_of_deriv2 (fun a _ => axial_derivative 0 c l t a)
      (fun a _ => axial_second 0 c l t a)
    intro a ha
    have ha' : a∈Icc 0 t := ⟨hL.trans ha.1,ha.2.trans hU⟩
    have hh := high_rest_curvature hl hcLow hcHigh ht ha'
      (high_axial_bound (split_domain ht ha').1)
    simpa only [zero_mul,add_zero] using hh.le.trans (by linarith : -(1/50)*l≤0)
  by_cases hcut : t≤ASupport.alpha
  · have hh := hax (L:=0) (U:=t) le_rfl le_rfl
    have heq {a : ℝ} (ha : a∈Icc 0 t) : axialRest 0 c l t a=rest c l t a := by
      simp [axialRest,rest,ASupport.charge,if_pos (ha.2.trans hcut)]
    refine ⟨hh.1,?_⟩
    intro x hx y hy r v hr hv hrv
    have h := hh.2 hx hy hr hv hrv
    rw [heq hx,heq hy,heq (hh.1 hx hy hr hv hrv)] at h
    exact h
  · have halpha : ASupport.alpha∈Icc 0 t :=
      ⟨by linarith [ASupport.alpha_bounds.1],(lt_of_not_ge hcut).le⟩
    have hcirc : ConcaveOn ℝ (Icc ASupport.alpha t) (circleRest 0 c l t) := by
      apply concave_of_deriv2 (fun a _ => circle_derivative 0 c l t a)
        (fun a _ => circle_second 0 c l t a)
      intro a ha
      have ha' : a∈Icc 0 t := ⟨halpha.1.trans ha.1,ha.2⟩
      have haFrame := (split_domain ht ha').1
      have hmajor := ASupport.high_curvature_majorant
        (show a∈Icc (1/2:ℝ) frameCap from
          ⟨by linarith [ha.1,ASupport.alpha_bounds.1],haFrame.2⟩)
      have hd := (ASupport.circle_curvature haFrame).trans hmajor
      have hh := high_rest_curvature hl hcLow hcHigh ht ha' hd
      simpa only [zero_mul,add_zero] using hh.le.trans (by linarith : -(1/50)*l≤0)
    have he : axialRest 0 c l t ASupport.alpha=circleRest 0 c l t ASupport.alpha := by
      simp only [axialRest,circleRest,ASupport.transition_value]
    have hd : smoothD c t ASupport.alpha+l*ASupport.axialD ASupport.alpha=
        smoothD c t ASupport.alpha+l*ASupport.circleD ASupport.alpha := by
      rw [ASupport.transition_derivative]
    have hleft := axial_derivative 0 c l t ASupport.alpha
    have hright := circle_derivative 0 c l t ASupport.alpha
    simp only [zero_mul,sub_zero] at hleft hright
    rw [← hd] at hright
    have hj := join halpha (hax le_rfl halpha.2) hcirc he hleft hright
    simpa only [axialRest,circleRest,rest,ASupport.charge,zero_mul,sub_zero,
      ← mul_ite,← add_ite] using hj

/-- The balanced single-negative alternatives retain their actual
`min/max` coefficient kink throughout the high split. -/
theorem high_scalar_concave {c l t s g e L U : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hL : 0<L) (hU : U≤(23/20)*l)
    (hge : e≤g) (he : Real.cos s-1≤e)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)∈Icc L U) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => Coefficient.H l (-s) g e (tilted c (t-a))+rest c l t a) := by
  have hc : 0<c := by linarith
  have hH := Coefficient.H_concave hl hL
    (show |-s|≤frameCap by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2) hge
  have hmono := Coefficient.H_high_monotone hl hL hU hs hge he
  exact (compose hH hmono (tilted_concave hc ht) hm).add
    (high_rest_concave hl hcLow hcHigh ht)

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Split
