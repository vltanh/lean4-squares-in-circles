module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighT
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Split

/-!
# High-BT3 split calculus at fixed original total and DE magnitude

Uncompiled split step. The full-circle D lower stress suffices here:
both intrinsic split endpoints have already been proved for that lower
stress. Its coefficient branch is shifted by 21/1000, as in the existing
BT3 split lemma, and the compensating term is retained in the remainder.
The total-dependent eta and sigma are held fixed during differentiation.
The axial and circular A support branches retain their common value
and first derivative at the exact transition.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open SplitConcavityTools

abbrev shift : ℝ := 21/1000
abbrev k (θ : ℝ) := Explicit.k .high θ
abbrev l (θ : ℝ) := Explicit.l .high θ
abbrev m (θ : ℝ) := Explicit.m .high θ
abbrev sigma (θ : ℝ) := Explicit.sigma .high θ
abbrev eta (θ : ℝ) := Explicit.eta .high θ

def tilt (θ a : ℝ) : ℝ := Explicit.c .high θ (θ-a)
def tiltD (θ a : ℝ) : ℝ := m θ*(Real.sin (θ-a)-eta θ*Real.cos (θ-a))
def smooth (θ a : ℝ) : ℝ :=
  m θ*(1+Real.cos (θ-a)+Real.sin (θ-a))/2-m θ*sigma θ*Real.sin (θ-a)
def smoothD (θ a : ℝ) : ℝ :=
  m θ*(Real.sin (θ-a)-Real.cos (θ-a))/2+m θ*sigma θ*Real.cos (θ-a)
def smoothDD (θ a : ℝ) : ℝ :=
  m θ*(-Real.cos (θ-a)/2+(sigma θ-1/2)*Real.sin (θ-a))
def rest (θ a : ℝ) : ℝ := smooth θ a+l θ*TwoPositive.ASupport.charge a-shift*tilt θ a
def axial (θ a : ℝ) : ℝ := smooth θ a+l θ*TwoPositive.ASupport.axialCharge a-shift*tilt θ a
def circle (θ a : ℝ) : ℝ := smooth θ a+l θ*TwoPositive.ASupport.circleCharge a-shift*tilt θ a

private lemma r72_trig (θ a : ℝ) :
    HasDerivAt (fun x => Real.cos (θ-x)) (-Real.sin (θ-a)*-1) a ∧
      HasDerivAt (fun x => Real.sin (θ-x)) (Real.cos (θ-a)*-1) a := by
  have hz : HasDerivAt (fun x : ℝ => θ-x) (-1) a := (hasDerivAt_id' a).const_sub θ
  exact ⟨(Real.hasDerivAt_cos (θ-a)).comp a hz,(Real.hasDerivAt_sin (θ-a)).comp a hz⟩

theorem tilt_derivative (θ a : ℝ) : HasDerivAt (tilt θ) (tiltD θ a) a := by
  obtain ⟨hc,hs⟩ := r72_trig θ a
  have h : HasDerivAt (fun x => m θ*(Real.cos (θ-x)+eta θ*Real.sin (θ-x)))
      (m θ*(-Real.sin (θ-a)*-1+eta θ*(Real.cos (θ-a)*-1))) a :=
    (hc.fun_add (hs.const_mul (eta θ))).const_mul (m θ)
  rw [show tiltD θ a=m θ*(-Real.sin (θ-a)*-1+eta θ*(Real.cos (θ-a)*-1)) by
    simp only [tiltD]; ring]
  exact h

theorem tilt_second (θ a : ℝ) : HasDerivAt (tiltD θ) (-tilt θ a) a := by
  obtain ⟨hc,hs⟩ := r72_trig θ a
  have h : HasDerivAt (fun x => m θ*(Real.sin (θ-x)-eta θ*Real.cos (θ-x)))
      (m θ*(Real.cos (θ-a)*-1-eta θ*(-Real.sin (θ-a)*-1))) a :=
    (hs.fun_sub (hc.const_mul (eta θ))).const_mul (m θ)
  rw [show -tilt θ a=m θ*(Real.cos (θ-a)*-1-eta θ*(-Real.sin (θ-a)*-1)) by
    simp only [tilt,Explicit.c,m,eta]; ring]
  exact h

theorem tilt_range {θ a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (ha : a∈Icc 0 θ) :
    tilt θ a∈Icc (4/5:ℝ) (6/5) := by
  have hb := Explicit.high_bounds hθ
  have hc := Explicit.high_c hθ (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)
  exact ⟨by dsimp [tilt]; linarith [hb.m_lower,hc.1],
    by dsimp [tilt]; linarith [hb.m_upper,hc.2]⟩

theorem tilt_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (tilt θ) := by
  apply concave_of_deriv2 (fun a _ => tilt_derivative θ a) (fun a _ => tilt_second θ a)
  intro a ha
  have hh := (tilt_range hθ ha).1
  linarith

theorem smooth_derivative (θ a : ℝ) : HasDerivAt (smooth θ) (smoothD θ a) a := by
  obtain ⟨hc,hs⟩ := r72_trig θ a
  have h : HasDerivAt
      (fun x => m θ*(1+Real.cos (θ-x)+Real.sin (θ-x))/2-m θ*sigma θ*Real.sin (θ-x))
      (m θ*(-Real.sin (θ-a)*-1+Real.cos (θ-a)*-1)/2-m θ*sigma θ*(Real.cos (θ-a)*-1)) a :=
    ((((hc.const_add 1).fun_add hs).const_mul (m θ)).div_const 2).fun_sub
      (hs.const_mul (m θ*sigma θ))
  rw [show smoothD θ a=m θ*(-Real.sin (θ-a)*-1+Real.cos (θ-a)*-1)/2-
      m θ*sigma θ*(Real.cos (θ-a)*-1) by simp only [smoothD]; ring]
  exact h

theorem smooth_second (θ a : ℝ) : HasDerivAt (smoothD θ) (smoothDD θ a) a := by
  obtain ⟨hc,hs⟩ := r72_trig θ a
  have h : HasDerivAt
      (fun x => m θ*(Real.sin (θ-x)-Real.cos (θ-x))/2+m θ*sigma θ*Real.cos (θ-x))
      (m θ*(Real.cos (θ-a)*-1-(-Real.sin (θ-a)*-1))/2+m θ*sigma θ*(-Real.sin (θ-a)*-1)) a :=
    (((hs.fun_sub hc).const_mul (m θ)).div_const 2).fun_add (hc.const_mul (m θ*sigma θ))
  rw [show smoothDD θ a=m θ*(Real.cos (θ-a)*-1-(-Real.sin (θ-a)*-1))/2+
      m θ*sigma θ*(-Real.sin (θ-a)*-1) by simp only [smoothDD]; ring]
  exact h

theorem axial_derivative (θ a : ℝ) : HasDerivAt (axial θ)
    (smoothD θ a+l θ*TwoPositive.ASupport.axialD a-shift*tiltD θ a) a := by
  exact ((smooth_derivative θ a).add ((TwoPositive.ASupport.axial_derivative a).const_mul (l θ))).sub
    ((tilt_derivative θ a).const_mul shift)

theorem axial_second (θ a : ℝ) :
    HasDerivAt (fun a => smoothD θ a+l θ*TwoPositive.ASupport.axialD a-shift*tiltD θ a)
      (smoothDD θ a+l θ*TwoPositive.ASupport.axialDD a+shift*tilt θ a) a := by
  convert ((smooth_second θ a).add ((TwoPositive.ASupport.axial_second a).const_mul (l θ))).sub
    ((tilt_second θ a).const_mul shift) using 1
  ring

theorem circle_derivative (θ a : ℝ) : HasDerivAt (circle θ)
    (smoothD θ a+l θ*TwoPositive.ASupport.circleD a-shift*tiltD θ a) a := by
  exact ((smooth_derivative θ a).add ((TwoPositive.ASupport.circle_derivative a).const_mul (l θ))).sub
    ((tilt_derivative θ a).const_mul shift)

theorem circle_second (θ a : ℝ) :
    HasDerivAt (fun a => smoothD θ a+l θ*TwoPositive.ASupport.circleD a-shift*tiltD θ a)
      (smoothDD θ a+l θ*TwoPositive.ASupport.circleDD a+shift*tilt θ a) a := by
  convert ((smooth_second θ a).add ((TwoPositive.ASupport.circle_second a).const_mul (l θ))).sub
    ((tilt_second θ a).const_mul shift) using 1
  ring

lemma rest_curvature {θ a d : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (ha : a∈Icc 0 θ)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    smoothDD θ a+l θ*d+shift*tilt θ a< -(1/20)*l θ := by
  have hb := Explicit.high_bounds hθ
  have hl : 0<l θ := by linarith [hb.l_lower]
  have hm : 0< m θ := by linarith [hb.m_lower]
  have hf := Explicit.frame_domain .high hθ
  have hdom := TwoPositive.Split.split_domain hf ha
  have hsa := (transport_trig hdom.1).2.2.1
  have hsz := (transport_trig hdom.2).2.2.1
  have hca := (transport_trig hdom.1).1
  have hcz := (transport_trig hdom.2).1
  have heta := Explicit.high_eta hθ
  have hsigma : sigma θ≤57/40 :=
    (Explicit.sigma_upper ⟨heta.1,heta.2.le⟩).le
  have hcm := mul_le_mul_of_nonneg_right hb.m_l_lower.le (show 0≤Real.cos (θ-a) by linarith)
  have hcos := mul_lt_mul_of_pos_left (PositiveBT3.Analytic.cosine_sum hf ha) hl
  have hcosA := mul_lt_mul_of_pos_left hca hl
  have hsig := mul_le_mul_of_nonneg_right (show sigma θ-1/2≤37/40 by linarith) hsz
  have hsigM := mul_le_mul_of_nonneg_left hsig hm.le
  have hms := mul_le_mul_of_nonneg_right
    (show m θ≤(11/10)*l θ by linarith [hb.m_l_upper,hb.l_lower]) hsz
  have hsin : Real.sin a+Real.sin (θ-a)≤frameCap := by
    linarith [Real.sin_le ha.1,Real.sin_le hdom.2.1,hf.2]
  have hsinL := mul_le_mul_of_nonneg_left hsin hl.le
  have hsinAL := mul_nonneg hl.le hsa
  have hcharge := mul_le_mul_of_nonneg_left hd hl.le
  have htilt := Explicit.high_c_ratio hθ
    (show θ-a∈Icc 0 θ from ⟨hdom.2.1,by linarith [ha.1]⟩) (1:Fin 3)
  change tilt θ a<(109/100)*l θ at htilt
  have hshift := mul_le_mul_of_nonneg_left htilt.le (show 0≤ shift by norm_num [shift])
  dsimp [smoothDD,shift,frameCap] at *
  nlinarith only [hcm,hcos,hcosA,hsigM,hms,hsinL,hsinAL,hcharge,hshift,hl]

theorem rest_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (rest θ) := by
  have hf := Explicit.frame_domain .high hθ
  have hax {L U : ℝ} (hL : 0≤L) (hU : U≤θ) :
      ConcaveOn ℝ (Icc L U) (axial θ) := by
    apply concave_of_deriv2 (fun a _ => axial_derivative θ a) (fun a _ => axial_second θ a)
    intro a ha
    have ha' : a∈Icc 0 θ := ⟨hL.trans ha.1,ha.2.trans hU⟩
    exact (rest_curvature hθ ha'
      (TwoPositive.Split.high_axial_bound (TwoPositive.Split.split_domain hf ha').1)).le.trans
        (by linarith [(Explicit.high_bounds hθ).l_lower])
  by_cases hcut : θ≤TwoPositive.ASupport.alpha
  · apply TwoPositive.Split.congr_on (hax (L:=0) (U:=θ) le_rfl le_rfl)
    intro a ha
    simp only [axial,rest,TwoPositive.ASupport.charge,ha.2.trans hcut,↓reduceIte]
  · have halpha : TwoPositive.ASupport.alpha∈Icc 0 θ :=
      ⟨by linarith [TwoPositive.ASupport.alpha_bounds.1],(lt_of_not_ge hcut).le⟩
    have hcirc : ConcaveOn ℝ (Icc TwoPositive.ASupport.alpha θ) (circle θ) := by
      apply concave_of_deriv2 (fun a _ => circle_derivative θ a) (fun a _ => circle_second θ a)
      intro a ha
      have ha' : a∈Icc 0 θ := ⟨halpha.1.trans ha.1,ha.2⟩
      have haf := (TwoPositive.Split.split_domain hf ha').1
      have hmajor := TwoPositive.ASupport.high_curvature_majorant
        (show a∈Icc (1/2:ℝ) frameCap from
          ⟨by linarith [ha.1,TwoPositive.ASupport.alpha_bounds.1],haf.2⟩)
      exact (rest_curvature hθ ha'
        ((TwoPositive.ASupport.circle_curvature haf).trans hmajor)).le.trans
          (by linarith [(Explicit.high_bounds hθ).l_lower])
    have he : axial θ TwoPositive.ASupport.alpha=circle θ TwoPositive.ASupport.alpha := by
      simp only [axial,circle,TwoPositive.ASupport.transition_value]
    have hl := axial_derivative θ TwoPositive.ASupport.alpha
    have hr := circle_derivative θ TwoPositive.ASupport.alpha
    rw [←TwoPositive.ASupport.transition_derivative] at hr
    have hj := join halpha (hax le_rfl halpha.2) hcirc he hl hr
    apply TwoPositive.Split.congr_on hj
    intro a _
    by_cases h : a≤TwoPositive.ASupport.alpha
    · simp only [axial,rest,TwoPositive.ASupport.charge,h,↓reduceIte]
    · simp only [circle,rest,TwoPositive.ASupport.charge,h,↓reduceIte]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighSplit
