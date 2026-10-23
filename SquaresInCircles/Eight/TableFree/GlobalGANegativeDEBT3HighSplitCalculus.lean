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
open TwoPositive (ASupport)

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
def rest (θ a : ℝ) : ℝ := smooth θ a+l θ*ASupport.charge a-shift*tilt θ a
def axial (θ a : ℝ) : ℝ := smooth θ a+l θ*ASupport.axialCharge a-shift*tilt θ a
def circle (θ a : ℝ) : ℝ := smooth θ a+l θ*ASupport.circleCharge a-shift*tilt θ a

theorem tilt_derivative (θ a : ℝ) : HasDerivAt (tilt θ) (tiltD θ a) a := by
  have hz := (hasDerivAt_id a).const_sub θ
  convert (((Real.hasDerivAt_cos (θ-a)).comp a hz).add
    (((Real.hasDerivAt_sin (θ-a)).comp a hz).const_mul (eta θ))).const_mul (m θ) using 1 <;>
    dsimp [tilt,tiltD,Explicit.c,m,eta] <;> ring

theorem tilt_second (θ a : ℝ) : HasDerivAt (tiltD θ) (-tilt θ a) a := by
  have hz := (hasDerivAt_id a).const_sub θ
  convert (((Real.hasDerivAt_sin (θ-a)).comp a hz).sub
    (((Real.hasDerivAt_cos (θ-a)).comp a hz).const_mul (eta θ))).const_mul (m θ) using 1 <;>
    dsimp [tilt,tiltD,Explicit.c,m,eta] <;> ring

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
  have hz := (hasDerivAt_id a).const_sub θ
  have hc := (Real.hasDerivAt_cos (θ-a)).comp a hz
  have hs := (Real.hasDerivAt_sin (θ-a)).comp a hz
  convert ((((hc.const_add 1).add hs).const_mul (m θ)).div_const 2).sub
    (hs.const_mul (m θ*sigma θ)) using 1 <;> dsimp [smooth,smoothD] <;> ring

theorem smooth_second (θ a : ℝ) : HasDerivAt (smoothD θ) (smoothDD θ a) a := by
  have hz := (hasDerivAt_id a).const_sub θ
  have hc := (Real.hasDerivAt_cos (θ-a)).comp a hz
  have hs := (Real.hasDerivAt_sin (θ-a)).comp a hz
  convert (((hs.sub hc).const_mul (m θ)).div_const 2).add
    (hc.const_mul (m θ*sigma θ)) using 1 <;> dsimp [smoothD,smoothDD] <;> ring

theorem axial_derivative (θ a : ℝ) : HasDerivAt (axial θ)
    (smoothD θ a+l θ*ASupport.axialD a-shift*tiltD θ a) a := by
  exact ((smooth_derivative θ a).add ((ASupport.axial_derivative a).const_mul (l θ))).sub
    ((tilt_derivative θ a).const_mul shift)

theorem axial_second (θ a : ℝ) :
    HasDerivAt (fun a => smoothD θ a+l θ*ASupport.axialD a-shift*tiltD θ a)
      (smoothDD θ a+l θ*ASupport.axialDD a+shift*tilt θ a) a := by
  convert ((smooth_second θ a).add ((ASupport.axial_second a).const_mul (l θ))).sub
    ((tilt_second θ a).const_mul shift) using 1 <;> ring

theorem circle_derivative (θ a : ℝ) : HasDerivAt (circle θ)
    (smoothD θ a+l θ*ASupport.circleD a-shift*tiltD θ a) a := by
  exact ((smooth_derivative θ a).add ((ASupport.circle_derivative a).const_mul (l θ))).sub
    ((tilt_derivative θ a).const_mul shift)

theorem circle_second (θ a : ℝ) :
    HasDerivAt (fun a => smoothD θ a+l θ*ASupport.circleD a-shift*tiltD θ a)
      (smoothDD θ a+l θ*ASupport.circleDD a+shift*tilt θ a) a := by
  convert ((smooth_second θ a).add ((ASupport.circle_second a).const_mul (l θ))).sub
    ((tilt_second θ a).const_mul shift) using 1 <;> ring

lemma rest_curvature {θ a d : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (ha : a∈Icc 0 θ)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    smoothDD θ a+l θ*d+shift*tilt θ a<-(1/20)*l θ := by
  have hb := Explicit.high_bounds hθ
  have hl : 0<l θ := by linarith [hb.l_lower]
  have hm : 0<m θ := by linarith [hb.m_lower]
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
  have hshift := mul_le_mul_of_nonneg_left htilt.le (show 0≤shift by norm_num [shift])
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
  by_cases hcut : θ≤ASupport.alpha
  · apply TwoPositive.Split.congr_on (hax (L:=0) (U:=θ) le_rfl le_rfl)
    intro a ha
    simp [axial,rest,ASupport.charge,if_pos (ha.2.trans hcut)]
  · have halpha : ASupport.alpha∈Icc 0 θ :=
      ⟨by linarith [ASupport.alpha_bounds.1],(lt_of_not_ge hcut).le⟩
    have hcirc : ConcaveOn ℝ (Icc ASupport.alpha θ) (circle θ) := by
      apply concave_of_deriv2 (fun a _ => circle_derivative θ a) (fun a _ => circle_second θ a)
      intro a ha
      have ha' : a∈Icc 0 θ := ⟨halpha.1.trans ha.1,ha.2⟩
      have haf := (TwoPositive.Split.split_domain hf ha').1
      have hmajor := ASupport.high_curvature_majorant
        (show a∈Icc (1/2:ℝ) frameCap from
          ⟨by linarith [ha.1,ASupport.alpha_bounds.1],haf.2⟩)
      exact (rest_curvature hθ ha' ((ASupport.circle_curvature haf).trans hmajor)).le.trans
        (by linarith [(Explicit.high_bounds hθ).l_lower])
    have he : axial θ ASupport.alpha=circle θ ASupport.alpha := by
      simp only [axial,circle,ASupport.transition_value]
    have hl := axial_derivative θ ASupport.alpha
    have hr := circle_derivative θ ASupport.alpha
    rw [←ASupport.transition_derivative] at hr
    have hj := join halpha (hax le_rfl halpha.2) hcirc he hl hr
    simpa only [axial,circle,rest,ASupport.charge,←mul_ite,←add_ite,←ite_sub] using hj

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighSplit
