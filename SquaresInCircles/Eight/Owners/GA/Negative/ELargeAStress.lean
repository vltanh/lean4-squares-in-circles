module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3PositivePure
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Positive.ANegativeTDScalars
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Split
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveScalar

/-!
# Eight squares: the large-A negative-E / nonpositive-TD2 contradiction

The D circle gives the secant correction `M` (`de_gain_lower`), the EH entry gives its small
tangent (`eh_gain_lower`), and the signed state of T gives the TD secant gain (`t_gain_lower`).
Each term is compared before the inequalities of the cycle are summed. `actual_false` assumes no
support or gain reserve.
-/

section
/-!
## High-BT3 split calculus at a fixed total and DE magnitude

The full-circle lower stress of D suffices here, since both intrinsic split endpoints hold for it.
Its coefficient branch is shifted by `21/1000`, as in the BT3 split lemma, and the compensating
term stays in the remainder `rest`. The total-dependent `eta` and `sigma` are held fixed during
differentiation. The axial and circular branches of the A support share their value and first
derivative at the transition (`rest_concave`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSplit
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

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSplit
end
end
end

section
/-!
## The intrinsic A and combined-angle shapes for negative core E

The actual A support is joined only at its matching value and
first derivative. The combined EH gain keeps its separate cut at 1/4.
Every curvature and derivative bound below is proved on its whole domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeSlope TwoPositive.ASupport
open NegativeAPositiveTD.PositiveSlope

def gD (s : ℝ) : ℝ := K*Real.cos s-beta*Real.sin s
def gDD (s : ℝ) : ℝ := -K*Real.sin s-beta*Real.cos s

theorem g_hasDerivAt (s : ℝ) : HasDerivAt g (gD s) s := by
  have h : HasDerivAt (fun s => K*Real.sin s-beta*(1-Real.cos s))
      (K*Real.cos s-beta*(- -Real.sin s)) s :=
    ((Real.hasDerivAt_sin s).const_mul K).sub
      (((Real.hasDerivAt_cos s).const_sub 1).const_mul beta)
  exact h.congr_deriv (by dsimp [gD]; ring)

theorem gD_hasDerivAt (s : ℝ) : HasDerivAt gD (gDD s) s := by
  have h : HasDerivAt (fun s => K*Real.cos s-beta*Real.sin s)
      (K*(-Real.sin s)-beta*Real.cos s) s :=
    ((Real.hasDerivAt_cos s).const_mul K).sub ((Real.hasDerivAt_sin s).const_mul beta)
  exact h.congr_deriv (by dsimp [gDD]; ring)

@[simp] theorem g_zero : g 0=0 := by simp [g]
@[simp] theorem jointGain_zero : jointGain 0=0 := by norm_num [jointGain,u]
@[simp] theorem jointGain_cut : jointGain u=g u := by simp [jointGain]

theorem g_concave : ConcaveOn ℝ (Icc 0 frameCap) g := by
  apply concave_of_deriv2 (fun s _ => g_hasDerivAt s) (fun s _ => gD_hasDerivAt s)
  intro s hs
  have ht := transport_trig hs
  dsimp [gDD,K,beta]
  linarith [ht.1,ht.2.2.1]

theorem combined_gain_lower {s r : ℝ} (hs : s∈Icc 0 u) (hr : 0≤r)
    (hw : s+r≤frameCap) :
    min (M*(s+r)) (jointGain (s+r))≤g s+M*r := by
  obtain ⟨b,hbdef⟩ : ∃b : ℝ,b=min (s+r) u := ⟨_,rfl⟩
  have hb0 : 0≤b := hbdef ▸ le_min (by linarith [hs.1]) (by norm_num [u])
  have hbf : b≤frameCap := hbdef ▸ (min_le_left _ _).trans hw
  have hsb : s∈Icc 0 b := ⟨hs.1,hbdef ▸ le_min (by linarith) hs.2⟩
  have hc := (g_concave.subset (Icc_subset_Icc le_rfl hbf) (convex_Icc 0 b)).add
    (affine_concave (-M) 0 0 b)
  have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hb0⟩ ⟨hb0,le_rfl⟩ hsb
  simp only [Pi.add_apply,g_zero,mul_zero,add_zero] at hm
  have he : min (M*(s+r)) (jointGain (s+r))=M*(s+r)+min 0 (g b-M*b) := by
    rw [← min_add_add_left,add_zero]
    by_cases hcut : s+r≤u
    · rw [jointGain,ite_eq_left hcut,hbdef,min_eq_left hcut]
      congr 1; ring
    · rw [jointGain,ite_eq_right hcut,hbdef,min_eq_right (lt_of_not_ge hcut).le]
      congr 1; ring
  rw [he]
  have hh : min 0 (g b-M*b)≤g s-M*s := by
    convert hm using 2 <;> ring
  linarith

theorem axial_derivative_lower {a : ℝ} (ha : a∈Icc 0 frameCap) :
    -(11/10:ℝ)<axialD a := by
  have ht := transport_trig ha
  have hp : (1/2)*Real.sin a+(183/200)*Real.cos a<(21/20:ℝ) := by
    have hs : ((1/2)*Real.sin a+(183/200)*Real.cos a)^2≤
        (1/4:ℝ)+(183/200)^2 := by
      nlinarith [Real.sin_sq_add_cos_sq a,
        sq_nonneg ((183/200)*Real.sin a-(1/2)*Real.cos a)]
    nlinarith
  have hm := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) (by linarith [ht.1] : 0≤Real.cos a)
  dsimp [axialD]
  linarith

theorem circle_derivative_lower {a : ℝ} (ha : a∈Icc 0 frameCap) :
    -(11/10:ℝ)<circleD a := by
  have hm : AntitoneOn circleD (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun a _ => (circle_second a).continuousAt.continuousWithinAt)
      (fun a _ => circle_second a)
    intro a ha
    exact circle_curvature (Ioo_subset_Icc_self ha)
  have hlast := hm ha (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ha.2
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hh := cos_upper_four (show (0:ℝ)≤7/20 by norm_num)
  have hhalf0 : 0≤Real.cos (7/20) := by
    have := (half_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2.le
    rwa [show frameCap/2=(7/20:ℝ) by norm_num [frameCap]] at this
  have hmul := mul_le_mul_of_nonneg_right radius_tight.2.le hhalf0
  simp only [radiusHi] at hmul
  norm_num at hc hh
  have e : circleD frameCap=Real.cos (7/10)-R*Real.cos (7/20) := by
    simp only [circleD]
    rw [show frameCap/2=(7/20:ℝ) by norm_num [frameCap]]
  linarith

theorem negative_curvature (i : Fin 4) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    curvature R (p i) (q i) (-x)-q i*Real.cos x< -(81/1250)*q i := by
  have hc := coefficients i
  have hq := hc.1.trans_le hc.2.1
  have hb := curvature_constant_bounds (Real.sqrt_nonneg qCap) radius_sq.le
    hc.1 hc.2.1 (by linarith [hc.2.2.1])
  have hn := curvature_negative_upper (Real.sqrt_nonneg qCap) hc.1 hq
    (show -x∈Icc (-frameCap) 0 from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  have ht := mul_lt_mul_of_pos_left (transport_trig hx).1 hq
  linarith [hb.2.2.1]

theorem positive_curvature (i : Fin 4) {x : ℝ} (hx : x∈Icc 0 span) :
    curvature R (p i) (q i) x-p i*PositiveAngularEnvelope.phi x< -(1/10)*p i := by
  have hc := coefficients i
  have hxf : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans (by norm_num [span,frameCap])⟩
  have hb := curvature_constant_bounds (Real.sqrt_nonneg qCap) radius_sq.le
    hc.1 hc.2.1 (by linarith [hc.2.2.1])
  have hp := curvature_positive_upper (Real.sqrt_nonneg qCap)
    hc.1 hc.2.1 (by linarith [hc.2.2.1]) hxf
  have hs := mul_le_mul_of_nonneg_right hb.2.1.le hx.1
  have hphi := mul_lt_mul_of_pos_left
    (PositiveANegativeTD.Fixed.phi_short_reserve hx) hc.1
  linarith [hb.1]

private theorem concave_congr_on {A B : ℝ} {f h : ℝ→ℝ}
    (hf : ConcaveOn ℝ (Icc A B) f) (he : ∀x∈Icc A B,f x=h x) :
    ConcaveOn ℝ (Icc A B) h := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r s hr hs hrs
  have hh := hf.2 hx hy hr hs hrs
  rw [he x hx,he y hy,he _ (hf.1 hx hy hr hs hrs)] at hh
  exact hh

/-- All A intervals used below start at L or u, below the true support
transition. Their upper endpoint may lie on either support branch. -/
theorem charge_add_concave {A B : ℝ} {f fd fdd : ℝ→ℝ}
    (hA : A∈Icc L u) (_hAB : A≤B) (hB : B≤frameCap)
    (hd : ∀a∈Icc A B,HasDerivAt f (fd a) a)
    (hdd : ∀a∈Icc A B,HasDerivAt fd (fdd a) a)
    (hcurv : ∀a∈Icc A B,fdd a≤-l/50) :
    ConcaveOn ℝ (Icc A B) (fun a => l*charge a+f a) := by
  have hA0 : 0≤A := by have h := hA.1; simp only [L] at h; linarith
  have hAα : A≤TwoPositive.ASupport.alpha := by
    have h := hA.2; simp only [u] at h; linarith [TwoPositive.ASupport.alpha_bounds.1]
  have hl : (0:ℝ)≤l := by norm_num [l]
  have haxis {b : ℝ} (hb : b≤B) (hbα : b≤TwoPositive.ASupport.alpha) :
      ConcaveOn ℝ (Icc A b) (fun a => l*axialCharge a+f a) := by
    apply concave_of_deriv2
      (fun a ha => ((axial_derivative a).const_mul l).add (hd a ⟨ha.1,ha.2.trans hb⟩))
      (fun a ha => ((axial_second a).const_mul l).add (hdd a ⟨ha.1,ha.2.trans hb⟩))
    intro a ha
    have hj := PositiveANegativeTD.ABounds.axial_second_upper ⟨hA0.trans ha.1,ha.2.trans hbα⟩
    have hf := hcurv a ⟨ha.1,ha.2.trans hb⟩
    have hm := mul_le_mul_of_nonneg_left hj.le hl
    simp only [l] at hm hf ⊢
    linarith
  by_cases hBα : B≤TwoPositive.ASupport.alpha
  · apply concave_congr_on (haxis le_rfl hBα)
    intro a ha
    rw [TwoPositive.ASupport.charge,ite_eq_left (ha.2.trans hBα)]
  · have hαB : TwoPositive.ASupport.alpha≤B := (lt_of_not_ge hBα).le
    have hcircle : ConcaveOn ℝ (Icc TwoPositive.ASupport.alpha B) (fun a => l*circleCharge a+f a) := by
      apply concave_of_deriv2
        (fun a ha => ((circle_derivative a).const_mul l).add (hd a ⟨hAα.trans ha.1,ha.2⟩))
        (fun a ha => ((circle_second a).const_mul l).add (hdd a ⟨hAα.trans ha.1,ha.2⟩))
      intro a ha
      have hj := circle_curvature ⟨by linarith [TwoPositive.ASupport.alpha_bounds.1,ha.1],ha.2.trans hB⟩
      have hf := hcurv a ⟨hAα.trans ha.1,ha.2⟩
      have hm := mul_le_mul_of_nonneg_left hj hl
      simp only [l] at hm hf ⊢
      linarith
    have he : l*axialCharge TwoPositive.ASupport.alpha+f TwoPositive.ASupport.alpha=l*circleCharge TwoPositive.ASupport.alpha+f TwoPositive.ASupport.alpha := by
      rw [transition_value]
    have hdl := ((axial_derivative TwoPositive.ASupport.alpha).const_mul l).add (hd TwoPositive.ASupport.alpha ⟨hAα,hαB⟩)
    have hdr := ((circle_derivative TwoPositive.ASupport.alpha).const_mul l).add (hd TwoPositive.ASupport.alpha ⟨hAα,hαB⟩)
    rw [← transition_derivative] at hdr
    have hj := SplitConcavityTools.join ⟨hAα,hαB⟩ (haxis hαB le_rfl) hcircle he hdl hdr
    convert hj using 1
    funext a
    by_cases ha : a≤TwoPositive.ASupport.alpha <;> simp [TwoPositive.ASupport.charge,ha]

theorem shifted_negative_concave (i : Fin 4) {A B b : ℝ}
    (hA : A∈Icc L u) (hAB : A≤B) (hB : B≤frameCap)
    (harg : ∀a∈Icc A B,a-b∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc A B) (fun a => l*charge a+V R (p i) (q i) (a-b)) := by
  have hc := coefficients i
  have hq := hc.1.trans_le hc.2.1
  apply charge_add_concave hA hAB hB
    (fd:=fun a => Vd R (p i) (q i) (a-b))
    (fdd:=fun a => curvature R (p i) (q i) (-(a-b))-q i*Real.cos (a-b))
  · intro a ha
    exact ((V_hasDerivAt (R:=R) hc.1 hq (harg a ha)).comp a
      ((hasDerivAt_id' a).sub_const b)).congr_deriv (by ring)
  · intro a ha
    exact ((Vd_hasDerivAt (R:=R) hc.1 hq (harg a ha)).comp a
      ((hasDerivAt_id' a).sub_const b)).congr_deriv (by ring)
  · intro a ha
    have hh := negative_curvature i (harg a ha)
    have hql := hc.2.2.2.2.1
    simp only [l] at hql ⊢
    linarith

theorem shifted_positive_concave (i : Fin 4) {B b : ℝ}
    (hLB : L≤B) (hB : B≤frameCap)
    (harg : ∀a∈Icc L B,b-a∈Icc 0 span) :
    ConcaveOn ℝ (Icc L B) (fun a => l*charge a+U R (p i) (q i) (b-a)) := by
  have hc := coefficients i
  have hq := hc.1.trans_le hc.2.1
  have hargf {a : ℝ} (ha : a∈Icc L B) : b-a∈Icc 0 frameCap :=
    ⟨(harg a ha).1,(harg a ha).2.trans (by norm_num [span,frameCap])⟩
  apply charge_add_concave (by norm_num [L,u]) hLB hB
    (fd:=fun a => -Ud (p i) (q i) (b-a))
    (fdd:=fun a => curvature R (p i) (q i) (b-a)-p i*PositiveAngularEnvelope.phi (b-a))
  · intro a ha
    exact ((U_hasDerivAt hc.1 hq (hargf ha)).comp a
      ((hasDerivAt_const a b).sub (hasDerivAt_id' a))).congr_deriv (by ring)
  · intro a ha
    exact ((Ud_hasDerivAt hc.1 hq (hargf ha)).comp a
      ((hasDerivAt_const a b).sub (hasDerivAt_id' a))).neg.congr_deriv (by ring)
  · intro a ha
    have hh := positive_curvature i (harg a ha)
    have hpk := hc.2.2.2.1
    have hl : l=457/500 := rfl
    have hk : k=717/1000 := rfl
    rw [hl]
    rw [hk] at hpk
    linarith

theorem linear_middle_monotone : MonotoneOn (fun a => l*charge a+M*a) (Icc L frameCap) := by
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by have h := ha.1; simp only [L] at h; linarith,ha.2⟩
  have hfD (a : ℝ) : HasDerivAt (fun a => l*axialCharge a+M*a) (l*axialD a+M) a :=
    (((axial_derivative a).const_mul l).add ((hasDerivAt_id' a).const_mul M)).congr_deriv
      (by ring)
  have hhD (a : ℝ) : HasDerivAt (fun a => l*circleCharge a+M*a) (l*circleD a+M) a :=
    (((circle_derivative a).const_mul l).add ((hasDerivAt_id' a).const_mul M)).congr_deriv
      (by ring)
  have hf : MonotoneOn (fun a => l*axialCharge a+M*a) (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hfD a).continuousAt.continuousWithinAt) (fun a _ => hfD a)
    intro a ha
    have hd := axial_derivative_lower (hmem (Ioo_subset_Icc_self ha))
    simp only [l,M]
    linarith
  have hh : MonotoneOn (fun a => l*circleCharge a+M*a) (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hhD a).continuousAt.continuousWithinAt) (fun a _ => hhD a)
    intro a ha
    have hd := circle_derivative_lower (hmem (Ioo_subset_Icc_self ha))
    simp only [l,M]
    linarith
  have hj := monotone_continuous_switch (e:=fun a => a-TwoPositive.ASupport.alpha) (by fun_prop) hf hh
    (fun a _ he => by
      have ha : a=TwoPositive.ASupport.alpha := by linarith
      subst ha
      rw [transition_value])
  convert hj using 1
  funext a
  by_cases ha : a≤TwoPositive.ASupport.alpha <;> simp [TwoPositive.ASupport.charge,ha]

theorem D_remainder_antitone (b : ℝ) :
    AntitoneOn (fun a => l*charge a-aD*(b-a)) (Icc L frameCap) := by
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by have h := ha.1; simp only [L] at h; linarith,ha.2⟩
  have hfD (a : ℝ) : HasDerivAt (fun a => -(l*axialCharge a-aD*(b-a))) (-(l*axialD a+aD)) a :=
    ((((axial_derivative a).const_mul l).sub
      (((hasDerivAt_const a b).sub (hasDerivAt_id' a)).const_mul aD)).neg).congr_deriv (by ring)
  have hhD (a : ℝ) : HasDerivAt (fun a => -(l*circleCharge a-aD*(b-a))) (-(l*circleD a+aD)) a :=
    ((((circle_derivative a).const_mul l).sub
      (((hasDerivAt_const a b).sub (hasDerivAt_id' a)).const_mul aD)).neg).congr_deriv (by ring)
  have hf : MonotoneOn (fun a => -(l*axialCharge a-aD*(b-a))) (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hfD a).continuousAt.continuousWithinAt) (fun a _ => hfD a)
    intro a ha
    have hd := (PositiveANegativeTD.ABounds.axial_derivative_bounds
      (hmem (Ioo_subset_Icc_self ha))).2
    have hdg := GlobalGA.Secondary.diagonal_bounds.2
    simp only [l,aD]
    linarith
  have hh : MonotoneOn (fun a => -(l*circleCharge a-aD*(b-a))) (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hhD a).continuousAt.continuousWithinAt) (fun a _ => hhD a)
    intro a ha
    have hd := (PositiveANegativeTD.ABounds.circle_derivative_bounds
      (hmem (Ioo_subset_Icc_self ha))).2
    have hdg := GlobalGA.Secondary.diagonal_bounds.2
    simp only [l,aD]
    linarith
  have hj := monotone_continuous_switch (e:=fun a => a-TwoPositive.ASupport.alpha) (by fun_prop) hf hh
    (fun a _ he => by
      have ha : a=TwoPositive.ASupport.alpha := by linarith
      subst ha
      rw [transition_value])
  have he (a : ℝ) : (if a-TwoPositive.ASupport.alpha≤0 then -(l*axialCharge a-aD*(b-a))
      else -(l*circleCharge a-aD*(b-a)))= -(l*TwoPositive.ASupport.charge a-aD*(b-a)) := by
    by_cases ha : a≤TwoPositive.ASupport.alpha <;> simp [TwoPositive.ASupport.charge,ha]
  intro a ha x hx hax
  have h := hj ha hx hax
  simp only [he] at h
  linarith

theorem short_middle_concave : ConcaveOn ℝ (Icc L u) (fun a => l*charge a+g a) := by
  apply charge_add_concave (by norm_num [L,u]) (by norm_num [L,u])
    (by norm_num [u,frameCap]) (fun a _ => g_hasDerivAt a) (fun a _ => gD_hasDerivAt a)
  intro a ha
  have ha0 : 0≤a := by dsimp [L] at ha; linarith [ha.1]
  have hs := (transport_trig (show a∈Icc 0 frameCap from
    ⟨ha0,ha.2.trans (by norm_num [u,frameCap])⟩)).2.2.1
  have hc := Real.one_sub_sq_div_two_le_cos (x:=a)
  have ha2 : a^2≤(1/4:ℝ)^2 := pow_le_pow_left₀ ha0 ha.2 2
  dsimp [gDD,K,beta,l]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
end
end
end

section
/-!
## Scalar positivity for nonnegative A and a combined negative gain

Both gains `M w` and `J_M(w)` are proved positive separately (`sum_scalar_positive_linear`,
`sum_scalar_positive_joint`). The cut at `w = 1/4` is kept in every concavity argument. The final
theorem `sum_scalar_positive` takes the two sign budgets and a lower bound of the combined gain;
all coefficient, derivative and endpoint facts are proved here.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity TwoPositive.ASupport

theorem jointGain_of_ge {w : ℝ} (hw : u≤w) : jointGain w=g u+M*(w-u) := by
  unfold jointGain
  by_cases he : w≤u
  · have hwu : w=u := le_antisymm he hw
    rw [ite_eq_left he,hwu,sub_self,mul_zero,add_zero]
  · rw [ite_eq_right he]

private theorem const_add_concave {A B : ℝ} {f : ℝ→ℝ}
    (hf : ConcaveOn ℝ (Icc A B) f) (b : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun x => b+f x) := by
  have h := (affine_concave 0 b A B).add hf
  convert h using 1
  funext x
  simp only [Pi.add_apply,zero_mul,zero_add]

theorem zero_negative_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+V R (p i) (q i) a := by
  have hc := shifted_negative_concave i (A:=L) (B:=frameCap) (b:=0)
    (by norm_num [L,u]) (by norm_num [L,frameCap]) le_rfl
    (fun a ha => ⟨by dsimp [L] at ha; linarith [ha.1],by simpa using ha.2⟩)
  have he := negative_endpoint_reserves i
  have hleft : 0<base+l*charge L+V R (p i) (q i) L :=
    (by fin_cases i <;> norm_num [leftReserve] : 0<leftReserve i).trans he.1
  have hright : 0<base+l*charge frameCap+V R (p i) (q i) frameCap :=
    (by fin_cases i <;> norm_num [capReserve] : 0<capReserve i).trans he.2.1
  simpa only [sub_zero,add_assoc] using concave_gt_of_endpoints (const_add_concave hc base) ha
    (by simpa only [sub_zero,add_assoc] using hleft)
    (by simpa only [sub_zero,add_assoc] using hright)

theorem linear_middle_positive {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+M*a := by
  have hm : l*TwoPositive.ASupport.charge L+M*L≤l*TwoPositive.ASupport.charge a+M*a :=
    linear_middle_monotone (by norm_num [L,frameCap]) ha ha.1
  have h := zero_increment_reserves.2.2.2.1
  simp only [l,M] at hm h ⊢
  linarith

theorem joint_middle_positive {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+jointGain a := by
  by_cases hau : a≤u
  · have hc := const_add_concave short_middle_concave base
    have h1 := zero_increment_reserves.1
    have h2 := zero_increment_reserves.2.1
    have hl : 0<base+(l*TwoPositive.ASupport.charge L+g L) := by simp only [l] at h1 ⊢; linarith
    have hu : 0<base+(l*TwoPositive.ASupport.charge u+g u) := by simp only [l] at h2 ⊢; linarith
    have hh := concave_gt_of_endpoints (c:=0) hc ⟨ha.1,hau⟩ hl hu
    rw [jointGain,ite_eq_left hau]
    simp only [l] at hh ⊢
    linarith
  · have hua : u≤a := (lt_of_not_ge hau).le
    have hm : l*TwoPositive.ASupport.charge u+M*u≤l*TwoPositive.ASupport.charge a+M*a :=
      linear_middle_monotone (by norm_num [L,u,frameCap]) ha hua
    rw [jointGain_of_ge hua]
    have h2 := zero_increment_reserves.2.1
    simp only [l,M] at hm h2 ⊢
    linarith

theorem cut_negative_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc u frameCap) :
    0<base+l*charge a+g u+V R (p i) (q i) (a-u) := by
  have hc := shifted_negative_concave i (A:=u) (B:=frameCap) (b:=u)
    (by norm_num [L,u]) (by norm_num [u,frameCap]) le_rfl
    (fun a ha => ⟨by linarith [ha.1],by
      have h := ha.2; simp only [u,frameCap] at h ⊢; linarith⟩)
  have hleft : 0<base+g u+(l*TwoPositive.ASupport.charge u+V R (p i) (q i) (u-u)) := by
    simp only [sub_self,V_zero,add_zero]
    have h := zero_increment_reserves.2.1
    simp only [l] at h ⊢
    linarith
  have hright : 0<base+g u+(l*TwoPositive.ASupport.charge frameCap+V R (p i) (q i) (frameCap-u)) := by
    have hh := (negative_endpoint_reserves i).2.2
    have hp : 0<cutNegativeReserve i := by fin_cases i <;> norm_num [cutNegativeReserve]
    simp only [l] at hh ⊢
    linarith
  have hh := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+g u)) ha hleft hright
  simp only [l] at hh ⊢
  linarith

theorem cut_positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L u) :
    0<base+l*charge a+g u+positive i (u-a) := by
  by_cases hi : i=3
  · subst hi
    have hm : l*TwoPositive.ASupport.charge u-aD*(u-u)≤l*TwoPositive.ASupport.charge a-aD*(u-a) := D_remainder_antitone u
      ⟨ha.1,ha.2.trans (by norm_num [u,frameCap])⟩ (by norm_num [L,u,frameCap]) ha.2
    simp only [sub_self,mul_zero,sub_zero] at hm
    simp only [positive,PositiveTD.Hybrid.positive,ite_true]
    have h := zero_increment_reserves.2.1
    simp only [l] at hm h ⊢
    linarith
  · have hc := shifted_positive_concave i (B:=u) (b:=u)
      (by norm_num [L,u]) (by norm_num [u,frameCap])
      (fun a ha => ⟨by linarith [ha.2],by
        have h := ha.1; simp only [L,u,span] at h ⊢; linarith⟩)
    have hleft : 0<base+g u+(l*TwoPositive.ASupport.charge L+U R (p i) (q i) (u-L)) := by
      have hh := (positive_endpoint_reserves i).1
      have hp : 0<cutPositiveReserve i := by fin_cases i <;> norm_num [cutPositiveReserve]
      simp only [l] at hh ⊢
      linarith
    have hright : 0<base+g u+(l*TwoPositive.ASupport.charge u+U R (p i) (q i) (u-u)) := by
      simp only [sub_self,U_zero,add_zero]
      have h := zero_increment_reserves.2.1
      simp only [l] at h ⊢
      linarith
    have hh := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+g u)) ha hleft hright
    simp only [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    simp only [l] at hh ⊢
    linarith

theorem cap_positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) :
    0<base+l*charge a+M*frameCap+positive i (frameCap-a) ∧
    0<base+l*charge a+jointGain frameCap+positive i (frameCap-a) := by
  have hcut : u≤frameCap := by norm_num [u,frameCap]
  rw [jointGain_of_ge hcut]
  by_cases hi : i=3
  · subst hi
    have hm : l*TwoPositive.ASupport.charge frameCap-aD*(frameCap-frameCap)≤l*TwoPositive.ASupport.charge a-aD*(frameCap-a) :=
      D_remainder_antitone frameCap ha (by norm_num [L,frameCap]) ha.2
    simp only [sub_self,mul_zero,sub_zero] at hm
    simp only [positive,PositiveTD.Hybrid.positive,ite_true]
    have h1 := zero_increment_reserves.2.2.2.2
    have h2 := zero_increment_reserves.2.2.1
    simp only [l,M] at hm h1 h2 ⊢
    constructor
    · linarith
    · linarith
  · have hc := shifted_positive_concave i (B:=frameCap) (b:=frameCap)
      (by norm_num [L,frameCap]) le_rfl
      (fun a ha => ⟨by linarith [ha.2],by
        have h := ha.1; simp only [L,span,frameCap] at h ⊢; linarith⟩)
    have he : frameCap-L=span := by norm_num [L,span,frameCap]
    have hleft₁ : 0<base+M*frameCap+(l*TwoPositive.ASupport.charge L+U R (p i) (q i) (frameCap-L)) := by
      have hh := (positive_endpoint_reserves i).2.2
      have hp : 0<linearCapReserve i := by fin_cases i <;> norm_num [linearCapReserve]
      rw [he]
      simp only [l,M] at hh ⊢
      linarith
    have hleft₂ : 0<base+g u+M*(frameCap-u)+(l*TwoPositive.ASupport.charge L+U R (p i) (q i) (frameCap-L)) := by
      have hh := (positive_endpoint_reserves i).2.1
      have hp : 0<jointCapReserve i := by fin_cases i <;> norm_num [jointCapReserve]
      rw [he]
      simp only [l,M] at hh ⊢
      linarith
    have hright₁ : 0<base+M*frameCap+(l*TwoPositive.ASupport.charge frameCap+U R (p i) (q i) (frameCap-frameCap)) := by
      simp only [sub_self,U_zero,add_zero]
      have h := zero_increment_reserves.2.2.2.2
      simp only [l,M] at h ⊢
      linarith
    have hright₂ : 0<base+g u+M*(frameCap-u)+
        (l*TwoPositive.ASupport.charge frameCap+U R (p i) (q i) (frameCap-frameCap)) := by
      simp only [sub_self,U_zero,add_zero]
      have h := zero_increment_reserves.2.2.1
      simp only [l,M] at h ⊢
      linarith
    have hh₁ := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+M*frameCap)) ha
      hleft₁ hright₁
    have hh₂ := concave_gt_of_endpoints (c:=0) (const_add_concave hc (base+g u+M*(frameCap-u))) ha
      hleft₂ hright₂
    simp only [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    simp only [l,M] at hh₁ hh₂ ⊢
    exact ⟨by linarith,by linarith⟩

private theorem negative_gain_concave (i : Fin 4) {a A B : ℝ} {C : ℝ→ℝ}
    (hC : ConcaveOn ℝ (Icc A B) C)
    (harg : ∀w∈Icc A B,a-w∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc A B) (fun w => base+l*charge a+C w+V R (p i) (q i) (a-w)) := by
  have hc := coefficients i
  have hV := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:= -1) (b:=a) (l:=A) (u:=B)
    (fun w hw => by rw [show -1*w+a=a-w by ring]; exact harg w hw)
  have hV' : ConcaveOn ℝ (Icc A B) (fun w => V R (p i) (q i) (a-w)) := by
    convert hV using 1
    funext w
    rw [show -1*w+a=a-w by ring]
  convert const_add_concave (hC.add hV') (base+l*charge a) using 1
  funext w
  simp only [Pi.add_apply]
  ring

private theorem positive_gain_concave (i : Fin 4) {a A B : ℝ} {C : ℝ→ℝ}
    (hC : ConcaveOn ℝ (Icc A B) C)
    (harg : ∀w∈Icc A B,w-a∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc A B) (fun w => base+l*charge a+C w+positive i (w-a)) := by
  have hc := coefficients i
  have hU := concave_affine_argument
    (PositiveTD.Hybrid.positive_concave (R:=R) (a:=aD) (p:=p) (q:=q) (d:=3) (i:=i)
      (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=1) (b:= -a) (l:=A) (u:=B) (fun w hw => by convert harg w hw using 1; ring)
  have hU' : ConcaveOn ℝ (Icc A B) (fun w => positive i (w-a)) := by
    convert hU using 1
    funext w
    dsimp [positive]
    congr 1
    ring
  convert const_add_concave (hC.add hU') (base+l*charge a) using 1
  funext w
  dsimp [positive]
  ring

private theorem linear_gain_concave (A B : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun w => M*w) := by
  have h := affine_concave M 0 A B
  simp only [add_zero] at h
  exact h

private theorem upper_gain_concave (A B : ℝ) :
    ConcaveOn ℝ (Icc A B) (fun w => g u+M*(w-u)) := by
  convert affine_concave M (g u-M*u) A B using 1
  funext w
  ring

private theorem r78_positive_zero (i : Fin 4) : positive i 0=0 := by
  simp [positive,PositiveTD.Hybrid.positive]

private theorem r78_neg_arg {a A B : ℝ} (ha : a≤frameCap) (hA : 0≤A) :
    ∀w∈Icc A B,w≤a → a-w∈Icc 0 frameCap := by
  intro w hw hwa
  refine ⟨by linarith,?_⟩
  have h := hw.1
  simp only [frameCap] at ha ⊢
  linarith

private theorem r78_pos_arg {a A B : ℝ} (ha : 0≤a) (hB : B≤frameCap) :
    ∀w∈Icc A B,a≤w → w-a∈Icc 0 frameCap := by
  intro w hw haw
  refine ⟨by linarith,?_⟩
  have h := hw.2
  simp only [frameCap] at hB ⊢
  linarith

theorem linear_negative_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 a) :
    0<base+l*charge a+M*w+V R (p i) (q i) (a-w) := by
  have hc := negative_gain_concave i (a:=a) (linear_gain_concave 0 a)
    (fun w hw => r78_neg_arg ha.2 le_rfl w hw hw.2)
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+M*0+V R (p i) (q i) (a-0) := by
    rw [mul_zero,add_zero,sub_zero]; exact zero_negative_positive i ha
  have h1 : 0<base+l*TwoPositive.ASupport.charge a+M*a+V R (p i) (q i) (a-a) := by
    rw [sub_self,V_zero,add_zero]; exact linear_middle_positive ha
  have hh := concave_gt_of_endpoints hc hw h0 h1
  exact hh

theorem linear_positive_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc a frameCap) :
    0<base+l*charge a+M*w+positive i (w-a) := by
  have ha0 : 0≤a := by have h := ha.1; simp only [L] at h; linarith
  have hc := positive_gain_concave i (a:=a) (linear_gain_concave a frameCap)
    (fun w hw => r78_pos_arg ha0 le_rfl w hw hw.1)
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+M*a+positive i (a-a) := by
    rw [sub_self,r78_positive_zero,add_zero]; exact linear_middle_positive ha
  have hh := concave_gt_of_endpoints hc hw h0 (cap_positive_positive i ha).1
  exact hh

theorem joint_negative_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 a) :
    0<base+l*charge a+jointGain w+V R (p i) (q i) (a-w) := by
  have ha0 : 0≤a := by have h := ha.1; simp only [L] at h; linarith
  have h0 : 0<base+l*TwoPositive.ASupport.charge a+g 0+V R (p i) (q i) (a-0) := by
    rw [g_zero,add_zero,sub_zero]; exact zero_negative_positive i ha
  by_cases hau : a≤u
  · have hC := g_concave.subset (Icc_subset_Icc le_rfl ha.2) (convex_Icc 0 a)
    have hc := negative_gain_concave i (a:=a) hC (fun w hw => r78_neg_arg ha.2 le_rfl w hw hw.2)
    have h1 : 0<base+l*TwoPositive.ASupport.charge a+g a+V R (p i) (q i) (a-a) := by
      have h := joint_middle_positive ha
      rw [jointGain,ite_eq_left hau] at h
      rw [sub_self,V_zero,add_zero]; exact h
    have hh := concave_gt_of_endpoints hc hw h0 h1
    rw [jointGain,ite_eq_left (hw.2.trans hau)]
    exact hh
  · have hua : u≤a := (lt_of_not_ge hau).le
    by_cases hwu : w≤u
    · have hC := g_concave.subset (Icc_subset_Icc le_rfl (by norm_num [u,frameCap]))
        (convex_Icc 0 u)
      have hc := negative_gain_concave i (a:=a) hC
        (fun w hw => r78_neg_arg ha.2 le_rfl w hw (hw.2.trans hua))
      have hh := concave_gt_of_endpoints hc ⟨hw.1,hwu⟩ h0 (cut_negative_positive i ⟨hua,ha.2⟩)
      rw [jointGain,ite_eq_left hwu]
      exact hh
    · have huw : u≤w := (lt_of_not_ge hwu).le
      have hc := negative_gain_concave i (a:=a) (upper_gain_concave u a)
        (fun w hw => r78_neg_arg ha.2 (by norm_num [u]) w hw hw.2)
      have h1 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(u-u))+V R (p i) (q i) (a-u) := by
        rw [sub_self,mul_zero,add_zero]; exact cut_negative_positive i ⟨hua,ha.2⟩
      have h2 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(a-u))+V R (p i) (q i) (a-a) := by
        have h := joint_middle_positive ha
        rw [jointGain_of_ge hua] at h
        rw [sub_self,V_zero,add_zero]; exact h
      have hh := concave_gt_of_endpoints hc ⟨huw,hw.2⟩ h1 h2
      rw [jointGain_of_ge huw]
      exact hh

theorem joint_positive_positive (i : Fin 4) {a w : ℝ}
    (ha : a∈Icc L frameCap) (hw : w∈Icc a frameCap) :
    0<base+l*charge a+jointGain w+positive i (w-a) := by
  have ha0 : 0≤a := by have h := ha.1; simp only [L] at h; linarith
  have hcap : u≤frameCap := by norm_num [u,frameCap]
  by_cases hua : u≤a
  · have hc := positive_gain_concave i (a:=a) (upper_gain_concave a frameCap)
      (fun w hw => r78_pos_arg ha0 le_rfl w hw hw.1)
    have h1 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(a-u))+positive i (a-a) := by
      have h := joint_middle_positive ha
      rw [jointGain_of_ge hua] at h
      rw [sub_self,r78_positive_zero,add_zero]; exact h
    have h2 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(frameCap-u))+positive i (frameCap-a) := by
      have h := (cap_positive_positive i ha).2
      rw [jointGain_of_ge hcap] at h
      exact h
    have hh := concave_gt_of_endpoints hc hw h1 h2
    rw [jointGain_of_ge (hua.trans hw.1)]
    exact hh
  · have hau : a≤u := (lt_of_not_ge hua).le
    by_cases hwu : w≤u
    · have hC := g_concave.subset (Icc_subset_Icc ha0 hcap) (convex_Icc a u)
      have hc := positive_gain_concave i (a:=a) hC
        (fun w hw => r78_pos_arg ha0 hcap w hw hw.1)
      have h1 : 0<base+l*TwoPositive.ASupport.charge a+g a+positive i (a-a) := by
        have h := joint_middle_positive ha
        rw [jointGain,ite_eq_left hau] at h
        rw [sub_self,r78_positive_zero,add_zero]; exact h
      have hh := concave_gt_of_endpoints hc ⟨hw.1,hwu⟩ h1 (cut_positive_positive i ⟨ha.1,hau⟩)
      rw [jointGain,ite_eq_left hwu]
      exact hh
    · have huw : u≤w := (lt_of_not_ge hwu).le
      have hc := positive_gain_concave i (a:=a) (upper_gain_concave u frameCap)
        (fun w hw => r78_pos_arg ha0 le_rfl w hw (hau.trans hw.1))
      have h1 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(u-u))+positive i (u-a) := by
        rw [sub_self,mul_zero,add_zero]; exact cut_positive_positive i ⟨ha.1,hau⟩
      have h2 : 0<base+l*TwoPositive.ASupport.charge a+(g u+M*(frameCap-u))+positive i (frameCap-a) := by
        have h := (cap_positive_positive i ha).2
        rw [jointGain_of_ge hcap] at h
        exact h
      have hh := concave_gt_of_endpoints hc ⟨huw,hw.2⟩ h1 h2
      rw [jointGain_of_ge huw]
      exact hh

theorem sum_scalar_positive_linear {a w : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w) :
    0<base+l*charge a+M*w+∑i,block i (P i) (N i) := by
  obtain ⟨i,hi⟩ := sum_pure_lower P N ha hw hP hN hPt hNt hbalance
  by_cases hwa : w≤a
  · rw [ite_eq_left hwa] at hi
    have hp := linear_negative_positive i ha ⟨hw.1,hwa⟩
    linarith
  · rw [ite_eq_right hwa] at hi
    have hp := linear_positive_positive i ha ⟨(lt_of_not_ge hwa).le,hw.2⟩
    linarith

theorem sum_scalar_positive_joint {a w : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w) :
    0<base+l*charge a+jointGain w+∑i,block i (P i) (N i) := by
  obtain ⟨i,hi⟩ := sum_pure_lower P N ha hw hP hN hPt hNt hbalance
  by_cases hwa : w≤a
  · rw [ite_eq_left hwa] at hi
    have hp := joint_negative_positive i ha ⟨hw.1,hwa⟩
    linarith
  · rw [ite_eq_right hwa] at hi
    have hp := joint_positive_positive i ha ⟨(lt_of_not_ge hwa).le,hw.2⟩
    linarith

/-- The scalar statement used on the cycle. The combined gain may come from DE, EH and TD, or from
a T-pair reduction. No coefficient or endpoint fact is a hypothesis. -/
theorem sum_scalar_positive {a w gain : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w)
    (hgain : min (M*w) (jointGain w)≤gain) :
    0<base+l*charge a+gain+∑i,block i (P i) (N i) := by
  have hlinear := sum_scalar_positive_linear P N ha hw hP hN hPt hNt hbalance
  have hjoint := sum_scalar_positive_joint P N ha hw hP hN hPt hNt hbalance
  rcases le_total (M*w) (jointGain w) with h|h
  · rw [min_eq_left h] at hgain
    linarith
  · rw [min_eq_right h] at hgain
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE

theorem de_gain_lower {Q : ℝ} {C : SignedCycle} (de : Bool)
    (hs : (C.point D).Sorted) (hc : (C.point D).Contained Q)
    (hq : Q≤qCap) (hy : (C.point D).y≤0)
    (hsmall : |delta C.theta D|≤frameCap) (hde : de=true→delta C.theta D≤0) :
    M*magnitude C D de≤deGain C de := by
  cases hd : de
  · simp [magnitude,NegativeELowA.magnitude,selected,deGain]
  · have hn : -delta C.theta D∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (hde hd),(neg_le_abs _).trans hsmall⟩
    have hcos := NegativeESecant.cos_pos hn
    have hh := actual_correction_lower (D:=(C.point D).reflect)
      (by simpa using hs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hy)
      (by simpa using hc) hq hn
    have hwidth := edgeWidth_negative_formula hn
    simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hwidth
    have he : deGain C true=(secant (-delta C.theta D)-1)/2+K*Real.tan (-delta C.theta D)-
        (secant (-delta C.theta D)*(C.point D).a+c*(-(C.point D).y)-clippedSupport 1 c) := by
      dsimp [deGain,secant,K]
      simp only [Real.cos_neg,Real.sin_neg,Real.tan_eq_sin_div_cos]
      rw [hwidth]
      simp only [Real.cos_neg] at hcos
      field_simp [hcos.ne']
      ring
    simpa [magnitude,NegativeELowA.magnitude,selected,he,SignedPoint.reflect] using hh

theorem eh_gain_lower {C : SignedCycle} (eh : Bool)
    (hflat : (C.point E).a=7/12)
    (heh : eh=true→-delta C.theta E∈Icc 0 u ∧ -(C.point E).y≤39/250) :
    g (magnitude C E eh)≤ehGain C eh := by
  cases he : eh
  · simp [magnitude,NegativeELowA.magnitude,selected,ehGain]
  · obtain ⟨hs,hEy⟩ := heh he
    have hsf : -delta C.theta E∈Icc 0 frameCap :=
      ⟨hs.1,hs.2.trans (by norm_num [u,frameCap])⟩
    have hwidth := edgeWidth_negative_formula hsf
    simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hwidth
    have hcos : 0≤1-Real.cos (delta C.theta E) := sub_nonneg.mpr (Real.cos_le_one _)
    have hres := mul_le_mul_of_nonneg_right
      (show 1/2-(C.point E).y≤beta by dsimp [beta]; linarith) hcos
    dsimp [magnitude,NegativeELowA.magnitude,selected,ehGain,g,K,beta]
    simp only [Real.cos_neg,Real.sin_neg,hflat,hwidth]
    dsimp [beta] at hres
    nlinarith

theorem t_gain_lower {Q : ℝ} {C : SignedCycle}
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcore : (C.point T).AvoidsCore) (hq : Q≤qCap) (hDy : (C.point D).y≤0)
    (hsmall : |delta C.theta T|≤frameCap) (ht : delta C.theta T≤0) :
    M*(-delta C.theta T)≤tGain C := by
  have hz : -delta C.theta T∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr ht,(neg_le_abs _).trans hsmall⟩
  have hg := PositiveANegativeTD.actual_gain_lower (hs T) hcore (hc T)
    (hs D) hDy (hc D) hq (show 0≤c by norm_num [c]) hz
  have hw := edgeWidth_negative_formula hz
  simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hw
  have he : tGain C=PositiveANegativeTD.gain c (-delta C.theta T)
      (C.point T).a (-(C.point D).y) := by
    dsimp [tGain,PositiveANegativeTD.gain]
    simp only [Real.cos_neg,Real.sin_neg]
    rw [hw]
    ring
  rw [he]
  dsimp [M,c] at *
  nlinarith [hz.1]

theorem negative_magnitudes {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta T≤0) (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u) :
    0≤ magnitude C D de ∧ magnitude C E eh∈Icc 0 u ∧ 0≤-delta C.theta T := by
  have hD : 0≤ magnitude C D de := by
    cases hd : de
    · simp [magnitude,NegativeELowA.magnitude,selected]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using neg_nonneg.mpr (hde hd)
  have hE : magnitude C E eh∈Icc 0 u := by
    cases he : eh
    · norm_num [magnitude,NegativeELowA.magnitude,selected,u]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using heh he
  exact ⟨hD,hE,neg_nonneg.mpr ht⟩

/-- Simultaneous negative E primaries are allowed. All scalar quantities come from the weak
separating inequalities of the cycle. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc L frameCap) (ht : delta C.theta T≤0)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u ∧ -(C.point E).y≤39/250) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have ha0 : 0≤aTotal C ga ab := by dsimp [L] at ha; linarith [ha.1]
  have hEsgn : eh=true→delta C.theta E≤0 := fun he => by linarith [(heh he).1.1]
  have hb := budgets hg ga ab de eh hvar ha0 ht hde hEsgn
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hweights (i : Vertex) : 0≤weights C de i := by
    cases de <;> fin_cases i <;> simp [weights,k,l,c]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hupper : stress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have h := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at h
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hblocks := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha0 ht hde hEsgn i)
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hb.1
  have hAmul := mul_le_mul_of_nonneg_left hA (show 0≤l by norm_num [l])
  have hDEgain := de_gain_lower de (hs D) (hc D) hq hDy (hsmall D) hde
  have hEHgain := eh_gain_lower eh hflat heh
  have hTgain := t_gain_lower hs hc hcoreT hq hDy (hsmall T) ht
  have hmags := negative_magnitudes de eh ht hde (fun he => (heh he).1)
  have hcombined := combined_gain_lower (s:=magnitude C E eh)
    (r:=magnitude C D de-delta C.theta T) hmags.2.1 (by linarith [hmags.1,hmags.2.2])
    (by dsimp [negativeTotal] at hb; linarith [hb.2.1.2])
  have hsumangle : magnitude C E eh+(magnitude C D de-delta C.theta T)=negativeTotal C de eh := by
    dsimp [negativeTotal]
    ring
  rw [hsumangle] at hcombined
  have hgain : min (M*negativeTotal C de eh) (jointGain (negativeTotal C de eh))≤
      deGain C de+ehGain C eh+tGain C := by linarith
  have hscalar := sum_scalar_positive
    (fun i => (blocks C hg ga ab de eh i).P) (fun i => (blocks C hg ga ab de eh i).N)
    ha hb.2.1 (fun i => (blocks C hg ga ab de eh i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh i).N_nonneg)
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hgain
  rw [decomposition C hg ga ab de eh hflat (hcos T).ne' (hcos D).ne'] at hupper
  change l*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAmul
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA.Source
end
end
end
