module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDFixedData

/-!
# The three intrinsic s-endpoint families are positive

Uncompiled transcription of Sections 6--7 of the positive-A/negative-TD2
hand proof. The actual A support is joined at its common value and first
derivative. Curvature gives the pure-negative and ordinary positive
endpoint minima; the two remaining expressions are monotone.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.Fixed
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeSlope
open TwoPositive.ASupport

abbrev aD : ℝ := GlobalGA.Secondary.diagonal-1/2

def positive (i : Fin 4) (b : ℝ) : ℝ := PositiveTD.Hybrid.positive R aD p q 3 i b
def pureScalar (i : Fin 4) (a : ℝ) : ℝ := base+l*charge a+V R (p i) (q i) a
def middleScalar (a : ℝ) : ℝ := base+l*charge a+speed*a
def positiveScalar (i : Fin 4) (a : ℝ) : ℝ := base+l*charge a+speed*frameCap+positive i (frameCap-a)

theorem negative_curvature (i : Fin 4) {a : ℝ} (ha : a∈Icc 0 frameCap) :
    curvature R (p i) (q i) (-a)-q i*Real.cos a< -(81/1250)*q i := by
  have hc := coefficients i
  have hq0 := hc.1.trans_le hc.2.1
  have hbound := curvature_constant_bounds (Real.sqrt_nonneg qCap) radius_sq.le
    hc.1 hc.2.1 (by linarith [hc.2.2.1])
  have hnegative := curvature_negative_upper (Real.sqrt_nonneg qCap) hc.1 hq0
    (show -a∈Icc (-frameCap) 0 from ⟨by linarith [ha.2],by linarith [ha.1]⟩)
  have hcos := mul_lt_mul_of_pos_left (transport_trig ha).1 hq0
  linarith [hbound.2.2.1]

theorem phi_short_reserve {b : ℝ} (hb : b∈Icc 0 span) :
    (431/500:ℝ)+(921/1000)*b<PositiveAngularEnvelope.phi b := by
  have hh : (431/500:ℝ)< -(921/1000)*b+1*Real.sin b+1*Real.cos b := by
    apply trig_concave_gt (by norm_num) (by norm_num) (le_refl 0)
      (by simp only [span]; linarith [Real.pi_gt_three]) hb
    · norm_num
    · have hsin := sin_lower_seven (show (0:ℝ)≤ span by norm_num [span])
      have hcos := cos_lower_six (show (0:ℝ)≤ span by norm_num [span])
      simp only [span] at hsin hcos ⊢
      norm_num at hsin hcos ⊢
      linarith
  dsimp [PositiveAngularEnvelope.phi]
  linarith

theorem positive_curvature (i : Fin 4) {b : ℝ} (hb : b∈Icc 0 span) :
    curvature R (p i) (q i) b-p i*PositiveAngularEnvelope.phi b< -(1/10)*p i := by
  have hc := coefficients i
  have hb' : b∈Icc 0 frameCap := ⟨hb.1,hb.2.trans (by norm_num [span,frameCap])⟩
  have hbound := curvature_constant_bounds (Real.sqrt_nonneg qCap) radius_sq.le
    hc.1 hc.2.1 (by linarith [hc.2.2.1])
  have hpositive := curvature_positive_upper (Real.sqrt_nonneg qCap)
    hc.1 hc.2.1 (by linarith [hc.2.2.1]) hb'
  have hslope := mul_le_mul_of_nonneg_right hbound.2.1.le hb.1
  have hphi := mul_lt_mul_of_pos_left (phi_short_reserve hb) hc.1
  linarith [hbound.1]

/-- The exact C¹ support join used in (32)--(33). The auxiliary scalar
is supplied by the ordinary V or U formula and its proved derivatives. -/
theorem charge_add_concave {g gd gdd : ℝ→ℝ}
    (hderiv : ∀a∈Icc L frameCap,HasDerivAt g (gd a) a)
    (hsecond : ∀a∈Icc L frameCap,HasDerivAt gd (gdd a) a)
    (hcurv : ∀a∈Icc L frameCap,gdd a≤-l/50) :
    ConcaveOn ℝ (Icc L frameCap) (fun a => l*charge a+g a) := by
  have halpha : TwoPositive.ASupport.alpha∈Icc L frameCap :=
    ⟨by simp only [L]; linarith [alpha_bounds.1],alpha_bounds.2.le⟩
  have hleft : ConcaveOn ℝ (Icc L TwoPositive.ASupport.alpha) (fun a => l*axialCharge a+g a) := by
    apply concave_of_deriv2
      (fun a ha => ((axial_derivative a).const_mul l).add
        (hderiv a ⟨ha.1,ha.2.trans halpha.2⟩))
      (fun a ha => ((axial_second a).const_mul l).add
        (hsecond a ⟨ha.1,ha.2.trans halpha.2⟩))
    intro a ha
    have hA := ABounds.axial_second_upper
      (show a∈Icc 0 TwoPositive.ASupport.alpha from ⟨by simp only [L] at ha; linarith [ha.1],ha.2⟩)
    have hg := hcurv a ⟨ha.1,ha.2.trans halpha.2⟩
    simp only [l] at *
    linarith
  have hright : ConcaveOn ℝ (Icc TwoPositive.ASupport.alpha frameCap) (fun a => l*circleCharge a+g a) := by
    apply concave_of_deriv2
      (fun a ha => ((circle_derivative a).const_mul l).add
        (hderiv a ⟨halpha.1.trans ha.1,ha.2⟩))
      (fun a ha => ((circle_second a).const_mul l).add
        (hsecond a ⟨halpha.1.trans ha.1,ha.2⟩))
    intro a ha
    have hA := circle_curvature
      (show a∈Icc 0 frameCap from ⟨by linarith [alpha_bounds.1,ha.1],ha.2⟩)
    have hg := hcurv a ⟨halpha.1.trans ha.1,ha.2⟩
    simp only [l] at *
    nlinarith
  have he : l*axialCharge TwoPositive.ASupport.alpha+g TwoPositive.ASupport.alpha=l*circleCharge TwoPositive.ASupport.alpha+g TwoPositive.ASupport.alpha := by
    rw [transition_value]
  have hdl := ((axial_derivative TwoPositive.ASupport.alpha).const_mul l).add (hderiv TwoPositive.ASupport.alpha halpha)
  have hdr := ((circle_derivative TwoPositive.ASupport.alpha).const_mul l).add (hderiv TwoPositive.ASupport.alpha halpha)
  rw [← transition_derivative] at hdr
  have hj := SplitConcavityTools.join halpha hleft hright he hdl hdr
  convert hj using 1
  funext a
  by_cases ha : a≤TwoPositive.ASupport.alpha <;> simp [TwoPositive.ASupport.charge,ha]

theorem pureScalar_concave (i : Fin 4) : ConcaveOn ℝ (Icc L frameCap) (pureScalar i) := by
  have hc := coefficients i
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hh := charge_add_concave
    (g:=fun a => base+V R (p i) (q i) a)
    (gd:=Vd R (p i) (q i))
    (gdd:=fun a => curvature R (p i) (q i) (-a)-q i*Real.cos a)
    (fun a ha => (V_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) (hmem ha)).const_add base)
    (fun a ha => Vd_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) (hmem ha))
    (fun a ha => by
      have hn := negative_curvature i (hmem ha)
      dsimp [l]
      linarith [hc.2.2.2.2.1])
  convert hh using 1
  funext a
  dsimp [pureScalar]
  ring

theorem ordinary_positive_concave (i : Fin 4) :
    ConcaveOn ℝ (Icc L frameCap)
      (fun a => base+l*charge a+speed*frameCap+U R (p i) (q i) (frameCap-a)) := by
  have hc := coefficients i
  have hq0 := hc.1.trans_le hc.2.1
  have hb {a : ℝ} (ha : a∈Icc L frameCap) : frameCap-a∈Icc 0 span := by
    constructor <;> simp only [L,frameCap,span] at ha ⊢ <;> linarith [ha.1,ha.2]
  have hbf {a : ℝ} (ha : a∈Icc L frameCap) : frameCap-a∈Icc 0 frameCap :=
    ⟨(hb ha).1,(hb ha).2.trans (by norm_num [span,frameCap])⟩
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfirst (a : ℝ) (ha : a∈Icc L frameCap) :
      HasDerivAt (fun a => base+speed*frameCap+U R (p i) (q i) (frameCap-a))
        (-mixedPDerivative R (p i) (q i) (frameCap-a) 0) a := by
    have hh : HasDerivAt (fun x => mixedBlock R (p i) (q i) (frameCap-x) 0)
        (mixedPDerivative R (p i) (q i) (frameCap-a) 0*(0-1)) a :=
      (mixedP_hasDerivAt (R:=R) hc.1 hq0 (hbf ha) hzero).comp a
        ((hasDerivAt_const a frameCap).sub (hasDerivAt_id a))
    have h2 := hh.const_add (base+speed*frameCap)
    simp only [mixedBlock_zero_right] at h2
    exact h2.congr_deriv (by ring)
  have hsecond (a : ℝ) (ha : a∈Icc L frameCap) :
      HasDerivAt (fun a => -mixedPDerivative R (p i) (q i) (frameCap-a) 0)
        (curvature R (p i) (q i) (frameCap-a)-p i*PositiveAngularEnvelope.phi (frameCap-a)) a := by
    have hh : HasDerivAt (fun x => mixedPDerivative R (p i) (q i) (frameCap-x) 0)
        ((curvature R (p i) (q i) (frameCap-a-0)-p i*PositiveAngularEnvelope.phi (frameCap-a))*
          (0-1)) a :=
      (mixedPDerivative_hasDerivAt (R:=R) hc.1 hq0 (hbf ha) hzero).comp a
        ((hasDerivAt_const a frameCap).sub (hasDerivAt_id a))
    simp only [sub_zero] at hh
    exact hh.neg.congr_deriv (by ring)
  have hh := charge_add_concave hfirst hsecond (fun a ha => by
    have hP := positive_curvature i (hb ha)
    simp only [l]
    linarith [hc.2.2.2.1])
  convert hh using 1
  funext a
  ring

theorem middleScalar_monotone : MonotoneOn middleScalar (Icc L frameCap) := by
  let f (a : ℝ) := base+l*axialCharge a+speed*a
  let g (a : ℝ) := base+l*circleCharge a+speed*a
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by simp only [L] at ha; linarith [ha.1],ha.2⟩
  have hfD (a : ℝ) : HasDerivAt f (l*axialD a+speed) a := by
    have h : HasDerivAt (fun a => base+l*axialCharge a+speed*a) (l*axialD a+speed*1) a :=
      (((axial_derivative a).const_mul l).const_add base).add
        ((hasDerivAt_id' a).const_mul speed)
    exact h.congr_deriv (by ring)
  have hgD (a : ℝ) : HasDerivAt g (l*circleD a+speed) a := by
    have h : HasDerivAt (fun a => base+l*circleCharge a+speed*a) (l*circleD a+speed*1) a :=
      (((circle_derivative a).const_mul l).const_add base).add
        ((hasDerivAt_id' a).const_mul speed)
    exact h.congr_deriv (by ring)
  have hf : MonotoneOn f (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro a _; exact (hfD a).continuousAt.continuousWithinAt
    · intro a _; exact hfD a
    · intro a ha
      have hh := (ABounds.axial_derivative_bounds (hmem (Ioo_subset_Icc_self ha))).1
      norm_num [l,speed,c]
      linarith
  have hg : MonotoneOn g (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro a _; exact (hgD a).continuousAt.continuousWithinAt
    · intro a _; exact hgD a
    · intro a ha
      have hh := (ABounds.circle_derivative_bounds (hmem (Ioo_subset_Icc_self ha))).1
      norm_num [l,speed,c]
      linarith
  have hj := monotone_continuous_switch (e:=fun a => a-TwoPositive.ASupport.alpha) (by fun_prop) hf hg
    (fun a _ he => by
      have ha : a=TwoPositive.ASupport.alpha := by linarith
      subst a
      simp only [f,g]
      rw [transition_value])
  convert hj using 1
  funext a
  by_cases ha : a≤TwoPositive.ASupport.alpha <;>
    simp [middleScalar,TwoPositive.ASupport.charge,f,g,ha,sub_nonpos]

theorem D_positive_antitone : AntitoneOn (positiveScalar 3) (Icc L frameCap) := by
  let f (a : ℝ) := -(base+l*axialCharge a+speed*frameCap-aD*(frameCap-a))
  let g (a : ℝ) := -(base+l*circleCharge a+speed*frameCap-aD*(frameCap-a))
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by simp only [L] at ha; linarith [ha.1],ha.2⟩
  have hfD (a : ℝ) : HasDerivAt f (-(l*axialD a+aD)) a := by
    have hh : HasDerivAt (fun a => -(base+l*axialCharge a+speed*frameCap-aD*(frameCap-a)))
        (-(l*axialD a-aD*(0-1))) a :=
      (((((axial_derivative a).const_mul l).const_add base).add_const
        (speed*frameCap)).sub
        (((hasDerivAt_const a frameCap).sub (hasDerivAt_id' a)).const_mul aD)).neg
    exact hh.congr_deriv (by ring)
  have hgD (a : ℝ) : HasDerivAt g (-(l*circleD a+aD)) a := by
    have hh : HasDerivAt (fun a => -(base+l*circleCharge a+speed*frameCap-aD*(frameCap-a)))
        (-(l*circleD a-aD*(0-1))) a :=
      (((((circle_derivative a).const_mul l).const_add base).add_const
        (speed*frameCap)).sub
        (((hasDerivAt_const a frameCap).sub (hasDerivAt_id' a)).const_mul aD)).neg
    exact hh.congr_deriv (by ring)
  have hf : MonotoneOn f (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro a _; exact (hfD a).continuousAt.continuousWithinAt
    · intro a _; exact hfD a
    · intro a ha
      have hh := (ABounds.axial_derivative_bounds (hmem (Ioo_subset_Icc_self ha))).2
      have hd := diagonal_bounds.2
      simp only [aD,l] at hh hd ⊢
      linarith
  have hg : MonotoneOn g (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro a _; exact (hgD a).continuousAt.continuousWithinAt
    · intro a _; exact hgD a
    · intro a ha
      have hh := (ABounds.circle_derivative_bounds (hmem (Ioo_subset_Icc_self ha))).2
      have hd := diagonal_bounds.2
      simp only [aD,l] at hh hd ⊢
      linarith
  have hj := monotone_continuous_switch (e:=fun a => a-TwoPositive.ASupport.alpha) (by fun_prop) hf hg
    (fun a _ he => by
      have ha : a=TwoPositive.ASupport.alpha := by linarith
      subst a
      simp only [f,g]
      rw [transition_value])
  have he (a : ℝ) : (if a-TwoPositive.ASupport.alpha≤0 then f a else g a)= -positiveScalar 3 a := by
    by_cases ha : a≤TwoPositive.ASupport.alpha <;>
      simp [positiveScalar,positive,PositiveTD.Hybrid.positive,TwoPositive.ASupport.charge,
        f,g,ha,sub_nonpos] <;> ring
  intro a ha b hb hab
  have hh := hj ha hb hab
  simp only [he] at hh
  linarith

theorem pure_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) : 0<pureScalar i a := by
  have he := pure_endpoint_reserves i
  exact concave_gt_of_endpoints (pureScalar_concave i) ha
    ((by norm_num : (0:ℝ)<3/500).trans he.1) ((by norm_num : (0:ℝ)<3/500).trans he.2)

theorem middle_positive {a : ℝ} (ha : a∈Icc L frameCap) : 0< middleScalar a := by
  have hm := middleScalar_monotone (by norm_num [L,frameCap]) ha ha.1
  have he := middle_left_reserve
  exact ((by norm_num : (0:ℝ)<27/1000).trans he).trans_le hm

theorem positive_positive (i : Fin 4) {a : ℝ} (ha : a∈Icc L frameCap) :
    0<positiveScalar i a := by
  by_cases hi : i=3
  · subst i
    have hm := D_positive_antitone ha (by norm_num [L,frameCap]) ha.2
    have he := (positive_endpoint_reserves 0).2
    have h0 : positiveScalar 3 frameCap=
        base+l*TwoPositive.ASupport.charge frameCap+speed*frameCap := by
      simp [positiveScalar,positive,PositiveTD.Hybrid.positive]
    rw [h0] at hm
    exact ((by norm_num : (0:ℝ)<149/1000).trans he).trans_le hm
  · have hc := ordinary_positive_concave i
    have he := positive_endpoint_reserves i
    have hleft : 0<base+l*charge L+speed*frameCap+U R (p i) (q i) (frameCap-L) := by
      have hid : frameCap-L=span := by norm_num [frameCap,L,span]
      rw [hid]
      exact (by norm_num : (0:ℝ)<8/25).trans he.1
    have hright : 0<base+l*charge frameCap+speed*frameCap+
        U R (p i) (q i) (frameCap-frameCap) := by
      simp only [sub_self,U_zero,add_zero]
      exact (by norm_num : (0:ℝ)<149/1000).trans he.2
    simpa only [positiveScalar,positive,PositiveTD.Hybrid.positive,if_neg hi] using
      concave_gt_of_endpoints hc ha hleft hright

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.Fixed
