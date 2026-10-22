module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAConcentration

/-!
# The intrinsic A and combined-angle shapes for negative core E

Uncompiled transcription of Section 5 of the two fixed-family negative-E
proofs. The actual A support is joined only at its matching value and
first derivative. The combined EH gain keeps its separate cut at 1/4.
Every curvature and derivative bound below is proved on its whole domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeSlope TwoPositive.ASupport
open NegativeAPositiveTD.PositiveSlope

def gD (s : ℝ) : ℝ := K*Real.cos s-beta*Real.sin s
def gDD (s : ℝ) : ℝ := -K*Real.sin s-beta*Real.cos s

theorem g_hasDerivAt (s : ℝ) : HasDerivAt g (gD s) s := by
  convert ((Real.hasDerivAt_sin s).const_mul K).sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul beta) using 1 <;>
    dsimp [g,gD] <;> ring

theorem gD_hasDerivAt (s : ℝ) : HasDerivAt gD (gDD s) s := by
  convert ((Real.hasDerivAt_cos s).const_mul K).sub
    ((Real.hasDerivAt_sin s).const_mul beta) using 1 <;> dsimp [gD,gDD] <;> ring

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
  let b : ℝ := min (s+r) u
  have hb0 : 0≤b := le_min (by linarith [hs.1]) (by norm_num [u])
  have hbf : b≤frameCap := (min_le_left _ _).trans hw
  have hsb : s∈Icc 0 b := ⟨hs.1,le_min (by linarith) hs.2⟩
  have hc := (g_concave.subset (Icc_subset_Icc le_rfl hbf) (convex_Icc 0 b)).add
    (NegativeOrdinaryEnvelope.affine_concave (-M) 0 0 b)
  have hm := hc.min_le_of_mem_Icc ⟨le_rfl,hb0⟩ ⟨hb0,le_rfl⟩ hsb
  simp only [g_zero,mul_zero,add_zero,zero_add] at hm
  have he : min (M*(s+r)) (jointGain (s+r))=
      M*(s+r)+min 0 (g b-M*b) := by
    by_cases hcut : s+r≤u
    · rw [jointGain,if_pos hcut]
      dsimp [b]
      rw [min_eq_left hcut,add_min]
      congr 1 <;> ring
    · rw [jointGain,if_neg hcut]
      dsimp [b]
      rw [min_eq_right (lt_of_not_ge hcut).le,add_min]
      congr 1 <;> ring
  rw [he]
  have hh : min 0 (g b-M*b)≤g s-M*s := by
    simpa only [neg_mul,sub_eq_add_neg] using hm
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
  have hc := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hh := cos_upper_four (show (0:ℝ)≤frameCap/2 by norm_num [frameCap])
  have hhalf0 := (half_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2.le
  have hmul := mul_le_mul_of_nonneg_right radius_tight.2.le hhalf0
  norm_num [frameCap,radiusHi] at hc hh hmul
  dsimp [circleD] at hlast ⊢
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
    curvature R (p i) (q i) x-p i*phi x< -(1/10)*p i := by
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
    (hA : A∈Icc L u) (hAB : A≤B) (hB : B≤frameCap)
    (hd : ∀a∈Icc A B,HasDerivAt f (fd a) a)
    (hdd : ∀a∈Icc A B,HasDerivAt fd (fdd a) a)
    (hcurv : ∀a∈Icc A B,fdd a≤-l/50) :
    ConcaveOn ℝ (Icc A B) (fun a => l*charge a+f a) := by
  have hA0 : 0≤A := by dsimp [L] at hA; linarith [hA.1]
  have hAα : A≤alpha := by dsimp [u] at hA; linarith [hA.2,alpha_bounds.1]
  have haxis {b : ℝ} (hb : b≤B) (hbα : b≤alpha) :
      ConcaveOn ℝ (Icc A b) (fun a => l*axialCharge a+f a) := by
    apply concave_of_deriv2
      (fun a ha => ((axial_derivative a).const_mul l).add (hd a ⟨ha.1,ha.2.trans hb⟩))
      (fun a ha => ((axial_second a).const_mul l).add (hdd a ⟨ha.1,ha.2.trans hb⟩))
    intro a ha
    have hj := PositiveANegativeTD.ABounds.axial_second_upper
      ⟨hA0.trans ha.1,ha.2.trans hbα⟩
    have hf := hcurv a ⟨ha.1,ha.2.trans hb⟩
    dsimp [l] at *
    linarith
  by_cases hBα : B≤alpha
  · apply concave_congr_on (haxis le_rfl hBα)
    intro a ha
    rw [charge,if_pos (ha.2.trans hBα)]
  · have hαB : alpha≤B := (lt_of_not_ge hBα).le
    have hcircle : ConcaveOn ℝ (Icc alpha B) (fun a => l*circleCharge a+f a) := by
      apply concave_of_deriv2
        (fun a ha => ((circle_derivative a).const_mul l).add (hd a ⟨hAα.trans ha.1,ha.2⟩))
        (fun a ha => ((circle_second a).const_mul l).add (hdd a ⟨hAα.trans ha.1,ha.2⟩))
      intro a ha
      have hj := circle_curvature ⟨by linarith [alpha_bounds.1,ha.1],ha.2.trans hB⟩
      have hf := hcurv a ⟨hAα.trans ha.1,ha.2⟩
      dsimp [l] at *
      linarith
    have he : l*axialCharge alpha+f alpha=l*circleCharge alpha+f alpha := by rw [transition_value]
    have hdl := ((axial_derivative alpha).const_mul l).add (hd alpha ⟨hAα,hαB⟩)
    have hdr := ((circle_derivative alpha).const_mul l).add (hd alpha ⟨hAα,hαB⟩)
    rw [← transition_derivative] at hdr
    have hj := SplitConcavityTools.join ⟨hAα,hαB⟩ (haxis hαB le_rfl) hcircle he hdl hdr
    convert hj using 1
    funext a
    by_cases ha : a≤alpha <;> simp [charge,ha]

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
    simpa using (V_hasDerivAt hc.1 hq (harg a ha)).comp a ((hasDerivAt_id a).sub_const b)
  · intro a ha
    simpa using (Vd_hasDerivAt hc.1 hq (harg a ha)).comp a ((hasDerivAt_id a).sub_const b)
  · intro a ha
    have hh := negative_curvature i (harg a ha)
    dsimp [l] at *
    linarith [hc.2.2.2.2.1]

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
    (fdd:=fun a => curvature R (p i) (q i) (b-a)-p i*phi (b-a))
  · intro a ha
    have hh := (U_hasDerivAt hc.1 hq (hargf ha)).comp a
      ((hasDerivAt_const a b).sub (hasDerivAt_id a))
    convert hh using 1 <;> ring
  · intro a ha
    have hh := (Ud_hasDerivAt hc.1 hq (hargf ha)).comp a
      ((hasDerivAt_const a b).sub (hasDerivAt_id a))
    convert hh.neg using 1 <;> ring
  · intro a ha
    have hh := positive_curvature i (harg a ha)
    dsimp [l,k] at *
    linarith [hc.2.2.2.1]

theorem linear_middle_monotone : MonotoneOn (fun a => l*charge a+M*a) (Icc L frameCap) := by
  let f (a : ℝ) := l*axialCharge a+M*a
  let h (a : ℝ) := l*circleCharge a+M*a
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hfD (a : ℝ) : HasDerivAt f (l*axialD a+M) a :=
    ((axial_derivative a).const_mul l).add ((hasDerivAt_id a).const_mul M)
  have hhD (a : ℝ) : HasDerivAt h (l*circleD a+M) a :=
    ((circle_derivative a).const_mul l).add ((hasDerivAt_id a).const_mul M)
  have hf : MonotoneOn f (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hfD a).continuousAt.continuousWithinAt) (fun a _ => hfD a)
    intro a ha
    have hd := axial_derivative_lower (hmem (Ioo_subset_Icc_self ha))
    dsimp [l,M]
    linarith
  have hh : MonotoneOn h (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hhD a).continuousAt.continuousWithinAt) (fun a _ => hhD a)
    intro a ha
    have hd := circle_derivative_lower (hmem (Ioo_subset_Icc_self ha))
    dsimp [l,M]
    linarith
  have hj := monotone_continuous_switch (e:=fun a => a-alpha) (by fun_prop) hf hh
    (fun a _ he => by
      have ha : a=alpha := by linarith
      subst a
      dsimp [f,h]
      rw [transition_value])
  convert hj using 1
  funext a
  by_cases ha : a≤alpha <;> simp [charge,f,h,ha,sub_nonpos]

theorem D_remainder_antitone (b : ℝ) :
    AntitoneOn (fun a => l*charge a-aD*(b-a)) (Icc L frameCap) := by
  let f (a : ℝ) := -(l*axialCharge a-aD*(b-a))
  let h (a : ℝ) := -(l*circleCharge a-aD*(b-a))
  have hmem {a : ℝ} (ha : a∈Icc L frameCap) : a∈Icc 0 frameCap :=
    ⟨by dsimp [L] at ha; linarith [ha.1],ha.2⟩
  have hfD (a : ℝ) : HasDerivAt f (-(l*axialD a+aD)) a := by
    convert (((axial_derivative a).const_mul l).sub
      (((hasDerivAt_const a b).sub (hasDerivAt_id a)).const_mul aD)).neg using 1 <;> ring
  have hhD (a : ℝ) : HasDerivAt h (-(l*circleD a+aD)) a := by
    convert (((circle_derivative a).const_mul l).sub
      (((hasDerivAt_const a b).sub (hasDerivAt_id a)).const_mul aD)).neg using 1 <;> ring
  have hf : MonotoneOn f (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hfD a).continuousAt.continuousWithinAt) (fun a _ => hfD a)
    intro a ha
    have hd := (PositiveANegativeTD.ABounds.axial_derivative_bounds (hmem (Ioo_subset_Icc_self ha))).2
    dsimp [l,aD]
    linarith [diagonal_bounds.2]
  have hh : MonotoneOn h (Icc L frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (hhD a).continuousAt.continuousWithinAt) (fun a _ => hhD a)
    intro a ha
    have hd := (PositiveANegativeTD.ABounds.circle_derivative_bounds (hmem (Ioo_subset_Icc_self ha))).2
    dsimp [l,aD]
    linarith [diagonal_bounds.2]
  have hj := monotone_continuous_switch (e:=fun a => a-alpha) (by fun_prop) hf hh
    (fun a _ he => by
      have ha : a=alpha := by linarith
      subst a
      dsimp [f,h]
      rw [transition_value])
  have he (a : ℝ) : (if a-alpha≤0 then f a else h a)= -(l*charge a-aD*(b-a)) := by
    by_cases ha : a≤alpha <;> simp [charge,f,h,ha,sub_nonpos]
  intro a ha x hx hax
  have h := hj ha hx hax
  rw [he,he] at h
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA
