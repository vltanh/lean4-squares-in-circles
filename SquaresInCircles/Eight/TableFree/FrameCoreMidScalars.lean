module

public import SquaresInCircles.Eight.TableFree.FramePairCalculus
public import SquaresInCircles.Eight.TableFree.FrameCoreMidContact

/-!
# Whole-angle continuations for the original core/middle pair

The negative-middle-target support is controlled for every point of the
middle arc by its circle equation.  The negative-core-target support uses
one fixed multiplier even for negative angles.  Positive-target tails are
continued through the intrinsic quarter turn by their actual derivatives.
All endpoint bounds below are individual Taylor deductions.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreMidScalars
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc FramePairCalculus

def ac : ℝ := 7/12
def ap : ℝ := (g+9/50)/2
def cp : ℝ := (g-9/50)/2

def trigAffine (α k a b x : ℝ) : ℝ := α*x+k+a*Real.cos x+b*Real.sin x

theorem trigAffine_deriv (α k a b x : ℝ) :
    HasDerivAt (trigAffine α k a b) (α-a*Real.sin x+b*Real.cos x) x := by
  have h := ((((hasDerivAt_id' x).const_mul α).add_const k).fun_add
    ((Real.hasDerivAt_cos x).const_mul a)).fun_add ((Real.hasDerivAt_sin x).const_mul b)
  refine h.congr_deriv ?_
  ring

theorem trigAffine_monotone {α k a b l u : ℝ}
    (hα : 0<α) (hamp : a^2+b^2<α^2) :
    MonotoneOn (trigAffine α k a b) (Icc l u) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (trigAffine_deriv α k a b x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv α k a b x
  · intro x _
    have hh := projection_lt (a := a) (b := -b) hα (by nlinarith) x
    nlinarith

theorem trig_six_fifths :
    (93203/100000:ℝ)<Real.sin (6/5:ℝ) ∧ Real.sin (6/5:ℝ)<23301/25000 ∧
      (7247/20000:ℝ)<Real.cos (6/5:ℝ) ∧ Real.cos (6/5:ℝ)<9059/25000 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤6/5 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤6/5 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤6/5 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤6/5 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem trig_three_halves : (707/10000:ℝ)<Real.cos (3/2:ℝ) ∧
    (997/1000:ℝ)<Real.sin (3/2:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤3/2 by norm_num)
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤3/2 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  constructor <;> linarith

theorem trig_last : (41/50:ℝ)<Real.sin (109/50:ℝ) ∧
    -(573/1000:ℝ)<Real.cos (109/50:ℝ) := by
  have hs := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤109/50 by norm_num)
  have hc := HighOrderTaylor.C18_le_cos (show (0:ℝ)≤109/50 by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  constructor <;> linarith

theorem trig_corner_cut : (847/1000:ℝ)<Real.sin (213/100:ℝ) ∧
    -(133/250:ℝ)<Real.cos (213/100:ℝ) := by
  have hs := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤213/100 by norm_num)
  have hc := HighOrderTaylor.C18_le_cos (show (0:ℝ)≤213/100 by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  constructor <;> linarith

theorem trig_primary_cut : (233/250:ℝ)<Real.sin (97/50:ℝ) ∧
    -(181/500:ℝ)<Real.cos (97/50:ℝ) := by
  have hs := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤97/50 by norm_num)
  have hc := HighOrderTaylor.C18_le_cos (show (0:ℝ)≤97/50 by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  constructor <;> linarith

theorem high_angle_trig {x : ℝ} (hx : x∈Icc (153/100:ℝ) (109/50)) :
    (41/50:ℝ)<Real.sin x ∧ Real.cos x<4079/100000 := by
  have hs := sin_endpoint_lower (by norm_num : (0:ℝ)≤153/100)
    (by linarith [FrameLowPair.pi_lower] : (109/50:ℝ)≤Real.pi) hx
    (by linarith [FrameCoreMidFullCircle.endpoint_trig.1]) trig_last.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤153/100)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  exact ⟨hs,hc.trans_lt FrameCoreMidFullCircle.endpoint_trig.2.2.2⟩

theorem middle_sum_lower {b : ℝ} (hb : b∈Icc b1 b2) : a1+b1≤A b+b := by
  have hh := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) b1_mem.1 b2_mem.2 hb
  have he : a1+b1≤a2+b2 := by
    dsimp [b1,b2]
    linarith [a1_precise.2,a2_bounds.1]
  simpa only [linear,A_b1,A_b2,one_mul,min_eq_left he] using hh

theorem middle_negative_amplitude {b : ℝ} (hb : b∈Icc b1 b2) :
    (cp-g*b)^2+(g*A b-cp)^2<1 := by
  have hc := A_circle ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
  have hs := middle_sum_lower hb
  have hcoef : 0≤g^2+2*g*cp := by norm_num [g,cp]
  have hm := mul_le_mul_of_nonneg_left hs hcoef
  have hnum : g^2*(Q0-1/2)-(g^2+2*g*cp)*((5/4)*(1298747247/1000000000))+2*cp^2<1 := by
    norm_num [g,cp,Q0]
  have ha := mul_lt_mul_of_pos_left a1_precise.1
    (show 0<(g^2+2*g*cp)*(5/4) by norm_num [g,cp])
  dsimp [b1] at hm
  nlinarith

theorem middle_negative_coefficients {b : ℝ} (hb : b∈Icc b1 b2) :
    -(53/500:ℝ)<cp-g*b ∧ cp-g*b<53/500 ∧
      (87/50:ℝ)<cp+g*A b ∧ 0<g*A b-cp := by
  have ha := A_mid_bounds hb
  have hbL := b1_bounds.1.trans_le hb.1
  have hbU := hb.2.trans_lt b2_bounds.2
  have haL := a2_bounds.1.trans_le ha.1
  dsimp [cp,g] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem middle_zero_lower {b : ℝ} (hb : b∈Icc b1 b2) :
    (979/1000:ℝ)<g+M b-g*b := by
  have hh := loss_antitone (lam := g) (by norm_num [g]) hb
    ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  simp only [M_b2] at hh
  have hnum : (979/1000:ℝ)<g+M2-g*b2 := by
    dsimp [g,b2]
    linarith [M_endpoints.2.2.1,a2_bounds.2]
  linarith

def negativeMid (b x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+g*pairWidth x+M b-
    g*A b*Real.sin x-g*b*Real.cos x

def negativeMidFirst (b x : ℝ) : ℝ :=
  trigAffine 1 (ap+M b) (cp-g*b) (-(g*A b-cp)) x
def negativeMidSecond (b x : ℝ) : ℝ :=
  trigAffine 1 (ap+M b) (-cp-g*b) (-(g*A b-cp)) x
def negativeMidLeft (b z : ℝ) : ℝ :=
  trigAffine (-1) (ap+M b) (cp-g*b) (cp+g*A b) z

theorem negativeMid_first {b x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    negativeMid b x=negativeMidFirst b x := by
  dsimp [negativeMid,negativeMidFirst,trigAffine,ap,cp]
  rw [(first_width hx).1,(first_width hx).2]
  ring

theorem negativeMid_second {b x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    negativeMid b x=negativeMidSecond b x := by
  dsimp [negativeMid,negativeMidSecond,trigAffine,ap,cp]
  rw [(second_width hx).1,(second_width hx).2]
  ring

theorem negativeMid_left {b x : ℝ} (hx : x∈Icc (-(54/125:ℝ)) 0) :
    negativeMid b x=negativeMidLeft b (-x) := by
  dsimp [negativeMid,negativeMidLeft,trigAffine,ap,cp]
  rw [(negative_width hx).1,(negative_width hx).2,Real.cos_neg,Real.sin_neg]
  ring

theorem negativeMidFirst_monotone {b : ℝ} (hb : b∈Icc b1 b2) :
    MonotoneOn (negativeMidFirst b) (Icc 0 (Real.pi/2)) := by
  apply trigAffine_monotone (by norm_num : (0:ℝ)<1)
  rw [neg_sq,one_pow]
  exact middle_negative_amplitude hb

theorem negativeMidSecond_monotone {b : ℝ} (hb : b∈Icc b1 b2) :
    MonotoneOn (negativeMidSecond b) (Icc (Real.pi/2) Real.pi) := by
  have hB : 0≤cp+g*b := by
    have hb0 := b1_mem.1.trans hb.1
    dsimp [cp,g]
    linarith
  have hA := (middle_negative_coefficients hb).2.2.2
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (trigAffine_deriv 1 _ _ _ x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv 1 _ _ _ x
  · intro x hx
    have hq := second_signs (Ioo_subset_Icc_self hx)
    have hs := mul_nonneg hB hq.1
    have hc := mul_nonpos_of_nonneg_of_nonpos hA.le hq.2
    nlinarith

theorem negativeMidLeft_monotone {b : ℝ} (hb : b∈Icc b1 b2) :
    MonotoneOn (negativeMidLeft b) (Icc 0 (54/125:ℝ)) := by
  have hcoef := middle_negative_coefficients hb
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (trigAffine_deriv (-1) _ _ _ x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv (-1) _ _ _ x
  · intro x hx
    have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨hx.1.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hq := FrameLowPair.quadrant hxq
    have hsU := Real.sin_le hx.1.le
    have hcL := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsquare := pow_le_pow_left₀ hx.1.le hx.2.le 2
    have hs := mul_le_mul hcoef.2.1.le (hsU.trans hx.2.le) hq.1
      (by norm_num : (0:ℝ)≤53/500)
    have hc0 : (14167/15625:ℝ)≤Real.cos x := by norm_num at hsquare; linarith
    have hc := mul_le_mul hcoef.2.2.1.le hc0
      (by norm_num : (0:ℝ)≤14167/15625)
      (by linarith [hcoef.2.2.1] : 0≤cp+g*A b)
    linarith

theorem negativeMid_lower {b x : ℝ} (hb : b∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) Real.pi) : (979/1000:ℝ)<negativeMid b x := by
  have hzero := middle_zero_lower hb
  have he0 : negativeMidFirst b 0=g+M b-g*b := by
    simp [negativeMidFirst,trigAffine,ap,cp]
    ring
  by_cases hx0 : x≤0
  · rw [negativeMid_left ⟨hx.1,hx0⟩]
    have hh := negativeMidLeft_monotone hb ⟨le_rfl,by norm_num⟩
      (show -x∈Icc 0 (54/125:ℝ) by constructor <;> linarith [hx.1])
      (by linarith : 0≤-x)
    have he : negativeMidLeft b 0=g+M b-g*b := by
      simp [negativeMidLeft,trigAffine,ap,cp]
      ring
    rw [he] at hh
    exact hzero.trans_le hh
  · have hx0' : 0≤x := (lt_of_not_ge hx0).le
    by_cases hxQ : x≤Real.pi/2
    · rw [negativeMid_first ⟨hx0',hxQ⟩]
      have hh := negativeMidFirst_monotone hb ⟨le_rfl,by positivity⟩ ⟨hx0',hxQ⟩ hx0'
      rw [he0] at hh
      exact hzero.trans_le hh
    · rw [negativeMid_second ⟨(lt_of_not_ge hxQ).le,hx.2⟩]
      have hjoin : negativeMidSecond b (Real.pi/2)=negativeMidFirst b (Real.pi/2) := by
        simp [negativeMidSecond,negativeMidFirst,trigAffine]
      have hfirst := negativeMidFirst_monotone hb ⟨le_rfl,by positivity⟩
        ⟨by positivity,le_rfl⟩ (by positivity : (0:ℝ)≤Real.pi/2)
      have hsecond := negativeMidSecond_monotone hb
        ⟨le_rfl,by linarith [Real.pi_pos]⟩ ⟨(lt_of_not_ge hxQ).le,hx.2⟩
        (lt_of_not_ge hxQ).le
      rw [hjoin] at hsecond
      rw [he0] at hfirst
      linarith

def negativeCore (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+g*pairWidth x+M2-g*b2-g*ac*Real.sin x

theorem negativeCore_lower {x : ℝ} (hx : x∈Icc (-(54/125:ℝ)) Real.pi) :
    (19/20:ℝ)<negativeCore x := by
  obtain ⟨k,hk⟩ : ∃ k : ℝ, k=ap+M2-g*b2 := ⟨_,rfl⟩
  have hzero : (979/1000:ℝ)<k+cp := by
    have hh := middle_zero_lower ⟨b1_lt_b2.le,le_rfl⟩
    rw [M_b2] at hh
    rw [hk]
    dsimp only [ap,cp]
    linarith
  have hfm : MonotoneOn (trigAffine 1 k cp (cp-g*ac)) (Icc 0 (Real.pi/2)) := by
    apply trigAffine_monotone (by norm_num : (0:ℝ)<1)
    norm_num [cp,g,ac]
  have hf0 : trigAffine 1 k cp (cp-g*ac) 0=k+cp := by simp [trigAffine]
  have hhm : MonotoneOn (trigAffine 1 k (-cp) (cp-g*ac)) (Icc (Real.pi/2) Real.pi) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun y _ => (trigAffine_deriv 1 k (-cp) (cp-g*ac) y).continuousAt.continuousWithinAt
    · exact fun y _ => trigAffine_deriv 1 k (-cp) (cp-g*ac) y
    · intro y hy
      have hq := second_signs (Ioo_subset_Icc_self hy)
      have hs := mul_nonneg (show 0≤cp by norm_num [cp,g]) hq.1
      have hc := mul_nonneg_of_nonpos_of_nonpos (show cp-g*ac≤0 by norm_num [cp,g,ac]) hq.2
      linarith
  have hn : ∀z∈Icc (0:ℝ) (54/125),(19/20:ℝ)<trigAffine (-1) k cp (cp+g*ac) z := by
    intro z hz
    have hsin := Real.sin_ge_sub_cube (show (0:ℝ)≤54/125 by norm_num)
    have hcos := Real.one_sub_sq_div_two_le_cos (x := (54/125:ℝ))
    have hlast : (19/20:ℝ)<trigAffine (-1) k cp (cp+g*ac) (54/125) := by
      have hs := mul_le_mul_of_nonneg_left hsin (show 0≤cp+g*ac by norm_num [cp,g,ac])
      have hc := mul_le_mul_of_nonneg_left hcos (show 0≤cp by norm_num [cp,g])
      dsimp only [trigAffine]
      rw [hk]
      dsimp only [ap,cp,g,ac] at hs hc ⊢
      norm_num at hs hc ⊢
      linarith [M_endpoints.2.2.1,b2_bounds.2]
    have hh := trig_concave_gt (α := -1) (m := 19/20-k)
      (show 0≤cp+g*ac by norm_num [cp,g,ac]) (show 0≤cp by norm_num [cp,g])
      (le_refl 0) (by linarith [FrameLowPair.pi_lower] : (54/125:ℝ)≤Real.pi/2) hz
      (by simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add]; linarith)
      (by dsimp only [trigAffine] at hlast; linarith)
    dsimp only [trigAffine]
    linarith
  by_cases hx0 : x≤0
  · have he : negativeCore x=trigAffine (-1) k cp (cp+g*ac) (-x) := by
      rw [hk]
      dsimp [negativeCore,trigAffine,ap,cp]
      rw [(negative_width ⟨hx.1,hx0⟩).1,(negative_width ⟨hx.1,hx0⟩).2,
        Real.cos_neg,Real.sin_neg]
      ring
    rw [he]
    exact hn (-x) (by constructor <;> linarith [hx.1])
  · have hx0' : 0≤x := (lt_of_not_ge hx0).le
    by_cases hxQ : x≤Real.pi/2
    · have he : negativeCore x=trigAffine 1 k cp (cp-g*ac) x := by
        rw [hk]
        dsimp [negativeCore,trigAffine,ap,cp]
        rw [(first_width ⟨hx0',hxQ⟩).1,(first_width ⟨hx0',hxQ⟩).2]
        ring
      rw [he]
      have hh := hfm ⟨le_rfl,by positivity⟩ ⟨hx0',hxQ⟩ hx0'
      linarith
    · have he : negativeCore x=trigAffine 1 k (-cp) (cp-g*ac) x := by
        rw [hk]
        dsimp [negativeCore,trigAffine,ap,cp]
        rw [(second_width ⟨(lt_of_not_ge hxQ).le,hx.2⟩).1,
          (second_width ⟨(lt_of_not_ge hxQ).le,hx.2⟩).2]
        ring
      have hjoin : trigAffine 1 k (-cp) (cp-g*ac) (Real.pi/2)=
          trigAffine 1 k cp (cp-g*ac) (Real.pi/2) := by simp [trigAffine]
      have hfirst := hfm ⟨le_rfl,by positivity⟩ ⟨by positivity,le_rfl⟩ (by positivity)
      have hsecond := hhm ⟨le_rfl,by linarith [Real.pi_pos]⟩
        ⟨(lt_of_not_ge hxQ).le,hx.2⟩ (lt_of_not_ge hxQ).le
      rw [he]
      rw [hjoin] at hsecond
      linarith

def positiveCore (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+pairWidth x+M2-b2-coreLabel FrameCoreArc.diagonal FrameCoreArc.diagonal+
    FrameCoreArc.diagonal*(Real.cos x-Real.sin x)

theorem positiveCore_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) Real.pi) :
    (23/20:ℝ)<positiveCore x := by
  let k : ℝ := 59/100+M2-b2-coreLabel FrameCoreArc.diagonal FrameCoreArc.diagonal
  let f : ℝ → ℝ := trigAffine 1 k (41/100+FrameCoreArc.diagonal) (41/100-FrameCoreArc.diagonal)
  let h : ℝ → ℝ := trigAffine 1 k (FrameCoreArc.diagonal-41/100) (41/100-FrameCoreArc.diagonal)
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hfm : MonotoneOn f (Icc (6/5:ℝ) (Real.pi/2)) := by
    apply trigAffine_monotone (by norm_num : (0:ℝ)<1)
    nlinarith
  have hhm : MonotoneOn h (Icc (Real.pi/2) Real.pi) := by
    apply trigAffine_monotone (by norm_num : (0:ℝ)<1)
    nlinarith
  have hdiag : CoreState FrameCoreArc.diagonal FrameCoreArc.diagonal := by
    right
    exact ⟨by linarith [hd.1],le_rfl,by nlinarith [CoreAngleEndpoint.diagonal_sq]⟩
  have hlabel := (label_bounds hdiag).2
  have ht := trig_six_fifths
  have hstart : (23/20:ℝ)<f (6/5) := by
    have hc := mul_le_mul_of_nonneg_left ht.2.2.1.le
      (show 0≤41/100+FrameCoreArc.diagonal by linarith [hd.1])
    have hs := mul_le_mul_of_nonpos_left ht.2.1.le
      (show 41/100-FrameCoreArc.diagonal≤0 by linarith [hd.1])
    dsimp [f,k,trigAffine]
    nlinarith [M_endpoints.2.2.1,b2_bounds.2]
  by_cases hxQ : x≤Real.pi/2
  · have he : positiveCore x=f x := by
      dsimp [positiveCore,f,k,trigAffine]
      rw [(first_width ⟨by linarith [hx.1],hxQ⟩).1,
        (first_width ⟨by linarith [hx.1],hxQ⟩).2]
      ring
    rw [he]
    exact hstart.trans_le (hfm ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩
      ⟨hx.1,hxQ⟩ hx.1)
  · have he : positiveCore x=h x := by
      dsimp [positiveCore,h,k,trigAffine]
      rw [(second_width ⟨(lt_of_not_ge hxQ).le,hx.2⟩).1,
        (second_width ⟨(lt_of_not_ge hxQ).le,hx.2⟩).2]
      ring
    have hjoin : h (Real.pi/2)=f (Real.pi/2) := by simp [h,f,trigAffine]
    have hfirst := hfm ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩
      ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ (by linarith [FrameLowPair.pi_lower])
    have hsecond := hhm ⟨le_rfl,by linarith [Real.pi_pos]⟩
      ⟨(lt_of_not_ge hxQ).le,hx.2⟩ (lt_of_not_ge hxQ).le
    rw [he]
    rw [hjoin] at hsecond
    linarith

def quarterValue : ℝ := Real.pi/2-M2+g*(1-a2)
def positiveMidFirst (x : ℝ) : ℝ :=
  trigAffine 1 (ap-M2) (cp+g*b2) (-(g*a2-cp)) x
def positiveMidSecond (x : ℝ) : ℝ :=
  trigAffine 1 (ap-M2) (-cp+g*b2) (-(g*a2-cp)) x

theorem quarter_lower : (4503/5000:ℝ)<quarterValue := by
  have hπ : (314159/100000:ℝ)<Real.pi := by linarith [Arithmetic.pi_hand_enclosure.1]
  dsimp [quarterValue,g]
  linarith [M_endpoints.2.2.2,a2_bounds.2]

theorem positiveMidFirst_antitone :
    AntitoneOn positiveMidFirst (Icc (153/100:ℝ) (Real.pi/2)) := by
  have hA : 0<cp+g*b2 := by dsimp [cp,g]; linarith [b2_bounds.1]
  have hB : 0<g*a2-cp := by dsimp [cp,g]; linarith [a2_bounds.1]
  have hstart : 1<(cp+g*b2)*(24979/25000) := by
    dsimp [cp,g,b2]
    linarith [a2_bounds.1]
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (trigAffine_deriv 1 _ _ _ x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv 1 _ _ _ x
  · intro x hx
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤(153/100:ℝ)) hx.2.le hx.1.le
    have hq := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2.le⟩
    have hmul := mul_le_mul_of_nonneg_left
      (FrameCoreMidFullCircle.endpoint_trig.1.le.trans hs) hA.le
    have hc := mul_nonneg hB.le hq.2.2.1
    nlinarith

theorem positiveMidSecond_monotone :
    MonotoneOn positiveMidSecond (Icc (Real.pi/2) Real.pi) := by
  have hA : 0≤-cp+g*b2 ∧ -cp+g*b2<11/100 := by
    dsimp [cp,g,b2]
    constructor <;> linarith [a2_bounds.1,a2_bounds.2]
  have hB : 0≤g*a2-cp := by dsimp [cp,g]; linarith [a2_bounds.1]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (trigAffine_deriv 1 _ _ _ x).continuousAt.continuousWithinAt
  · exact fun x _ => trigAffine_deriv 1 _ _ _ x
  · intro x hx
    have hq := second_signs (Ioo_subset_Icc_self hx)
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one x) hA.1
    have hc := mul_nonpos_of_nonneg_of_nonpos hB hq.2
    nlinarith [hA.2]

theorem positiveMidFirst_lower {x : ℝ} (hx : x∈Icc (153/100:ℝ) (Real.pi/2)) :
    (4503/5000:ℝ)<positiveMidFirst x := by
  have hh := positiveMidFirst_antitone hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2
  have he : positiveMidFirst (Real.pi/2)=quarterValue := by
    simp [positiveMidFirst,trigAffine,quarterValue,ap,cp]
    ring
  rw [he] at hh
  exact quarter_lower.trans_le hh

theorem positiveMidSecond_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    (4503/5000:ℝ)<positiveMidSecond x := by
  have hh := positiveMidSecond_monotone ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  have he : positiveMidSecond (Real.pi/2)=quarterValue := by
    simp [positiveMidSecond,trigAffine,quarterValue,ap,cp]
    ring
  rw [he] at hh
  exact quarter_lower.trans_le hh

end SquaresInCircles.Eight.TableFree.FrameCoreMidScalars
