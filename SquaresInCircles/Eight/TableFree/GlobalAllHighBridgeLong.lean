module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeData

/-!
# A fixed dual excludes every long high-source outer bridge

The single multiplier .79 makes the source old-marker expression
increase across the whole high arc.  A circle support for the high
target and endpoint concavity for the middle target finish both cases
on the whole interval [.5,.7].  No implicit contact curve is used.
Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor GlobalZeroSign FrameCircleArc FrameLowArc FrameMidArc

def longLambda : ℝ := 79/100
def longScalar (z : ℝ) : ℝ := 733/500-z-(37/80)*Real.cos z+(891/1000)*Real.sin z
def longScalarD (z : ℝ) : ℝ := -1+(37/80)*Real.sin z+(891/1000)*Real.cos z
def longSource (z b : ℝ) : ℝ :=
  (FrameHighArc.u-longLambda*Real.cos z)*A b+
    (longLambda*Real.sin z-FrameHighArc.v)*b

theorem long_trig {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    (479/1000:ℝ)<Real.sin z ∧ Real.cos z<439/500 := by
  have hz2 : z≤7/10 := by have h := hz.2; simp only [frameCap] at h; exact h
  have hp : z≤Real.pi/2 := by linarith [Real.pi_gt_three]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(1/2:ℝ)) hp hz.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤1/2) (by linarith [Real.pi_gt_three]) hz.1
  have hsl := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
  have hcu := cos_upper_four (show (0:ℝ)≤1/2 by norm_num)
  norm_num at hsl hcu
  constructor <;> linarith

theorem longScalar_deriv (z : ℝ) : HasDerivAt longScalar (longScalarD z) z := by
  have h1 : HasDerivAt (fun x : ℝ => 733/500-x) (-1) z := (hasDerivAt_id' z).const_sub _
  have h2 : HasDerivAt (fun x => 733/500-x-(37/80)*Real.cos x) (-1-(37/80)*(-Real.sin z)) z :=
    h1.fun_sub ((Real.hasDerivAt_cos z).const_mul (37/80))
  have h3 : HasDerivAt (fun x => 733/500-x-(37/80)*Real.cos x+(891/1000)*Real.sin x)
      (-1-(37/80)*(-Real.sin z)+(891/1000)*Real.cos z) z :=
    h2.fun_add ((Real.hasDerivAt_sin z).const_mul (891/1000))
  exact h3.congr_deriv (by dsimp [longScalarD]; ring)

theorem longScalar_concave : ConcaveOn ℝ (Icc (1/2:ℝ) frameCap) longScalar := by
  apply concave_of_deriv2 (fun z _ => longScalar_deriv z)
    (f' := longScalarD)
    (f'' := fun z => (37/80)*Real.cos z-(891/1000)*Real.sin z)
  · intro z hz
    have h1 : HasDerivAt (fun x : ℝ => -1+(37/80)*Real.sin x) ((37/80)*Real.cos z) z :=
      ((Real.hasDerivAt_sin z).const_mul (37/80)).const_add (-1)
    have h2 : HasDerivAt (fun x : ℝ => -1+(37/80)*Real.sin x+(891/1000)*Real.cos x)
        ((37/80)*Real.cos z+(891/1000)*(-Real.sin z)) z :=
      h1.fun_add ((Real.hasDerivAt_cos z).const_mul (891/1000))
    exact h2.congr_deriv (by ring)
  · intro z hz
    have ht := long_trig hz
    linarith

theorem longScalar_endpoints :
    (197/200:ℝ)<longScalar (1/2) ∧ (197/200:ℝ)<longScalar frameCap := by
  have hs0 := sin_lower_seven (show (0:ℝ)≤1/2 by norm_num)
  have hc0 := Arithmetic.cos_le_cos8 (show (0:ℝ)≤1/2 by norm_num)
  have hs1 := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc1 := Arithmetic.cos_le_cos8 (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [Arithmetic.cos8,frameCap] at hs0 hc0 hs1 hc1
  constructor <;> dsimp [longScalar,frameCap] <;> linarith

theorem longScalar_lower {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    (197/200:ℝ)<longScalar z :=
  concave_gt_of_endpoints longScalar_concave hz longScalar_endpoints.1 longScalar_endpoints.2

theorem longSource_monotone {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    MonotoneOn (longSource z) (Icc b2 c0) := by
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨by linarith [hz.1],hz.2⟩)
  have hs := (long_trig hz).1
  have hcoef : 0≤longLambda*Real.cos z-FrameHighArc.u := by
    dsimp [longLambda,FrameHighArc.u]
    linarith [ht.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (linear_hasDerivAt ⟨b2_mem.1.trans hb.1,hb.2⟩
      (FrameHighArc.u-longLambda*Real.cos z)
      (longLambda*Real.sin z-FrameHighArc.v)).continuousAt.continuousWithinAt
  · intro b hb
    exact linear_hasDerivAt ⟨b2_mem.1.trans hb.1.le,hb.2.le⟩
      (FrameHighArc.u-longLambda*Real.cos z)
      (longLambda*Real.sin z-FrameHighArc.v)
  · intro b hb
    have hr := FrameHighArc.slope_high_bounds (Ioo_subset_Icc_self hb)
    have hprod := mul_nonneg hcoef (show 0 ≤ slope b-(149/250:ℝ) by linarith)
    have hAd : Ad b=-FrameLowArc.slope b := by
      simp only [Ad,FrameLowArc.slope]; ring
    rw [hAd]
    dsimp [longLambda,FrameHighArc.u,FrameHighArc.v] at *
    nlinarith only [hprod,ht.1,hs]

theorem high_source_long (s : State) (hs : s.branch=.high)
    {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap) :
    -FrameHighArc.k+(FrameHighArc.u-longLambda*Real.cos z)*a2+
      (longLambda*Real.sin z-FrameHighArc.v)*b2≤
    -unsigned s-longLambda*s.a*Real.cos z+longLambda*s.b*Real.sin z := by
  have hchart := FrameHighArc.state_high_chart s hs
  have hm := longSource_monotone hz ⟨le_rfl,b2_mem.2⟩ hchart.2 hchart.2.1
  rw [unsigned_arc s (by simp [hs,Branch.type]),hs,arcMarker_high,hchart.1]
  dsimp [longSource,FrameHighArc.H] at hm ⊢
  rw [A_b2] at hm
  linarith

theorem middle_target_long (t : State) (ht : t.branch=.middle) :
    (6/125:ℝ)<unsigned t-longLambda*t.b := by
  have hchart := state_mid_chart t ht
  have hh := linear_endpoint_lower (p := FrameMidArc.p) (q := FrameMidArc.q-longLambda)
    (by norm_num [FrameMidArc.p]) b1_mem.1 b2_mem.2 hchart.2
  have he0 : (6/125:ℝ)<FrameMidArc.M b1-longLambda*b1 := by
    rw [FrameMidArc.M_b1]
    dsimp [longLambda]
    linarith [FrameMidArc.M_endpoints.1,b1_precise.2]
  have he1 : (6/125:ℝ)<FrameMidArc.M b2-longLambda*b2 := by
    rw [FrameMidArc.M_b2]
    dsimp [longLambda]
    linarith [FrameMidArc.M_endpoints.2.2.1,b2_precise.2]
  rw [unsigned_arc t (by simp [ht,Branch.type]),ht,arcMarker_middle]
  dsimp [FrameMidArc.M] at he0 he1 ⊢
  rcases le_total (linear FrameMidArc.p (FrameMidArc.q-longLambda) b1)
      (linear FrameMidArc.p (FrameMidArc.q-longLambda) b2) with hmin | hmin
  · rw [min_eq_left hmin] at hh
    dsimp [linear] at hh
    linarith
  · rw [min_eq_right hmin] at hh
    dsimp [linear] at hh
    linarith

theorem high_target_long (t : State) (ht : t.branch=.high) :
    FrameHighArc.k+(FrameHighArc.u+longLambda-FrameHighArc.v)/2-
      137607/100000<unsigned t-longLambda*t.b := by
  have hh := circle_product_support t
    (f := FrameHighArc.u) (g := longLambda-FrameHighArc.v)
    (K := 137607/100000) (by norm_num)
    (by norm_num [Q0,FrameHighArc.u,FrameHighArc.v,longLambda])
  have hstrict : FrameHighArc.u*t.a+(longLambda-FrameHighArc.v)*t.b<
      137607/100000-(FrameHighArc.u+longLambda-FrameHighArc.v)/2 := by
    have hh' := circle_product_support t
      (f := FrameHighArc.u) (g := longLambda-FrameHighArc.v)
      (K := 688031/500000) (by norm_num)
      (by norm_num [Q0,FrameHighArc.u,FrameHighArc.v,longLambda])
    linarith
  rw [unsigned_arc t (by simp [ht,Branch.type]),ht,arcMarker_high]
  rw [(FrameHighArc.state_high_chart t ht).1] at hstrict
  dsimp [FrameHighArc.H]
  linarith

theorem long_dual_coefficients :
    (733/500:ℝ)<Real.pi/2+(longLambda-9/50)/2+
      FrameHighArc.u*a2-FrameHighArc.v*b2+
      (FrameHighArc.u+longLambda-FrameHighArc.v)/2-137607/100000 ∧
    (1459/1000:ℝ)<Real.pi/2+(longLambda-9/50)/2+
      FrameHighArc.u*a2-FrameHighArc.v*b2-473/500+6/125 ∧
    -(37/80:ℝ)≤(longLambda+9/50)/2-longLambda*a2 ∧
    (891/1000:ℝ)≤(longLambda+9/50)/2+longLambda*b2 := by
  have hp := Arithmetic.pi_hand_enclosure.1
  have ha := a2_bounds
  have hb := b2_precise
  dsimp [longLambda,FrameHighArc.u,FrameHighArc.v]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem high_source_long_old (s t : State) (hs : s.branch=.high)
    {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b) :
    (t.branch=.high → (197/200:ℝ)<augmentedOld s t (-z)) ∧
    (t.branch=.middle → (489/500:ℝ)<augmentedOld s t (-z)) := by
  have tr := transport_trig (show z∈Icc 0 frameCap from ⟨by linarith [hz.1],hz.2⟩)
  have hp := mul_le_mul_of_nonneg_left hm (show 0≤longLambda by norm_num [longLambda])
  have hsource := high_source_long s hs hz
  have hcos := mul_le_mul_of_nonneg_right long_dual_coefficients.2.2.1
    (show 0≤Real.cos z by linarith [tr.1])
  have hsin := mul_le_mul_of_nonneg_right long_dual_coefficients.2.2.2 tr.2.2.1
  have hscalar := longScalar_lower hz
  rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hp
  constructor
  · intro ht
    have htarget := high_target_long t ht
    have hconstant := long_dual_coefficients.1
    dsimp [augmentedOld,oldCharge,frameCost,longScalar] at *
    rw [abs_neg,abs_of_nonneg (show 0≤z by linarith [hz.1])]
    nlinarith only [hp,hsource,htarget,hcos,hsin,hscalar,hconstant]
  · intro ht
    have htarget := middle_target_long t ht
    have hk := FrameHighArc.k_bounds.2.1
    have hconstant := long_dual_coefficients.2.1
    dsimp [augmentedOld,oldCharge,frameCost,longScalar] at *
    rw [abs_neg,abs_of_nonneg (show 0≤z by linarith [hz.1])]
    nlinarith only [hp,hsource,htarget,hcos,hsin,hscalar,hconstant,hk]

/-- The original cycle cap excludes the entire complementary long
interval at once, for either non-low original target chart. -/
theorem high_source_long_false (s t : State) (hs : s.branch=.high)
    (ht : t.branch=.middle ∨ t.branch=.high)
    {z : ℝ} (hz : z∈Icc (1/2:ℝ) frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) : False := by
  have hh := high_source_long_old s t hs hz hm
  rcases ht with ht | ht
  · have hm := hh.2 ht
    norm_num [hs,ht,Branch.type,cap,bonus,tau] at hc
    linarith
  · have hm := hh.1 ht
    norm_num [hs,ht,Branch.type,cap,bonus,tau] at hc
    linarith

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
