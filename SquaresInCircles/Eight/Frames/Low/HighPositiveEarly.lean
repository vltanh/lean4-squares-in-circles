module

public import SquaresInCircles.Eight.Frames.Low.HighGeometry

/-!
# Eight squares: the positive low/high secondary support from `1.1` to `1.35`

The entire high-target functional is increasing, so its first
intrinsic endpoint supplies the support.  The resulting scalar has an
increasing derivative which is still negative at the right endpoint.
Only exact endpoint Taylor bounds are used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPositiveEarly
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def domain : Set ℝ := Icc (11/10:ℝ) (27/20)
def C : ℝ := 153/400+(189/200)*b2
def S : ℝ := 153/400-(189/200)*a2
def K : ℝ := 9/16-1/100000-H2
def F (x : ℝ) : ℝ := x+K+C*Real.cos x+S*Real.sin x
def Fd (x : ℝ) : ℝ := 1-C*Real.sin x+S*Real.cos x
def Fdd (x : ℝ) : ℝ := -C*Real.cos x-S*Real.sin x
def selection (x : ℝ) : ℝ :=
  (189/200)*((149/250)*Real.sin x+Real.cos x)-(149/250)*FrameHighArc.u-FrameHighArc.v

theorem coefficient_bounds : (217/250:ℝ)<C ∧ C<869/1000 ∧
    -(94/125:ℝ)<S ∧ S< -(3/4:ℝ) := by
  dsimp [C,S]
  have hb := b2_bounds
  have ha := a2_bounds
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem quadrant {x : ℝ} (hx : x∈domain) : x∈Icc 0 (Real.pi/2) :=
  ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩

theorem endpoint_trig : (9757/10000:ℝ)<Real.sin (27/20) ∧
    Real.sin (27/20)<122/125 ∧ (219/1000:ℝ)<Real.cos (27/20) ∧
      (89/100:ℝ)<Real.sin (11/10) ∧ Real.cos (11/10)<227/500 := by
  have hs0 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤11/10 by norm_num)
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤11/10 by norm_num)
  have hs1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤27/20 by norm_num)
  have hsu := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤27/20 by norm_num)
  have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤27/20 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,HighOrderTaylor.C14,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    (89/100:ℝ)<Real.sin x ∧ Real.cos x<227/500 := by
  have hq := quadrant hx
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(11/10:ℝ)) hq.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤11/10) (by linarith [hq.2,Real.pi_pos]) hx.1
  exact ⟨by linarith [endpoint_trig.2.2.2.1],by linarith [endpoint_trig.2.2.2.2]⟩

theorem selection_deriv (x : ℝ) :
    HasDerivAt selection ((189/200)*((149/250)*Real.cos x-Real.sin x)) x := by
  have h := (((((Real.hasDerivAt_sin x).const_mul (149/250)).fun_add
    (Real.hasDerivAt_cos x)).const_mul (189/200)).sub_const
      ((149/250)*FrameHighArc.u)).sub_const FrameHighArc.v
  refine h.congr_deriv ?_
  ring

theorem selection_positive {x : ℝ} (hx : x∈domain) : 0<selection x := by
  have ha : AntitoneOn selection domain := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z _ => (selection_deriv z).continuousAt.continuousWithinAt
    · exact fun z _ => selection_deriv z
    · intro z hz
      have hs := (trig_bounds (Ioo_subset_Icc_self hz)).1
      have hc := Real.cos_le_one z
      linarith
  have hh := ha hx ⟨by norm_num,le_rfl⟩ hx.2
  have hp : 0<selection (27/20) := by
    dsimp [selection,FrameHighArc.u,FrameHighArc.v]
    linarith [endpoint_trig.1,endpoint_trig.2.2.1]
  exact hp.trans_le hh

theorem target_minimum {B x : ℝ} (hB : B∈Icc b2 c0) (hx : x∈domain) :
    linear (FrameHighArc.u-(189/200)*Real.sin x) ((189/200)*Real.cos x-FrameHighArc.v) b2≤
      linear (FrameHighArc.u-(189/200)*Real.sin x) ((189/200)*Real.cos x-FrameHighArc.v) B := by
  have hp : 0≤(189/200)*Real.sin x-FrameHighArc.u := by
    dsimp [FrameHighArc.u]
    linarith [(trig_bounds hx).1]
  have hm : MonotoneOn
      (linear (FrameHighArc.u-(189/200)*Real.sin x) ((189/200)*Real.cos x-FrameHighArc.v))
      (Icc b2 c0) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z hz => (linear_hasDerivAt ⟨b2_mem.1.trans hz.1,hz.2⟩ _ _).continuousAt.continuousWithinAt
    · exact fun z hz => linear_hasDerivAt ⟨b2_mem.1.trans hz.1.le,hz.2.le⟩ _ _
    · intro z hz
      have hr := slope_high_bounds (Ioo_subset_Icc_self hz)
      have hh := mul_le_mul_of_nonneg_left hr.1.le hp
      have hs := selection_positive hx
      simp only [Ad,FrameLowArc.slope,selection,neg_div] at hh hs ⊢
      nlinarith
  exact hm ⟨le_rfl,b2_mem.2⟩ hB hB.1

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  have h := (((hasDerivAt_id' x).add_const K).fun_add
    ((Real.hasDerivAt_cos x).const_mul C)).fun_add ((Real.hasDerivAt_sin x).const_mul S)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem Fd_deriv (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul C).const_sub 1).fun_add
    ((Real.hasDerivAt_cos x).const_mul S)
  refine h.congr_deriv ?_
  simp only [Fdd]
  ring

theorem Fdd_positive {x : ℝ} (hx : x∈domain) : 0<Fdd x := by
  have ht := trig_bounds hx
  have hq := FrameLowPair.quadrant (quadrant hx)
  have hcoef := coefficient_bounds
  have hc := mul_le_mul hcoef.2.1.le ht.2.le hq.2.2.1
    (by norm_num : (0:ℝ)≤869/1000)
  have hs := mul_le_mul
    (show (3/4:ℝ)≤-S by linarith [hcoef.2.2.2]) ht.1.le
    (by norm_num : (0:ℝ)≤89/100) (by linarith [hcoef.2.2.2] : 0≤-S)
  dsimp [Fdd]
  nlinarith

theorem final_derivative_negative : Fd (27/20)<0 := by
  have hcoef := coefficient_bounds
  have hs := mul_le_mul hcoef.1.le endpoint_trig.1.le
    (by norm_num : (0:ℝ)≤9757/10000) (by linarith [hcoef.1] : 0≤C)
  have hc := mul_le_mul
    (show (3/4:ℝ)≤-S by linarith [hcoef.2.2.2]) endpoint_trig.2.2.1.le
    (by norm_num : (0:ℝ)≤219/1000) (by linarith [hcoef.2.2.2] : 0≤-S)
  dsimp [Fd]
  nlinarith

theorem F_antitone : AntitoneOn F domain := by
  have hm : MonotoneOn Fd domain := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (Fd_deriv x).continuousAt.continuousWithinAt
    · exact fun x _ => Fd_deriv x
    · exact fun x hx => (Fdd_positive (Ioo_subset_Icc_self hx)).le
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · intro x hx
    exact (hm (Ioo_subset_Icc_self hx) ⟨by norm_num,le_rfl⟩ hx.2.le).trans final_derivative_negative.le

theorem final_lower : (8833/10000:ℝ)<F (27/20) := by
  have hcoef := coefficient_bounds
  have hc := mul_le_mul hcoef.1.le endpoint_trig.2.2.1.le
    (by norm_num : (0:ℝ)≤219/1000) (by linarith [hcoef.1] : 0≤C)
  have hsin := mul_le_mul
    (show -S≤94/125 by linarith [hcoef.2.2.1]) endpoint_trig.2.1.le
    (by linarith [endpoint_trig.1] : 0≤Real.sin (27/20)) (by norm_num : (0:ℝ)≤94/125)
  dsimp [F,K]
  nlinarith [H2_bounds.2]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x :=
  final_lower.trans_le (F_antitone hx ⟨by norm_num,le_rfl⟩ hx.2)

theorem support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) : F x≤lowHighCost true true b B x := by
  have hs := low_positive_source hb
  have ht := target_minimum hB hx
  dsimp [linear] at ht
  rw [A_b2] at ht
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [(first_width (quadrant hx)).1] at hscaled
  dsimp [F,C,S,K,lowHighCost,H,H2,sign]
  rw [(first_width (quadrant hx)).2]
  nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x :=
  (lower hx).trans_le (support hb hB hx hm)

end SquaresInCircles.Eight.FrameLowHighPositiveEarly
