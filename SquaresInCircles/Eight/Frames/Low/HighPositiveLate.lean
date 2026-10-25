module

public import SquaresInCircles.Eight.Frames.Low.HighSecondaryOpposite
public import SquaresInCircles.Eight.Frames.Low.HighExtendedQuarter
public import SquaresInCircles.Eight.Frames.Low.HighGeometry
public import SquaresInCircles.Eight.Frames.Low.MidSecondaryContinuation
public import SquaresInCircles.Eight.Owners.CircularNorm

/-!
# Eight squares: the positive low/high diagonal support after the quarter strip

The high-target functional decreases over the entire original high
arc.  Its diagonal support is increasing in the frame error.  The
global width estimate supplies the remaining unbounded angular tail.
The final theorem joins every positive/positive secondary angle.
-/

section
/-!
## The positive low/high secondary support from `1.1` to `1.35`

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
end
end
end

section
/-!
## Positive low/high circle support up to the quarter strip

The exact rotating norm has positive energy and controlled curvature
on the whole interval `[1.35,π/2-.02]`.  Its support is concave, with
strict reserves at the two actual endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPositiveCircle
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def domain : Set ℝ := Icc (27/20:ℝ) (Real.pi/2-1/50)
def N (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameHighArc.u^2+FrameHighArc.v^2+(189/200)^2)
    (-2*(189/200)*FrameHighArc.v) (-2*(189/200)*FrameHighArc.u) x
def Nd (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameHighArc.u^2+FrameHighArc.v^2+(189/200)^2)
    (-2*(189/200)*FrameHighArc.v) (-2*(189/200)*FrameHighArc.u) x
def Ndd (x : ℝ) : ℝ :=
  CircularNorm.d2 (FrameHighArc.u^2+FrameHighArc.v^2+(189/200)^2)
    (-2*(189/200)*FrameHighArc.v) (-2*(189/200)*FrameHighArc.u) x
def K : ℝ := 9/16-1/100000-FrameHighArc.k-(FrameHighArc.u-FrameHighArc.v)/2
def F (x : ℝ) : ℝ := x+K+(171/200)*Real.sin x-(9/100)*Real.cos x-R*N x
def Fd (x : ℝ) : ℝ := 1+(171/200)*Real.cos x+(9/100)*Real.sin x-R*Nd x
def Fdd (x : ℝ) : ℝ := -(171/200)*Real.sin x+(9/100)*Real.cos x-R*Ndd x

theorem energy_positive (x : ℝ) :
    0<CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+(189/200)^2)
      (-2*(189/200)*FrameHighArc.v) (-2*(189/200)*FrameHighArc.u) x := by
  have hh := FrameCoreArc.projection_lt (a := FrameHighArc.u) (b := FrameHighArc.v)
    (by norm_num : (0:ℝ)<7/10) (by norm_num [FrameHighArc.u,FrameHighArc.v]) x
  dsimp [CircularNorm.energy,FrameHighArc.u,FrameHighArc.v] at *
  linarith

theorem N_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)
theorem N_square (x : ℝ) :
    (N x)^2=FrameHighArc.u^2+FrameHighArc.v^2+(189/200)^2-
      2*(189/200)*(FrameHighArc.u*Real.sin x+FrameHighArc.v*Real.cos x) := by
  rw [N,CircularNorm.norm_sq (energy_positive x).le]
  dsimp [CircularNorm.energy]
  ring
theorem N_deriv (x : ℝ) : HasDerivAt N (Nd x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)
theorem Nd_deriv (x : ℝ) : HasDerivAt Nd (Ndd x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive x)
theorem Ndd_lower (x : ℝ) : -N x/4≤Ndd x :=
  CircularNorm.curvature_lower (energy_positive x)
    (by norm_num [FrameHighArc.u,FrameHighArc.v])

theorem trig_window {x : ℝ} (hx : x∈Icc (27/20:ℝ) (Real.pi/2)) :
    (9757/10000:ℝ)<Real.sin x ∧ Real.cos x<11/50 := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(27/20:ℝ)) hx.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤27/20)
    (by linarith [hx.2,Real.pi_pos]) hx.1
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤27/20 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc0
  exact ⟨by linarith [FrameLowHighPositiveEarly.endpoint_trig.1],by linarith⟩

theorem N_monotone : MonotoneOn N (Icc (27/20:ℝ) (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv x
  · intro x hx
    have ht := trig_window (Ioo_subset_Icc_self hx)
    have hp := N_positive x
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope]
    apply div_nonneg _ (by positivity)
    dsimp [FrameHighArc.u,FrameHighArc.v]
    linarith

theorem endpoint_norms : N (27/20)<399/1000 ∧
    N (Real.pi/2)<543/1000 ∧ N (Real.pi/2-1/50)<529/1000 := by
  have h0 := N_square (27/20)
  have hm := N_square (Real.pi/2)
  have h1 := N_square (Real.pi/2-1/50)
  have hp0 := N_positive (27/20)
  have hpm := N_positive (Real.pi/2)
  have hp1 := N_positive (Real.pi/2-1/50)
  have hs0 := FrameLowHighPositiveEarly.endpoint_trig.1
  have hc0 := FrameLowHighPositiveEarly.endpoint_trig.2.2.1
  have hs1 := sin_lower_seven (show (0:ℝ)≤1/50 by norm_num)
  have hc1 := Real.one_sub_sq_div_two_le_cos (x := (1/50:ℝ))
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
    one_mul,zero_mul,sub_zero,zero_add] at h1
  norm_num [FrameHighArc.u,FrameHighArc.v] at h0 hm h1 hs1 hc1
  refine ⟨lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_,lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_,
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_⟩
  · rw [h0]; norm_num; linarith
  · rw [hm]; norm_num
  · rw [h1]; norm_num; linarith

theorem N_upper {x : ℝ} (hx : x∈domain) : N x<543/1000 := by
  have hdom : x∈Icc (27/20:ℝ) (Real.pi/2) := ⟨hx.1,by linarith [hx.2]⟩
  exact (N_monotone hdom ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hdom.2).trans_lt
    endpoint_norms.2.1

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  have h := ((((hasDerivAt_id' x).add_const K).fun_add
    ((Real.hasDerivAt_sin x).const_mul (171/200))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).fun_sub ((N_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring
theorem Fd_deriv (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (171/200)).const_add 1).fun_add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).fun_sub ((Nd_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fdd]
  ring

theorem Fdd_negative {x : ℝ} (hx : x∈domain) : Fdd x<0 := by
  have ht := trig_window ⟨hx.1,by linarith [hx.2]⟩
  have hc := mul_le_mul_of_nonneg_left (Ndd_lower x) R_pos.le
  have hn := mul_le_mul (show R≤99/50 by linarith [radius_precise.2]) (N_upper hx).le
    (N_positive x).le (by norm_num : (0:ℝ)≤99/50)
  dsimp [Fdd]
  nlinarith

theorem F_concave : ConcaveOn ℝ domain F :=
  concave_of_deriv2 (fun x _ => F_deriv x) (fun x _ => Fd_deriv x)
    (fun _ hx => (Fdd_negative hx).le)

theorem endpoint_lower : (8833/10000:ℝ)<F (27/20) ∧
    (8833/10000:ℝ)<F (Real.pi/2-1/50) := by
  have hR : R≤99/50 := by linarith [radius_precise.2]
  have hN0 := mul_le_mul hR endpoint_norms.1.le (N_positive (27/20)).le
    (by norm_num : (0:ℝ)≤99/50)
  have hN1 := mul_le_mul hR endpoint_norms.2.2.le (N_positive (Real.pi/2-1/50)).le
    (by norm_num : (0:ℝ)≤99/50)
  have ht0 := trig_window (show (27/20:ℝ)∈Icc (27/20) (Real.pi/2) from
    ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩)
  have hc1 := Real.one_sub_sq_div_two_le_cos (x := (1/50:ℝ))
  have hs1 := Real.sin_le (show (0:ℝ)≤1/50 by norm_num)
  have hk := k_bounds.2.1
  constructor
  · dsimp [F,K,FrameHighArc.u,FrameHighArc.v]
    linarith
  · dsimp [F,K,FrameHighArc.u,FrameHighArc.v]
    simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
      one_mul,zero_mul,sub_zero,zero_add]
    nlinarith [Arithmetic.pi_hand_enclosure.1]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x :=
  concave_gt_of_endpoints F_concave hx endpoint_lower.1 endpoint_lower.2

theorem support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) : F x≤lowHighCost true true b B x := by
  have hs := low_positive_source hb
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have ht := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩)
    (FrameHighArc.u-(189/200)*Real.sin x) ((189/200)*Real.cos x-FrameHighArc.v)
  have hn : Real.sqrt ((FrameHighArc.u-(189/200)*Real.sin x)^2+
      ((189/200)*Real.cos x-FrameHighArc.v)^2)=N x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination (189/200:ℝ)^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  have hq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [(first_width hq).1] at hscaled
  dsimp [F,K,lowHighCost,H,sign]
  rw [(first_width hq).2]
  nlinarith

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x :=
  (lower hx).trans_le (support hb hB hx hm)

end SquaresInCircles.Eight.FrameLowHighPositiveCircle
end
end
end

section
/-!
## The original positive low/high pair throughout the quarter strip

This proof uses only the original weak source-secondary margin.  The
fixed-target scalar contact has a monotone angle cost on the nearby
part of the high arc; the remaining part has a direct strict reserve.
The analytically continued aligned inequality closes both cases.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighQuarterStrip
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds
open FrameLowHighQuarterCalculus

theorem quarter_width (x : ℝ) : pairWidth (Real.pi/2+x)=pairWidth x := by
  simp only [pairWidth,Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub,add_zero,abs_neg]
  ring

theorem quarter_charge (x : ℝ) : periodicFrameCost (Real.pi/2+x)=periodicFrameCost x := by
  simpa only [add_comm] using periodicFrameCost_pi_half x

theorem source_contact_le (positive : Bool) {b B x : ℝ}
    (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) : height positive (A B) x≤b := by
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
  rw [quarter_width,← width_eq positive hx] at hm
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub] at hm
  rw [height_eq positive hB]
  nlinarith

theorem actual_cost (positive : Bool) {b B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) :
    lowHighCost true true b B (Real.pi/2+x)=
      x-(9/50)*(FrameLowHighParallelCalculus.width positive x-1)+L b+G (A B) := by
  dsimp [lowHighCost,sign]
  rw [quarter_charge,quarter_label hB,← width_charge positive hx]
  ring

theorem contact_cost_le (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) :
    cost positive B x≤lowHighCost true true b B (Real.pi/2+x) := by
  have hz := height_domain positive hB hx
  have hsource : height positive (A B) x∈Icc (-(1/4:ℝ)) b1 :=
    ⟨hz.1,by linarith [hz.2,b1_bounds.1]⟩
  have hbwide : b∈Icc (-(1/4:ℝ)) b1 := ⟨by linarith [hb.1],hb.2⟩
  have hlabel := source_label_monotone hsource hbwide (source_contact_le positive hB hx hm)
  rw [actual_cost positive hB hx]
  dsimp [cost]
  linarith

@[simp] theorem cost_zero (positive : Bool) (B : ℝ) :
    cost positive B 0=L (1-A B)+G (A B) := by
  cases positive <;> simp [cost,height,FrameLowHighParallelCalculus.width]

theorem aligned_lower (positive : Bool) {B : ℝ} (hB : B∈Icc b2 c0) :
    (8833/10000:ℝ)<cost positive B 0 := by
  have hA := A_high_bounds hB
  have hzero : 1-A B∈FrameLowHighExtendedQuarter.domain := by
    dsimp [FrameLowHighExtendedQuarter.domain,FrameLowHighAligned.b0]
    constructor <;> linarith [hA.1,hA.2,a2_bounds.2]
  have hh := FrameLowHighExtendedQuarter.strict_lower hzero
  have hcancel : 1-(1-A B)=A B := by ring
  rw [hcancel] at hh
  simpa only [cost_zero] using hh

theorem move_to_zero (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) (hcap : positive=false → A B≤103/100) :
    cost positive B 0≤cost positive B x := by
  cases positive with
  | false =>
      have ha : AntitoneOn (cost false B) (Icc x 0) := by
        apply antiOn_of_hasDeriv_nonpos
        · intro t ht
          exact (cost_deriv false hB (show t∈angleDomain false from
            ⟨hx.1.trans ht.1,ht.2⟩)).continuousAt.continuousWithinAt
        · intro t ht
          exact cost_deriv false hB ⟨hx.1.trans ht.1.le,ht.2.le⟩
        · intro t ht
          exact (negative_derivative hB (hcap rfl) ⟨hx.1.trans ht.1.le,ht.2.le⟩).le
      exact ha ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  | true =>
      have hm : MonotoneOn (cost true B) (Icc 0 x) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          exact (cost_deriv true hB (show t∈angleDomain true from
            ⟨ht.1,ht.2.trans hx.2⟩)).continuousAt.continuousWithinAt
        · intro t ht
          exact cost_deriv true hB ⟨ht.1.le,ht.2.le.trans hx.2⟩
        · intro t ht
          exact (positive_derivative hB ⟨ht.1.le,ht.2.le.trans hx.2⟩).le
      exact hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1

theorem far_target (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hfar : (103/100:ℝ)≤A B) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+x) := by
  have hG := G_monotone
    (show (103/100:ℝ)∈extendedDomain by constructor <;> norm_num [extendedDomain])
    (target_chart hB) hfar
  have hw := width_bounds positive hx
  have hL := (L_bounds hb).1
  have hxlow : -(1/50:ℝ)≤x := by cases positive <;> dsimp [angleDomain] at hx <;> linarith [hx.1]
  rw [actual_cost positive hB hx]
  linarith [G_reference]

theorem phase (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+x) := by
  by_cases hcap : A B≤103/100
  · exact (aligned_lower positive hB).trans_le
      ((move_to_zero positive hB hx (fun _ => hcap)).trans
        (contact_cost_le positive hb hB hx hm))
  · exact far_target positive hb hB hx (le_of_not_ge hcap)

theorem weak_separator {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(1/50:ℝ)) (1/50))
    (hm : 0≤ secondary true true b B (Real.pi/2+x)) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+x) := by
  by_cases hsign : x≤0
  · exact phase false hb hB ⟨hx.1,hsign⟩ hm
  · exact phase true hb hB ⟨le_of_not_ge hsign,hx.2⟩ hm

theorem actual_angle {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (Real.pi/2-1/50) (Real.pi/2+1/50))
    (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x := by
  have he : x-Real.pi/2∈Icc (-(1/50:ℝ)) (1/50) := by constructor <;> linarith [hx.1,hx.2]
  have hid : Real.pi/2+(x-Real.pi/2)=x := by ring
  have hmargin : 0≤ secondary true true b B (Real.pi/2+(x-Real.pi/2)) := by rwa [hid]
  simpa only [hid] using weak_separator hb hB he hmargin

end SquaresInCircles.Eight.FrameLowHighQuarterStrip
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPositiveLate
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def domain : Set ℝ := Icc (1/50:ℝ) (27/250)
def F (e : ℝ) : ℝ := Real.pi/4+e-1/100000+9/16+
  (153/400-(189/200)*c0)*(Real.cos e+Real.sin e)
def Fd (e : ℝ) : ℝ := 1+(153/400-(189/200)*c0)*(Real.cos e-Real.sin e)

theorem trig_bounds {e : ℝ} (he : e∈domain) :
    0≤Real.sin e ∧ Real.sin e≤27/250 ∧
      (994/1000:ℝ)<Real.cos e ∧ Real.cos e≤1 := by
  have he0 : 0≤e := by linarith [he.1]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi he0 (by linarith [he.2,FrameLowPair.pi_lower])
  have hsu := Real.sin_le he0
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hsq := pow_le_pow_left₀ he0 he.2 2
  exact ⟨hs,by linarith [he.2],by nlinarith,Real.cos_le_one e⟩

theorem target_minimum {B e : ℝ} (hB : B∈Icc b2 c0) (he : e∈domain) :
    linear (FrameHighArc.u-(189/200)*Real.cos e) (-(189/200)*Real.sin e-FrameHighArc.v) c0≤
      linear (FrameHighArc.u-(189/200)*Real.cos e) (-(189/200)*Real.sin e-FrameHighArc.v) B := by
  have ht := trig_bounds he
  have hp : 0≤(189/200)*Real.cos e-FrameHighArc.u := by
    dsimp [FrameHighArc.u]
    linarith [ht.2.2.1]
  have ha : AntitoneOn
      (linear (FrameHighArc.u-(189/200)*Real.cos e) (-(189/200)*Real.sin e-FrameHighArc.v))
      (Icc b2 c0) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z hz => (linear_hasDerivAt ⟨b2_mem.1.trans hz.1,hz.2⟩ _ _).continuousAt.continuousWithinAt
    · exact fun z hz => linear_hasDerivAt ⟨b2_mem.1.trans hz.1.le,hz.2.le⟩ _ _
    · intro z hz
      have hr := slope_high_bounds (Ioo_subset_Icc_self hz)
      have hh := mul_le_mul_of_nonneg_left hr.2 hp
      simp only [Ad,FrameLowArc.slope,FrameHighArc.u,FrameHighArc.v,neg_div] at hh hp ⊢
      nlinarith [ht.1,ht.2.2.2]
  exact ha hB ⟨b2_mem.2,le_rfl⟩ hB.2

theorem F_deriv (e : ℝ) : HasDerivAt F (Fd e) e := by
  have h := ((((hasDerivAt_id' e).const_add (Real.pi/4)).sub_const (1/100000)).add_const
    (9/16)).fun_add (((Real.hasDerivAt_cos e).fun_add (Real.hasDerivAt_sin e)).const_mul
      (153/400-(189/200)*c0))
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem Fd_positive {e : ℝ} (he : e∈domain) : 0<Fd e := by
  have ht := trig_bounds he
  have hp : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hh := mul_le_mul_of_nonpos_left
    (show Real.cos e-Real.sin e≤1 by linarith [ht.1,ht.2.2.2]) hp
  dsimp [Fd]
  nlinarith [c0_bounds.2]

theorem F_monotone : MonotoneOn F domain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun e _ => (F_deriv e).continuousAt.continuousWithinAt
  · exact fun e _ => F_deriv e
  · exact fun e he => (Fd_positive (Ioo_subset_Icc_self he)).le

theorem initial_lower : (8833/10000:ℝ)<F (1/50) := by
  have hs := Real.sin_le (show (0:ℝ)≤1/50 by norm_num)
  have hc := Real.cos_le_one (1/50)
  have hp : 153/400-(189/200)*c0≤0 := by linarith [c0_bounds.1]
  have hh := mul_le_mul_of_nonpos_left
    (show Real.cos (1/50)+Real.sin (1/50)≤51/50 by linarith) hp
  dsimp [F]
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem lower {e : ℝ} (he : e∈domain) : (8833/10000:ℝ)<F e :=
  initial_lower.trans_le (F_monotone ⟨le_rfl,by norm_num⟩ he he.1)

theorem support {b B e : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (he : e∈domain) (hm : 0≤ secondary true true b B (Real.pi/2+e)) :
    F e≤lowHighCost true true b B (Real.pi/2+e) := by
  have hs := low_positive_source hb
  have ht := target_minimum hB he
  dsimp [linear] at ht
  rw [A_c0] at ht
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have hq : e∈Icc 0 (Real.pi/2) := ⟨by linarith [he.1],by linarith [he.2,FrameLowPair.pi_lower]⟩
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [FrameLowHighQuarterStrip.quarter_width,(first_width hq).1] at hscaled
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub] at hscaled
  dsimp [F,lowHighCost,sign,H,k]
  rw [FrameLowHighQuarterStrip.quarter_charge,(first_width hq).2]
  nlinarith

theorem weak_separator {b B e : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (he : e∈domain) (hm : 0≤ secondary true true b B (Real.pi/2+e)) :
    (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+e) :=
  (lower he).trans_le (support hb hB he hm)

theorem charge_linear {e : ℝ} (he : 0≤e) : periodicFrameCost e≤e/2 := by
  have hs := Real.abs_sin_le_abs (x := e)
  rw [abs_of_nonneg he] at hs
  have hc := Real.abs_cos_le_one e
  dsimp [periodicFrameCost]
  linarith

theorem tail {b B e : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (he : (27/250:ℝ)≤e) : (8833/10000:ℝ)<lowHighCost true true b B (Real.pi/2+e) := by
  have hc := charge_linear (show 0≤e by linarith)
  have hl := (L_bounds hb).1
  have hh := (H_bounds hB).2
  dsimp [lowHighCost,sign]
  rw [FrameLowHighQuarterStrip.quarter_charge]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem positive_positive_secondary {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x := by
  have hcut : (11/10:ℝ)<x := by
    simpa [FrameLowHighCuts.positiveCut] using
      FrameLowHighCuts.positive_secondary_cut true hb hB hx hm
  by_cases hearly : x≤27/20
  · exact FrameLowHighPositiveEarly.weak_separator hb hB ⟨hcut.le,hearly⟩ hm
  by_cases hcircle : x≤Real.pi/2-1/50
  · exact FrameLowHighPositiveCircle.weak_separator hb hB ⟨by linarith,hcircle⟩ hm
  by_cases hstrip : x≤Real.pi/2+1/50
  · exact FrameLowHighQuarterStrip.actual_angle hb hB ⟨by linarith,hstrip⟩ hm
  have hid : Real.pi/2+(x-Real.pi/2)=x := by ring
  by_cases htail : (27/250:ℝ)≤x-Real.pi/2
  · simpa only [hid] using tail hb hB htail
  · have he : x-Real.pi/2∈domain := by constructor <;> linarith
    have hmargin : 0≤ secondary true true b B (Real.pi/2+(x-Real.pi/2)) := by rwa [hid]
    simpa only [hid] using weak_separator hb hB he hmargin

end SquaresInCircles.Eight.FrameLowHighPositiveLate
end
end
end
