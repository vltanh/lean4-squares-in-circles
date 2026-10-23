module

public import SquaresInCircles.Eight.TableFree.FrameLowHighPositiveEarly

/-!
# Positive low/high circle support up to the quarter strip

The exact rotating norm has positive energy and controlled curvature
on the whole interval `[1.35,π/2-.02]`.  Its support is concave, with
strict reserves at the two actual endpoints.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighPositiveCircle
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
  convert CircularNorm.norm_sq (energy_positive x).le using 1
  all_goals dsimp [N,CircularNorm.energy]; ring
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
  repeat' constructor <;> nlinarith

theorem N_upper {x : ℝ} (hx : x∈domain) : N x<543/1000 := by
  have hdom : x∈Icc (27/20:ℝ) (Real.pi/2) := ⟨hx.1,by linarith [hx.2]⟩
  exact (N_monotone hdom ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hdom.2).trans_lt
    endpoint_norms.2.1

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  convert ((((hasDerivAt_id x).add_const K).add
    ((Real.hasDerivAt_sin x).const_mul (171/200))).sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((N_deriv x).const_mul R)
    using 1 <;> dsimp [F,Fd] <;> ring
theorem Fd_deriv (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (171/200)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub ((Nd_deriv x).const_mul R)
    using 1 <;> dsimp [Fd,Fdd] <;> ring

theorem Fdd_negative {x : ℝ} (hx : x∈domain) : Fdd x<0 := by
  have ht := trig_window ⟨hx.1,by linarith [hx.2]⟩
  have hc := mul_le_mul_of_nonneg_left (Ndd_lower x) R_pos.le
  have hn := mul_le_mul (show R≤99/50 by linarith [radius_precise.2]) (N_upper hx).le
    (N_positive x).le (by norm_num : (0:ℝ)≤99/50)
  dsimp [Fdd]
  nlinarith

theorem F_concave : ConcaveOn ℝ domain F :=
  concave_of_deriv2 (fun x _ => F_deriv x) (fun x _ => Fd_deriv x)
    (fun x hx => (Fdd_negative hx).le)

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
  have hs1 := Real.sin_le_self (show (0:ℝ)≤1/50 by norm_num)
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
    (hx : x∈domain) (hm : 0≤secondary true true b B x) : F x≤lowHighCost true true b B x := by
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
    (hx : x∈domain) (hm : 0≤secondary true true b B x) :
    (8833/10000:ℝ)<lowHighCost true true b B x :=
  (lower hx).trans_le (support hb hB hx hm)

end SquaresInCircles.Eight.TableFree.FrameLowHighPositiveCircle
