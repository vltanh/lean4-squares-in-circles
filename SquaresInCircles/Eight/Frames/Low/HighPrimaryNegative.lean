module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Low.HighCuts

/-!
# Eight squares: the primary axis of a low source against a negative high target

A low state and a negative high state separated along the primary axis of the low square, at a
frame angle `x ≥ -34/125`, have the cost of the pair above `8833/10000`, for both signs of the
source (`weak_separator`). The weak margin forces `x > 3/5`, and up to `4/5` the cost is at least
`F x`, with the source at the low endpoint `a1`, its label kept, and the target bounded by the
support of the containing circle (`circle_support`). That support increases, since the rotating
norm `N` has derivative at most `lam = 7/10` (`Nd_upper`, `F_monotone`), and `F (3/5)` exceeds
`8833/10000` (`initial_lower`, `lower`); beyond `4/5` the tail `low_high_tail` applies.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighPrimaryNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

def lam : ℝ := 7/10
def N (x : ℝ) : ℝ :=
  CircularNorm.norm (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x
def Nd (x : ℝ) : ℝ :=
  CircularNorm.d1 (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
    (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x
def K : ℝ := 9/100+FrameHighArc.k-L1-lam*a1+lam/2+
  (FrameHighArc.u-FrameHighArc.v)/2
def F (x : ℝ) : ℝ := x+K+(61/100)*Real.sin x-(9/100)*Real.cos x-R*N x
def Fd (x : ℝ) : ℝ := 1+(61/100)*Real.cos x+(9/100)*Real.sin x-R*Nd x

theorem energy_positive (x : ℝ) :
    0<CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
      (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x := by
  have he : CircularNorm.energy (FrameHighArc.u^2+FrameHighArc.v^2+lam^2)
      (-2*lam*FrameHighArc.u) (-2*lam*FrameHighArc.v) x=
        (FrameHighArc.u-lam*Real.cos x)^2+(FrameHighArc.v-lam*Real.sin x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -lam^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  by_contra! hbad
  have ha : FrameHighArc.u-lam*Real.cos x=0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (FrameHighArc.u-lam*Real.cos x),
      sq_nonneg (FrameHighArc.v-lam*Real.sin x)]
  have hb : FrameHighArc.v-lam*Real.sin x=0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (FrameHighArc.u-lam*Real.cos x),
      sq_nonneg (FrameHighArc.v-lam*Real.sin x)]
  have hc : Real.cos x=(10/7)*FrameHighArc.u := by dsimp [lam] at ha; linarith
  have hs : Real.sin x=(10/7)*FrameHighArc.v := by dsimp [lam] at hb; linarith
  have hunit := Real.sin_sq_add_cos_sq x
  rw [hc,hs] at hunit
  norm_num [FrameHighArc.u,FrameHighArc.v] at hunit

theorem N_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)
theorem N_square (x : ℝ) :
    (N x)^2=FrameHighArc.u^2+FrameHighArc.v^2+lam^2-
      2*lam*(FrameHighArc.u*Real.cos x+FrameHighArc.v*Real.sin x) := by
  have hh := CircularNorm.norm_sq (energy_positive x).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy] <;> ring
theorem N_deriv (x : ℝ) : HasDerivAt N (Nd x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)

/-- The derivative of the norm is at most `lam`, the speed of the moving force. -/
theorem Nd_upper (x : ℝ) : Nd x≤lam := by
  have hid : (N x)^2-(FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x)^2=
      (lam-FrameHighArc.u*Real.cos x-FrameHighArc.v*Real.sin x)^2 := by
    rw [N_square]
    linear_combination -(FrameHighArc.u^2+FrameHighArc.v^2)*(Real.sin_sq_add_cos_sq x)
  have hp := N_positive x
  have hforce : FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x≤N x := by
    by_contra! hbad
    have hh := mul_pos (sub_pos.mpr hbad)
      (show 0<FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x+N x by linarith)
    nlinarith [sq_nonneg (lam-FrameHighArc.u*Real.cos x-FrameHighArc.v*Real.sin x)]
  have he : Nd x=lam*(FrameHighArc.u*Real.sin x-FrameHighArc.v*Real.cos x)/N x := by
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope,N]
    ring
  rw [he]
  apply (div_le_iff₀ hp).2
  exact mul_le_mul_of_nonneg_left hforce (by norm_num [lam])

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  have h := ((((hasDerivAt_id' x).add_const K).fun_add
    ((Real.hasDerivAt_sin x).const_mul (61/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).fun_sub ((N_deriv x).const_mul R)
  refine h.congr_deriv ?_
  simp only [Fd]
  ring

theorem F_monotone : MonotoneOn F (Icc (3/5:ℝ) (4/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · intro x hx
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ))
      (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower] : (4/5:ℝ)≤Real.pi)
      hx.2.le
    have hsE := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
    have hcE := cos_lower_six (show (0:ℝ)≤4/5 by norm_num)
    norm_num at hsE hcE
    have hprod := mul_le_mul_of_nonneg_left (Nd_upper x) R_pos.le
    have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
    dsimp [Fd,lam] at *
    nlinarith

theorem initial_norm : N (3/5:ℝ)<1/20 := by
  have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
  have he := N_square (3/5)
  have hp := N_positive (3/5)
  norm_num [lam,FrameHighArc.u,FrameHighArc.v] at hs hc he
  nlinarith

theorem initial_lower : (8833/10000:ℝ)<F (3/5:ℝ) := by
  have hR : R<(99/50:ℝ) := by linarith [radius_precise.2]
  have hnorm := mul_le_mul hR.le initial_norm.le (N_positive (3/5)).le
    (by norm_num : (0:ℝ)≤99/50)
  have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  norm_num at hs
  have hc := Real.cos_le_one (3/5:ℝ)
  have hk := high_constant_lower
  have hL := L1_precise.2
  have ha := a1_precise.2
  dsimp [F,K,lam,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (4/5)) : (8833/10000:ℝ)<F x :=
  initial_lower.trans_le (F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1)

theorem circle_support {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (3/5:ℝ) (4/5)) (hm : 0≤primary false b B x) :
    F x≤lowHighCost false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := low_primary_source hb (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam])
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
  have ht := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩)
    (-FrameHighArc.u+lam*Real.cos x) (FrameHighArc.v-lam*Real.sin x)
  have hn : Real.sqrt ((-FrameHighArc.u+lam*Real.cos x)^2+
      (FrameHighArc.v-lam*Real.sin x)^2)=N x := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  dsimp [primary,FrameLowMidGeometry.primary,sign] at hscaled
  rw [(first_width hxq).1] at hscaled
  dsimp [F,K,lowHighCost,H,sign]
  rw [(first_width hxq).2]
  dsimp [lam] at hs ht hscaled ⊢
  nlinarith

theorem weak_separator (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary false b B x) : (8833/10000:ℝ)<lowHighCost i false b B x := by
  apply lt_of_lt_of_le _ (low_high_weaken_source i false hb)
  have hcut := FrameLowHighCuts.negative_primary_cut hb hB hx hm
  by_cases htail : (4/5:ℝ)≤x
  · exact low_high_tail false false hb hB (by simpa [lowHighTail] using htail)
  · exact (lower ⟨hcut.le,(lt_of_not_ge htail).le⟩).trans_le
      (circle_support hb hB ⟨hcut.le,(lt_of_not_ge htail).le⟩ hm)

end SquaresInCircles.Eight.FrameLowHighPrimaryNegative
