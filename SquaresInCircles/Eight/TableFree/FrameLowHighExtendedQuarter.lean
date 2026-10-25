module

public import SquaresInCircles.Eight.TableFree.FrameLowHighAligned

/-!
# Quarter-aligned support on the continued circle chart

The aligned quarter sum has curvature greater than `1/4` all the way
to a low coordinate `-.2`.  Its strict reserve follows from the same
exact aligned reference and derivative as the physical aligned case.
This is an analytic support inequality, with no new physical states.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighExtendedQuarter
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned

def domain : Set ℝ := Icc (-(1/5:ℝ)) b0

theorem chart_domain {b : ℝ} (hb : b∈domain) :
    b∈extendedDomain ∧ 1-b∈extendedDomain := by
  dsimp [domain,extendedDomain] at *
  constructor <;> constructor <;> linarith [hb.1,hb.2,b0_bounds.1,b0_bounds.2]

theorem quarter_deriv {b : ℝ} (hb : b∈domain) : HasDerivAt quarter (quarterD b) b := by
  have hd := chart_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (extended_L_deriv hd.1).fun_add ((G_deriv hd.2).comp b hm)
  refine h.congr_deriv ?_
  simp only [quarterD]
  ring

theorem quarterD_deriv {b : ℝ} (hb : b∈domain) :
    HasDerivAt quarterD (quarterDD b) b := by
  have hd := chart_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (extended_Ld_deriv hd.1).fun_sub ((Gd_deriv hd.2).comp b hm)
  refine h.congr_deriv ?_
  simp only [quarterDD,Gdd]
  ring

theorem curvature {b : ℝ} (hb : b∈domain) : (1/4:ℝ)<quarterDD b := by
  have hd := chart_domain hb
  have hc := extended_circle hd.1
  have hp := extended_shift_pos hd.1
  have htp := extended_shift_pos hd.2
  have hbsq := pow_le_pow_left₀
    (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤601/1000 by linarith [hb.2,b0_bounds.2]) 2
  have hA : (47/25:ℝ)<A b+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/25) hA.le 3
  have hsource : slopeD b<59/100 := by
    dsimp [slopeD]
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  have hc0 : c0∈extendedDomain := by constructor <;> linarith [c0_bounds.1,c0_bounds.2]
  have htargetA := extended_A_antitone hc0 hd.2 (by linarith [hb.2,show b0=1-c0 from rfl])
  rw [A_c0] at htargetA
  have htargetCube := pow_le_pow_left₀ htp.le
    (show A (1-b)+1/2≤7/5 by linarith [c0_bounds.2]) 3
  have htarget : (71/50:ℝ)<slopeD (1-b) := by
    dsimp [slopeD]
    apply (lt_div_iff₀ (pow_pos htp 3)).2
    norm_num [Q0] at *
    nlinarith
  dsimp [quarterDD,FrameLowArc.u,FrameHighArc.v]
  linarith

theorem lower {b : ℝ} (hb : b∈domain) : F0-2*d0^2≤L b+G (1-b) := by
  have hb0 : b0∈domain := ⟨by linarith [b0_bounds.1],le_rfl⟩
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/4:ℝ)) (fun z hz => quarter_deriv hz)
    (fun z hz => quarterD_deriv hz) (fun z hz => (curvature hz).le) hb0 hb
  rw [quarter_initial.1,quarter_initial.2] at hh
  dsimp [quarter] at hh
  nlinarith [sq_nonneg (b-b0+4*d0)]

theorem strict_lower {b : ℝ} (hb : b∈domain) :
    (8833/10000:ℝ)<L b+G (1-b) :=
  quarter_reserve.trans_le (lower hb)

end SquaresInCircles.Eight.TableFree.FrameLowHighExtendedQuarter
