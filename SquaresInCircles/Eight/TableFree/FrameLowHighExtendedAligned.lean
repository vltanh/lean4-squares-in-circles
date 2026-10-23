module

public import SquaresInCircles.Eight.TableFree.FrameLowHighAligned

/-!
# An enlarged parallel-contact support

The analytic labels are continued slightly past the intrinsic type
cuts.  Their aligned sum still has curvature greater than `1/5` on the
entire enlarged interval.  This permits an explicit source-coordinate
comparison in the narrow parallel strip, without selecting another
physical owner or presuming a continuation inside the type arcs.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighExtendedAligned
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned

def domain : Set ℝ := Icc (7/100:ℝ) (7/20)

theorem chart_domain {b : ℝ} (hb : b∈domain) :
    b∈extendedDomain ∧ 1-b∈extendedDomain := by
  dsimp [domain,extendedDomain] at *
  constructor <;> constructor <;> linarith [hb.1,hb.2]

theorem parallel_deriv {b : ℝ} (hb : b∈domain) : HasDerivAt parallel (parallelD b) b := by
  have hd := chart_domain hb
  convert (extended_L_deriv hd.1).add
    ((extended_H_deriv hd.2).comp b ((hasDerivAt_const b (1:ℝ)).sub (hasDerivAt_id b))) using 1
  all_goals dsimp [parallel,parallelD]; ring

theorem parallelD_deriv {b : ℝ} (hb : b∈domain) :
    HasDerivAt parallelD (parallelDD b) b := by
  have hd := chart_domain hb
  convert (extended_Ld_deriv hd.1).sub
    ((extended_Hd_deriv hd.2).comp b ((hasDerivAt_const b (1:ℝ)).sub (hasDerivAt_id b))) using 1
  all_goals dsimp [parallelD,parallelDD]; ring

theorem curvature {b : ℝ} (hb : b∈domain) : (1/5:ℝ)<parallelDD b := by
  have hd := chart_domain hb
  have hc := extended_circle hd.1
  have ht := extended_circle hd.2
  have hp := extended_shift_pos hd.1
  have htp := extended_shift_pos hd.2
  have hbU : b+1/2≤17/20 := by dsimp [domain] at hb; linarith [hb.2]
  have hbsq := pow_le_pow_left₀ (by dsimp [domain] at hb; linarith [hb.1] : 0≤b+1/2) hbU 2
  have hA : (89/50:ℝ)<A b+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hAcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤89/50) hA.le 3
  have hsource : slopeD b<7/10 := by
    dsimp [slopeD]
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  have hbL : (23/20:ℝ)≤1-b+1/2 := by dsimp [domain] at hb; linarith [hb.2]
  have htbsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤23/20) hbL 2
  have htA : A (1-b)+1/2<81/50 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤81/50) hbad 2
    norm_num [Q0] at ht
    nlinarith
  have htAcube := pow_le_pow_left₀ htp.le htA.le 3
  have htarget : (91/100:ℝ)<slopeD (1-b) := by
    dsimp [slopeD]
    apply (lt_div_iff₀ (pow_pos htp 3)).2
    norm_num [Q0] at *
    nlinarith
  dsimp [parallelDD,FrameLowArc.u,FrameHighArc.u]
  linarith

theorem lower {b : ℝ} (hb : b∈domain) :
    F0-(5/2)*d0^2≤L b+H (1-b) := by
  have hb0 : b0∈domain := by constructor <;> linarith [b0_bounds.1,b0_bounds.2]
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/5:ℝ)) (fun z hz => parallel_deriv hz)
    (fun z hz => parallelD_deriv hz) (fun z hz => (curvature hz).le) hb0 hb
  rw [FrameLowHighAligned.parallel_initial.1,FrameLowHighAligned.parallel_initial.2] at hh
  dsimp [parallel] at hh
  nlinarith [sq_nonneg (b-b0+5*d0)]

theorem reserve : (8833/10000:ℝ)<F0-(5/2)*d0^2 := by
  have hd := mul_pos (sub_pos.mpr d0_bounds.2)
    (show 0<(1/10000:ℝ)+d0 by linarith [d0_bounds.1])
  nlinarith [F0_lower]

theorem strict_lower {b : ℝ} (hb : b∈domain) :
    (8833/10000:ℝ)<L b+H (1-b) := reserve.trans_le (lower hb)

end SquaresInCircles.Eight.TableFree.FrameLowHighExtendedAligned
