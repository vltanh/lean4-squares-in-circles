module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterSignMarkers

/-!
# The original common marker dominates `.86` times the transverse coordinate

The proof covers each complete intrinsic chart and both core pieces.
No vertex is moved and a chart-junction marker is not reselected.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign
open FrameCircleArc FrameLowArc FrameMidArc

def k : ℝ := 43/50
def m : ℝ := 111/100

theorem marker_lower (s : State) : k*s.b≤unsigned s := by
  by_cases hcore : s.branch.type=0
  · have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hcore)).2.1
    have hh := core_marker_lower s hcore
    dsimp [k]
    nlinarith [s.b_nonneg]
  · cases hb : s.branch with
    | coreSide | coreCorner => simp [hb,Branch.type] at hcore
    | low =>
        have hax := axial_loss s hcore
        have hid : (a0-s.a)*(a0+s.a+1)=s.b^2+s.b := by
          have hcircle := s.outer_eq hcore
          have haxis := CommonQuarter.axial_circle
          change (a0+1/2)^2+(1/2:ℝ)^2=Q0 at haxis
          nlinarith
        have hcut : 4*s.b≤s.a := by simpa [hb,TypeMem] using s.type_mem
        have hden : s.b+1≤(2/5)*(a0+s.a+1) := by
          nlinarith [a0_bounds.1,primary_lower s]
        have hprod := mul_le_mul_of_nonneg_left hden s.b_nonneg
        have hdenpos : 0<a0+s.a+1 := by linarith [a0_bounds.1,s.a_pos]
        have hloss : a0-s.a≤(2/5)*s.b := by
          have hh : (a0-s.a-(2/5)*s.b)*(a0+s.a+1)≤0 := by nlinarith
          have hn := (mul_nonpos_iff_of_pos_right hdenpos).1 hh
          linarith
        dsimp [unsigned]
        rw [hb]
        dsimp [FramePair.label,k]
        nlinarith [s.b_nonneg]
    | middle =>
        have hchart := state_mid_chart s hb
        have hh := linear_endpoint_lower (p := (1489593/1000000:ℝ))
          (q := (720219/1000000:ℝ)) (by norm_num) b1_mem.1 b2_mem.2 hchart.2
        have hleft : (85723/40000:ℝ)≤linear (1489593/1000000) (720219/1000000) b1 := by
          rw [linear,A_b1]
          dsimp [b1]
          nlinarith [a1_bounds.1]
        have hright : (85723/40000:ℝ)≤linear (1489593/1000000) (720219/1000000) b2 := by
          rw [linear,A_b2]
          dsimp [b2]
          nlinarith [a2_bounds.1]
        have hlow := (le_min hleft hright).trans hh
        dsimp [unsigned]
        rw [hb]
        dsimp [FramePair.label,k]
        rw [hchart.1]
        dsimp [linear] at hlow
        linarith
    | high =>
        let u : ℝ := 8898/15625
        let v : ℝ := 43/50-195443/500000
        have hsupport := state_support s u v
        have hnorm : Real.sqrt (u^2+v^2)<37/50 := by
          have hh := Real.sq_sqrt (show 0≤u^2+v^2 by positivity)
          have hz := Real.sqrt_nonneg (u^2+v^2)
          dsimp [u,v] at *
          nlinarith
        have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
        have hprod := (mul_lt_mul_of_pos_left hnorm hR).trans
          (mul_lt_mul_of_pos_right CommonQuarter.radius_bounds.2
            (by norm_num : (0:ℝ)<37/50))
        dsimp [unsigned]
        rw [hb]
        dsimp [FramePair.label,k,u,v] at *
        nlinarith [c0_bounds.1,Arithmetic.pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.GlobalOuterAnchor
