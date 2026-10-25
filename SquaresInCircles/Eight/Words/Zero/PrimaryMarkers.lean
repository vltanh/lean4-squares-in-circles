module

public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Frames.Core.Arc

/-!
# Eight squares: whole-chart coarse supports for the unchanged G1 frame marker

The low, middle and high outer labels are bounded on their complete
intrinsic arcs. The middle and high endpoint rules use the original
positive circle branch; the other estimates are full-circle supports.
The same selected label remains attached to each original vertex.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ZeroPrimary

open FramePair FrameCircleArc FrameLowArc FrameMidArc

def unsigned (s : State) : ℝ := FramePair.label s.branch s.a s.b

lemma outer_data (s : State) (hs : s.branch.type≠0) :
    CommonQuarter.OuterState s.a s.b := ⟨s.b_nonneg,s.canonical,s.outer_eq hs⟩

lemma axial_loss (s : State) (hs : s.branch.type≠0) :
    0≤a0-s.a ∧ a0-s.a≤(3/5)*s.b := by
  have hb := CommonQuarter.outer_bounds (outer_data s hs)
  have hau : s.a≤a0 := hb.2.1
  have hid : (a0-s.a)*(a0+s.a+1)=s.b^2+s.b := by
    have hcircle := s.outer_eq hs
    have haxis := CommonQuarter.axial_circle
    change (a0+1/2)^2+(1/2:ℝ)^2=Q0 at haxis
    nlinarith
  have hden : (33/10:ℝ)≤a0+s.a+1 := by
    have ha := hb.1
    change c0≤ s.a at ha
    linarith [a0_bounds.1,c0_bounds.1]
  have hbU : s.b≤9/10 := s.b_upper
  have h₁ := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hau)
  have h₂ := mul_le_mul_of_nonneg_left (show s.b+1≤19/10 by linarith) s.b_nonneg
  exact ⟨sub_nonneg.mpr hau,by nlinarith [s.b_nonneg]⟩

lemma low_marker_bounds (s : State) (hs : s.branch=.low) :
    (4/5)*s.b≤unsigned s ∧ unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  have ht : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := axial_loss s ht
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label]
  constructor <;> nlinarith [s.b_nonneg]

lemma middle_marker_lower (s : State) (hs : s.branch=.middle) :
    (4/5)*s.b≤unsigned s := by
  have hb := state_mid_chart s hs
  have hh := linear_endpoint_lower (p := (1489593/1000000:ℝ))
    (q := (780219/1000000:ℝ)) (by norm_num) b1_mem.1 b2_mem.2 hb.2
  have hleft : (85723/40000:ℝ)≤linear (1489593/1000000) (780219/1000000) b1 := by
    rw [linear,A_b1]
    dsimp [b1]
    nlinarith [a1_bounds.1]
  have hright : (85723/40000:ℝ)≤linear (1489593/1000000) (780219/1000000) b2 := by
    rw [linear,A_b2]
    dsimp [b2]
    nlinarith [a2_bounds.1]
  have hlow := (le_min hleft hright).trans hh
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label]
  rw [hb.1]
  dsimp [linear] at hlow
  linarith

lemma middle_marker_upper (s : State) (hs : s.branch=.middle) :
    unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  let u : ℝ := 1089593/1000000
  let v : ℝ := 470219/1000000
  have hcircle := CommonQuarter.outer_circle_lower (X := -u) (Y := -v)
    (outer_data s (by simp [hs,Branch.type]))
  have hnorm : Real.sqrt (u^2+v^2)<1187/1000 := by
    have hh := Real.sq_sqrt (show 0≤u^2+v^2 by positivity)
    have hn := Real.sqrt_nonneg (u^2+v^2)
    dsimp [u,v] at *
    nlinarith
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hnorm hR).trans
    (mul_lt_mul_of_pos_right CommonQuarter.radius_bounds.2
      (by norm_num : (0:ℝ)<1187/1000))
  simp only [neg_sq] at hcircle
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label,u,v] at *
  nlinarith [a0_bounds.2]

lemma state_high_chart (s : State) (hs : s.branch=.high) :
    s.a=A s.b ∧ s.b∈Icc b2 c0 := by
  have ht : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := state_outer_chart s ht
  have hcut : 3*s.a≤7*s.b := by simpa [hs,TypeMem] using s.type_mem
  refine ⟨hh.1,?_,hh.2.2⟩
  by_contra! hn
  have ha := A_antitone hh.2 b2_mem hn.le
  rw [A_b2,← hh.1] at ha
  have hendpoint : 3*a2=7*b2 := by dsimp [b2]; ring
  nlinarith

lemma high_marker_lower (s : State) (hs : s.branch=.high) :
    (4/5)*s.b≤unsigned s := by
  let f : ℝ := 8898/15625
  let r : ℝ := 195443/500000
  have hcircle := CommonQuarter.outer_circle_lower (X := -f) (Y := -(4/5-r))
    (outer_data s (by simp [hs,Branch.type]))
  have hnorm : Real.sqrt (f^2+(4/5-r)^2)<71/100 := by
    have hh := Real.sq_sqrt (show 0≤f^2+(4/5-r)^2 by positivity)
    have hn := Real.sqrt_nonneg (f^2+(4/5-r)^2)
    dsimp [f,r] at *
    nlinarith
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hnorm hR).trans
    (mul_lt_mul_of_pos_right (show CommonQuarter.radius<2 by linarith [CommonQuarter.radius_bounds.2])
      (by norm_num : (0:ℝ)<71/100))
  simp only [neg_sq] at hcircle
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label,f,r] at *
  nlinarith [c0_bounds.1,Arithmetic.pi_hand_enclosure.1]

lemma high_marker_upper (s : State) (hs : s.branch=.high) :
    unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  let u : ℝ := 8898/15625+2/5
  let v : ℝ := 111/100-195443/500000
  let C0 : ℝ := Real.pi/4+(8898/15625-195443/500000)*c0+(2/5)*a0
  let Cup : ℝ := 11/14+(8898/15625-195443/500000)*(9/10)+(2/5)*(283/200)
  have hC : C0<Cup := by
    dsimp [C0,Cup]
    nlinarith [pi_lt_22_over_7,c0_bounds.2,a0_bounds.2]
  have hb := state_high_chart s hs
  have hh := linear_endpoint_lower (p := u) (q := v)
    (by norm_num [u]) b2_mem.1 le_rfl hb.2
  have hleft : Cup<linear u v b2 := by
    rw [linear,A_b2]
    dsimp [Cup,u,v,b2]
    nlinarith [a2_bounds.1]
  have hright : Cup<linear u v c0 := by
    rw [linear,A_c0]
    dsimp [Cup,u,v]
    nlinarith [c0_bounds.1]
  have hlow : C0<linear u v s.b := hC.trans_le
    ((lt_min hleft hright).le.trans hh)
  dsimp [unsigned]
  rw [hs]
  dsimp [FramePair.label,C0,u,v,linear] at *
  rw [hb.1]
  nlinarith

/-- Both bounds hold for every original outer chart, including both choices
at either type junction. -/
theorem outer_marker_bounds (s : State) (hs : s.branch.type≠0) :
    (4/5)*s.b≤unsigned s ∧ unsigned s≤(2/5)*(s.a-a0)+(111/100)*s.b := by
  cases hb : s.branch with
  | coreSide | coreCorner => simp [hb,Branch.type] at hs
  | low => exact low_marker_bounds s hb
  | middle => exact ⟨middle_marker_lower s hb,middle_marker_upper s hb⟩
  | high => exact ⟨high_marker_lower s hb,high_marker_upper s hb⟩

theorem core_marker_lower (s : State) (hs : s.branch.type=0) :
    7*(7/12-s.a)+(107/100)*s.b≤unsigned s := by
  have hh := FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hs)
  have hA : 0≤7/12-s.a := by linarith [hh.2.1]
  have hB := s.b_nonneg
  cases hb : s.branch <;> simp [hb,Branch.type] at hs
  all_goals dsimp [unsigned]; rw [hb]; dsimp [FramePair.label]; nlinarith

theorem marker_nonneg (s : State) : 0≤unsigned s := by
  by_cases hc : s.branch.type=0
  · have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).2.1
    nlinarith [core_marker_lower s hc,s.b_nonneg]
  · nlinarith [(outer_marker_bounds s hc).1,s.b_nonneg]

theorem signed_upper (s : State) : s.signedLabel≤unsigned s := by
  have hh : 0≤FramePair.label s.branch s.a s.b := marker_nonneg s
  cases hp : s.positive
  · simp only [State.signedLabel,unsigned,hp,FramePair.sign,Bool.false_eq_true,ite_false]
    linarith
  · simp [State.signedLabel,unsigned,hp,FramePair.sign]

end SquaresInCircles.Eight.ZeroPrimary
