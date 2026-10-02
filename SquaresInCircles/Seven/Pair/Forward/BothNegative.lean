import SquaresInCircles.Seven.Pair.AxialBoundary
import SquaresInCircles.Seven.Pair.BoundaryProfiles
import SquaresInCircles.Seven.Pair.Contacts

/-!
# Seven squares: the forward axis, both signs negative

The case of a side-selected source. The target support is minimised along the
exact axial and side label segments; its circular piece is concave, and the
endpoints reduce to the transition and diagonal profiles.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def sideCircleTarget (t s : ℝ) : ℝ :=
  -(X s-1)*Real.sin (gap-t+s)+Y s*Real.cos (gap-t+s)
def sideCircleTargetD (t s : ℝ) : ℝ :=
  Real.cos (gap-t+s)+(1/Z s-1)*(X s*Real.cos (gap-t+s)+Y s*Real.sin (gap-t+s))
def sideCircleTargetDD (t s : ℝ) : ℝ :=
  -Real.sin (gap-t+s)-D s*(X s*Real.cos (gap-t+s)+Y s*Real.sin (gap-t+s))/(Z s)^3-
    (1/Z s-1)^2*(Y s*Real.cos (gap-t+s)-X s*Real.sin (gap-t+s))

lemma sideTarget_derivatives {t s : ℝ} (hs : s0 ≤ s ∧ s ≤ td) :
    HasDerivAt (sideCircleTarget t) (sideCircleTargetD t s) s ∧
    HasDerivAt (sideCircleTargetD t) (sideCircleTargetDD t s) s := by
  have ha : HasDerivAt (fun x : ℝ => gap-t+x) 1 s := (hasDerivAt_id' s).const_add (gap-t)
  have hz : Z s ≠ 0 := ne_of_gt (Z_pos hs)
  have h1 := (((hasDerivAt_X hs).sub_const 1).neg.mul ha.sin).add
    ((hasDerivAt_Y hs).mul ha.cos)
  have h2 := ha.cos.add
    (((((hasDerivAt_const s (1:ℝ)).div (hasDerivAt_Z hs) hz).sub_const 1)).mul
      (((hasDerivAt_X hs).mul ha.cos).add ((hasDerivAt_Y hs).mul ha.sin)))
  constructor
  · convert h1 using 1
    · rfl
    · dsimp [sideCircleTargetD]
      field_simp [hz]
      ring
  · convert h2 using 1
    · rfl
    · dsimp [sideCircleTargetD,sideCircleTargetDD]
      field_simp [hz]
      ring

lemma sideTarget_concave_second {t s : ℝ}
    (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4) (hs : s0 ≤ s ∧ s ≤ td) :
    sideCircleTargetDD t s ≤ 0 := by
  let d := gap-t+s
  have hd : Real.pi/6 < d ∧ d < Real.pi/2 := by
    have hc := transition_coarse
    dsimp [d,gap]
    constructor <;> linarith [ht.1,ht.2,hs.1,hs.2,td_bounds.2,pi_lt_22_over_7]
  have hC := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hd.1,Real.pi_pos],hd.2.le⟩
  have hS : 1/2 < Real.sin d := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) hd.2.le hd.1
  have hb := circle_bounds hs
  have hZ0 : 0 < Z s := Z_pos hs
  have hZlow : 1 < Z s := hb.2.2.2.2.2.1
  have hZhigh : Z s < 7/5 := hb.2.2.2.2.2.2
  have hr : -(2/7:ℝ) < 1/Z s-1 ∧ 1/Z s-1 ≤ 0 := by
    have hlo : 5/7 < 1/Z s := (lt_div_iff₀ hZ0).mpr (by linarith)
    have hhi : 1/Z s ≤ 1 := (div_le_one hZ0).mpr hZlow.le
    constructor <;> linarith
  have hr2 : (1/Z s-1)^2 ≤ (2/7:ℝ)^2 := sq_le_sq' hr.1.le (by linarith [hr.2])
  have hK := dot_ge (p := -Real.sin d) (r := Real.cos d) (c := 2)
    (le_of_eq (circle_identities hs).1) (by norm_num)
    (by unfold targetSq; linarith [Real.sin_sq_add_cos_sq d])
  have hm := mul_nonneg (sq_nonneg (1/Z s-1))
    (show 0 ≤ Y s*Real.cos d-X s*Real.sin d+2 by linarith)
  have hdot : 0 ≤ X s*Real.cos d+Y s*Real.sin d :=
    add_nonneg (mul_nonneg (by linarith [hb.2.2.2.1]) hC) (mul_nonneg hb.1.le (by linarith))
  have hterm : 0 ≤ D s*(X s*Real.cos d+Y s*Real.sin d)/(Z s)^3 := by
    have hD0 : 0 ≤ D s := by linarith [(D_range hs).1]
    positivity
  dsimp [sideCircleTargetDD]
  change -Real.sin d-D s*(X s*Real.cos d+Y s*Real.sin d)/(Z s)^3-
    (1/Z s-1)^2*(Y s*Real.cos d-X s*Real.sin d) ≤ 0
  linarith

lemma sideTarget_at_transition (t : ℝ) : sideCircleTarget t s0=circleTarget t s0 := by
  have hx : X s0=a0+1/2 := by
    have hh : sideA s0=a0 := side_at_transition.1
    dsimp [sideA] at hh
    linarith
  have hy : Y s0=Y0 := by
    have hh : sideU s0=u0 := side_at_transition.2
    dsimp [sideU,u0] at hh
    linarith
  rw [circleTarget_transition]
  dsimp [sideCircleTarget]
  rw [hx,hy]
  ring

lemma diagonal_target_pos {a u s : ℝ}
    (h : Admissible a u) (hT : label a u=side a u)
    (ht : 2/5 ≤ label a u) (hs : td ≤ s ∧ s ≤ Real.pi/4) :
    0 < 1/2-u-(diagonal s-1/2)*Real.sin (gap-label a u+s)+
      (diagonal s+1/2)*Real.cos (gap-label a u+s) := by
  let t := label a u
  let d := gap-t+s
  let e := 7*Real.pi/12-t
  have hq := h.label_le_quarter
  have hd : Real.pi/4 ≤ d ∧ d ≤ e := by
    dsimp [d,e,gap]
    constructor <;> linarith [td_bounds.1,hs.1,hs.2,hq,pi_lt_22_over_7]
  have he : e < Real.pi/2 := by dsimp [e]; linarith [ht,pi_lt_22_over_7]
  have hS := Real.sin_nonneg_of_nonneg_of_le_pi (x := d)
    (by linarith [hd.1,Real.pi_pos]) (by linarith [hd.2,he,Real.pi_pos])
  have hC := Real.cos_nonneg_of_mem_Icc (x := d)
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,he]⟩
  have hCS := cos_le_sin_of_quarter ⟨hd.1,by linarith [hd.2,he]⟩
  have hdia : diagonal s < 31/40 := by
    have heq := diagonal_td
    have hh : diagonal s ≤ diagonal td := by dsimp [diagonal]; linarith [hs.1]
    rw [heq] at hh
    linarith [rd_bounds.2]
  have hp := mul_nonneg (show 0 ≤ 31/40-diagonal s by linarith)
    (show 0 ≤ Real.sin d-Real.cos d by linarith)
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hd.1,Real.pi_pos])
    (by linarith [he,Real.pi_pos]) hd.2
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hd.1,Real.pi_pos]) he.le hd.2
  have hu : u ≤ 1/2+(6/5)*(t-Real.pi/6) := by
    have hh := side_identity_transverse a u
    rw [← hT] at hh
    change t=_ at hh
    linarith [h.remainder_nonneg]
  have hk := diagonalK_pos ⟨ht,hq⟩
  dsimp [diagonalK] at hk
  change 0 < 1/2-u-(diagonal s-1/2)*Real.sin d+(diagonal s+1/2)*Real.cos d
  change 0 < (6/5)*(Real.pi/6-t)+(51/40)*Real.cos e-(11/40)*Real.sin e at hk
  linarith

lemma upper_target_pos {a u s : ℝ}
    (h : Admissible a u) (hT : label a u=side a u)
    (ht : 2/5 ≤ label a u) (hs : s0 ≤ s ∧ s ≤ Real.pi/4) :
    0 < 1/2-u+vertexTarget (label a u) s := by
  let t := label a u
  by_cases hsc : s ≤ td
  · let f : ℝ → ℝ := fun x => 1/2-u+sideCircleTarget t x
    have hd (x : ℝ) (hx : x ∈ Icc s0 td) : HasDerivAt f (sideCircleTargetD t x) x :=
      (sideTarget_derivatives hx).1.const_add (1/2-u)
    have hlo : 0 < f s0 := by
      dsimp [f]
      rw [sideTarget_at_transition,circleTarget_transition]
      linarith [transition_actual_pos h hT ht]
    have hhi : 0 < f td := by
      have hh := diagonal_target_pos h hT ht ⟨le_rfl,td_bounds.2.le⟩
      have hX : X td=rd+1/2 := by
        have ha := side_at_diagonal.1
        dsimp [sideA] at ha
        linarith
      have hY : Y td=rd+1/2 := by
        have hb := side_at_diagonal.2
        dsimp [sideU] at hb
        linarith
      rw [diagonal_td] at hh
      dsimp [f,sideCircleTarget]
      rw [hX,hY]
      linarith
    have hp := positive_of_second_nonpos ⟨hs.1,hsc⟩ hd
      (fun x hx => (sideTarget_derivatives hx).2)
      (fun x hx => sideTarget_concave_second ⟨ht,h.label_le_quarter⟩ hx) hlo hhi
    simp only [vertexTarget,sideTopA,sideTopU,ite_eq_left hsc,sideA,sideU]
    dsimp [f,sideCircleTarget] at hp
    linarith
  · simp only [vertexTarget,sideTopA,sideTopU,ite_eq_right hsc]
    linarith [diagonal_target_pos h hT ht ⟨(lt_of_not_ge hsc).le,hs.2⟩]

lemma target_side_pos {a u A v : ℝ}
    (h : Admissible a u) (hT : label a u=side a u) (ht : 2/5 ≤ label a u)
    (h' : Admissible A v) (hT' : label A v=side A v) :
    0 < 1/2-u-(A-1/2)*Real.sin (gap-label a u+label A v)+
      (v+1/2)*Real.cos (gap-label a u+label A v) := by
  let t := label a u
  let s := label A v
  let d := gap-t+s
  have ht' : 2/5 ≤ t ∧ t ≤ Real.pi/4 := ⟨ht,h.label_le_quarter⟩
  have hs : s0 ≤ s ∧ s ≤ Real.pi/4 :=
    ⟨(side_state_transition_bounds h' hT').2.2,h'.label_le_quarter⟩
  have hd : 0 ≤ d ∧ d ≤ Real.pi/2 := by
    have hc := transition_coarse
    dsimp [d,gap]
    constructor <;> linarith [ht'.1,ht'.2,hs.1,hs.2,pi_lt_22_over_7,Real.pi_gt_d2]
  have seg := side_segment h' hT'
  have heq : -(A-1/2)*Real.sin d+(v+1/2)*Real.cos d-lineTarget t s =
      (v-(4/5)*s)*(Real.cos d-(4/9)*Real.sin d) := by
    have hh := seg.2.2
    change A=tieA s+(4/9)*(v-(4/5)*s) at hh
    rw [hh]
    dsimp [lineTarget,d]
    ring
  by_cases hc : s ≤ switchLabel t
  · have hcoef : 0 ≤ Real.cos d-(4/9)*Real.sin d :=
      (switch_iff hd).mpr (by dsimp [d,switchLabel] at *; linarith)
    have hm := mul_nonneg (show 0 ≤ v-(4/5)*s by linarith [seg.1]) hcoef
    have hl := lineTarget_low_min ht' hs hc
    have hp : 0 < 1/2-u+circleTarget t s0 := by
      rw [circleTarget_transition]
      linarith [transition_actual_pos h hT ht]
    change 0 < 1/2-u-(A-1/2)*Real.sin d+(v+1/2)*Real.cos d
    linarith
  · have hp := upper_target_pos h hT ht hs
    have hcoef : Real.cos d-(4/9)*Real.sin d ≤ 0 := by
      by_contra hn
      have hle := (switch_iff hd).mp (le_of_lt (lt_of_not_ge hn))
      dsimp [d,switchLabel] at *
      linarith
    have htopline := tie_of_side (sideTop_state hs).2.2
    have heqtop : vertexTarget t s-lineTarget t s =
        (sideTopU s-(4/5)*s)*(Real.cos d-(4/9)*Real.sin d) := by
      dsimp [vertexTarget]
      rw [htopline]
      dsimp [lineTarget,d]
      ring
    have hm := mul_nonneg (show 0 ≤ sideTopU s-v by linarith [seg.2.1]) (neg_nonneg.mpr hcoef)
    change 0 < 1/2-u-(A-1/2)*Real.sin d+(v+1/2)*Real.cos d
    linarith

lemma target_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (hT : label a u=side a u) (ht : 2/5 ≤ label a u)
    (h' : Admissible A v) (hA' : label A v=axial v) :
    0 < 1/2-u-(A-1/2)*Real.sin (gap-label a u+label A v)+
      (v+1/2)*Real.cos (gap-label a u+label A v) := by
  let t := label a u
  let s := label A v
  have hs0 : 0 ≤ s := h'.label_nonneg
  have hs1 : s ≤ Real.pi/4 := h'.label_le_quarter
  have hv : v=(4/5)*s := by dsimp [s]; rw [hA']; dsimp [axial]; ring
  have hdelta : 0 ≤ gap-t+s ∧ gap-t+s ≤ Real.pi/2 := by
    dsimp [t,s,gap]
    constructor <;> linarith [h.label_le_quarter,hs0,hs1,ht,pi_lt_22_over_7,Real.pi_pos]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hdelta.1 (by linarith [hdelta.2,Real.pi_pos])
  have hup := axial_upper h' hA'
  by_cases hs : s ≤ s0
  · have hvc : 0 ≤ v ∧ v ≤ u0 := by rw [hv]; dsimp [s0] at hs; constructor <;> linarith
    rw [axialTop_left hvc] at hup
    have hm := mul_nonneg (sub_nonneg.mpr hup) hsin
    have hbound := circleTarget_decreases ⟨ht,h.label_le_quarter⟩
      ⟨hs0,hs⟩ ⟨by linarith [transition_coarse.2.2.2.2.1],le_rfl⟩ hs
    have hp : 0 < 1/2-u+circleTarget t s0 := by
      rw [circleTarget_transition]
      linarith [transition_actual_pos h hT ht]
    have hX : axialX s=circle v+1/2 := by
      rw [hv]
      dsimp only [axialX,circle]
      rw [add_comm (1/2:ℝ) ((4/5)*s)]
      ring
    have hY : axialY s=v+1/2 := by rw [hv]; dsimp only [axialY]; ring
    have hcs : circleTarget t s ≤
        -(A-1/2)*Real.sin (gap-t+s)+(v+1/2)*Real.cos (gap-t+s) := by
      dsimp only [circleTarget]
      rw [hX,hY]
      linarith
    change 0 < 1/2-u-(A-1/2)*Real.sin (gap-t+s)+(v+1/2)*Real.cos (gap-t+s)
    linarith
  · have hs' : s0 ≤ s := (lt_of_not_ge hs).le
    have hvr : v ≤ rd := by rw [hv]; linarith [hs1,pi_lt_22_over_7,rd_bounds.1]
    have hvu : u0 ≤ v := by rw [hv]; dsimp [s0] at hs'; linarith
    rw [axialTop_right ⟨hvu,hvr⟩] at hup
    have he : axialLine v=tieA s := by rw [hv]; dsimp [axialLine,tieA]; ring
    rw [he] at hup
    obtain ⟨hstate,hlabel,hside⟩ := tie_state ⟨hs',hs1⟩
    have hp := target_side_pos h hT ht hstate (hlabel.trans hside.symm)
    rw [hlabel] at hp
    have hm := mul_nonneg (sub_nonneg.mpr hup) hsin
    change 0 < 1/2-u-(A-1/2)*Real.sin (gap-t+s)+(v+1/2)*Real.cos (gap-t+s)
    rw [hv]
    linarith

end Boundary

lemma forward_negative_negative_small {a u A v : ℝ}
    (h : Admissible a u) (hT : label a u=side a u)
    (ht : label a u ≤ 2/5) (h' : Admissible A v) :
    0 < pairSupport a u A v .negative .negative 1 gap := by
  let t := label a u
  let s := label A v
  have hmarker := marker_arc_support h' .negative (x := -s-1/2)
    (by rw [abs_le]; dsimp [s,TransverseSign.coe]; constructor <;> linarith)
    (3*Real.pi/2-gap+t-s)
  have hang : 3*Real.pi/2-gap+t-s-(-s-1/2)=2*Real.pi-(5*Real.pi/6-t-1/2) := by dsimp [gap]; ring
  rw [hang,Real.cos_two_pi_sub] at hmarker
  have he : Real.cos (5*Real.pi/6-t-1/2) = -Real.sin (Real.pi/3-t-1/2) := by
    rw [show 5*Real.pi/6-t-1/2=Real.pi/2+(Real.pi/3-t-1/2) by ring,Real.cos_add]
    simp
  rw [he] at hmarker
  have harg : 0 ≤ Real.pi/3-t-1/2 := by dsimp [t]; linarith [ht,Real.pi_gt_d2]
  have hsin := Real.sin_le harg
  have hside := side_identity_transverse a u
  rw [← hT] at hside
  change t=_ at hside
  rw [pairSupport_one]
  simp only [TransverseSign.coe,neg_one_mul,sub_neg_eq_add]
  change 0 < 1/2-u+support A (-v) (3*Real.pi/2-gap+t-s)
  simp only [TransverseSign.coe,neg_one_mul] at hmarker
  linarith [h.remainder_nonneg,pi_lt_22_over_7]

/-- On the forward axis with both signs negative, the support sum is positive at
the gap `π/3` when the first label is the side term and the second is axial or
side. -/
theorem fixed_gap_forward_both_negative_side {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hactive : ActiveLabel A v) :
    0 < pairSupport a u A v .negative .negative 1 gap := by
  by_cases hs : label a u ≤ 2/5
  · exact forward_negative_negative_small h hT hs h'
  have ht : 2/5 ≤ label a u := (lt_of_not_ge hs).le
  let d := gap-label a u+label A v
  have hd : 0 < d ∧ d < Real.pi/2 := by
    have h0 := h.label_le_quarter
    have h1 := h'.label_nonneg
    have h2 := h'.label_le_quarter
    dsimp [d,gap]
    constructor <;> linarith [ht,pi_lt_22_over_7,Real.pi_pos]
  have hS := Real.sin_nonneg_of_nonneg_of_le_pi hd.1.le (by linarith [hd.2,Real.pi_pos])
  have hC := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hd.1,Real.pi_pos],hd.2.le⟩
  have hid : pairSupport a u A v .negative .negative 1 gap=
      1/2-u-(A-1/2)*Real.sin d+(v+1/2)*Real.cos d := by
    rw [pairSupport_one]
    simp only [TransverseSign.coe,neg_one_mul,sub_neg_eq_add]
    rw [show 3*Real.pi/2-gap+label a u+-label A v=3*Real.pi/2-d by dsimp [d]; ring,
      support_three_half_sub,abs_of_nonneg hS,abs_of_nonneg hC]
    ring
  rw [hid]
  rcases hactive with hA | hT'
  · exact Boundary.target_axial_pos h hT ht h' hA
  · exact Boundary.target_side_pos h hT ht h' hT'

end SquaresInCircles.Seven
