import SquaresInCircles.Seven.Contacts

/-!
# The forward axis, signs `(-, +)`

In the turn `w = label a u + label A v - π/3` the support sum is
`1/2 - u + A sin w - v cos w + (|sin w| + cos w)/2`. For two side labels,
Cauchy–Schwarz on both disks with a certificate tight only at zero turn bounds
it below by `0`, so it vanishes only at two side states. For the other active
labels a linear clearance between the labels and one-variable profiles in the
turn make it positive.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

def sideSideSupport (u A v w : ℝ) : ℝ :=
  1/2-u+A*Real.sin w-v*Real.cos w+(|Real.sin w|+Real.cos w)/2

/-- The turn of two labels on the forward axis with signs `(-, +)`. -/
lemma forward_turn_range {a u A v : ℝ} (h : Admissible a u) (h' : Admissible A v) :
    -Real.pi/3 ≤ label a u+label A v-gap ∧ label a u+label A v-gap ≤ Real.pi/6 := by
  obtain ⟨h0,h2⟩ := h.label_mem
  obtain ⟨h1,h3⟩ := h'.label_mem
  dsimp [gap]
  constructor <;> linarith

lemma pairSupport_forward_opposite {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .negative .positive 1 gap =
      sideSideSupport u A v (label a u+label A v-gap) := by
  have hw := forward_turn_range h h'
  have hc : 0 ≤ Real.cos (label a u+label A v-gap) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have he : 3*Real.pi/2-gap-TransverseSign.negative.coe*label a u+
      TransverseSign.positive.coe*label A v = 3*Real.pi/2-(-(label a u+label A v-gap)) := by
    simp only [TransverseSign.coe]
    ring
  rw [pairSupport_one,he,support_three_half_sub,Real.sin_neg,Real.cos_neg,abs_neg,
    abs_of_nonneg hc]
  simp only [sideSideSupport,TransverseSign.coe]
  ring

/-! ### Two side labels -/

def sideSideL (w : ℝ) : ℝ :=
  19/20+Real.cos w-min (Real.sin w) 0-(6/5)*w

lemma sideSideL_pos {w : ℝ} (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    0 < sideSideL w := by
  have hpi := Real.pi_lt_d4
  by_cases h : 0 ≤ w
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hw.2,Real.pi_pos])
    have hc := Real.one_sub_sq_div_two_le_cos (x := w)
    have hw' : w < 8/15 := by linarith [hw.2]
    unfold sideSideL
    rw [min_eq_right hs]
    nlinarith
  · have hz : 0 ≤ -w ∧ -w ≤ Real.pi/3 := ⟨by linarith,by linarith [hw.1]⟩
    have hc := cos_ge_half hz
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_pos])
    rw [Real.sin_neg] at hs
    rw [Real.cos_neg] at hc
    unfold sideSideL
    rw [min_eq_left (by linarith)]
    linarith

lemma sideSide_margin_pos {w : ℝ}
    (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) (hne : w ≠ 0) :
    0 < (sideSideL w)^2-targetSq*((Real.sin w-9/10)^2+(2/5-Real.cos w)^2) := by
  have hpi := Real.pi_lt_d4
  by_cases h : 0 < w
  · have hw' : w ≤ 8/15 := by linarith [hw.2]
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h.le (by linarith [hw.2,Real.pi_pos])
    have hs := Real.sin_ge_sub_cube h.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := w)
    have hcu := cos_upper_four h.le
    have hxc := mul_le_mul_of_nonneg_left hcu h.le
    have hc2 : 1-w^2 ≤ Real.cos w^2 := by
      linarith [Real.sin_sq_le_sq (x := w), Real.sin_sq_add_cos_sq w]
    have hpoly :
        w*(468-724*w+90*w^2-40*w^4) ≤
        (19+20*Real.cos w-24*w)^2-
          13*(197-180*Real.sin w-80*Real.cos w) := by
      linarith
    have hw4 : w^4 ≤ (8/15 : ℝ)^4 := by gcongr
    have hp : 0 < 468-724*w+90*w^2-40*w^4 := by
      linarith [sq_nonneg w]
    have hn := mul_pos h hp
    have hid :
        400*((sideSideL w)^2-targetSq*((Real.sin w-9/10)^2+(2/5-Real.cos w)^2)) =
        (19+20*Real.cos w-24*w)^2-
          13*(197-180*Real.sin w-80*Real.cos w) := by
      unfold sideSideL targetSq
      rw [min_eq_right hs0]
      linear_combination (-1300)*Real.sin_sq_add_cos_sq w
    linarith
  · let z := -w
    have hz : 0 < z := by dsimp [z]; linarith [lt_of_le_of_ne (not_lt.mp h) hne]
    have hzu : z ≤ Real.pi/3 := by dsimp [z]; linarith [hw.1]
    have hz9 : z < 9/8 := by linarith
    have hc := cos_ge_half ⟨hz.le,hzu⟩
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.le (by linarith [hzu,Real.pi_pos])
    have hsU := Real.sin_le hz.le
    have hsL := Real.sin_ge_sub_cube hz.le
    have hcL := Real.one_sub_sq_div_two_le_cos (x := z)
    have hp1 := mul_nonneg (show 0 ≤ Real.cos z-1/2 by linarith) hs0
    have hp2 := mul_nonneg (show 0 ≤ Real.cos z-1/2 by linarith) hz.le
    have hp3 := mul_le_mul_of_nonneg_left hsL hz.le
    let N := 800*Real.cos z*Real.sin z+960*z*Real.cos z+
      1800*(Real.cos z-1)+960*z*Real.sin z-1580*Real.sin z+576*z^2+912*z
    have hN : z*(212+z*(636-160*z^2)) ≤ N := by
      dsimp [N]
      linarith
    have hp : 0 < 212+z*(636-160*z^2) := by
      have hi : 0 < 636-160*z^2 := by nlinarith
      have hm := mul_nonneg hz.le hi.le
      linarith
    have hn := mul_pos hz hp
    have hid : 400*((sideSideL w)^2-targetSq*((Real.sin w-9/10)^2+(2/5-Real.cos w)^2)) = N := by
      have he : w = -z := by dsimp [z]; ring
      rw [he]
      unfold sideSideL targetSq
      rw [Real.cos_neg,Real.sin_neg,min_eq_left (neg_nonpos.mpr hs0)]
      dsimp [N]
      linear_combination (-900)*Real.sin_sq_add_cos_sq z
    linarith

/-- Cauchy–Schwarz on both disks: the side–side sum is nonnegative, and zero only
at two side states. -/
theorem side_side_property {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hT' : label A v = side A v) :
    0 ≤ sideSideSupport u A v (label a u+label A v-gap) ∧
      (sideSideSupport u A v (label a u+label A v-gap) = 0 → SideState a u ∧ SideState A v) := by
  let w := label a u+label A v-gap
  have hr := forward_turn_range h h'
  have hL := sideSideL_pos hr
  have hid : sideSideSupport u A v w = sideSideL w+39/20+
      ((-9/10)*(a+1/2)+(-3/5)*(u+1/2))+
      ((Real.sin w-9/10)*(A+1/2)+(2/5-Real.cos w)*(v+1/2)) := by
    have hw : w = side a u+side A v-gap := by simp only [w,hT,hT']
    have habs : |Real.sin w| = Real.sin w-2*min (Real.sin w) 0 := by
      rcases le_total 0 (Real.sin w) with hs | hs
      · rw [abs_of_nonneg hs,min_eq_right hs]; ring
      · rw [abs_of_nonpos hs,min_eq_left hs]; ring
    unfold sideSideSupport sideSideL
    rw [habs]
    dsimp [side,gap] at hw
    linear_combination (6/5)*hw
  have hfirst := dot_ge (p := -9/10) (r := -3/5) (c := 39/20) h.phi_le (by norm_num)
    (by norm_num [targetSq])
  have hmargin (hw : w ≠ 0) :
      targetSq*((Real.sin w-9/10)^2+(2/5-Real.cos w)^2) < (sideSideL w)^2 := by
    linarith [sideSide_margin_pos hr hw]
  have hsecond := dot_ge (p := Real.sin w-9/10) (r := 2/5-Real.cos w) (c := sideSideL w)
    h'.phi_le hL.le (by
      by_cases hw : w = 0
      · rw [hw]; norm_num [sideSideL,targetSq]
      · exact (hmargin hw).le)
  change 0 ≤ sideSideSupport u A v w ∧ (sideSideSupport u A v w = 0 → _)
  refine ⟨by linarith,fun hz => ?_⟩
  have hw0 : w = 0 := by
    by_contra hw
    linarith [dot_gt (p := Real.sin w-9/10) (r := 2/5-Real.cos w) h'.phi_le hL.le (hmargin hw)]
  have hsum : side a u+side A v = gap := by rw [← hT,← hT']; linarith [hw0]
  rw [hid,hw0] at hz
  norm_num [sideSideL] at hz
  have hrem : remainder a u+remainder A v = 0 := by
    unfold side gap at hsum
    unfold remainder
    linarith
  exact ⟨remainder_zero h (by linarith [h.remainder_nonneg,h'.remainder_nonneg]),
    remainder_zero h' (by linarith [h.remainder_nonneg,h'.remainder_nonneg])⟩

/-- The side–side sum vanishes only at two side states. -/
lemma side_side_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hT' : label A v = side A v)
    (hz : sideSideSupport u A v (label a u+label A v-gap) = 0) :
    SideState a u ∧ SideState A v :=
  (side_side_property h h' hT hT').2 hz

/-! ### Axial labels -/

lemma forward_turn_nonneg {w : ℝ} (hw : 0 ≤ w ∧ w ≤ Real.pi/6) :
    0 ≤ Real.sin w-(4/5)*w-(1/2)*(1-Real.cos w) := by
  have hlim : w ≤ 8/15 := by linarith [hw.2,pi_lt_22_over_7]
  have hs := Real.sin_ge_sub_cube hw.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := w)
  have hsq : w^2 ≤ (8/15 : ℝ)^2 := by nlinarith [hw.1]
  have hp : 0 ≤ 1/5-w/4-w^2/6 := by linarith
  have hm := mul_nonneg hw.1 hp
  linarith

lemma opposite_support_positive_turn {u A v w : ℝ}
    (hA : 1/2 ≤ A) (hv : 0 ≤ v) (hw : 0 ≤ w ∧ w ≤ Real.pi/6) :
    1-u-v+Real.sin w-(1/2)*(1-Real.cos w) ≤ sideSideSupport u A v w := by
  have hs : 0 ≤ Real.sin w := Real.sin_nonneg_of_nonneg_of_le_pi hw.1
    (by linarith [hw.2,Real.pi_pos])
  have hc : 0 ≤ 1-Real.cos w := sub_nonneg.mpr (Real.cos_le_one w)
  have hp := mul_nonneg (show 0 ≤ A-1/2 by linarith) hs
  have hp' := mul_nonneg hv hc
  dsimp [sideSideSupport]
  rw [abs_of_nonneg hs]
  linarith

lemma opposite_support_negative_turn {u A v z : ℝ}
    (h' : Admissible A v) (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    1-u-v-(A-1/2)*Real.sin z-(1/2)*(1-Real.cos z) ≤
      sideSideSupport u A v (-z) := by
  have hs : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,Real.pi_pos])
  have hc : 0 ≤ 1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hp := mul_nonneg h'.u_nonneg hc
  dsimp [sideSideSupport]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs]
  linarith

lemma opposite_axial_scalar {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    0 < 1-4*Real.pi/15+(4/5)*z-(Real.sqrt 3-1)*Real.sin z
      -(1/2)*(1-Real.cos z) := by
  have hz1 : z ≤ 11/10 := by linarith [hz.2,pi_lt_22_over_7]
  have hp : 0 < 17/105+z/20-z^2/4+7*z^3/60-z^5/160 :=
    bernstein_pos (p := fun z => 17/105+z/20-z^2/4+7*z^3/60-z^5/160)
      ![17/105,3631/21000,12907/84000,502669/4200000,22711/262500,20033129/336000000]
      (fun i => by fin_cases i <;> norm_num) (by norm_num)
      (fun x => by simp only [bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
                   norm_num [Nat.choose]; ring) ⟨hz.1,hz1⟩
  have c0 : 0 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have cL : 7/10 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have cU : Real.sqrt 3-1 ≤ 3/4 := by linarith [sqrt_three_bounds.2]
  have hs := mul_le_mul_of_nonneg_left (sin_upper_five hz.1) c0
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have h1 := mul_nonneg hz.1 (show 0 ≤ 3/4-(Real.sqrt 3-1) by linarith)
  have h3 := mul_nonneg (pow_nonneg hz.1 3)
    (show 0 ≤ Real.sqrt 3-1-7/10 by linarith)
  have h5 := mul_nonneg (pow_nonneg hz.1 5)
    (show 0 ≤ 3/4-(Real.sqrt 3-1) by linarith)
  linarith [pi_lt_22_over_7]

lemma opposite_axial_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u=axial u) (hB : label A v=axial v) :
    0 < sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := forward_turn_range h h'
  have he : u+v=(4/5)*(gap+w) := by
    dsimp [w]
    rw [hA,hB]
    dsimp [axial]
    ring
  change 0 < sideSideSupport u A v w
  by_cases hpos : 0 ≤ w
  · have hl := opposite_support_positive_turn (u := u) h'.half_le h'.u_nonneg ⟨hpos,hw.2⟩
    have hr := forward_turn_nonneg ⟨hpos,hw.2⟩
    dsimp [gap] at he
    linarith [pi_lt_22_over_7]
  · let z := -w
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by
      dsimp [z]
      constructor <;> linarith [hw.1]
    have hl := opposite_support_negative_turn (u := u) h' hz
    have hr := opposite_axial_scalar hz
    have hs : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    have hm := mul_nonneg (show 0 ≤ Real.sqrt 3-1-(A-1/2) by
      linarith [h'.a_le_sqrt_three_sub_half]) hs
    have hwz : w = -z := by dsimp [z]; ring
    rw [hwz]
    rw [hwz] at he
    dsimp [gap] at he
    linarith

/-- Clearance of an axial and a side label: on the disk, Cauchy–Schwarz bounds
`(3/5)(A + 1/2) + (11/15)(v + 1/2)` by `41/24`. -/
lemma mixed_clearance_bound {a u A v : ℝ}
    (h' : Admissible A v)
    (hA : label a u=axial u) (hT : label A v=side A v) :
    1/170-(4/5)*(label a u+label A v-gap) ≤ 1-u-v := by
  have hl := dot_ge (p := -(3/5)) (r := -(11/15)) (c := 41/24) h'.phi_le (by norm_num)
    (by norm_num [targetSq])
  rw [hA,hT]
  dsimp [axial,side,gap]
  linarith [pi_lt_22_over_7]

lemma mixed_positive_turn {u A v w : ℝ}
    (h' : Admissible A v) (hw : 0 ≤ w ∧ w ≤ Real.pi/6)
    (hclear : 1/170-(4/5)*w ≤ 1-u-v) :
    0 < sideSideSupport u A v w := by
  have hl := opposite_support_positive_turn (u := u) h'.half_le h'.u_nonneg hw
  have hr := forward_turn_nonneg hw
  linarith

lemma side_axial_far_profile {z : ℝ} (hz : 1/3 ≤ z ∧ z ≤ 7/10) :
    0 < 1/2-Real.pi/5+(6/5)*z-(Real.sqrt 3-1)*Real.sin z
      -(1/2)*(1-Real.cos z) := by
  let B : ℝ → ℝ := fun x => 1/2-Real.pi/5+(6/5)*x-
    (Real.sqrt 3-1)*Real.sin x-(1/2)*(1-Real.cos x)
  have hc0 : 0 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have hc1 : Real.sqrt 3-1 < 11/15 := by linarith [sqrt_three_bounds.2]
  have hm : MonotoneOn B (Icc (1/3) (7/10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by dsimp [B]; fun_prop)
    · exact Differentiable.differentiableOn (by dsimp [B]; fun_prop)
    · intro x hx
      have hx' : x ∈ Icc (1/3 : ℝ) (7/10) := interior_subset hx
      have hsin := Real.sin_le (show 0 ≤ x by linarith [hx'.1])
      have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hc0
      have hd : deriv B x = 6/5-(Real.sqrt 3-1)*Real.cos x-(1/2)*Real.sin x := by
        simp (disch := fun_prop) [B]
      rw [hd]
      linarith [hx'.2]
  have hb : 0 < B (1/3) := by
    have hsin := sin_upper_five (show (0 : ℝ) ≤ 1/3 by norm_num)
    have hcos := Real.one_sub_sq_div_two_le_cos (x := (1/3 : ℝ))
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi
      (show (0 : ℝ) ≤ 1/3 by norm_num) (by linarith [Real.pi_gt_d2])
    have hp := mul_nonneg (show 0 ≤ 11/15-(Real.sqrt 3-1) by linarith) hsin0
    dsimp [B]
    linarith [pi_lt_22_over_7]
  exact hb.trans_le (hm (by constructor <;> norm_num) hz hz.1)

lemma opposite_axial_side_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u=axial u) (hT : label A v=side A v) :
    0 < sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := forward_turn_range h h'
  have hclear := mixed_clearance_bound h' hA hT
  change 1/170-(4/5)*w ≤ 1-u-v at hclear
  change 0 < sideSideSupport u A v w
  by_cases hpos : 0 ≤ w
  · exact mixed_positive_turn h' ⟨hpos,hw.2⟩ hclear
  · let z := -w
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by dsimp [z]; constructor <;> linarith [hw.1]
    have hz7 : z < 7/10 := by
      have ht := side_selected_label_gt h' hT
      have ha := h.label_nonneg
      dsimp [z,w,gap]
      linarith [pi_lt_22_over_7]
    have hl := opposite_support_negative_turn (u := u) h' hz
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    have hsin := Real.sin_le hz.1
    have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
    have hA1 := side_selected_a_lt h' hT
    have hp := mul_nonneg (show 0 ≤ 5/8-(A-1/2) by linarith) hsin0
    have hq := mul_nonneg hz.1 (show 0 ≤ 7/40-z/4 by linarith)
    have he : w = -z := by dsimp [z]; ring
    rw [he]
    rw [he] at hclear
    linarith

lemma opposite_side_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v) :
    0 < sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := forward_turn_range h h'
  have hclear : 1/170-(4/5)*w ≤ 1-u-v := by
    have hc := mixed_clearance_bound h hA hT
    dsimp [w]
    linarith
  change 0 < sideSideSupport u A v w
  by_cases hpos : 0 ≤ w
  · exact mixed_positive_turn h' ⟨hpos,hw.2⟩ hclear
  · let z := -w
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by dsimp [z]; constructor <;> linarith [hw.1]
    have hz7 : z < 7/10 := by
      have ht := side_selected_label_gt h hT
      have ha := h'.label_nonneg
      dsimp [z,w,gap]
      linarith [pi_lt_22_over_7]
    have he : w = -z := by dsimp [z]; ring
    rw [he]
    rw [he] at hclear
    have hl := opposite_support_negative_turn (u := u) h' hz
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    have hA1 := h'.a_le_sqrt_three_sub_half
    have hp := mul_nonneg (show 0 ≤ Real.sqrt 3-1-(A-1/2) by linarith) hsin0
    by_cases hzsmall : z ≤ 1/3
    · have hsin := Real.sin_le hz.1
      have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
      have hq := mul_nonneg hz.1 (show 0 ≤ 1/3-z by linarith)
      have hpc := mul_nonneg
        (show 0 ≤ 11/15-(Real.sqrt 3-1) by linarith [sqrt_three_bounds.2]) hsin0
      linarith
    · have hsource := side_identity_transverse a u
      rw [← hT] at hsource
      have hu : u ≤ 1/2+(6/5)*(label a u-Real.pi/6) := by
        linarith [h.remainder_nonneg]
      have hv : v=(4/5)*label A v := by rw [hA]; dsimp [axial]; ring
      have hs : 1/2-Real.pi/5+(6/5)*z ≤ 1-u-v := by
        have hw' : label a u+label A v=gap-z := by
          dsimp [z,w]
          ring
        have ht := h'.label_nonneg
        dsimp [gap] at hw'
        linarith
      have hprof := side_axial_far_profile ⟨(lt_of_not_ge hzsmall).le,hz7.le⟩
      linarith

/-- Complete A/T sector, including the only possible side--side contact. -/
theorem fixed_gap_forward_opposite_active {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v) :
    PairProperty a u A v .negative .positive 1 := by
  have he := pairSupport_forward_opposite h h'
  rcases ha with hA | hT <;> rcases hb with hA' | hT'
  · exact .of_pos (he ▸ opposite_axial_axial_pos h h' hA hA')
  · exact .of_pos (he ▸ opposite_axial_side_pos h h' hA hT')
  · exact .of_pos (he ▸ opposite_side_axial_pos h h' hT hA')
  · rw [PairProperty,he]
    exact ⟨(side_side_property h h' hT hT').1,fun hz =>
      Or.inl ⟨rfl,rfl,side_side_zero h h' hT hT' hz⟩⟩

end SquaresInCircles.Seven
