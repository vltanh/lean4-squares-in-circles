import SquaresInCircles.Seven.Contacts

/-!
# The inward axis, positive source sign, axial target

In the turn `e = label a u - t label A v - π/6` the support sum is
`1/2 - a - A sin e + |sin e|/2 + (1/2 - t v) cos e`. A nonnegative turn is at
most `π/12`, and the label inequality of the source bounds `1 - a - v` below. A
negative turn `-z` is controlled by the profile
`sin z - (4/5) z cos z - (3/4)(1 - cos z) ≥ z/50`. For two axial labels the sum
is positive, for either target sign when the turn is nonpositive; for a side
source it is at least the remainder plus a multiple of the turn, which vanish
together only at the contact of a side square with the top or bottom square.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- The profile of a negative turn `-z`. -/
lemma inward_turn_profile {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    z/50 ≤ Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z) := by
  have hq : 0 < 9/50-3*z/8+7*z^2/30+z^3/32-z^4/30-z^5/960 :=
    bernstein_pos (p := fun z => 9/50-3*z/8+7*z^2/30+z^3/32-z^4/30-z^5/960)
      ![9/50,123/2000,937/750000,462959/40000000,237199301/3750000000,
        22578739001/300000000000]
      (fun i => by fin_cases i <;> norm_num) (by norm_num)
      (fun x => by simp only [bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
                   norm_num [Nat.choose]; ring)
      ⟨hz.1,show z ≤ 79/50 by linarith [Real.pi_lt_d2]⟩
  have hs := Real.sin_ge_sub_cube hz.1
  have hcu := mul_le_mul_of_nonneg_left (cos_upper_four hz.1) hz.1
  have hcl := cos_lower_six hz.1
  nlinarith [mul_nonneg hz.1 hq.le]

/-- Positive turn: the radial extent of the target is the only upper bound used. -/
lemma inward_positive_turn_bound {A v e : ℝ}
    (hA : A ≤ Real.sqrt 3-1/2) (hv : 0 ≤ v)
    (he : 0 ≤ e ∧ e ≤ Real.pi/12) :
    e/840 ≤ (4/5)*e-A*Real.sin e+|Real.sin e|/2+
      (v-1/2)*(1-Real.cos e) := by
  have hs0 : 0 ≤ Real.sin e := Real.sin_nonneg_of_nonneg_of_le_pi
    he.1 (by linarith [he.2,Real.pi_pos])
  have hc0 : 0 ≤ 1-Real.cos e := sub_nonneg.mpr (Real.cos_le_one e)
  have hs := Real.sin_le he.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hroot : Real.sqrt 3 ≤ 26/15 := by linarith [sqrt_three_bounds.2]
  have hroot0 : 0 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have he1 : e ≤ 11/42 := by linarith [he.2,pi_lt_22_over_7]
  have hAprod := mul_nonneg (sub_nonneg.mpr hA) hs0
  have hvprod := mul_nonneg hv hc0
  have hsinprod := mul_nonneg hroot0 (sub_nonneg.mpr hs)
  have hrootprod := mul_nonneg he.1 (show 0 ≤ 26/15-Real.sqrt 3 by linarith)
  have heprod := mul_nonneg he.1 (show 0 ≤ 11/42-e by linarith)
  rw [abs_of_nonneg hs0]
  linarith

/-- For an axial target and a nonnegative turn, the sum is at least the remainder
of the source plus a multiple of the turn, whatever the source label. -/
lemma inward_axial_positive_turn {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (hB : label A v = axial v)
    (he : 0 ≤ label a u-label A v-Real.pi/6) :
    (2/15)*remainder a u+(label a u-label A v-Real.pi/6)/840 ≤
      pairSupport a u A v .positive .positive 2 gap := by
  have hclear : (4/5)*(label a u-label A v-Real.pi/6)+(2/15)*remainder a u ≤ 1-a-v := by
    have ht := h.label_le_side
    rw [side_identity_radial] at ht
    rw [hB]
    dsimp [axial]
    linarith
  have hturn := inward_positive_turn_bound h'.a_le_sqrt_three_sub_half h'.u_nonneg
    ⟨he,by linarith [h.label_le_quarter,h'.label_nonneg]⟩
  rw [pairSupport_inward .positive h h']
  simp only [TransverseSign.coe,one_mul]
  linarith

/-- Two axial labels and a nonpositive turn, for either target sign: the profile
of the turn and the axial bound `a + u < 113/80` make the sum positive. -/
lemma inward_axial_nonpositive_turn {a u A v : ℝ} (t : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u = axial u) (hB : label A v = axial v)
    (he : label a u-t.coe*label A v-Real.pi/6 ≤ 0) :
    0 < pairSupport a u A v .positive t 2 gap := by
  let z := -(label a u-t.coe*label A v-Real.pi/6)
  have hz : 0 ≤ z ∧ z ≤ Real.pi/2 := by
    obtain ⟨h0,-⟩ := h.label_mem
    obtain ⟨h1,h2⟩ := h'.label_mem
    dsimp [z]
    cases t <;> simp only [TransverseSign.coe] at he ⊢ <;> constructor <;> linarith
  have hb : t.coe*v = u+(4/5)*z-2*Real.pi/15 := by
    dsimp [z]
    rw [hA,hB]
    dsimp [axial]
    ring
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hz.2⟩
  have hp := inward_turn_profile hz
  have h0 := mul_nonneg hc (show 0 ≤ 1+2*Real.pi/15-a-u-1/200 by
    linarith [axial_sum_lt h hA,Real.pi_gt_d2])
  have h1 := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z)) (show 0 ≤ 5/4-a-1/200 by
    linarith [h.a_le_sqrt_three_sub_half,sqrt_three_bounds.2])
  have h2 := mul_nonneg (show 0 ≤ A-1/2 by linarith [h'.half_le]) hs
  rw [pairSupport_inward t h h',show label a u-t.coe*label A v-Real.pi/6 = -z by dsimp [z]; ring,
    Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs,hb]
  linarith

/-- Two axial labels with positive signs: a positive sum. -/
theorem inward_axial_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u = axial u) (hB : label A v = axial v) :
    0 < pairSupport a u A v .positive .positive 2 gap := by
  by_cases he0 : label a u-label A v-Real.pi/6 ≤ 0
  · exact inward_axial_nonpositive_turn .positive h h' hA hB
      (by simp only [TransverseSign.coe,one_mul]; exact he0)
  have hl := inward_axial_positive_turn h h' hB (lt_of_not_ge he0).le
  -- an axial label is not the side state, whose label is `π/6`
  have hr : 0 < remainder a u := by
    refine h.remainder_nonneg.lt_of_ne fun hz => ?_
    have hc := remainder_zero h hz.symm
    have hle := h.label_le_side
    rw [hA,hc.1,hc.2] at hle
    dsimp [axial,side] at hle
    linarith [pi_lt_22_over_7]
  linarith

/-- A side source and an axial target with positive signs: at least the
remainder of the source plus a multiple of the turn. -/
theorem inward_side_axial_lower {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    (2/15)*remainder a u+|label a u-label A v-Real.pi/6|/840 ≤
      pairSupport a u A v .positive .positive 2 gap := by
  rcases le_or_gt 0 (label a u-label A v-Real.pi/6) with he0 | he0
  · rw [abs_of_nonneg he0]
    exact inward_axial_positive_turn h h' hA he0
  have hlabel : Real.pi/12 < label a u := by
    linarith [side_selected_label_gt h hT,Real.pi_lt_d2]
  have hlin : 1-a-v = (4/5)*(label a u-label A v-Real.pi/6)+(2/15)*remainder a u := by
    rw [hT,hA]
    dsimp [side,axial,remainder]
    ring
  have hv : (4/5)*(-(label a u-label A v-Real.pi/6))-3/4 ≤ v-1/2 := by
    rw [hA]
    dsimp [axial]
    linarith [pi_lt_22_over_7]
  have hrange : -(label a u-label A v-Real.pi/6) ≤ Real.pi/2 := by
    linarith [h'.label_le_quarter]
  rw [pairSupport_inward .positive h h']
  simp only [TransverseSign.coe,one_mul]
  generalize label a u-label A v-Real.pi/6 = e at *
  have hz : 0 ≤ -e ∧ -e ≤ Real.pi/2 := ⟨by linarith,hrange⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos])
  have hAprod := mul_nonneg (show 0 ≤ A-1/2 by linarith [h'.half_le]) hs0
  have hvprod := mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr (Real.cos_le_one (-e)))
  have hp := inward_turn_profile hz
  simp only [Real.sin_neg,Real.cos_neg] at hs0 hAprod hvprod hp
  rw [abs_of_neg he0,abs_of_nonpos (by linarith)]
  linarith

/-- The inward axis with positive signs, side source and axial target. Zero
support forces the side state and zero transverse coordinate of the axial
square; no particular value of `A` is concluded. -/
theorem inward_side_axial_property {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    PairProperty a u A v .positive .positive 2 :=
  .of_side_axial h h' hA (e := label a u-label A v-Real.pi/6) (by simp [TransverseSign.coe])
    (c := 1/840) (by norm_num) (by linarith [inward_side_axial_lower h h' hT hA])

end SquaresInCircles.Seven
