import SquaresInCircles.Seven.Pair.Contacts

/-!
# Seven squares: the inward axis, positive source sign, axial target

In the turn `e = label a u - t label A v - π/6` the support sum is
`1/2 - a - A sin e + |sin e|/2 + (1/2 - t v) cos e`. A nonnegative turn is at
most `π/12`, and the label inequality of the source bounds `1 - a - v` below. A
negative turn `-z` is controlled by the profile
`sin z - (4/5) z cos z - (3/4)(1 - cos z) ≥ z/40`. For two axial labels the sum
is positive, for either target sign when the turn is nonpositive; for a side
source it is at least the remainder plus a multiple of the turn, which vanish
together only at the contact of a side square with the top or bottom square.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

/-- A negative turn `-z` with `z ≤ 1`: the Taylor bounds of the profile are
`z (9z² - 15z + 8)/40 + (z³/960)(5 + (1 - z)(z² + 33z + 3))`. -/
lemma inward_small_turn_bound {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    z*(9*z^2-15*z+8)/40 ≤
      Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z) := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hcu := mul_le_mul_of_nonneg_left (cos_upper_four hz.1) hz.1
  have hcl := cos_lower_six hz.1
  have he : 0 ≤ z^3*(5+(1-z)*(z^2+33*z+3)) := mul_nonneg (pow_nonneg hz.1 3)
    (add_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hz.2) (by nlinarith [hz.1])))
  linarith

/-- The profile of a negative turn `-z`. Up to `z = 1` the Taylor bound is at least
`z/40`, as `9z² - 15z + 8 = (3z - 5/2)² + 7/4`. Past `z = 1` the profile less `z/20`
increases: its slope is `(3/20) cos z + (4/5)(z - 1) sin z + (cos z + sin z - 1)/20`. -/
lemma inward_turn_profile {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    z/40 ≤ Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z) := by
  rcases le_total z 1 with hz1 | hz1
  · linarith [inward_small_turn_bound ⟨hz.1,hz1⟩,
      mul_nonneg hz.1 (show 0 ≤ (3*z-5/2)^2+3/4 by positivity)]
  have hm : MonotoneOn (fun y => Real.sin y-(4/5)*y*Real.cos y-(3/4)*(1-Real.cos y)-y/20)
      (Icc 1 (Real.pi/2)) := by
    apply monoOn_of_hasDeriv_nonneg
      (d := fun y => (1/5)*Real.cos y+((4/5)*y-3/4)*Real.sin y-1/20) (by fun_prop)
    · intro y _
      exact ((((Real.hasDerivAt_sin y).sub (((hasDerivAt_id' y).const_mul (4/5)).mul
        (Real.hasDerivAt_cos y))).sub (((hasDerivAt_const y 1).sub
        (Real.hasDerivAt_cos y)).const_mul (3/4))).sub
        ((hasDerivAt_id' y).div_const 20)).congr_deriv (by ring)
    · intro y hy
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := y) (by linarith [hy.1])
        (by linarith [hy.2,Real.pi_pos])
      have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hy.1,Real.pi_pos],hy.2.le⟩
      -- `cos y + sin y ≥ cos² y + sin² y = 1` in the first quadrant
      have hs2 := mul_nonneg hs (sub_nonneg.mpr (Real.sin_le_one y))
      have hc2 := mul_nonneg hc (sub_nonneg.mpr (Real.cos_le_one y))
      have hys := mul_nonneg (sub_nonneg.mpr hy.1.le) hs
      linarith [Real.sin_sq_add_cos_sq y]
  have h1 := inward_small_turn_bound (z := 1) ⟨zero_le_one,le_rfl⟩
  have h2 := hm ⟨le_rfl,hz1.trans hz.2⟩ ⟨hz1,hz.2⟩ hz1
  linarith

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
of the turn and the axial bound `a + u < 1 + 2π/15` make the sum positive. -/
lemma inward_axial_nonpositive_turn {a u A v : ℝ} (t : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u = axial u) (hB : label A v = axial v)
    (he : label a u-t.coe*label A v-Real.pi/6 ≤ 0) :
    0 < pairSupport a u A v .positive t 2 gap := by
  let z := -(label a u-t.coe*label A v-Real.pi/6)
  have hz : 0 ≤ z ∧ z ≤ 5*Real.pi/12 := by
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
  have hc : 0 < Real.cos z := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hp := inward_turn_profile ⟨hz.1,by linarith [Real.pi_pos]⟩
  have h0 := mul_pos hc (show 0 < 1+2*Real.pi/15-a-u by linarith [axial_sum_lt h hA])
  have h1 := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z)) (show 0 ≤ 5/4-a by
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
