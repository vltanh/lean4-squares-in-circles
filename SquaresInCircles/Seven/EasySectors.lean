import SquaresInCircles.Seven.Contacts

/-!
# Four sectors valid for every label

At the gap `π/3`: the outward axis, because the centre of the other square is
near the disk centre; the backward axis, by the marker point of the other
square; the inward axis with a negative source sign, by its marker arc; and the
forward axis with both signs positive, by Cauchy–Schwarz on the disk and the
marker bounds.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

/-- Outward radial source: no active-label case distinction. -/
theorem fixed_gap_outward {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (s t : TransverseSign) :
    0 < pairSupport a u A v s t 0 gap := by
  rw [pairSupport_zero]
  linarith [h.half_le,support_lower (sign_admissible h' t) (Real.pi-gap-s.coe*label a u+
    t.coe*label A v)]

/-- Backward transverse source: the other square's marker point suffices. -/
theorem fixed_gap_backward {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (s t : TransverseSign) :
    0 < pairSupport a u A v s t 3 gap := by
  rw [pairSupport_three]
  have hp := marker_arc_support h' t (x := t.coe*label A v) (by norm_num)
    (5*Real.pi/2-gap-s.coe*label a u+t.coe*label A v)
  rw [show 5*Real.pi/2-gap-s.coe*label a u+t.coe*label A v-t.coe*label A v =
      Real.pi/2-(gap+s.coe*label a u)+2*Real.pi by ring,Real.cos_add_two_pi,
    Real.cos_pi_div_two_sub] at hp
  obtain ⟨h0,h1⟩ := h.label_mem
  cases s
  · rw [show gap+TransverseSign.positive.coe*label a u = Real.pi/2-(Real.pi/6-label a u) by
      simp [gap,TransverseSign.coe]; ring,Real.sin_pi_div_two_sub] at hp
    have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi/6-label a u)
    have hsq : (Real.pi/6-label a u)^2 < (3/5)^2 := by
      nlinarith [Real.pi_lt_d2,Real.pi_pos]
    simp only [TransverseSign.coe,one_mul] at hp ⊢
    linarith [h.u_lt]
  · have hs : 0 ≤ Real.sin (gap+TransverseSign.negative.coe*label a u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (by simp [gap,TransverseSign.coe]; linarith [Real.pi_pos])
        (by simp [gap,TransverseSign.coe]; linarith [Real.pi_pos])
    simp only [TransverseSign.coe,neg_one_mul,sub_neg_eq_add] at hp hs ⊢
    linarith [h.u_nonneg]

/-- The inward radial source is uniformly positive when its transverse sign
is negative. The other square may have either sign and any label. -/
theorem fixed_gap_inward_negative {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (t : TransverseSign) :
    0 < pairSupport a u A v .negative t 2 gap := by
  rw [pairSupport_two]
  let y := gap-label a u-801/1600
  have hp := marker_arc_support h' t (x := t.coe*label A v-801/1600)
    (by norm_num) (2*Real.pi-gap-TransverseSign.negative.coe*label a u+t.coe*label A v)
  rw [show 2*Real.pi-gap-TransverseSign.negative.coe*label a u+t.coe*label A v-
      (t.coe*label A v-801/1600) = 2*Real.pi-y by simp [y,TransverseSign.coe]; ring,
    Real.cos_two_pi_sub] at hp
  have hb : -(2/3 : ℝ) < y ∧ y < 2/3 := by
    obtain ⟨h0,h1⟩ := h.label_mem
    dsimp [y,gap]
    constructor <;> linarith [Real.pi_gt_d2,Real.pi_lt_d4]
  have hy : y^2 < (2/3)^2 := by nlinarith [hb.1,hb.2]
  have hc := Real.one_sub_sq_div_two_le_cos (x := y)
  have ha := h.a_le_sqrt_three_sub_half
  linarith [sqrt_three_bounds.2]

lemma trig_sum_monotone : MonotoneOn (fun x : ℝ => Real.cos x+Real.sin x)
    (Icc 0 (Real.pi/4)) := by
  apply monoOn_of_hasDeriv_nonneg (d := fun x => Real.cos x-Real.sin x) (by fun_prop)
  · intro x _
    exact ((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).congr_deriv (by ring)
  · intro x hx
    exact sub_nonneg.mpr (sin_le_cos_of_small ⟨hx.1.le,hx.2.le⟩)

/-- The forward axis with both signs positive: positive for every label. -/
theorem fixed_gap_forward_positive {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    0 < pairSupport a u A v .positive .positive 1 gap := by
  let t := label a u
  let z := Real.pi/6-t+label A v
  obtain ⟨ht0,ht1⟩ := h.label_mem
  obtain ⟨hs0,hs1⟩ := h'.label_mem
  have htu : (4/5)*t ≤ u := by
    have hh := h.label_le_axial
    dsimp [axial] at hh
    dsimp [t]
    linarith
  have he : pairSupport a u A v .positive .positive 1 gap =
      1/2+u-A*Real.cos z-v*Real.sin z+(|Real.cos z|+|Real.sin z|)/2 := by
    rw [pairSupport_one,show 3*Real.pi/2-gap-TransverseSign.positive.coe*label a u+
      TransverseSign.positive.coe*label A v = Real.pi+z by simp [gap,z,t,TransverseSign.coe]; ring]
    simp [support,Real.cos_add,Real.sin_add,abs_neg,TransverseSign.coe]
    ring
  rw [he]
  by_cases ht : 5/16 ≤ t
  · have hl := support_lower (a := A) (b := v) (by rw [abs_of_nonneg h'.u_nonneg]; exact h')
      (Real.pi+z)
    simp [support,Real.cos_add,Real.sin_add,abs_neg] at hl
    linarith
  have hz : 21/100 ≤ z ∧ z ≤ Real.pi/2 := by
    dsimp [z]
    constructor <;> linarith [Real.pi_gt_d2,Real.pi_pos]
  have hc : 0 ≤ Real.cos z := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hz.2⟩
  have hsn : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
    (by linarith [Real.pi_pos])
  rw [abs_of_nonneg hc,abs_of_nonneg hsn]
  by_cases hquarter : Real.pi/4 ≤ z
  · have hcs := cos_le_sin_of_quarter ⟨hquarter,hz.2⟩
    have hp := mul_nonneg (show 0 ≤ A-v by linarith [h'.u_le]) (sub_nonneg.mpr hcs)
    have hprod := mul_nonneg (show 0 ≤ 31/20-A-v by linarith [h'.sum_lt]) (add_nonneg hc hsn)
    have hunit : Real.sin z+Real.cos z < 3/2 := by
      nlinarith [Real.sin_sq_add_cos_sq z,sq_nonneg (Real.sin z-Real.cos z)]
    linarith [h.u_nonneg]
  · have hd := dot_ge (p := -Real.cos z) (r := -Real.sin z) (c := 181/100) h'.phi_le
      (by norm_num) (by unfold targetSq; nlinarith [Real.sin_sq_add_cos_sq z])
    have hm := trig_sum_monotone ⟨show 0 ≤ Real.pi/6-t by linarith [Real.pi_gt_d2],
      show Real.pi/6-t ≤ Real.pi/4 by linarith⟩ ⟨by linarith,by linarith⟩
      (show Real.pi/6-t ≤ z by dsimp [z]; linarith)
    -- `1/2 + (4/5) t + cos (π/6 - t) + sin (π/6 - t)` is concave in `π/6 - t`
    have hf := trig_concave_gt (α := -4/5) (A := 1) (B := 1) (m := 131/100-2*Real.pi/15)
      (x := Real.pi/6-t) (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_pos])
      (show 21/100 ≤ Real.pi/6-t ∧ Real.pi/6-t ≤ Real.pi/6 by
        constructor <;> linarith [Real.pi_gt_d2])
      (by
        have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 21/100 by norm_num)
        have hc := Real.one_sub_sq_div_two_le_cos (x := (21/100:ℝ))
        linarith [Real.pi_gt_d2])
      (by
        rw [Real.sin_pi_div_six,Real.cos_pi_div_six]
        linarith [sqrt_three_bounds.1])
    dsimp at hm
    linarith

end SquaresInCircles.Seven
