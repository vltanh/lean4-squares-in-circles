import SquaresInCircles.Seven.SmoothMinima
import SquaresInCircles.Seven.FixedGap

/-!
# All marker gaps below `π/3`

The support sums of an admissible pair are positive for every gap in
`[0, π/3)`. For gaps up to 1 the two marker arcs share three points of the unit
circle, which a weakly separating line would contain. For larger gaps a
nonpositive value, with the sum nonnegative at `π/3`, forces a leftmost minimum
inside `[1, π/3]`. There the relative phase lies in `(-π/2, π)`. At `0` the
squares are parallel, and side by side across the axis their labels would add up
to at least `π/3`; at `π/2` they are quarter-turned, and a separating side would
bring their labels within `π/6`. Otherwise the minimum is smooth and positive.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Small gaps: the marker arcs share three points of the unit circle. -/
lemma small_gap_support_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0≤g ∧ g≤1) :
    0<pairSupport a u A v s t k g := by
  let p := s.coe*label a u
  let r := t.coe*label A v
  let z := cardinalAngle k-p-g/2
  let h1 := support a (s.coe*u) (cardinalAngle k)
  let h2 := support A (t.coe*v) (cardinalAngle k+Real.pi-g-p+r)
  have hb (e : ℝ) (he : |e|≤1/3200) : Real.cos (z-e)≤h1 ∧ -Real.cos (z-e)≤h2 := by
    have he' := abs_le.mp he
    have hfirst := marker_arc_support h s (x := p+g/2+e)
      (abs_le.mpr ⟨by linarith [hg.1,hg.2,he'.1,he'.2],by linarith [hg.1,hg.2,he'.1,he'.2]⟩)
      (cardinalAngle k)
    have hsecond := marker_arc_support h' t (x := r-g/2+e)
      (abs_le.mpr ⟨by linarith [hg.1,hg.2,he'.1,he'.2],by linarith [hg.1,hg.2,he'.1,he'.2]⟩)
      (cardinalAngle k+Real.pi-g-p+r)
    rw [show cardinalAngle k-(p+g/2+e) = z-e by dsimp [z]; ring] at hfirst
    rw [show cardinalAngle k+Real.pi-g-p+r-(r-g/2+e) = (z-e)+Real.pi by dsimp [z]; ring,
      Real.cos_add_pi] at hsecond
    exact ⟨hfirst,hsecond⟩
  by_contra hn
  have hsum : h1+h2≤0 := le_of_not_gt hn
  have heq (e : ℝ) (he : |e|≤1/3200) : Real.cos (z-e)=h1 := by
    have hh := hb e he
    linarith
  have h0 := heq 0 (by norm_num)
  have hp := heq (1/3200) (by norm_num)
  have hm := heq (-1/3200) (by norm_num)
  rw [sub_zero] at h0
  rw [show z-(-1/3200) = z+1/3200 by ring,Real.cos_add] at hm
  rw [Real.cos_sub] at hp
  have hsin0 : 0<Real.sin (1/3200:ℝ) := Real.sin_pos_of_pos_of_lt_pi
    (by norm_num) (by linarith [Real.pi_gt_d2])
  have hcos1 : Real.cos (1/3200:ℝ) < 1 := by
    have hu := Real.sin_sq_add_cos_sq (1/3200:ℝ)
    nlinarith [Real.cos_le_one (1/3200:ℝ)]
  have hsz : Real.sin z = 0 := (mul_eq_zero.mp (show Real.sin z*Real.sin (1/3200) = 0 by
    linear_combination (hp-hm)/2)).resolve_right hsin0.ne'
  have hcz : Real.cos z = 0 := (mul_eq_zero.mp (show Real.cos z*(Real.cos (1/3200)-1) = 0 by
    linear_combination (hp+hm)/2-h0)).resolve_right (by linarith)
  have hu := Real.sin_sq_add_cos_sq z
  rw [hsz,hcz] at hu
  norm_num at hu

/-- Two labels on opposite sides of parallel squares add up to at least
`π/3`. -/
theorem opposite_labels_ge {a x A y : ℝ}
    (h : Admissible a x) (h' : Admissible A y) (hs : 1 ≤ x+y) :
    gap ≤ label a x+label A y := by
  have := h.tangent
  have := h'.tangent
  have := h.sum_lt
  have := h'.sum_lt
  have := h.u_lt
  have := h'.u_lt
  rcases h.selected with hx | hx | hx <;> rcases h'.selected with hy | hy | hy <;>
    rw [hx,hy] <;> dsimp [axial,side,gap] <;> linarith [h.u_le,h'.u_le,pi_lt_22_over_7,Real.pi_gt_d2]

/-- At the relative phase `0` below the gap `π/3` every support sum is positive:
parallel squares side by side across the axis would have labels adding up to at
least `π/3`. -/
lemma parallel_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 < g ∧ g < gap)
    (hd : relativePhase a u A v g s t = 0) :
    0 < pairSupport a u A v s t k g := by
  obtain ⟨e0,e1,e2,e3⟩ := pair_support_axis_values a u A v g s t
  simp only [pairWidth,centerDX,centerDY,hd,Real.cos_zero,Real.sin_zero,
    abs_zero,abs_one,mul_zero,mul_one] at e0 e1 e2 e3
  have := h.a_lt_five_fourths
  have := h'.a_lt_five_fourths
  have := h.u_lt
  have := h'.u_lt
  have hl := h.label_nonneg
  have hL := h'.label_nonneg
  have hside (hs : s = .negative) (ht : t = .positive) : u+v < 1 := by
    by_contra hn
    have := opposite_labels_ge h h' (le_of_not_gt hn)
    subst hs ht
    simp only [relativePhase,TransverseSign.coe] at hd
    linarith
  obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by fin_cases k <;> simp
  · rw [e0]; linarith [h.half_le]
  · rw [e1]
    cases s <;> cases t <;> simp only [relativePhase,TransverseSign.coe] at hd ⊢ <;>
      first | linarith [h.u_nonneg,h'.u_nonneg] | linarith [hside rfl rfl]
  · rw [e2]; linarith [h'.half_le]
  · rw [e3]
    cases s <;> cases t <;> simp only [relativePhase,TransverseSign.coe] at hd ⊢ <;>
      linarith [h.u_nonneg,h'.u_nonneg]

/-- A quarter-turned pair with the first square beyond a whole side of the second
along the first axis: the signed labels differ by at most `π/6`. -/
lemma quarter_difference_horizontal {a u A v : ℝ} (h : Admissible a u) (h' : Admissible A v)
    (s t : TransverseSign) (hsep : 1 ≤ a+t.coe*v) :
    s.coe*label a u-t.coe*label A v ≤ Real.pi/6 := by
  have := h.tangent
  have := h.a_lt_five_fourths
  have hS := h.label_le_side
  have hA := h'.label_le_axial
  obtain ⟨h0,h1⟩ := h.label_mem
  obtain ⟨h2,h3⟩ := h'.label_mem
  dsimp [side,axial] at hS hA
  cases s <;> cases t <;> simp only [TransverseSign.coe] at hsep ⊢
  · rcases h'.selected with hL | hL | hL
    · rw [hL]
      dsimp [axial]
      linarith
    · linarith [side_selected_label_gt h' hL,Real.pi_lt_d2]
    · linarith
  · linarith
  · linarith
  · linarith [h'.u_nonneg,Real.pi_gt_d2]

/-- Either separating coordinate suffices for the quarter-turn label inequality. -/
theorem quarter_difference_le {a u A v : ℝ} (h : Admissible a u) (h' : Admissible A v)
    (s t : TransverseSign) (hsep : 1 ≤ a+t.coe*v ∨ 1 ≤ A-s.coe*u) :
    s.coe*label a u-t.coe*label A v ≤ Real.pi/6 := by
  rcases hsep with hh | hh
  · exact quarter_difference_horizontal h h' s t hh
  · have hq := quarter_difference_horizontal h' h t.flip s.flip
      (by rw [TransverseSign.coe_flip]; linarith)
    rw [TransverseSign.coe_flip,TransverseSign.coe_flip] at hq
    linarith

/-- At the relative phase `π/2` below the gap `π/3` every support sum is
positive: a separating side would bring the labels within `π/6`. -/
lemma quarter_turn_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : g < gap)
    (hd : relativePhase a u A v g s t = Real.pi/2) :
    0 < pairSupport a u A v s t k g := by
  obtain ⟨e0,e1,e2,e3⟩ := pair_support_axis_values a u A v g s t
  simp only [pairWidth,centerDX,centerDY,hd,Real.cos_pi_div_two,Real.sin_pi_div_two,
    abs_zero,abs_one,mul_zero,mul_one] at e0 e1 e2 e3
  have hsep (hh : 1 ≤ a+t.coe*v ∨ 1 ≤ A-s.coe*u) : False := by
    have hq := quarter_difference_le h h' s t hh
    simp only [relativePhase,gap] at hd hg
    linarith
  have hu : |s.coe*u| < 31/40 := by
    cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.u_nonneg] using h.u_lt
  have hv : |t.coe*v| < 31/40 := by
    cases t <;> simpa [TransverseSign.coe,abs_of_nonneg h'.u_nonneg] using h'.u_lt
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by fin_cases k <;> simp
  · rw [e0]; linarith [h.half_le]
  · rw [e1]; by_contra hn; exact hsep (Or.inr (by linarith))
  · rw [e2]; by_contra hn; exact hsep (Or.inl (by linarith))
  · rw [e3]; linarith [h'.half_le]

lemma pairSupport_continuous (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) :
    Continuous (fun g => pairSupport a u A v s t k g) := by
  unfold pairSupport support
  fun_prop

/-- Admissible states: the support sums are positive below the gap `π/3`. -/
theorem all_gap_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 ≤ g ∧ g < gap) :
    0 < pairSupport a u A v s t k g := by
  by_cases hg1 : g≤1
  · exact small_gap_support_pos s t k h h' ⟨hg.1,hg1⟩
  by_contra hn
  obtain ⟨x,hx,hxnon,hmin,hbefore⟩ := leftmost_nonpositive_minimum
    (pairSupport_continuous a u A v s t k) ⟨(lt_of_not_ge hg1).le,hg.2⟩ (le_of_not_gt hn)
    (small_gap_support_pos s t k h h' (g := 1) ⟨by norm_num,le_rfl⟩)
    (fixed_gap_nonneg s t k h h')
  have hd : -Real.pi/2 < relativePhase a u A v x s t ∧ relativePhase a u A v x s t < Real.pi := by
    obtain ⟨h0,h1⟩ := h.label_mem
    obtain ⟨h2,h3⟩ := h'.label_mem
    have := hx.1
    have := hx.2
    simp only [relativePhase,gap] at *
    cases s <;> cases t <;> simp only [TransverseSign.coe] <;> constructor <;>
      linarith [Real.pi_gt_d2,Real.pi_lt_d2]
  by_cases hs : Real.sin (relativePhase a u A v x s t) = 0
  · have hp := parallel_pos s t k h h' ⟨by linarith [hx.1],hx.2⟩
      (sin_zero_between ⟨by linarith [Real.pi_pos],hd.2⟩ hs)
    linarith
  by_cases hc : Real.cos (relativePhase a u A v x s t) = 0
  · have hq := quarter_turn_pos s t k h h' hx.2 (cos_zero_between hd hc)
    linarith
  · have hp := smooth_leftmost_support_pos s t k h h' hx hmin hbefore hc hs
    linarith

end SquaresInCircles.Seven
