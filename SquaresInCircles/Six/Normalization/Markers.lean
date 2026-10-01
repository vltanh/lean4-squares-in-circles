import SquaresInCircles.Six.Normalization.CapGeometry
import SquaresInCircles.Seven.MarkerArc

/-!
# Signed markers

The marker of an exterior square at the phase `t` with chart `(a, b)` lifts to
the real number `liftedMarker t a b = t ± label a |b|`, with the sign of `b`. It
lies within `π/4` of `t`, and between `t - 5|b|/4` and `t` when `b ≤ 0`. A
contained chart has `|b| < 7/10`, and `|b| ≥ 1/2` forces a label of at least
`5/8`. The point of the unit circle at the marker lies in the closed square, by
the marker arc of `Seven.MarkerArc`; so a square west of the line
`x = c_x - 1/2` has its marker in the open western half-plane, and when
`c_x < 1/2` a square whose phase is within `π/4` of `0` is not west of that
line.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- The label of the state `(a, |b|)`, with the sign of `b`. -/
def signedLabel (a b : ℝ) : ℝ :=
  if b < 0 then -Seven.label a |b| else Seven.label a |b|

/-- The marker of the square at the phase `t` with chart `(a, b)`, as a real
number. -/
def liftedMarker (t a b : ℝ) : ℝ := t + signedLabel a b

lemma signedLabel_of_neg {a b : ℝ} (hb : b < 0) :
    signedLabel a b = -Seven.label a |b| := by simp [signedLabel, hb]

lemma signedLabel_of_nonneg {a b : ℝ} (hb : 0 ≤ b) :
    signedLabel a b = Seven.label a |b| := by
  simp [signedLabel, not_lt.mpr hb]

lemma signedLabel_zero {a : ℝ} (ha : Seven.Admissible a 0) :
    signedLabel a 0 = 0 := by
  simp [signedLabel, (ha.label_zero_iff).mpr rfl]

lemma abs_signedLabel {a b : ℝ} (ha : Seven.Admissible a |b|) :
    |signedLabel a b| = Seven.label a |b| := by
  unfold signedLabel
  split_ifs <;> simp [abs_of_nonneg ha.label_nonneg]

lemma signedLabel_bounds {a b : ℝ} (ha : Seven.Admissible a |b|) :
    |signedLabel a b| ≤ Real.pi / 4 ∧ |signedLabel a b| ≤ 5 * |b| / 4 := by
  rw [abs_signedLabel ha]
  exact ⟨ha.label_le_quarter, ha.label_le_axial⟩

lemma liftedMarker_bounds {t a b : ℝ} (ha : Seven.Admissible a |b|) :
    t - Real.pi / 4 ≤ liftedMarker t a b ∧
      liftedMarker t a b ≤ t + Real.pi / 4 := by
  have hh := abs_le.mp (signedLabel_bounds ha).1
  dsimp [liftedMarker]
  constructor <;> linarith

lemma liftedMarker_of_nonpos {t a b : ℝ} (ha : Seven.Admissible a |b|)
    (hb : b ≤ 0) :
    t - 5 * |b| / 4 ≤ liftedMarker t a b ∧ liftedMarker t a b ≤ t := by
  rcases hb.eq_or_lt with rfl | hb
  · have hz := signedLabel_zero (by simpa using ha)
    simp [liftedMarker, hz]
  · rw [liftedMarker, signedLabel_of_neg hb]
    have hu := ha.label_le_axial
    dsimp [Seven.axial] at hu
    constructor <;> linarith [ha.label_nonneg]

/-- A contained chart has transverse offset `u < 7/10`. -/
lemma ContainedChart.u_lt_seven_tenths {a u : ℝ} (h : ContainedChart a u) :
    u < 7 / 10 := by
  have hm := mul_nonneg (sub_nonneg.mpr h.u_le)
    (show 0 ≤ a + u + 1 by linarith [h.half_le, h.u_nonneg])
  have hc := h.containment
  norm_num [Q0] at hc
  by_contra! hu
  nlinarith [sq_nonneg (u - 7 / 10)]

/-- A transverse offset `u ≥ 1/2` forces a label of at least `5/8`: the far
corner gives `a < 861/1000`, which keeps the side term above `5/8`. -/
lemma ContainedChart.large_offset_label {a u : ℝ} (h : ContainedChart a u)
    (hu : 1 / 2 ≤ u) : 5 / 8 ≤ Seven.label a u := by
  have ha : a < 861 / 1000 := by
    have hc := h.containment
    norm_num [Q0] at hc
    by_contra! ha
    nlinarith [sq_nonneg (a - 861 / 1000), sq_nonneg (u - 1 / 2)]
  unfold Seven.label
  apply le_min
  · apply le_min
    · dsimp [Seven.axial]
      linarith
    · dsimp [Seven.side]
      linarith [Real.pi_gt_d2]
  · linarith [Real.pi_gt_d2]

lemma marker_circle_localX (t a b z : ℝ) :
    localX (orientedSquare t a b) (Real.cos (t + z), Real.sin (t + z)) =
      Real.cos z - a := by
  rw [orientedSquare_localX]
  dsimp only
  rw [Real.cos_add, Real.sin_add]
  linear_combination Real.cos z * (Real.sin_sq_add_cos_sq t)

lemma marker_circle_localY (t a b z : ℝ) :
    localY (orientedSquare t a b) (Real.cos (t + z), Real.sin (t + z)) =
      Real.sin z - b := by
  rw [orientedSquare_localY]
  dsimp only
  rw [Real.cos_add, Real.sin_add]
  linear_combination Real.sin z * (Real.sin_sq_add_cos_sq t)

/-- The point of the unit circle at the marker lies in the closed square. -/
theorem marker_point_mem {t a b : ℝ} (h : ContainedChart a |b|) :
    closedSquare (orientedSquare t a b)
      (Real.cos (liftedMarker t a b), Real.sin (liftedMarker t a b)) := by
  have hm := Seven.marker_arc h.seven_admissible
    (t := Seven.label a |b|) (by norm_num)
  unfold closedSquare liftedMarker
  rw [marker_circle_localX, marker_circle_localY]
  by_cases hb : b < 0
  · rw [signedLabel_of_neg hb, Real.cos_neg, Real.sin_neg]
    have hY : -Real.sin (Seven.label a |b|) - b =
        -(Real.sin (Seven.label a |b|) - |b|) := by
      rw [abs_of_neg hb]
      ring
    rw [hY, abs_neg]
    exact hm
  · rw [signedLabel_of_nonneg (le_of_not_gt hb)]
    simpa only [abs_of_nonneg (le_of_not_gt hb)] using hm

/-- A square west of the line `x = c_x - 1/2` has its marker in the open western
half-plane. -/
theorem west_cap_marker_cos_neg {t a b cx : ℝ} (hc : ContainedChart a |b|)
    (hx : cx < 1 / 2)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → p.1 ≤ cx - 1 / 2) :
    Real.cos (liftedMarker t a b) < 0 := by
  have hm := hcap _ (marker_point_mem hc)
  dsimp only at hm
  linarith

/-- For `c_x < 1/2`, a square whose phase is within `π/4` of `0` is not west of
the line `x = c_x - 1/2`. -/
theorem no_west_cap_in_east_quadrant {t a b cx : ℝ}
    (hc : ContainedChart a |b|) (ht : |t| ≤ Real.pi / 4) (hx : cx < 1 / 2)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → p.1 ≤ cx - 1 / 2) : False := by
  have hm := liftedMarker_bounds (t := t) hc.seven_admissible
  have ht' := abs_le.mp ht
  have hdom : liftedMarker t a b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos := Real.cos_nonneg_of_mem_Icc hdom
  linarith [west_cap_marker_cos_neg hc hx hcap]

end SquaresInCircles.Six.Normalization
