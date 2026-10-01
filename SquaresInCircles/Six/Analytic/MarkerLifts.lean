import SquaresInCircles.Six.Analytic.NorthMarker

/-!
# Lifted markers of the squares above and below C

A square at the phase `t` with centre `(a, b)` in its frame has the lifted
marker `t ± label a |b|`, with the sign of `b`, and the label is at most
`(5/4)|b|`. At the phases `π/2 + t` and `-π/2 + t` with `|t| ≤ π/4` the lift
lies in `[0, π]` and `[-π, 0]`. Such a square separated from C along the west
side of C has its marker in the left half-plane, beyond `π/2` or `-π/2`. A
square below C separated from C along its negative secondary axis has an
offset `|b| ≥ 1/2`, and its marker is at most `-π/4 - 5/8`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma label_signed_lower {a b : ℝ} (h : ContainedChart a |b|) :
    -(5/4)*|b| ≤ signedLabel a b := by
  have hh := (abs_le.mp (signedLabel_bounds h.seven_admissible).2).1
  linarith

lemma label_signed_upper {a b : ℝ} (h : ContainedChart a |b|) :
    signedLabel a b ≤ (5/4)*|b| := by
  have hh := (abs_le.mp (signedLabel_bounds h.seven_admissible).2).2
  linarith

lemma north_lift_range {a b t : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) :
    0 ≤ liftedMarker (Real.pi/2+t) a b ∧
      liftedMarker (Real.pi/2+t) a b ≤ Real.pi := by
  have hm := liftedMarker_bounds (t := Real.pi/2+t) h.seven_admissible
  have hh := abs_le.mp ht
  constructor <;> linarith [hm.1,hm.2,hh.1,hh.2]

lemma south_lift_range {a b t : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) :
    -Real.pi ≤ liftedMarker (-Real.pi/2+t) a b ∧
      liftedMarker (-Real.pi/2+t) a b ≤ 0 := by
  have hm := liftedMarker_bounds (t := -Real.pi/2+t) h.seven_admissible
  have hh := abs_le.mp ht
  constructor <;> linarith [hm.1,hm.2,hh.1,hh.2]

lemma north_west_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : x < 1/2)
    (hw : 0 ≤ centralMargin .west (Real.pi/2+t) a b x y) :
    Real.pi/2 < liftedMarker (Real.pi/2+t) a b := by
  have hn := west_cap_marker_cos_neg h hx (west_margin_cap hw)
  have hr := north_lift_range h ht
  by_contra! hm
  have hc := Real.cos_nonneg_of_mem_Icc
    (show liftedMarker (Real.pi/2+t) a b ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hr.1,Real.pi_pos])
  linarith

lemma south_west_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : x < 1/2)
    (hw : 0 ≤ centralMargin .west (-Real.pi/2+t) a b x y) :
    liftedMarker (-Real.pi/2+t) a b < -Real.pi/2 := by
  have hn := west_cap_marker_cos_neg h hx (west_margin_cap hw)
  have hr := south_lift_range h ht
  by_contra! hm
  have hc := Real.cos_nonneg_of_mem_Icc
    (show liftedMarker (-Real.pi/2+t) a b ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hr.2,Real.pi_pos])
  linarith

lemma south_secondary_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : x ≤ 1/2) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hm : 0 ≤ centralMargin .secMinus (-Real.pi/2+t) a b x y) :
    liftedMarker (-Real.pi/2+t) a b ≤ -Real.pi/4-5/8 := by
  rw [south_secMinus] at hm
  have hoff := outward_secondary_offset (b := -b) ht hx hy0 hy1 (by linarith)
  have hb : b < 0 := by linarith [hoff.1]
  have hu : 1/2 ≤ |b| := by rw [abs_of_neg hb]; exact hoff.1
  have hl := h.large_offset_label hu
  have ht1 := (abs_le.mp ht).2
  rw [liftedMarker,signedLabel_of_neg hb]
  linarith

lemma sin_nonneg_octant {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.pi/4) : 0 ≤ Real.sin t :=
  Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])

lemma sin_nonpos_octant {t : ℝ} (ht0 : t ≤ 0) (ht : -Real.pi/4 ≤ t) : Real.sin t ≤ 0 := by
  have h := sin_nonneg_octant (t := -t) (by linarith) (by linarith)
  rw [Real.sin_neg] at h
  linarith

/-- The containment of a chart, with `|a|` in place of `a`. -/
lemma chart_corner {a b : ℝ} (h : ContainedChart a |b|) :
    (|a|+1/2)^2+(|b|+1/2)^2 ≤ Q0 := by
  simpa only [abs_of_nonneg (show 0 ≤ a by linarith [h.half_le])] using h.containment

lemma half_ge_core : coreRadius ≤ (1:ℝ)/2 := by
  dsimp [coreRadius]
  linarith [rho0_gt_one]

end SquaresInCircles.Six.Analytic
