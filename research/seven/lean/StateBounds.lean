import research.seven.lean.Basic
import SquaresInCircles.Seven.Labels

/-! M: independent replacements for the three tuned state inequalities. -/
noncomputable section
namespace SquaresInCircles.Seven.Human

lemma state_disk {a u : ℝ} (h : Admissible a u) :
    (a+1/2)^2+(u+1/2)^2 ≤ (13 : ℝ)/4 := by
  simpa only [phi, targetSq] using h.phi_le

lemma side_line {a u : ℝ} (hs : label a u = side a u) :
    9*a-4*u = 2*Real.pi+7-12*label a u := by
  rw [hs]
  unfold side
  ring

lemma axial_line {a u : ℝ} (h : Admissible a u)
    (hs : label a u = axial u) : 9*a+11*u ≤ 2*Real.pi+7 := by
  have hl := h.label_le_side
  rw [hs] at hl
  dsimp [axial,side] at hl
  linarith

/-- The separating direction is (2,1); its norm is sqrt(5). -/
lemma state_projection_2_1 {a u : ℝ} (h : Admissible a u) :
    2*a+u < (38 : ℝ)/15 := by
  have hp := disk_dot_sq (p := (2 : ℝ)) (q := (1 : ℝ)) (state_disk h)
  by_contra hn
  have hl : (38 : ℝ)/15 ≤ 2*a+u := le_of_not_gt hn
  nlinarith [sq_nonneg (2*a+u-38/15)]

lemma side_selected_label_gt {a u : ℝ} (h : Admissible a u)
    (hs : label a u = side a u) : (9 : ℝ)/25 < label a u := by
  have hproj := state_projection_2_1 h
  have hline := side_line hs
  have hu := h.label_le_axial
  dsimp [axial] at hu
  by_contra hn
  have ht : label a u ≤ (9 : ℝ)/25 := le_of_not_gt hn
  linarith [pi_lower]

lemma side_selected_a_lt {a u : ℝ} (h : Admissible a u)
    (hs : label a u = side a u) : a < (9 : ℝ)/8 := by
  have ht := side_selected_label_gt h hs
  have he := side_line hs
  have hp := state_disk h
  by_contra hn
  have ha : (9 : ℝ)/8 ≤ a := le_of_not_gt hn
  have hu : (9 : ℝ)/32 < u := by linarith [pi_upper]
  have hx : (13/8 : ℝ)^2 ≤ (a+1/2)^2 := by nlinarith
  have hy : (25/32 : ℝ)^2 < (u+1/2)^2 := by nlinarith
  nlinarith

lemma axial_sum_lt {a u : ℝ} (h : Admissible a u)
    (hs : label a u = axial u) : a+u < (113 : ℝ)/80 := by
  have hl := axial_line h hs
  have hp := state_disk h
  by_contra hn
  have hsum : (113 : ℝ)/80 ≤ a+u := le_of_not_gt hn
  have hu : u < (23 : ℝ)/80 := by linarith [pi_upper]
  let v : ℝ := 23/80-u
  have hv : 0 < v := by dsimp [v]; linarith
  have ha : 9/8+v ≤ a := by dsimp [v]; linarith
  have hx : (13/8+v)^2 ≤ (a+1/2)^2 := by nlinarith
  have hy : u+1/2 = 63/80-v := by dsimp [v]; ring
  rw [hy] at hp
  have hid : (13/8+v)^2+(63/80-v)^2 =
      (13 : ℝ)/4+69/6400+(67/40)*v+2*v^2 := by ring
  nlinarith [sq_nonneg v]

/-- The same geometric slack estimate used by the inward-circle proof. -/
lemma side_remainder_quadratic {a u : ℝ} (h : Admissible a u)
    (hs : label a u = side a u) :
    (9/5 : ℝ)*(label a u-Real.pi/6)^2 ≤ remainder a u := by
  let D := label a u-Real.pi/6
  let W := remainder a u
  have hW : 0 ≤ W := h.remainder_nonneg
  have hD : D ≤ (4 : ℝ)/15 := by
    dsimp [D]
    linarith [h.label_le_quarter,pi_upper]
  have hx : a-1 = -(4/5)*D-(2/15)*W := by
    have he := side_identity_radial a u
    rw [← hs] at he
    dsimp [D,W]
    linarith
  have hy : u-1/2 = (6/5)*D-(3/10)*W := by
    have he := side_identity_transverse a u
    rw [← hs] at he
    dsimp [D,W]
    linarith
  have hrad : (a-1)^2+(u-1/2)^2 ≤ W := by
    have he := remainder_identity a u
    dsimp [W]
    linarith [h.slack_nonneg]
  have hid : (a-1)^2+(u-1/2)^2 =
      (52/25)*D^2-(38/75)*D*W+(97/900)*W^2 := by
    rw [hx,hy]
    ring
  have hm := mul_nonneg hW (show 0 ≤ 4/15-D by linarith)
  change (9/5)*D^2 ≤ W
  nlinarith [sq_nonneg W,sq_nonneg D]

end SquaresInCircles.Seven.Human
