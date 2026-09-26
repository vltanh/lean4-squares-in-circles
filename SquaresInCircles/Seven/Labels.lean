import SquaresInCircles.Common.ElementaryTrig
import SquaresInCircles.Common.Charts

/-!
# States, labels and markers

The state of an exterior square is its pair of offsets `(a, u)` of the disk
centre, larger first. Its label, the least of an axial, a side and a capped
term, is the angle from the chart phase to the marker.
-/
noncomputable section
namespace SquaresInCircles.Seven

def targetSq : ℝ := 13 / 4
def gap : ℝ := Real.pi / 3
def axial (u : ℝ) : ℝ := 5 * u / 4
def side (a u : ℝ) : ℝ := Real.pi / 6 + (u - 1/2) / 3 + 3 * (1-a) / 4
def label (a u : ℝ) : ℝ := min (min (axial u) (side a u)) (Real.pi / 4)
def remainder (a u : ℝ) : ℝ := 4 - 3*a - 2*u

/-- An admissible state: `1/2 ≤ a`, `0 ≤ u ≤ a` and `φ(a, u) ≤ 13/4`. -/
structure Admissible (a u : ℝ) : Prop where
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  half_le : 1/2 ≤ a
  phi_le : phi a u ≤ targetSq

lemma remainder_identity (a u : ℝ) :
    remainder a u = (a-1)^2 + (u-1/2)^2 + targetSq - phi a u := by
  unfold remainder targetSq phi
  ring

lemma side_identity_transverse (a u : ℝ) :
    side a u = Real.pi/6 + (5/6)*(u-1/2) + remainder a u/4 := by
  unfold side remainder
  ring

lemma side_identity_radial (a u : ℝ) :
    side a u = Real.pi/6 - (5/4)*(a-1) - remainder a u/6 := by
  unfold side remainder
  ring

namespace Admissible
variable {a u : ℝ} (h : Admissible a u)
include h

lemma a_nonneg : 0 ≤ a := by linarith [h.half_le]
lemma slack_nonneg : 0 ≤ targetSq - phi a u := sub_nonneg.mpr h.phi_le

lemma remainder_nonneg : 0 ≤ remainder a u := by
  rw [remainder_identity]
  linarith [sq_nonneg (a-1), sq_nonneg (u-1/2), h.slack_nonneg]

lemma tangent : 3*a + 2*u ≤ 4 := by
  have hw := h.remainder_nonneg
  dsimp [remainder] at hw
  linarith

lemma a_le_sqrt_three_sub_half : a ≤ Real.sqrt 3 - 1/2 := by
  have hp := h.phi_le
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  dsimp [phi, targetSq] at hp
  nlinarith [h.u_nonneg, h.half_le, sq_nonneg u]

lemma a_lt_five_fourths : a < 5/4 := by
  nlinarith [h.a_le_sqrt_three_sub_half, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg 3]

lemma sum_lt : a+u < 31/20 := by
  have hp := h.phi_le
  dsimp [phi, targetSq] at hp
  nlinarith [h.u_nonneg, h.half_le, sq_nonneg (a-u)]

lemma u_lt : u < 31/40 := by linarith [h.sum_lt, h.u_le]

lemma side_pos : 0 < side a u := by
  have ha := h.a_lt_five_fourths
  have hp := Real.pi_gt_d2
  dsimp [side]
  linarith [h.u_nonneg]

lemma label_nonneg : 0 ≤ label a u :=
  le_min (le_min (by dsimp [axial]; linarith [h.u_nonneg]) h.side_pos.le) (by positivity)

omit h in
lemma label_le_axial (_h : Admissible a u) : label a u ≤ axial u :=
  (min_le_left _ _).trans (min_le_left _ _)

omit h in
lemma label_le_side (_h : Admissible a u) : label a u ≤ side a u :=
  (min_le_left _ _).trans (min_le_right _ _)

omit h in
lemma label_le_quarter (_h : Admissible a u) : label a u ≤ Real.pi/4 := min_le_right _ _

/-- The label lies in `[0, π/4]`. -/
lemma label_mem : 0 ≤ label a u ∧ label a u ≤ Real.pi/4 :=
  ⟨h.label_nonneg, h.label_le_quarter⟩

lemma label_zero_iff : label a u = 0 ↔ u = 0 := by
  constructor
  · intro hl
    by_contra hu
    have hu' : 0 < u := lt_of_le_of_ne h.u_nonneg (Ne.symm hu)
    have hp : 0 < label a u :=
      lt_min (lt_min (by dsimp [axial]; linarith) h.side_pos) (by positivity)
    exact hp.ne' hl
  · rintro rfl
    exact le_antisymm (by simpa [axial] using h.label_le_axial) h.label_nonneg

lemma radial_label_bound : a ≤ 1 + 2*Real.pi/15 - (4/5)*label a u := by
  have ht := h.label_le_side
  rw [side_identity_radial] at ht
  linarith [h.remainder_nonneg]

omit h in
/-- The label is one of its three terms. -/
lemma selected (_h : Admissible a u) :
    label a u = axial u ∨ label a u = side a u ∨ label a u = Real.pi/4 := by
  unfold label
  rcases min_choice (min (axial u) (side a u)) (Real.pi/4) with h | h <;> rw [h]
  · rcases min_choice (axial u) (side a u) with h' | h' <;> simp [h']
  · simp

end Admissible

lemma side_selected_label_gt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : (9 : ℝ)/25 < label a u := by
  let t := label a u
  have ht0 : 0 ≤ t := h.label_nonneg
  have htu : (4/5)*t ≤ u := by
    have ht := h.label_le_axial
    dsimp [axial] at ht
    dsimp [t]
    linarith
  have he : 9*a-4*u = 2*Real.pi+7-12*t := by
    dsimp [t] at *
    rw [hsel]
    dsimp [side]
    ring
  by_contra hn
  have ht1 : t ≤ 9/25 := le_of_not_gt hn
  have ha : 332/225-(44/45)*t < a := by linarith [Real.pi_gt_d2]
  have hp := h.phi_le
  dsimp [phi,targetSq] at hp
  have hsqA := sq_nonneg (a-(332/225-(44/45)*t))
  have hsqU := sq_nonneg (u-(4/5)*t)
  have hlinA := mul_nonneg
    (show 0 ≤ a-(332/225-(44/45)*t) by linarith)
    (show 0 ≤ 2*(332/225-(44/45)*t)+1 by linarith)
  have hlinU := mul_nonneg
    (show 0 ≤ u-(4/5)*t by linarith)
    (show 0 ≤ 2*(4/5)*t+1 by linarith)
  have hquad := mul_nonneg (show 0 ≤ 9/25-t by linarith)
    (show 0 ≤ 139744/50625-(3232/2025)*(t+9/25) by linarith)
  linarith

lemma side_selected_a_lt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : a < 9/8 := by
  have hl := side_selected_label_gt h hsel
  have hp := h.phi_le
  rw [hsel] at hl
  dsimp [side] at hl
  dsimp [phi, targetSq] at hp
  by_contra hn
  linarith [Real.pi_lt_d2, sq_nonneg (u-2862/10000), sq_nonneg (a-9/8)]

lemma side_selected_a_gt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : (7 : ℝ)/10 < a := by
  have ht := h.label_le_axial
  have hq := h.label_le_quarter
  rw [hsel] at ht hq
  dsimp [side,axial] at ht hq
  linarith [pi_lt_22_over_7]

lemma axial_tie_line {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = axial u) : 9*a+11*u ≤ 2*Real.pi+7 := by
  have hh := h.label_le_side
  rw [hsel] at hh
  dsimp [side,axial] at hh
  linarith

lemma axial_sum_lt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = axial u) : a+u < (113 : ℝ)/80 := by
  have ht := axial_tie_line h hsel
  by_contra hn
  have hu : u < 23/80 := by linarith [pi_lt_22_over_7]
  have hp := h.phi_le
  dsimp [phi,targetSq] at hp
  linarith [sq_nonneg (a-9/8),sq_nonneg (u-23/80)]

/-- A side label above `π/6` costs a remainder quadratic in the excess. -/
lemma side_remainder_quadratic {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) :
    (9/5)*(label a u-Real.pi/6)^2 ≤ remainder a u := by
  let D := label a u-Real.pi/6
  let W := remainder a u
  have hW : 0 ≤ W := h.remainder_nonneg
  have hD : D ≤ 4/15 := by
    have hh := h.label_le_quarter
    dsimp [D]
    linarith [pi_lt_22_over_7]
  have hx : a-1 = -(4/5)*D-(2/15)*W := by
    have hh := side_identity_radial a u
    rw [← hsel] at hh
    dsimp [D,W]
    linarith
  have hy : u-1/2 = (6/5)*D-(3/10)*W := by
    have hh := side_identity_transverse a u
    rw [← hsel] at hh
    dsimp [D,W]
    linarith
  have hs : (a-1)^2+(u-1/2)^2 ≤ W := by
    have hh := remainder_identity a u
    have hp := h.slack_nonneg
    dsimp [W]
    linarith
  have hid : (a-1)^2+(u-1/2)^2 =
      (52/25)*D^2-(38/75)*D*W+(97/900)*W^2 := by
    rw [hx,hy]
    ring
  have hprod := mul_nonneg hW (show 0 ≤ 4/15-D by linarith)
  change (9/5)*D^2 ≤ W
  linarith [sq_nonneg W,sq_nonneg D]

/-- The marker in an existing square chart. Reflections are not lost. -/
def chartMarker {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (label C.a C.b)

lemma chart_admissible {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hp : phi (alpha S o) (beta S o) ≤ targetSq) : Admissible C.a C.b :=
  ⟨C.nonneg.2, hsort, C.exterior hsort hout, chart_phi C hp⟩

end SquaresInCircles.Seven
