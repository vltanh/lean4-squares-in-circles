import research.seven.lean.StateBounds
import SquaresInCircles.Seven.LabelBoundary

/-!
L: locate the chosen circle/line intersection without J_bounds,
transition_bounds, transition_coarse, or rd_bounds from production.
Only the production definitions are used below.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human
open Boundary

lemma transition_M_bounds : (23 : ℝ) < M ∧ M < 24 := by
  dsimp [M]
  constructor <;> linarith [pi_lower,pi_upper]

lemma transition_J_sq : J^2 = 202*(13/4 : ℝ)-M^2 := by
  have hm := transition_M_bounds
  have hr : 0 ≤ 202*targetSq-M^2 := by
    dsimp [targetSq]
    nlinarith [hm.1,hm.2]
  simpa only [J,targetSq] using Real.sq_sqrt hr

lemma transition_J_coarse : (8 : ℝ) < J ∧ J < 12 := by
  have hm := transition_M_bounds
  have hs := transition_J_sq
  have hn : 0 ≤ J := Real.sqrt_nonneg _
  constructor <;> nlinarith [hm.1,hm.2]

lemma transition_coordinates_positive : 0 < X0 ∧ 0 < Y0 ∧ Y0 < 1 := by
  have hm := transition_M_bounds
  have hj := transition_J_coarse
  dsimp [X0,Y0]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma transition_circle_exact : X0^2+Y0^2 = (13 : ℝ)/4 := by
  have hj := transition_J_sq
  dsimp [X0,Y0]
  nlinarith

lemma transition_line_exact : 9*X0+11*Y0 = M := by
  dsimp [X0,Y0]
  ring

lemma transition_state_line : 9*a0+11*u0 = 2*Real.pi+7 := by
  have he := transition_line_exact
  dsimp [a0,u0,M] at *
  linarith

def lineCircle (y : ℝ) : ℝ := 9*Real.sqrt (13/4-y^2)+11*y

lemma circle_root_data {y : ℝ} (hy : 0 ≤ y ∧ y ≤ 1) :
    (Real.sqrt (13/4-y^2))^2 = 13/4-y^2 ∧
    (3 : ℝ)/2 ≤ Real.sqrt (13/4-y^2) := by
  have hr : 0 ≤ (13 : ℝ)/4-y^2 := by nlinarith
  have hs := Real.sq_sqrt hr
  exact ⟨hs,by nlinarith [Real.sqrt_nonneg ((13 : ℝ)/4-y^2)]⟩

/-- The radical decreases at rate at most 2/3, while the line rises at rate 11. -/
lemma lineCircle_growth {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) (hab : a ≤ b) :
    5*(b-a) ≤ lineCircle b-lineCircle a := by
  let A := Real.sqrt (13/4-a^2)
  let B := Real.sqrt (13/4-b^2)
  have hA := circle_root_data ha
  have hB := circle_root_data hb
  change A^2=13/4-a^2 ∧ (3 : ℝ)/2 ≤ A at hA
  change B^2=13/4-b^2 ∧ (3 : ℝ)/2 ≤ B at hB
  have hBA : B ≤ A := by
    dsimp [A,B]
    apply Real.sqrt_le_sqrt
    nlinarith [ha.1,hb.1]
  have hm := mul_nonneg (sub_nonneg.mpr hBA)
    (show 0 ≤ A+B-3 by linarith [hA.2,hB.2])
  have hn := mul_nonneg (sub_nonneg.mpr hab)
    (show 0 ≤ 2-a-b by linarith [ha.2,hb.2])
  have hrad : 3*(A-B) ≤ 2*(b-a) := by nlinarith [hA.1,hB.1]
  change 5*(b-a) ≤ (9*B+11*b)-(9*A+11*a)
  linarith

lemma lineCircle_mono : MonotoneOn lineCircle (Icc 0 1) := by
  intro a ha b hb hab
  have hh := lineCircle_growth ha hb hab
  linarith

lemma lineCircle_at_transition : lineCircle Y0 = M := by
  have hp := transition_coordinates_positive
  have hs := transition_circle_exact
  have hr := circle_root_data ⟨hp.2.1.le,hp.2.2.le⟩
  have he : Real.sqrt (13/4-Y0^2) = X0 := by nlinarith [hp.1]
  dsimp [lineCircle]
  rw [he]
  exact transition_line_exact

lemma lower_circle_comparison : lineCircle (79/100) < (582 : ℝ)/25 := by
  have hs := circle_root_data (y := (79/100 : ℝ)) (by constructor <;> norm_num)
  have hr : Real.sqrt (13/4-(79/100 : ℝ)^2) < 1459/900 := by
    nlinarith [Real.sqrt_nonneg ((13 : ℝ)/4-(79/100 : ℝ)^2)]
  dsimp [lineCircle]
  linarith

lemma upper_circle_comparison : (1397 : ℝ)/60 < lineCircle (281/355) := by
  have hs := circle_root_data (y := (281/355 : ℝ)) (by constructor <;> norm_num)
  have hr : (1397/60-11*(281/355 : ℝ))/9 <
      Real.sqrt (13/4-(281/355 : ℝ)^2) := by
    nlinarith [hs.1,hs.2]
  dsimp [lineCircle]
  linarith

lemma transition_u_bounds : (29 : ℝ)/100 < u0 ∧ u0 < 207/710 := by
  have hp := transition_coordinates_positive
  have he := lineCircle_at_transition
  constructor
  · by_contra hn
    have hu : Y0 ≤ (79 : ℝ)/100 := by
      dsimp [u0] at hn
      linarith
    have hh := lineCircle_mono ⟨hp.2.1.le,hp.2.2.le⟩
      (show (79/100 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hu
    have hc := lower_circle_comparison
    rw [he] at hh
    dsimp [M] at hh
    linarith [pi_lower]
  · by_contra hn
    have hu : (281 : ℝ)/355 ≤ Y0 := by
      dsimp [u0] at hn
      linarith
    have hh := lineCircle_mono
      (show (281/355 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
      ⟨hp.2.1.le,hp.2.2.le⟩ hu
    have hc := upper_circle_comparison
    rw [he] at hh
    dsimp [M] at hh
    linarith [pi_upper_transition]

lemma transition_xy_bounds :
    (97 : ℝ)/60 < X0 ∧ X0 < 13/8 ∧
    (79 : ℝ)/100 < Y0 ∧ Y0 < 19/24 := by
  have hu := transition_u_bounds
  have hp := transition_coordinates_positive
  have hs := transition_circle_exact
  have hY : (79 : ℝ)/100 < Y0 ∧ Y0 < 19/24 := by
    dsimp [u0] at hu
    constructor <;> linarith
  exact ⟨by nlinarith [hY.2],by nlinarith [hY.1],hY.1,hY.2⟩

lemma transition_coarse_geometric :
    (67 : ℝ)/60 < a0 ∧ a0 < 9/8 ∧
    (29 : ℝ)/100 < u0 ∧ u0 < 7/24 ∧
    (9 : ℝ)/25 < s0 ∧ s0 < 2/5 := by
  have hx := transition_xy_bounds
  have hu := transition_u_bounds
  dsimp [a0,u0,s0] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_radius_coarse : (55 : ℝ)/71 < rd ∧ rd < 31/40 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 13/8 by norm_num)
  have hn := Real.sqrt_nonneg (13/8 : ℝ)
  dsimp [rd]
  constructor <;> nlinarith

lemma diagonal_label_coarse : (627 : ℝ)/800 < td ∧ td < Real.pi/4 := by
  have hr := diagonal_radius_coarse
  dsimp [td]
  constructor <;> linarith [pi_lower,pi_upper]

lemma diagonal_angle_coarse :
    (3 : ℝ)/5 < td+s0-Real.pi/6 ∧ td+s0-Real.pi/6 < 5/8 := by
  have hr := diagonal_radius_coarse
  have hu := transition_u_bounds
  dsimp [td,s0]
  constructor <;> linarith

lemma transition_endpoint_angle :
    (31 : ℝ)/50 < Real.pi/3-td+s0 ∧ Real.pi/3-td+s0 < 2/3 := by
  have hr := diagonal_radius_coarse
  have hu := transition_u_bounds
  dsimp [td,s0]
  constructor <;> linarith [pi_lower,pi_upper_transition]

lemma transition_tangent_reserve : (1 : ℝ)/100 < Y0-(12/25)*X0 := by
  have hx := transition_xy_bounds
  linarith

/-- Locate arbitrary side-selected states relative to the transition. -/
lemma side_state_transition {a u : ℝ} (h : Admissible a u)
    (ht : label a u = side a u) : u0 ≤ u ∧ a ≤ a0 ∧ s0 ≤ label a u := by
  have hdisk := state_disk h
  have hlabel := h.label_le_axial
  rw [ht] at hlabel
  have hline : M ≤ 9*(a+1/2)+11*(u+1/2) := by
    dsimp [side,axial] at hlabel
    dsimp [M]
    linarith
  have hp := transition_coordinates_positive
  have hu0 := transition_u_bounds
  have hcircle := transition_circle_exact
  have hu : u0 ≤ u := by
    by_contra hn
    have hlt : u < u0 := lt_of_not_ge hn
    have hY : 0 ≤ u+1/2 ∧ u+1/2 ≤ 1 := by
      dsimp [u0] at hlt
      constructor <;> linarith [h.u_nonneg,hp.2.2]
    have hroot := circle_root_data hY
    have ha : a+1/2 ≤ Real.sqrt (13/4-(u+1/2)^2) := by
      nlinarith [h.half_le,hroot.1,hroot.2]
    have hg := lineCircle_growth hY ⟨hp.2.1.le,hp.2.2.le⟩
      (show u+1/2 ≤ Y0 by dsimp [u0] at hlt; linarith)
    rw [lineCircle_at_transition] at hg
    dsimp [lineCircle,u0] at *
    linarith
  have ha : a ≤ a0 := by
    have hY : Y0 ≤ u+1/2 := by dsimp [u0] at hu; linarith
    have hh := mul_nonneg (sub_nonneg.mpr hY)
      (show 0 ≤ u+1/2+Y0 by linarith [h.u_nonneg,hp.2.1])
    dsimp [a0]
    nlinarith [h.half_le,hp.1]
  refine ⟨hu,ha,?_⟩
  have he := transition_state_line
  rw [ht]
  dsimp [side,s0]
  linarith

lemma side_transition_trade {a u : ℝ} (h : Admissible a u)
    (ht : label a u = side a u) : (12/25 : ℝ)*(u-u0) ≤ a0-a := by
  have hb := side_state_transition h ht
  have hdisk := state_disk h
  have hc := transition_circle_exact
  have hr := transition_tangent_reserve
  have hx := transition_coordinates_positive
  have htan : X0*(a-a0)+Y0*(u-u0) ≤ 0 := by
    dsimp [a0,u0]
    nlinarith [sq_nonneg (a+1/2-X0),sq_nonneg (u+1/2-Y0)]
  have hm := mul_nonneg (sub_nonneg.mpr hb.1)
    (show 0 ≤ Y0-(12/25)*X0 by linarith)
  have hprod : 0 ≤ X0*((a0-a)-(12/25)*(u-u0)) := by nlinarith
  have hnon := nonneg_of_mul_nonneg_left hprod hx.1
  linarith

end SquaresInCircles.Seven.Human
