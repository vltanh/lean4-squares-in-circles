import SquaresInCircles.Six.Analytic.SecondaryReduction
import SquaresInCircles.Six.Analytic.SecondaryGapPolynomial

/-!
# A one-radian gap for a genuine D-sourced west edge

The old quarter-turn restriction is sharpened by a single quadratic
obstruction. The actual W central separator is retained: OWN gives the radial
profile directly; cardinal W gives the same weaker scalar profile when its
signed transverse coordinate is negative. A nonnegative transverse coordinate
is excluded by the elementary radial estimate. No candidate edge is assumed.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma west_synthetic_own {R : ℝ} (P : NormalizedPacking R) {v : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 1/2) (hp : P.phase 2=Real.pi-v)
    (hb : P.transverse 2 ≤ 0) :
    0 ≤ centralMargin .own (Real.pi-v) (P.radial 2) (P.transverse 2) c0 0 := by
  have hcos : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hcos1 : 0 ≤ 1-Real.cos v := sub_nonneg.mpr (Real.cos_le_one v)
  cases hbit : P.ownBits 2
  · have hcard := P.cardinal_separator 2 hbit
    change 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 at hcard
    rw [hp] at hcard
    have hA := mul_nonneg
      (show 0 ≤ P.radial 2-1/2 by linarith [(P.contained 2).half_le]) hcos1
    have hZ := mul_nonneg (show 0 ≤ 1/2-c0 by linarith [c0_lt_23_200]) hcos1
    have hB := mul_nonpos_of_nonpos_of_nonneg hb hsin
    simp only [centralMargin,centralNormal,centerX,angularWidth,Real.cos_pi_sub,
      Real.sin_pi_sub,abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin,
      zero_mul,add_zero] at hcard ⊢
    nlinarith only [hcard,hA,hZ,hB,P.box.1.2]
  · have hown := P.own_separator 2 hbit
    rw [hp] at hown
    have hX := mul_nonneg (sub_nonneg.mpr P.box.1.2) hcos
    have hY := mul_nonneg P.box.2.1 hsin
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,
      Real.sin_pi_sub,abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin,
      zero_mul,add_zero] at hown ⊢
    nlinarith only [hown,hX,hY]

/-- Every actual D-sourced W/D separator has phase gap strictly greater than 1,
for either canonical W bit. This uses only analytic normalization consequences. -/
theorem DW_Dsecondary_gap_gt_one {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    1 < P.phase 3-P.phase 2 := by
  have hquarter := DW_Dsecondary_gap_gt_quarter P hsep
  by_contra! hsmall
  let q := P.phase 3-P.phase 2
  let v := -P.helperAngle 2
  let d := P.diagonalAngle
  have hq : Real.pi/4 ≤ q ∧ q ≤ 1 := ⟨hquarter.le,hsmall⟩
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2]
    dsimp [v]
    ring
  have hsum : q=d+v := by dsimp [q]; rw [hDphase,hWphase]; ring
  have hd : 1/2 < d ∧ d ≤ Real.pi/4 :=
    ⟨normalized_diagonal_gt_half P,P.diagonal_angle_range.2⟩
  have hv : 0 ≤ v ∧ v ≤ 1/2 := by
    constructor <;> linarith [hq.1,hq.2,hd.1,hd.2,hsum]
  have hdiag : P.transverse 3 ≤ 31/100-(17/100)*d :=
    (le_abs_self _).trans (normalized_diagonal_transverse_affine P).le
  have hdiag0 : P.transverse 3 ≤ 9/40 :=
    (le_abs_self _).trans (normalized_diagonal_transverse_lt_nine_fortieths P).le
  have hproj : 1/2+angularWidth q ≤
      P.radial 2*Real.sin q-P.transverse 2*Real.cos q+P.transverse 3 := by
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
    rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right] at hsep
    dsimp [q]
    linarith only [hsep]
  by_cases hb : 0 ≤ P.transverse 2
  · have hbad := west_secondary_nonnegative_transverse (P.contained 2).a_le_rho0
      hb hdiag0 hq
    linarith
  · have hsynthetic := west_synthetic_own P hv hWphase (lt_of_not_ge hb).le
    have hwing := own_west_transverse_small_angle (P.contained 2)
      (le_rfl : c0 ≤ c0) (by norm_num : (0:ℝ) ≤ 0) hv hsynthetic
    have hbad := west_secondary_profile_obstruction (P.contained 2) hv.1 hq hsum
      hwing.le hdiag
    linarith

lemma MissingWestWing.one_radian_gap {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : 1 < P.phase 3-P.phase 2 :=
  DW_Dsecondary_gap_gt_one P h.from_diagonal

lemma MissingWestWing.sharper_phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.helperAngle 2 < P.diagonalAngle-1 := by
  have hg := h.one_radian_gap
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [P.phase_from_deviation 2,hDphase] at hg
  linarith

/-- A simple rational form of the strict phase restriction. -/
lemma MissingWestWing.west_lt_neg_three_fourteenths {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.helperAngle 2 < -3/14 := by
  have hg := h.sharper_phase_wall
  linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]

/-- A cardinal west mixed case must also lie in the upper diagonal strip. -/
lemma MissingWestWing.cardinal_diagonal_gt_three_fifths {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hW : P.ownBits 2=false) : 3/5 < P.diagonalAngle := by
  have hg := h.sharper_phase_wall
  have hw := (abs_lt.mp (P.cardinal_angle 2 hW)).1
  linarith

/-- The larger closed region now has its actual candidate wing inequality. -/
theorem DW_candidate_of_one_radian_wall {R : ℝ} (P : NormalizedPacking R)
    (hwall : P.diagonalAngle-1 ≤ P.helperAngle 2) :
    Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) := by
  by_contra hnot
  have h := (missing_west_of_failure P hnot).sharper_phase_wall
  linarith

end SquaresInCircles.Six.Analytic
