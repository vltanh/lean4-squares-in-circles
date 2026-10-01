import SquaresInCircles.Six.Analytic.CardinalWestOwnSouth.Support
import SquaresInCircles.Six.Analytic.OwnWingFrontier
import SquaresInCircles.Six.Analytic.CanonicalSouthSign

/-!
# A missing west wing must have OWN W

For cardinal W and OWN S, use the scalar change of variables
 (v,s,d)=(old s,-old w,pi/2-old d),
 swap the two central coordinates, and negate each transverse coordinate.
This is not a reflection of NormalizedPacking: the new diagonal window is
proved explicitly from old d>3/5 and old d<=pi/4. The old one-radian D-sourced
west gap gives the new d-s<4/7. All five reflected inequalities are derived
below from the original actual witnesses.
The both-cardinal case was already excluded. No finite classification is used.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CardinalWestOwnSouth
open Normalization

private lemma cos_pi_add' (x : ℝ) : Real.cos (Real.pi+x) = -Real.cos x := by
  rw [add_comm,Real.cos_add_pi]

private lemma sin_pi_add' (x : ℝ) : Real.sin (Real.pi+x) = -Real.sin x := by
  rw [add_comm,Real.sin_add_pi]

theorem not_missing_west {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=true) : ¬ MissingWestWing P := by
  intro hmissing
  let v := P.helperAngle 4
  let s := -P.helperAngle 2
  let d := Real.pi/2-P.diagonalAngle
  have hv : 0 ≤ v ∧ v ≤ 2/3 :=
    ⟨(canonical_own_south_positive P hS).le,P.helper_windows.2.2.2.2.le⟩
  have hgap := hmissing.diagonal_minus_west_gt_one
  have hdold := hmissing.diagonal_gt_three_fifths
  have hd : 157/200 ≤ d ∧ d ≤ 34/35 := by
    dsimp [d]
    constructor <;> linarith [P.diagonal_angle_range.2,Real.pi_gt_d2,Real.pi_lt_d4]
  have hs : 0 ≤ s ∧ s ≤ 2/5 := by
    have hc := abs_lt.mp (P.cardinal_angle 2 hW)
    dsimp [s]
    constructor <;> linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]
  have hr : 0 ≤ d-s ∧ d-s ≤ 4/7 := by
    constructor
    · linarith [hs.2,hd.1]
    · dsimp [d,s]
      linarith [hgap,Real.pi_lt_d4]
  have hWphase : P.phase 2=Real.pi-s := by
    have h : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
    rw [h]
    dsimp [s]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+v := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+(Real.pi/2-d) := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 4+P.center.2*Real.cos v-P.center.1*Real.sin v := by
    have h := P.own_separator 4 hS
    rw [hSphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,add_zero,zero_sub,neg_neg,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCS : 1/2+angularWidth s ≤
      P.radial 2*Real.cos s-(-P.transverse 2)*Real.sin s+P.center.1 := by
    have h := P.cardinal_separator 2 hW
    change 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 at h
    rw [hWphase] at h
    simp only [centralMargin,Normalization.centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
      abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.2*Real.cos d+P.center.1*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase] at h
    simp only [centralMargin,centralNormal,angularWidth,cos_pi_add',sin_pi_add',
      Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (d+v) ≤
      P.radial 3*Real.sin (d+v)+(-P.transverse 3)*Real.cos (d+v)-(-P.transverse 4) := by
    have h := hmissing.south_wing
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_right,
      show (3*Real.pi/2+v)-(Real.pi+(Real.pi/2-d))=d+v by ring] at h
    nlinarith only [h]
  have hDS : 1/2+angularWidth (d-s) ≤
      P.radial 2*Real.cos (d-s)+(-P.transverse 2)*Real.sin (d-s)-(-P.transverse 3) := by
    have h := hmissing.from_diagonal
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_right,
      show (Real.pi+(Real.pi/2-d))-(Real.pi-s)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    nlinarith only [h]
  exact scalar_impossible hv hs hd hr
    (by simpa only [abs_neg] using P.contained 4)
    (by simpa only [abs_neg] using P.contained 3)
    (by simpa only [abs_neg] using P.contained 2)
    (P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    ⟨P.box.1.1,P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2⟩ hCW hCS hCD hWD hDS

end SquaresInCircles.Six.Analytic.CardinalWestOwnSouth

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- Both S bits are covered; no missing-west configuration has cardinal W. -/
theorem not_missing_west_of_cardinal_west {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) : ¬ MissingWestWing P := by
  intro h
  cases hS : P.ownBits 4
  · exact MixedCardinalWest.not_missing_west P hW hS h
  · exact CardinalWestOwnSouth.not_missing_west P hW hS h

lemma MissingWestWing.west_own {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.ownBits 2=true := by
  cases hW : P.ownBits 2
  · exact False.elim (not_missing_west_of_cardinal_west P hW h)
  · rfl

end SquaresInCircles.Six.Analytic
